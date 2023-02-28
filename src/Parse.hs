{-# LANGUAGE PatternGuards #-}
module Parse where

import Control.Monad
import Control.Applicative
import Control.Arrow ((***))

import qualified Data.Text as T

import Bwd
import Hide
import Lex

data Reach = Nowhere  -- the parser has not touched the file
           | Reached Pos (Hide [Tok]) -- has visited the given pos and
                                      -- found the list of toks there
  deriving (Eq, Ord)

instance Show Reach where
  show Nowhere = "Found nothing"
  show (Reached (l,c) (Hide ts)) = "Line " <> show (l + 1)
                                 <> " Col " <> show c
                                 <> "\n" <> take 70 (ts >>= raw)

instance Monoid Reach where
  mempty = Nowhere
  mappend = max

instance Semigroup Reach where
  (<>) = mappend

reached :: [Tok] -> Reach
reached [] = Nowhere
reached tts@(t:_) = Reached (unhide $ pos t) (Hide tts)

reachBind  :: (Reach,[a])
           -> (a -> ((Reach, [b]), b -> c))
           -> (Reach, [c])
reachBind (r, as) k = max r *** id $ foldMap go as
  where
    go a = let ((r, bs), f) = k a
           in (r, map f bs)

newtype Parser a = Parser
  { parser :: [Tok] ->
    (Reach
    , [(Bwd Tok -- consumed tokens
      , a       -- meaning
      , [Tok]   -- remaining tokens
      )]
    )
  }
  deriving (Semigroup, Monoid, Functor)

-- Convention: parsers for meaningful structures do not consume
-- leading or trailing space.

instance Monad Parser where
  return a = Parser $ \ ts -> (Nowhere, [ (B0, a, ts) ])
  Parser pa >>= k = Parser $ \ ts -> reachBind (pa ts) $ \(az, a, ts) ->
                    (parser (k a) ts, \(bz, b, ts) -> (az <> bz, b, ts))


instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Alternative Parser where
  empty = mempty
  (<|>) = mappend

data WithSource a = a :<=: [Tok]

pws :: Parser a -> Parser (WithSource a)
pws p = Parser $ \ ts -> reachBind (parser p ts) $ \(az, a, ts) ->
        ((Nowhere, [(az, a :<=: (az <>> []), ts)]), id)

-- TODO: at some point, we will need to record more provenance in the
-- token sequence

ptok :: (Tok -> Maybe a) -> Parser a
ptok f = Parser $ \ts -> (reached ts,) $ case ts of
  t:ts | Just a <- f t -> [(B0 :< t, a, ts)]
  _ -> []

peoi :: Parser ()
peoi = Parser $ \ ts -> (reached ts,) $ case ts of
  [] -> [(B0, (), [])]
  _ ->  []

ppeek :: Parser [Tok]
ppeek = Parser $ \ ts -> (Nowhere, [(B0, ts, ts)])

pgrp :: (Grouping -> Bool) -> Parser a -> Parser a
pgrp f p = Parser $ \ ts -> (max (reached ts) *** id) $ case ts of
  t:ts | Grp g (Hide ss) <- kin t, f g -> reachBind (parser p ss) $ \(_, a, as) ->
                              (,id) . (Nowhere,) $ case as of
                                [] -> [(B0 :< t, a, ts)]
                                _  -> []
  _ -> (Nowhere, [])


pline :: Parser a -> Parser a
pline p = id <$ many (ptok junkLine)
            <*> pgrp isLine (id <$ pospc <*> p <* many (ptok (guard . junk)))
  where
    isLine (Line _) = True
    isLine _ = False
    junk t = case kin t of
      Spc -> True
      Ret -> True
      Grp Comment _ -> True
      Sym | raw t == ";" -> True
      _ -> False
    junkLine t = case kin t of
      Grp (Line _) (Hide ts) | all junk ts -> Just ()
      _ -> Nothing

ponespc :: Parser ()
ponespc = ptok (\ t -> guard (kin t == Spc || isComment t))

pspc :: Parser ()
pspc = () <$ ponespc <* pospc

-- We are relying on the lexer combining all consecutive space tokens

-- Optional space
pospc :: Parser ()
pospc = () <$ pgreedy ponespc

-- The string s must be in the lexer symbol table
-- Leading and trailing space is consumed => do not use on its own!
punc :: String -> Parser ()
punc = pspcaround . psym

pspcaround :: Parser a -> Parser a
pspcaround p = id <$ pospc <*> p <* pospc

psep1 :: Parser () -> Parser a -> Parser [a]
psep1 sep p = (:) <$> p <*> many (id <$ sep <*> p)

psep0 :: Parser () -> Parser a -> Parser [a]
psep0 sep p = psep1 sep p <|> pure []

pkin :: Kin -> String -> Parser ()
pkin k s = ptok $ \ t -> guard $ Tok {kin = k, raw = s, pos = Hide (0,0)} == t

psym :: String -> Parser ()
psym = pkin Sym

prawif :: Kin -> Parser String
prawif k = ptok $ \ t -> raw t <$ guard (kin t == k)

pnom :: Parser String
pnom = ptok $ \ t -> if kin t == Nom then Just (raw t) else Nothing

pcond :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
pcond pc ps pf = Parser $ \ ts -> case parser pc ts of
  (r,[]) -> max r *** id $ parser pf ts
  p ->
    reachBind p $ \(tz, a, ts) ->
    (parser (ps a) ts,) $ \(tz', b, ts) ->
    (tz <> tz', b, ts)

pgreedy :: Parser a -> Parser [a]
pgreedy p = pcond p
  (\a -> (a:) <$> pgreedy p)
  (pure [])

testparser :: String -> Parser a -> (Reach, [a])
testparser s p = fmap (\ (a,b,c) -> b) <$> parser p (lexer (T.pack s))
