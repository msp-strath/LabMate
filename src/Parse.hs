{-# LANGUAGE PatternGuards #-}
module Parse where

import Control.Monad
import Control.Applicative
import Control.Arrow (first)

import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as Map

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
reachBind (r, as) k = first (max r) $ foldMap go as
  where
    go a = let ((r, bs), f) = k a
           in (r, map f bs)

newtype Parser a = Parser
  { parser :: (Map Nonce String, Nonce) -> [Tok] ->
    (Reach
    , [(Bwd Tok -- consumed tokens
      , a         -- meaning
      , (Map Nonce String, Nonce) -- updated nonce table and fresh nonce
      , [Tok]     -- remaining tokens
      )]
    )
  }
  deriving (Semigroup, Monoid, Functor)

-- Convention: parsers for meaningful structures do not consume
-- leading or trailing space.

instance Monad Parser where
  return a = Parser $ \ tabn ts -> (Nowhere, [ (B0, a, tabn, ts) ])
  Parser pa >>= k = Parser $ \ tabn ts -> reachBind (pa tabn ts) $ \(az, a, tabn, ts) ->
                    (parser (k a) tabn ts, \(bz, b, tabn, ts) -> (az <> bz, b, tabn, ts))


instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Alternative Parser where
  empty = mempty
  (<|>) = mappend

pws :: Parser a -> Parser (WithSource a)
pws p = Parser $ \ tabn ts -> reachBind (parser p tabn ts) $ \(az, a, tabn@(table, n), ts) ->
         let as = az <>> [] in
         ((Nowhere, [(B0 :< non n, a :<=: (n, Hide as), (Map.insert n (as >>= nonceExpand table) table, n+1), ts)]), id)

-- Parser p is assumed to produce output including the source src passed in
pws' :: Nonce -> Parser a -> Parser (WithSource a)
pws' m p = Parser $ \ tabn ts -> reachBind (parser p tabn ts) $ \(az, a, tabn@(table, n), ts) ->
            let as = non m : az <>> [] in
            ((Nowhere, [(az, a :<=: (n, Hide as), (Map.insert n (as >>= nonceExpand table) table, n+1), ts)]), id)

pwn :: Nonce -> Parser ()
pwn n = Parser $ \ tabn ts -> (Nowhere , [(B0 :< Tok{raw = "", kin = Non n, pos = dump}, (), tabn, ts)])

pblank :: Parser Nonce
pblank = Parser $ \ (tab, n) ts -> (Nowhere, [(B0, n, (Map.insert n "" tab, n+1), ts)])

-- TODO: at some point, we will need to record more provenance in the
-- token sequence

ptok :: (Tok -> Maybe a) -> Parser a
ptok f = Parser $ \ n ts -> (reached ts,) $ case ts of
  t:ts | Just a <- f t -> [(B0 :< t, a, n, ts)]
  _ -> []

peoi :: Parser ()
peoi = Parser $ \ n ts -> (reached ts,) $ case ts of
  [] -> [(B0, (), n, [])]
  _ ->  []

ppeek :: Parser [Tok]
ppeek = Parser $ \ n ts -> (Nowhere, [(B0, ts, n, ts)])


-- The parser p must handle leading and trailing space/junk
pgrp :: (Grouping -> Bool) -> Parser a -> Parser a
pgrp f p = Parser $ \ n ts -> first (max (reached ts)) $ case ts of
 t:ts | Grp g (Hide ss) <- kin t, f g -> reachBind (parser p n ss) $ \(az, a, n, as) ->
          let toks = az <>> [] in
            (,id) . (Nowhere,) $ case as of
              [] -> [(B0 :< t { raw = groupRaw g toks, kin = Grp g (Hide toks) }, a, n, ts)]
              _  -> []
 _ -> (Nowhere, [])


pline :: (Nonce -> Parser a) -> Parser a
pline np = do
  n <- pblank
  many (ptok junkLine)
  pgrp isLine (id <$ pospc <*> np n <* pgreedy (ptok (guard . junk False)) <* pwn n <* pgreedy (ptok (guard . junk True)))
  where
    isLine (Line _) = True
    isLine _ = False
    junk b t = case kin t of -- b tells us whether Ret is junk
      Spc -> True
      Ret -> b
      Grp Comment _ -> True
      Sym | raw t == ";" -> True
      _ -> False
    junkLine t = case kin t of
      Grp (Line _) (Hide ts) | all (junk True) ts -> Just ()
      _ -> Nothing

plink :: Parser a -> Parser a
plink = pline . const

ponespc :: Parser ()
ponespc = ptok (\ t -> guard (kin t == Spc || isComment t))

pspc :: Parser ()
pspc = void ponespc <* pospc

-- We are relying on the lexer combining all consecutive space tokens

-- Optional space
pospc :: Parser ()
pospc = void (pgreedy ponespc)

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

ppercent :: Parser Int -- returns the column of '%'
ppercent = ptok $ \ t -> snd (unhide $ pos t) <$ guard (kin t == Sym && raw t == "%")

prawif :: Kin -> Parser String
prawif k = ptok $ \ t -> raw t <$ guard (kin t == k)

pnom :: Parser String
pnom = ptok $ \ t -> if kin t == Nom then Just (raw t) else Nothing

pcond :: Parser a -> (a -> Parser b) -> Parser b -> Parser b
pcond pc ps pf = Parser $ \ n ts -> case parser pc n ts of
  (r,[]) -> first (max r) $ parser pf n ts
  p ->
    reachBind p $ \(tz, a, n, ts) ->
    (parser (ps a) n ts,) $ \(tz', b, n, ts) ->
    (tz <> tz', b, n, ts)

pgreedy :: Parser a -> Parser [a]
pgreedy p = pcond p
  (\a -> (a:) <$> pgreedy p)
  (pure [])

testparser :: String -> Parser a -> (Reach, [(a, Map Nonce String)])
testparser s p = fmap (\ (a,b,n,c) -> (b, fst n)) <$> parser p (Map.empty, 0) (lexer (T.pack s))
