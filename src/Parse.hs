{-# LANGUAGE PatternGuards #-}
module Parse where

import Control.Monad
import Control.Applicative

import Data.Text as T

import Bwd
import Hide
import Lex

newtype Parser a = Parser
  { parser :: [Tok] -> [(Bwd Tok -- consumed tokens
                        , a      -- meaning
                        , [Tok]  -- remaining tokens
                        )]
  }
  deriving (Semigroup, Monoid, Functor)

-- Convention: parsers for meaningful structures do not consume
-- leading or trailing space.

instance Monad Parser where
  return a = Parser $ \ ts -> [ (B0, a, ts) ]
  Parser pa >>= k = Parser $ \ ts -> do
    (az, a, ts) <- pa ts
    (bz, b, ts) <- parser (k a) ts
    pure (az <> bz, b, ts)

instance Applicative Parser where
  pure = return
  (<*>) = ap

instance Alternative Parser where
  empty = mempty
  (<|>) = mappend

data WithSource a = a :<=: [Tok]

pws :: Parser a -> Parser (WithSource a)
pws p = Parser $ \ ts -> do
  (az, a, ts) <- parser p ts
  pure (az, a :<=: (az <>> []), ts)

-- TODO: at some point, we will need to record more provenance in the
-- token sequence

ptok :: (Tok -> Maybe a) -> Parser a
ptok f = Parser $ \ ts -> case ts of
  t:ts | Just a <- f t -> [(B0 :< t, a, ts)]
  _ -> []

peoi :: Parser ()
peoi = Parser $ \ ts -> case ts of
  [] -> [(B0, (), [])]
  _  -> []

ppeek :: Parser [Tok]
ppeek = Parser $ \ ts -> [(B0, ts, ts)]

pgrp :: (Grouping -> Bool) -> Parser a -> Parser a
pgrp f p = Parser $ \ ts -> case ts of
  t:ts | Grp g (Hide ss) <- kin t, f g -> do
           (_, a, []) <- parser p ss
           pure (B0 :< t, a, ts)
  _ -> []

pline :: Parser a -> Parser a
pline p = pgrp isLine (p <* many (ptok junk))
  where
    isLine (Line _) = True
    isLine _ = False
    junk t = case kin t of
      Spc -> Just ()
      Ret -> Just ()
      Grp Comment _ -> Just ()
      Sym | raw t == ";" -> Just ()
      _ -> Nothing

isComment :: Tok -> Bool
isComment (Tok { kin = Grp Comment _ }) = True
isComment t = False

pspc :: Parser ()
pspc = () <$ some (ptok (\ t -> guard (kin t == Spc || isComment t)))

-- We are relying on the lexer combining all consecutive space tokens

-- Optional space
pospc :: Parser ()
pospc = pspc <|> pure ()

-- The string s must be in the lexer symbol table
-- Leading and trailing space is consumed => do not use on its own!
punc :: String -> Parser ()
punc s = pospc <* psym s <* pospc

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
  [] -> parser pf ts
  xs -> do
    (tz, a, ts) <- xs
    (tz', b, ts) <- parser (ps a) ts
    pure (tz <> tz', b, ts)

testparser :: String -> Parser a -> [a]
testparser s p = fmap (\ (a,b,c) -> b) $ parser p (lexer (T.pack s))

