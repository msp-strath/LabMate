{-# LANGUAGE PatternGuards #-}
module Parse where

import Control.Monad
import Control.Applicative

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

pgrp :: (Grouping -> Bool) -> Parser a -> Parser a
pgrp f p = Parser $ \ ts -> case ts of
  t:ts | Grp g (Hide ss) <- kin t, f g -> do
           (_, a, []) <- parser p ss
           pure (B0 :< t, a, ts)
  _ -> []

pspc :: Parser ()
pspc = ptok (\ t -> guard (kin t == Spc))

-- We are relying on the lexer combining all consecutive space tokens

-- Optional space
pospc :: Parser ()
pospc = pspc <|> pure ()

-- The string s must be in the lexer symbol table
-- Leading and trailing space is consumed => do not use on its own!
punc :: String -> Parser ()
punc s = pospc <* ptok (\ t -> guard (t == sym s)) <* pospc

pnom :: Parser String
pnom = ptok $ \ t -> if kin t == Nom then Just (raw t) else Nothing
