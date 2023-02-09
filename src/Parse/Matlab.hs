module Parse.Matlab where

import Control.Monad
import Control.Applicative

import Bwd
import Hide
import Lex

import Syntax
import Parse

import Lisp

pcommand :: Parser Command
pcommand = Assign <$> plhs <* punc "=" <*> pexpr topCI

plhs :: Parser LHS
plhs = LVar <$> pnom

data ContextInfo = CI { precedence :: Int
                      , matrixMode :: Bool -- spacing rules for unary
                                           -- +- are different inside
                                           -- square brackets
                      }

topCI :: ContextInfo
topCI = CI
  { precedence = 0
  , matrixMode = False
  }

matrixCI :: ContextInfo
matrixCI = topCI { matrixMode = True }

plusLevel, timesLevel, andLevel :: Int
plusLevel = 60
timesLevel = 70
andLevel = 90

contextBinop :: ContextInfo -- with context info ci,
             -> BinOperator -- we encounter operator op
             -> Maybe       -- Is op part of the expression we are parsing?
                  ( ContextInfo -- The context for the operand
                  , ContextInfo -- The context for the rest of the expression after the operand
                  )
contextBinop ci Plus  | precedence ci < plusLevel  = Just (ci {precedence = plusLevel }, ci)
contextBinop ci Minus | precedence ci < plusLevel  = Just (ci {precedence = plusLevel }, ci)
contextBinop ci Times | precedence ci < timesLevel = Just (ci {precedence = timesLevel }, ci)
contextBinop ci And | precedence ci < andLevel = Just (ci {precedence = andLevel }, ci)
contextBinop ci Or | precedence ci < andLevel = Just (ci {precedence = andLevel }, ci)
contextBinop ci op = Nothing

pexpr :: ContextInfo -> Parser Expr
pexpr ci = go >>= more ci where
  go = id <$> pgrp (== Bracket Round) (id <$ pospc <*> pexpr topCI <* pospc)
   <|> UnaryOp <$> punaryop <* pospc <*> pexpr ci
   <|> Var <$> pnom
   <|> IntLiteral <$> pint
   <|> Matrix <$> pgrp (== Bracket Square) (many prow)
{-  <|> StringLiteral <$> pstringlit
  <|> DoubleLiteral <$> pdouble
  <|> App <$> undefined <*> undefined
-}
  more ci e = ppeek >>= \case
    t1:t2:t3:ts | kin t1 == Spc
               && matrixMode ci
               && t2 `elem` [sym "+", sym "-"]
               && not (kin t3 == Spc) -> pure e
    _ -> tight e
    -- pcond pspc (\ _ -> loose e) (tight e)
    where
      trybinop = (id <$ pospc <*> pbinaryop) >>= \ b -> case contextBinop ci b of
        Nothing -> empty
        Just (cio, cia) -> pure (b, cio, cia)
      tight e = pcond trybinop
                      (\ (b, cio, cia) -> (BinaryOp b e <$ pospc <*> pexpr cio) >>= more cia)
                      (pure e)
      loose e | not (matrixMode ci) = tight e
      loose e = do
        ts <- ppeek
        case ts of
          (t1:t2:ts) | t1 `elem` [sym "+", sym "-"] && not (kin t2 == Spc) -> pure e
          _ -> tight e

prow :: Parser [Expr]
prow = pline (pospc *> psep0 (pspc <|> punc ",") (pexpr matrixCI))

punaryop :: Parser UnOperator
punaryop = UPlus <$ psym "+"
       <|> UMinus <$ psym "-"
       <|> UTilde <$ psym "~"

pbinaryop :: Parser BinOperator
pbinaryop = Plus <$ psym "+"
        <|> Minus <$ psym "-"
        <|> Times <$ psym "*"
        <|> And <$ psym "&&"
        <|> Or <$ psym "||"
        -- ...

pint :: Parser Int
pint = ptok (\ t -> read (raw t) <$ guard (kin t == Dig))

pdouble :: Parser Double
pdouble = undefined

pstringlit :: Parser String
pstringlit = undefined
