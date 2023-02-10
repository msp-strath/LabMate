{-# LANGUAGE LambdaCase #-}

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
pcommand
  = (id <$ pospc <*>) $
      Assign <$> plhs <* punc "=" <*> pexpr topCI
  <|> id <$> pgrp (== Block) (If <$> pif True <*> pelse <* pline (pkin Key "end"))
  where
    pif b = (:)
      <$> ((,) <$> pline (id <$ (if b then pkin Blk "if" else pkin Key "elseif")
                           <* pospc <*> pexpr topCI)
               <*> many (pline pcommand))
      <*> (pif False <|> pure [])
    pelse = pure Nothing
        <|> Just <$ pline (pkin Key "else") <*> many (pline pcommand)

plhs :: Parser LHS
plhs = (LVar <$> pnom) >>= more where
  more l = pcond
    (Index l <$ pospc <*> pargs <|> Field l <$ punc "." <*> pnom)
    more
    (pure l)

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

ororLevel, andandLevel, orLevel, andLevel, compLevel, colonLevel,
  plusLevel, timesLevel, unaryLevel, supLevel :: Int
supLevel = 110
unaryLevel = 90
timesLevel = 80
plusLevel = 70
colonLevel = 60
compLevel = 50
andLevel = 40
orLevel = 30
andandLevel = 20
ororLevel = 10

contextBinop :: ContextInfo -- with context info ci,
             -> BinOperator -- we encounter operator op
             -> Maybe       -- Is op part of the expression we are parsing?
                  ( ContextInfo -- The context for the operand
                  , ContextInfo -- The context for the rest of the expression after the operand
                  )
contextBinop ci (Sup _ _)   | precedence ci < supLevel    = Just (ci {precedence = supLevel }, ci)
contextBinop ci (Mul _ _)   | precedence ci < timesLevel  = Just (ci {precedence = timesLevel }, ci)
contextBinop ci Plus        | precedence ci < plusLevel   = Just (ci {precedence = plusLevel }, ci)
contextBinop ci Minus       | precedence ci < plusLevel   = Just (ci {precedence = plusLevel }, ci)
contextBinop ci Colon       | precedence ci < colonLevel  = Just (ci {precedence = colonLevel }, ci)
contextBinop ci (Comp _ _)  | precedence ci < compLevel   = Just (ci {precedence = compLevel }, ci)
contextBinop ci (And True)  | precedence ci < andLevel    = Just (ci {precedence = andLevel }, ci)
contextBinop ci (Or True)   | precedence ci < orLevel     = Just (ci {precedence = orLevel }, ci)
contextBinop ci (And False) | precedence ci < andandLevel = Just (ci {precedence = andandLevel }, ci)
contextBinop ci (Or False)  | precedence ci < ororLevel   = Just (ci {precedence = ororLevel }, ci)
contextBinop ci op = Nothing

pexpr :: ContextInfo -> Parser Expr
pexpr ci = go >>= more ci where
  go = id <$> pgrp (== Bracket Round) (id <$ pospc <*> pexpr topCI <* pospc)
   <|> UnaryOp <$> punaryop <* pospc <*> pexpr (ci {precedence = unaryLevel})
   <|> (pnom >>= \ n ->
         pcond
           (App n <$ (if matrixMode ci then pure () else pospc) <*> pargs)
           pure
           (pure (Var n)))
   <|> IntLiteral <$> pint
   <|> Matrix <$> pgrp (== Bracket Square) (many prow)
   <|> ColonAlone <$ psym ":"
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

pargs :: Parser [Expr]
pargs = pgrp (== Bracket Round) (psep0 (punc ",") (pexpr topCI))

prow :: Parser [Expr]
prow = pline (pospc *> psep0 (pspc <|> punc ",") (pexpr matrixCI))

punaryop :: Parser UnOperator
punaryop = UPlus <$ psym "+"
       <|> UMinus <$ psym "-"
       <|> UTilde <$ psym "~"

pbinaryop :: Parser BinOperator
pbinaryop = Sup False <$> (Xpose <$ psym "'" <|> Power <$ psym "^")
        <|> Sup True <$> (Xpose <$ psym ".'" <|> Power <$ psym ".^")
        <|> Mul False <$> (Times <$ psym "*" <|> RDiv <$ psym "/" <|> LDiv <$ psym "\\")
        <|> Mul True <$> (Times <$ psym ".*" <|> RDiv <$ psym "./" <|> LDiv <$ psym ".\\")
        <|> Plus <$ psym "+" <|> Minus <$ psym "-"
        <|> Colon <$ psym ":"
        <|> Comp True <$> (LT <$ psym "<" <|> EQ <$ psym "==" <|> GT <$ psym ">")
        <|> Comp False <$> (LT <$ psym ">=" <|> EQ <$ psym "~=" <|> GT <$ psym "<=")
        <|> And <$> (False <$ psym "&&" <|> True <$ psym "&")
        <|> Or <$> (False <$ psym "||" <|> True <$ psym "|")
        -- ...

pint :: Parser Int
pint = ptok (\ t -> read (raw t) <$ guard (kin t == Dig))

pdouble :: Parser Double
pdouble = undefined

pstringlit :: Parser String
pstringlit = undefined
