{-# LANGUAGE LambdaCase #-}

module Parse.Matlab where

import Control.Monad
import Control.Applicative
import Data.Char

import Bwd
import Hide
import Lex

import Syntax
import Parse

import Lisp

pfile :: Parser [Command]
pfile = many (pline pcommand) <* peoi

pcommand :: Parser Command
pcommand
  = pcond
  ( Assign <$> plhs <* punc "=" <*> pexpr topCI
  <|> Assign (LHS (Mat [])) <$> pexpr comCI
  <|> id <$> pgrp (== Block)
      (    If <$> pif True{-looking for if-} <*> pelse <* pend
       <|> For <$> pline ((,) <$ pkin Blk "for" <* pospc
                             <*> pnom <* punc "="
                             <*> pexpr topCI)
               <*> many (pline pcommand)
               <*  pend
       <|> While <$> pline (id <$ pkin Blk "while" <* pospc <*> pexpr topCI)
                 <*> many (pline pcommand)
                 <*  pend
       <|> Function
           <$> pline ((,,) <$ pkin Blk "function" <* pospc
                 <*> (plhs <* punc "=" <|> pure (LHS $ Mat []))
                 <*> pnom <* pospc
                 <*> (pgrp (== Bracket Round) (psep0 (punc ",") pnom) <|> pure []))
           <*> many (pline pcommand)
           <*  (pend <|> pure ())
       <|> Switch <$> pline (id <$ pkin Blk "switch" <* pospc <*> pexpr topCI)
                  <*> many pcase
                  <*> optional potherwise
                  <* pend
      )
  <|> Break <$ pkin Key "break"
  <|> Continue <$ pkin Key "continue"
  <|> Return <$ pkin Key "return"
  <|> Direct <$> pgrp (== Directive) (id <$ psym "%" <* psym ">" <*> pdir)
  <|> Respond <$> pgrp (== Response) pres
  <|> GeneratedCode <$> pgrp (== Generated) (many (pline pcommand))
  )
  (\ c -> case c of
     Assign (LHS (Mat [])) (EL (Var f)) ->
       Assign (LHS (Mat [])) <$> (EL <$>
          (App (Var f) <$> many (id <$ pspc <*> (StringLiteral <$> pcmdarg))))
     _ -> pure c
  )
  empty
  where
    pif b = (:)
      <$> ((,) <$> pline (id <$ (if b then pkin Blk "if" else pkin Key "elseif")
                           <* pospc <*> pexpr topCI)
               <*> many (pline pcommand))
      <*> (pif False{-looking for elseif, from now on-} <|> pure [])
    pelse = pure Nothing
        <|> Just <$ pline (pkin Key "else") <*> many (pline pcommand)
    pend = pline (pkin Key "end")
    pcase = (,) <$> pline (id <$ pkin Key "case" <* pospc <*> pexpr topCI)
                <*> many (pline pcommand)
    potherwise = id <$  pline (id <$ pkin Key "otherwise")
                    <*> many (pline pcommand)

pcmdarg :: Parser String
pcmdarg = pstring
      <|> concat <$> ((:) <$> ptok start <*> many (ptok more))
      where
      start t = case kin t of
        k | k `elem` [Nom, Blk, Key, Dig] -> Just (raw t)
        Grp (Bracket b) _ | b /= Round -> Just (raw t)
        Sym | not (elem (raw t) [",", ";", "="]) -> Just (raw t)  -- only those?
        _ -> Nothing
      more t = start t <|> extra t
      extra t = case kin t of
        Grp (Bracket _) _ -> Just (raw t)
        Sym | raw t == "=" -> Just (raw t)
        _ -> Nothing

pdir :: Parser Dir
pdir = Declare <$ pospc <*> plarrow ptensortype

ptensortype :: Parser TensorType
ptensortype = Tensor <$> (id <$> pgrp (== Bracket Square) (pline psquex) <* pospc
                         <|> pure (one , one))
                     <*> pentrytype
  where
  one = ("", IntLiteral 1)
  psquex = (,) <$> (id <$> plarrow (pexpr topCI) <* pospc <* pkin Nom "x" <* pospc
                    <|> pure one)
               <*> plarrow (pexpr topCI)

plarrow :: Parser a -> Parser (String, a)
plarrow p = pcond ((,) <$> pnom <* pospc <* psym "<" <* psym "-" <* pospc ) (<$> p)
            (("",) <$> p)
        <|> pgrp (== Bracket Round) (plarrow p)

pentrytype :: Parser EntryType
pentrytype =
      Cmhn <$> plarrow (pexpr topCI) <* punc "," <*> pexpr topCI
  <|> Ty <$> pexpr topCI

pres :: Parser Res
pres = id <$ psym "%" <* psym "<" <*> many (ptok Just)

plhs' :: Parser matrix -> ContextInfo -> Parser (LHS' matrix)
plhs' pm ci = ((Var <$> pnom) >>= more)
   <|> Mat <$> pgrp (== Bracket Square) pm
  where
  more l = pcond
    (App l <$ pcxspc ci <*> pargs Round <|> Brp l <$ pcxspc ci <*> pargs Curly
     <|> Dot l <$ (if commandMode ci then yuk else punc ".") <*> pnom)
    more
    (pure l)
  yuk = () <$ psym "." <* pospc
    <|> () <$ pspc <* psym "." <* pspc

plhs :: Parser LHS
plhs = LHS <$> plhs' (pline (psep0 (pspc <|> punc ",") p) <|> [] <$ peoi) topCI
  where
    p = Left Tilde <$ psym "~"  <|> Right <$> plhs

data ContextInfo = CI { precedence  :: Int
                      , matrixMode  :: Bool -- spacing rules for unary
                                            -- +- are different inside
                                            -- square brackets
                      , commandMode :: Bool -- is "command syntax" ok?
                      }

topCI :: ContextInfo
topCI = CI
  { precedence  = 0
  , matrixMode  = False
  , commandMode = False
  }

comCI :: ContextInfo
comCI = topCI { commandMode = True }

matrixCI :: ContextInfo
matrixCI = topCI { matrixMode = True }

ororLevel, andandLevel, orLevel, andLevel, compLevel, colonLevel,
  plusLevel, timesLevel, unaryLevel, powLevel :: Int
-- the higher the level, the tighter the operator
powLevel = 110
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
contextBinop ci (Pow _)     | precedence ci < powLevel    = Just (ci {precedence = powLevel }, ci)
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

pcxspc :: ContextInfo -> Parser ()
pcxspc ci = if matrixMode ci then pure () else pospc

pstring :: Parser String
pstring = ptok stringy where
  stringy (Tok {kin = Grp Literal _, raw = '\'': cs@(_ : _)}) = Just (escape (init cs))
  stringy _ = Nothing

  escape ('\'':'\'':cs) = '\'' : escape cs
  escape (c:cs) = c : escape cs
  escape [] = []

pexpr :: ContextInfo -> Parser Expr
pexpr ci = go >>= more ci where
  go = id <$> pgrp (== Bracket Round) (id <$ pospc <*> pexpr topCI <* pospc)
   <|> UnaryOp <$> punaryop <* pospc <*> pexpr (ci {precedence = unaryLevel})
       -- should UnaryOp check precedence level?
   <|> EL <$> plhs' (many prow) ci
   <|> Cell <$> pgrp (== Bracket Curly) (many prow)
   <|> (prawif Dig >>= pnumber)
   <|> ColonAlone <$ psym ":"
   <|> StringLiteral <$> pstring
   <|> Handle <$ psym "@" <* pospc <*> pnom
   <|> Lambda <$ psym "@" <* pospc
              <*> pgrp (== Bracket Round) (pspcaround $ psep0 (punc ",") pnom)
              <* pospc <*> pexpr (ci { commandMode = False })
  more ci e = ppeek >>= \case
    t1:t2:t3:ts | kin t1 == Spc
               && matrixMode ci
               && t2 `elem` [sym "+", sym "-"]
               && not (kin t3 == Spc) -> pure e
    t1:t2:t3:ts | kin t1 == Spc
               && commandMode ci
               && (case e of { (EL (Var _)) -> True ; _ -> False })
               && t2 `elem` (sym <$> binOps)
               && not (kin t3 == Spc) -> pure e
    _ -> tight e
    -- pcond pspc (\ _ -> loose e) (tight e)
    where
      trybinop = (id <$ pospc <*> pbinaryop) >>= \ b -> case contextBinop ci b of
        Nothing -> empty
        Just (cio, cia) -> pure (b, cio { commandMode = False }
                                  , cia { commandMode = False })
      tight e = pcond trybinop
                      (\ (b, cio, cia) -> (BinaryOp b e <$ pospc <*> pexpr cio) >>= more cia)
                      (pcond ptranspose (\ op -> more ci (UnaryOp op e)) (pure e))
      loose e | not (matrixMode ci) = tight e
      loose e = do
        ts <- ppeek
        case ts of
          (t1:t2:ts) | t1 `elem` [sym "+", sym "-"] && not (kin t2 == Spc) -> pure e
          _ -> tight e

pargs :: Bracket -> Parser [Expr]
pargs b = pgrp (== Bracket b) $ wrap b $ pspcaround $ psep0 (punc ",") (pexpr topCI)
  where
    wrap Round = id
    wrap _     = pline

prow :: Parser [Expr]
prow = pline (psep0 (pspc <|> punc ",") (pexpr matrixCI))

punaryop :: Parser UnOperator
punaryop = UPlus <$ psym "+"
       <|> UMinus <$ psym "-"
       <|> UTilde <$ psym "~"

ptranspose :: Parser UnOperator
ptranspose = UTranspose <$ psym "'"
         <|> UDotTranspose <$ psym ".'"

pbinaryop :: Parser BinOperator
pbinaryop = Pow False <$ psym "^"
        <|> Pow True <$ psym ".^"
        <|> Mul False <$> (Times <$ psym "*" <|> RDiv <$ psym "/" <|> LDiv <$ psym "\\")
        <|> Mul True <$> (Times <$ psym ".*" <|> RDiv <$ psym "./" <|> LDiv <$ psym ".\\")
        <|> Plus <$ psym "+" <|> Minus <$ psym "-"
        <|> Colon <$ psym ":"
        <|> Comp True  <$> (LT <$ psym "<"  <|> EQ <$ psym "==" <|> GT <$ psym ">")
        <|> Comp False <$> (LT <$ psym ">=" <|> EQ <$ psym "~=" <|> GT <$ psym "<=")
        <|> And <$> (False <$ psym "&&" <|> True <$ psym "&")
        <|> Or <$> (False <$ psym "||" <|> True <$ psym "|")
        -- ...

pnumber :: String -> Parser Expr
pnumber ds = mkNum <$> optional (id <$ psym "." <*> (prawif Dig <|> pure "0"))
                   <*> optional ((,) <$ (pkin Nom "e" <|> pkin Nom "E")
                                    <*> ('-' <$ psym "-" <|> ('+' <$ psym "+"))
                                    <*> prawif Dig
                                 <|> (ptok $ \case
                                   Tok {kin = Nom, raw = e:es@(_ : _)}
                                     | elem e "eE" && all isDigit es
                                        -> Just ('+', es)
                                   _ -> Nothing)
                                 )
  where
  mkNum :: Maybe String -> Maybe (Char, String) -> Expr
  mkNum Nothing Nothing = IntLiteral (read ds)
  mkNum Nothing (Just ('+', es)) =
    IntLiteral (read (ds ++ replicate (read es) '0'))
  mkNum m e = DoubleLiteral (read (ds ++ mant m ++ expo e)) where
    mant Nothing = ""
    mant (Just ms) = '.' : ms
    expo Nothing = ""
    expo (Just (s, es)) = 'e' : s : es
