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

import Debug.Trace

pfile :: Parser File
pfile = pws pfile'

pfile' :: Parser [Command]
pfile' = many (pline pcommand) <* peoi

pcommand :: Nonce -> Parser Command
pcommand = pws . pcommand'

pcommand' :: Nonce -> Parser Command'
pcommand' n
  = pcond
  ( Assign <$> plhs <* punc "=" <*> pexpr topCI
  <|> Assign EmptyLHS <$> pexpr comCI
  <|> pgrp (== Block)
      (    If <$> pif True{-looking for if-} <*> pelse <* pend
       <|> For <$> plink ((,) <$ pkin Blk "for" <* pospc
                             <*> pws pnom <* punc "="
                             <*> pexpr topCI)
               <*> many (pline pcommand)
               <*  pend
       <|> While <$> plink (id <$ pkin Blk "while" <* pospc <*> pexpr topCI)
                 <*> many (pline pcommand)
                 <*  pend
       <|> Function
           <$> plink ((,,) <$ pkin Blk "function" <* pospc
                 <*> (plhs <* punc "=" <|> pure EmptyLHS)
                 <*> pws pnom <* pospc
                 <*> (pgrp (== Bracket Round) (psep0 (punc ",") $ pws pnom) <|> pure []))
           <*> many (pline pcommand)
           <*  (pend <|> pure ())
       <|> Switch <$> plink (id <$ pkin Blk "switch" <* pospc <*> pexpr topCI)
                  <*> many pcase
                  <*> optional potherwise
                  <* pend
      )
  <|> Break <$ pkin Key "break"
  <|> Continue <$ pkin Key "continue"
  <|> Return <$ pkin Key "return"
  <|> pgrp' (== Directive) (\(_, col) -> Direct (n,col) <$> pdir)
  <|> Respond <$> pgrp (== Response) pres
  <|> GeneratedCode <$> pgrp (== Generated) ([] <$ pgreedy (ptok Just)) -- (many (pline pcommand)) -- TODO: reinstate command parsing
  )
  (\ c -> case c of
     Assign EmptyLHS (Var f :<=: src) ->
       Assign EmptyLHS <$> pws' (fst src)
          (App (Var f :<=: src) <$> many (id <$ pspc <*> (fmap StringLiteral <$> pcmdarg)))
     _ -> pure c
  )
  empty
  where
    pif b = (:)
      <$> ((,) <$> plink (id <$ (if b then pkin Blk "if" else pkin Key "elseif")
                           <* pospc <*> pexpr topCI)
               <*> many (pline pcommand))
      <*> (pif False{-looking for elseif, from now on-} <|> pure [])
    pelse = pure Nothing
        <|> Just <$ plink (pkin Key "else") <*> many (pline pcommand)
    pend = plink (pkin Key "end")
    pcase = (,) <$> plink (id <$ pkin Key "case" <* pospc <*> pexpr topCI)
                <*> many (pline pcommand)
    potherwise = id <$  plink (id <$ pkin Key "otherwise")
                    <*> many (pline pcommand)

pcmdarg :: Parser (WithSource String)
pcmdarg = pws pcmdarg'

pcmdarg' :: Parser String
pcmdarg' = pstringlit
      <|> concat <$> ((:) <$> ptok start <*> many (ptok more))
      where
      start t = case kin t of
        k | k `elem` [Nom, Blk, Key, Dig] -> Just (raw t)
        Grp (Bracket b) _ | b /= Round -> Just (raw t)
        Sym | raw t `notElem` [",", ";", "="] -> Just (raw t)  -- only those?
        _ -> Nothing
      more t = start t <|> extra t
      extra t = case kin t of
        Grp (Bracket _) _ -> Just (raw t)
        Sym | raw t == "=" -> Just (raw t)
        _ -> Nothing

pdir :: Parser Dir
pdir = pws pdir'

pdir' :: Parser Dir'
pdir' = pvspcaround $
        plink (id <$ pprejunk <*> pws pdirhead <* pospc)
                >>= (\case
                        h@(InputFormat x :<=: _) ->  (h, ). Just . InputFormatBody <$> pgreedy (pgrp isLine pstring)
                        h  -> pure (h, Nothing))
  where
    isLine (Line _) = True
    isLine _ = False

pprejunk :: Parser ()
pprejunk = () <$ pospc <* (psym "%" <|> pure ())  <* psym ">"  <* pospc

patom :: Parser String
patom = id <$ psym "`" <*> pnom

pdirhead :: Parser DirHeader
pdirhead = Declare <$> psep1 (pspc <|> punc ",") (pws pnomNotLabMateKey) <* pospc <* psym "::" <* pospc <*> ptensortype
    <|> Rename <$ pkin Nom "rename" <* pospc <*> pnomNotLabMateKey <* pspc <*> pnomNotLabMateKey
    <|> InputFormat <$ pkin Nom "input" <* pospc <*> pnom
    <|> ReadFrom <$ pkin Nom "readfrom" <* pospc <*> pstringlit <* pspc <*> psep1 pspc pnom
    <|> Typecheck <$ pkin Nom "typecheck" <* pospc <*> ptensortype <* pspc <*> pexpr topCI
    <|> SynthType <$ pkin Nom "typeof" <* pospc <*> pexpr topCI
    <|> Dimensions <$ pkin Nom "dimensions" <* pspc
                   <*> pws pnomNotLabMateKey <* pspc
                   <* pkin Blk "for" <* pspc
                   <*> pws pnomNotLabMateKey <* pspc
                   <* pkin Nom "over" <* pspc
                   <*> psep0 (pspc <|> punc ",")
                         ((,) <$> optional (pws pnomNotLabMateKey <* pspc <* pkin Blk "for" <* pspc)
                              <*> pws patom
                         )
    <|> Unit <$ pkin Nom "unit" <* pspc
             <*> pws pnomNotLabMateKey <* pospc
             <* psym "::" <* pospc <*> ptypeexpr topCI
--    <|> EverythingOkay <$ pkin Nom ""

ptensortype :: Parser TensorType
ptensortype = pws ptensortype'

ptensortype' :: Parser TensorType'
ptensortype' = Tensor <$> (pgrp (== Bracket Square) (plink psquex) <* pospc
                           <|> pure (one , one))
                      <*> ptypeexpr topCI
  where
  one = ("", TyNum 1  :<=: (-1, Hide []))
  psquex = (,) <$> (plarrow (ptypeexpr topCI) <* pospc <* pkin Nom "x" <* pospc
                    <|> pure one)
               <*> plarrow (ptypeexpr topCI)

plarrow :: Parser a -> Parser (String, a)
plarrow p = pcond ((,) <$> pnom <* pospc <* psym "<" <* psym "-" <* pospc ) (<$> p)
            (("",) <$> p)
        <|> pgrp (== Bracket Round) (plarrow p)

ptypeexpr :: ContextInfo -> Parser TypeExpr
ptypeexpr ci = go >>= more ci where
  go :: Parser TypeExpr
  go = pgrp (== Bracket Round) (id <$ pospc <*> ptypeexpr topCI <* pospc)
   <|> pws (tyUnaryOp <$> punaryop <* pospc <*> ptypeexpr (ci {precedence = unaryLevel}))
   <|> lhsstuff ci
   <|> pws (prawif Dig >>= pnumber >>= \case
               IntLiteral i -> pure $ TyNum i
               _ -> mempty)
   <|> pws (TyStringLiteral <$> pstringlit)
   <|> pws (TyAtom <$> patom)
   <|> pws (pgrp (== Bracket Curly) (TyBraces . join <$> optional (plink (id <$ pospc <*> optional (ptypeexpr topCI <* pospc)))))
  lhsstuff ci = (pws (TyVar <$> pnom) >>= lmore)
            <|> (do
                        (e :<=: src) <- pws (pgrp (== Bracket Square) (many (prow ptypeexpr)))
                        pure $ tyMat src e :<=: src)
  lmore l = pcond
              (pws' (nonce l) (TyApp l <$ pcxspc ci <*> pargs Round (ptypeexpr topCI)))
              lmore
              (pure l)
  yuk = void (psym ".") <* pospc
    <|> void pspc <* psym "." <* pspc

  more :: ContextInfo -> TypeExpr -> Parser TypeExpr
  more ci e = ppeek >>= \case
    t1:t2:t3:ts | kin t1 == Spc
               && matrixMode ci
               && t2 `elem` [sym "+", sym "-"]
               && kin t3 /= Spc -> pure e
    t1:t2:t3:ts | kin t1 == Spc
               && commandMode ci
               && (case what e of { (TyVar _) -> True ; _ -> False })
               && t2 `elem` (sym <$> binOps)
               && kin t3 /= Spc -> pure e
    _ -> tight e
    -- pcond pspc (\ _ -> loose e) (tight e)
    where
      trybinop :: Parser (BinOperator, ContextInfo, ContextInfo)
      trybinop = (id <$ pospc <*> pbinaryop) >>= \ b -> case contextBinop ci b of
        Nothing -> empty
        Just (cio, cia) -> pure (b, cio { commandMode = False }
                                  , cia { commandMode = False })
      tight :: TypeExpr -> Parser TypeExpr
      tight e = pcond (pws' (nonce e) trybinop)
                      (\ ((b, cio, cia) :<=: src) -> pws' (fst src) (TyBinaryOp b e <$ pospc <*> ptypeexpr cio) >>= more cia)
                      (pcond (pws' (nonce e) ptranspose) (\ (op :<=: src) -> more ci (TyUnaryOp op e :<=: src)) (pure e))


pres :: Parser Res
pres = pgreedy (ptok Just)

plhs' :: ContextInfo -> Parser LHS
plhs' ci = (pws (LVar <$> pnom) >>= more)
   <|> pws (LMat <$> pgrp (== Bracket Square) (plink (psep0 (pspc <|> punc ",") p) <|> [] <$ peoi))
  where
  more :: LHS -> Parser LHS
  more l = pcond
    (pws' (nonce l) (LApp l <$ pcxspc ci <*> pargs Round (pexpr topCI) <|> LBrp l <$ pcxspc ci <*> pargs Curly (pexpr topCI)
     <|> LDot l <$ (if commandMode ci then yuk else punc ".") <*> pnom))
    more
    (pure l)
  yuk = void (psym ".") <* pospc
    <|> void pspc <* psym "." <* pspc
  p :: Parser (Either Tilde LHS)
  p = Left Tilde <$ psym "~"  <|> Right <$> plhs

plhs :: Parser LHS
plhs = plhs' topCI

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
pcxspc ci = unless (matrixMode ci) pospc

pstringlit :: Parser String
pstringlit = ptok stringy where
  stringy (Tok {kin = Grp Literal _, raw = '\'': cs@(_ : _)}) = Just (escape (init cs))
  stringy _ = Nothing

  escape ('\'':'\'':cs) = '\'' : escape cs
  escape (c:cs) = c : escape cs
  escape [] = []

pexpr :: ContextInfo -> Parser Expr
pexpr ci = go >>= more ci where
  go :: Parser Expr
  go = pgrp (== Bracket Round) (id <$ pospc <*> pexpr topCI <* pospc)
   <|> pws (UnaryOp <$> punaryop <* pospc <*> pexpr (ci {precedence = unaryLevel}))
       -- should UnaryOp check precedence level?
   <|> lhsstuff ci
   <|> pws (Cell <$> pgrp (== Bracket Curly) (many $ prow pexpr))
   <|> pws (prawif Dig >>= pnumber)
   <|> pws (ColonAlone <$ psym ":")
   <|> pws (StringLiteral <$> pstringlit)
   <|> pws (Handle <$ psym "@" <* pospc <*> pnom)
   <|> pws (Lambda <$ psym "@" <* pospc
              <*> pgrp (== Bracket Round) (pspcaround $ psep0 (punc ",") pnom)
              <* pospc <*> pexpr (ci { commandMode = False }))
  lhsstuff ci = (pws (Var <$> pnom) >>= lmore)
            <|> pws (Mat <$> pgrp (== Bracket Square) (many $ prow pexpr))
  lmore l = pcond
              (pws' (nonce l) (App l <$ pcxspc ci <*> pargs Round (pexpr topCI) <|> Brp l <$ pcxspc ci <*> pargs Curly (pexpr topCI)
                <|> Dot l <$ (if commandMode ci then yuk else punc ".") <*> pnom))
              lmore
              (pure l)
  yuk = void (psym ".") <* pospc
    <|> void pspc <* psym "." <* pspc

  more :: ContextInfo -> Expr -> Parser Expr
  more ci e = ppeek >>= \case
    t1:t2:t3:ts | kin t1 == Spc
               && matrixMode ci
               && t2 `elem` [sym "+", sym "-"]
               && kin t3 /= Spc -> pure e
    t1:t2:t3:ts | kin t1 == Spc
               && commandMode ci
               && (case what e of { (Var _) -> True ; _ -> False })
               && t2 `elem` (sym <$> binOps)
               && kin t3 /= Spc -> pure e
    _ -> tight e
    -- pcond pspc (\ _ -> loose e) (tight e)
    where
      trybinop :: Parser (BinOperator, ContextInfo, ContextInfo)
      trybinop = (id <$ pospc <*> pbinaryop) >>= \ b -> case contextBinop ci b of
        Nothing -> empty
        Just (cio, cia) -> pure (b, cio { commandMode = False }
                                  , cia { commandMode = False })
      tight :: Expr -> Parser Expr
      tight e = pcond (pws' (nonce e) trybinop)
                      (\ ((b, cio, cia) :<=: src) -> pws' (fst src) (BinaryOp b e <$ pospc <*> pexpr cio) >>= more cia)
                      (pcond (pws' (nonce e) ptranspose) (\ (op :<=: src) -> more ci (UnaryOp op e :<=: src)) (pure e))

      {-
      loose e | not (matrixMode ci) = tight e
      loose e = do
        ts <- ppeek
        case ts of
          (t1:t2:ts) | t1 `elem` [sym "+", sym "-"] && not (kin t2 == Spc) -> pure e
          _ -> tight e
      -}

pargs :: Bracket -> Parser a -> Parser [a]
pargs b p = pgrp (== Bracket b) $ wrap b $ pspcaround $ psep0 (punc ",") p
  where
    wrap Round = id
    wrap _     = plink

prow :: (ContextInfo -> Parser a) -> Parser [a]
prow p = plink (psep0 (pspc <|> punc ",") (p matrixCI))

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

pnumber :: String -> Parser Expr'
pnumber ds = mkNum <$> optional (id <$ psym "." <*> (prawif Dig <|> pure "0"))
                   <*> optional ((,) <$ (pkin Nom "e" <|> pkin Nom "E")
                                    <*> ('-' <$ psym "-" <|> ('+' <$ psym "+"))
                                    <*> prawif Dig
                                 <|> ptok (\case
                                   Tok {kin = Nom, raw = e:es@(_ : _)}
                                     | elem e "eE" && all isDigit es
                                        -> Just ('+', es)
                                   _ -> Nothing)
                                 )
  where
  mkNum :: Maybe String -> Maybe (Char, String) -> Expr'
  mkNum Nothing Nothing = IntLiteral (read ds)
  mkNum Nothing (Just ('+', es)) =
    IntLiteral (read (ds ++ replicate (read es) '0'))
  mkNum m e = DoubleLiteral (read (ds ++ mant m ++ expo e)) where
    mant Nothing = ""
    mant (Just ms) = '.' : ms
    expo Nothing = ""
    expo (Just (s, es)) = 'e' : s : es
