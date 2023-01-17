{-# LANGUAGE OverloadedStrings, LambdaCase #-}

module Lex where

import Data.Char
import Data.List
import Control.Monad
import Control.Applicative
import qualified Data.Text as T
import qualified Data.Map as M

import Bwd

data Kin
  = Nom
  | Key
  | Sym
  | Grp Grouping [Tok]
  | Spc
  | Dig
  | Ret
  | Urk
  deriving (Show, Eq)

data Tok = Tok
  { kin :: Kin
  , pos :: Pos
  , raw :: String
  } deriving Show

data Grouping = Literal | Comment | Error
  deriving (Show, Eq)

type Pos = (Int, Int) -- line, column with 0 origin

instance Eq Tok where
  s == t = kin s == kin t && raw s == raw t

type Doc = (T.Text, Pos)

lexer :: T.Text -> [Tok]
lexer = lex1 . lex0

lex1 :: [Tok] -> [Tok]
lex1 = normal where
  normal [] = []
  normal (t:ts)
    | t == squote = charlit (B0 :< t) ts
    | t == percent = lcomment (B0 :< t) ts
    | t == percentopenbrace = mlcomment (B0 :< (B0 :< t)) ts
    | otherwise = t : normal ts

  charlit acc [] = [group Error acc]
  charlit acc (t:ts)
    | t == squote = group Literal (acc :< t) : normal ts
    | kin t == Ret = group Error acc : normal (t:ts)
    | otherwise = charlit (acc :< t) ts

  lcomment acc [] = [group Comment acc]
  lcomment acc (t:ts)
    | kin t == Ret = group Comment acc : normal (t:ts)
    | otherwise = lcomment (acc :< t) ts

  mlcomment B0 _ = error "stack should never be empty"
  mlcomment (az :< a) [] = let c0 = group Error a in
    case az of
      B0 -> [c0]
      az :< a -> mlcomment (az :< (a :< c0)) []
  mlcomment acc@(az :< a) (t:ts)
    | t == percentopenbrace = mlcomment (acc :< (B0 :< t)) ts
    | t == percentclosbrace = let c0 = group Comment (a :< t) in
        case az of
          B0 -> c0 : normal ts
          az :< a -> mlcomment (az :< (a :< c0)) ts
    | otherwise = mlcomment (az :< (a :< t)) ts



  group :: Grouping -> Bwd Tok -> Tok
  group grp tz = case tz <>> [] of
    ts@(t:_) -> Tok (Grp grp ts) (pos t) (ts >>= raw)
    [] -> error "should not make empty group"

  squote = Tok Sym (0,0) "'"
  percent = Tok Sym (0,0) "%"
  percentopenbrace = Tok Sym (0,0) "%{"
  percentclosbrace = Tok Sym (0,0) "%}"


lex0 :: T.Text -> [Tok]
lex0 t = unfoldr tok (t, (0, 0))

unix :: T.Text -> T.Text
unix t = case T.uncons t of
  Nothing -> t
  Just (c,t) -> case c of
    '\r' -> case T.uncons t of
      Just ('\n', _) -> unix t
      _ -> T.cons '\n' (unix t)
    _ -> T.cons c (unix t)

tok :: Doc -> Maybe (Tok, Doc)
tok d@(_, p) = case munch d symbols of
  Just (s, d) -> return (Tok Sym p s, d)
  Nothing -> peek d >>= \case
    (c, d)
      | isAlpha c ->
        let (s, d') = spand (\ c -> isAlphaNum c || c == '_') d
            x = c : s
            k = case M.lookup x keywords of
              Just _ -> Key
              _      -> Nom
        in  return (Tok k p x, d')
      | isNL c -> return (Tok Ret p [c], d)
      | isSpace c -> let (s, d') = spand (\ c -> isSpace c && not (isNL c)) d in
          return (Tok Spc p (c : s), d')
      | isDigit c -> let (s, d') = spand isDigit d in
          return (Tok Dig p (c : s), d')
      | otherwise -> return (Tok Urk p [c], d)

peek :: Doc -> Maybe (Char, Doc)
peek (t, p) = T.uncons t >>= \ (x, t) -> return (x, (t, p `after` x))

spand :: (Char -> Bool) -> Doc -> (String, Doc)
spand p d = case peek d of
  Just (c, d) | p c -> let (s, d') = spand p d in (c : s, d')
  _ -> ("", d)

isNL :: Char -> Bool
isNL c = c == '\n' || c == '\r'

after :: Pos -> Char -> Pos
after (l, c) x | isNL x = (l + 1, 0)
after (l, c) _ = (l, c + 1)

data Table = Table Bool (M.Map Char Table) deriving Show

empT :: Table
empT = Table False M.empty

insT :: String -> Table -> Table
insT [] (Table _ m) = Table True m
insT (c : s) (Table b m) = Table b (M.alter go c m) where
  go Nothing  = Just (insT s empT)
  go (Just t) = Just (insT s t)

munch :: Doc -> Table -> Maybe (String, Doc)
munch d (Table b m) = (do
  (c, d') <- peek d
  t <- M.lookup c m
  (s, d) <- munch d' t
  return (c : s, d)
  ) <|> ("", d) <$ guard b

keywords :: M.Map String ()
keywords = M.fromList $ map (,()) ["if", "else", "elseif", "end", "function", "for"]

symbols :: Table
symbols = foldr insT empT
  [ "+", "-", ".*", "*", "./", "/", ".\\", "\\", ".^", "^", ".'", "'"
  , "==", "~=", ">", ">=", "<", "<="
  , "&", "|", "&&", "||", "~"
  , "@"
  , "."
  , "..."
  , "%", "%{", "%}"
  , ":"
  ,"!", "?"
  , "\"", "''", "\"\""
  , "="
  , ".?"
  , "(", ")", "[", "]", "{", "}", ",", ";"
  ]
