{-# LANGUAGE OverloadedStrings, LambdaCase #-}

module Lex where

import Data.Char
import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow ((***))
import qualified Data.Text as T
import qualified Data.Map as M

import Bwd

data Kin
  = Nom
  | Key
  | Blk
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

data Grouping = Literal | Comment | Block | Bracket Bracket | Error
  deriving (Show, Eq)

data Bracket = Round | Square | Curly
  deriving (Show, Eq)

type Pos = (Int, Int) -- line, column with 0 origin

instance Eq Tok where
  s == t = kin s == kin t && raw s == raw t

type Doc = (T.Text, Pos)

lexer :: T.Text -> [Tok]
lexer = lex3 . lex2 . lex1 . lex0

-- basic lexing 
lex0 :: T.Text -> [Tok]
lex0 t = unfoldr tok (t, (0, 0)) where
  tok :: Doc -> Maybe (Tok, Doc)
  tok d@(_, p) = case munch d symbols of
    Just (s, d) -> return (Tok Sym p s, d)
    Nothing -> peek d >>= \case
      (c, d)
        | isAlpha c ->
          let (s, d') = spand (\ c -> isAlphaNum c || c == '_') d
              x = c : s
              k = case M.lookup x keywords of
                Just False -> Key
                Just True  -> Blk
                _          -> Nom
          in  return (Tok k p x, d')
        | isNL c -> return (Tok Ret p [c], d)
        | isSpace c -> let (s, d') = spand (\ c -> isSpace c && not (isNL c)) d in
            return (Tok Spc p (c : s), d')
        | isDigit c -> let (s, d') = spand isDigit d in
            return (Tok Dig p (c : s), d')
        | otherwise -> return (Tok Urk p [c], d)


-- grouping character literals (surrounded by `'`), end of line comments (`%`)
-- and multiline comments (`%{` and `%}`)
lex1 :: [Tok] -> [Tok]
lex1 = normal where
  normal [] = []
  normal (t:ts)
    | t == squote = charlit (B0 :< t) ts
    | t == percent = lcomment (B0 :< t) ts
    | t == percentopenbrace = mlcomment (B0 :< (B0 :< t)) ts
    | otherwise = t : normal ts

  charlit acc [] = [grp Error acc]
  charlit acc (t:ts)
    | t == squote = grp Literal (acc :< t) : normal ts
    | kin t == Ret = grp Error acc : normal (t:ts)
    | otherwise = charlit (acc :< t) ts

  lcomment acc [] = [grp Comment acc]
  lcomment acc (t:ts)
    | kin t == Ret = grp Comment acc : normal (t:ts)
    | otherwise = lcomment (acc :< t) ts

  mlcomment B0 _ = error "stack should never be empty"
  mlcomment (az :< a) [] = let c0 = grp Error a in
    case az of
      B0 -> [c0]
      az :< a -> mlcomment (az :< (a :< c0)) []
  mlcomment acc@(az :< a) (t:ts)
    | t == percentopenbrace = mlcomment (acc :< (B0 :< t)) ts
    | t == percentclosbrace = let c0 = grp Comment (a :< t) in
        case az of
          B0 -> c0 : normal ts
          az :< a -> mlcomment (az :< (a :< c0)) ts
    | otherwise = mlcomment (az :< (a :< t)) ts

  squote = Tok Sym (0,0) "'"
  percent = Tok Sym (0,0) "%"
  percentopenbrace = Tok Sym (0,0) "%{"
  percentclosbrace = Tok Sym (0,0) "%}"

-- finds blocks delimited by a Blk keyword and `end`
lex2 :: [Tok] -> [Tok]
lex2 = helper B0 where
  helper B0 [] = []
  helper (az :< a) [] = helper az [grp Block a]
  helper az (t : ts)
    | kin t == Blk  = helper (az :< (B0 :< t)) ts
    | t == end = case az of
        az :< a -> helper az $ grp Block (a :< t) : ts
        B0 -> helper B0 $ grp Error (B0 :< t) : ts
  helper B0 (t : ts) = t : helper B0 ts
  helper (az :< a) (t : ts) = helper (az :< (a :< t)) ts

  end = Tok Key (0,0) "end"

-- finds brackets inside blocks but not vice versa
lex3 :: [Tok] -> [Tok]
lex3 = helper B0 where
  helper B0 [] = []
  helper (az :< (_, a)) [] = helper az [grp Error a]
  helper az (t : ts)
    | Just b <- opener t = helper (az :< (b, B0 :< t)) ts
  helper (az :< (b, a)) (t : ts)
    | t == closer b = helper az $ grp (Bracket b) (a :< t) : ts
    | otherwise = helper (az :< (b, a :< t)) ts
  helper B0 (Tok (Grp Block ss) p s : ts) = Tok (Grp Block $ lex3 ss) p s : helper B0 ts
  helper B0 (t : ts)  = t : helper B0 ts

grp :: Grouping -> Bwd Tok -> Tok
grp g tz = case tz <>> [] of
  ts@(t:_) -> Tok (Grp g ts) (pos t) (ts >>= raw)
  [] -> error "should not make empty group"

unix :: T.Text -> T.Text
unix t = case T.uncons t of
  Nothing -> t
  Just (c,t) -> case c of
    '\r' -> case T.uncons t of
      Just ('\n', _) -> unix t
      _ -> T.cons '\n' (unix t)
    _ -> T.cons c (unix t)

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

keywords :: M.Map String Bool -- whether the keyword begins a block ending with `end`
keywords = M.fromList (map (, True) ["if", "function", "for", "while", "switch"])
         <> M.fromList (map (, False) ["else", "elseif", "case", "otherwise", "end"])

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


opener :: Tok -> Maybe Bracket
opener = flip lookup $ map (Tok Sym (0,0) *** id) [("(", Round), ("[", Square), ("{", Curly)]

closer :: Bracket -> Tok
closer b = Tok Sym (0,0) $ case b of
   Round  -> ")"
   Square -> "]"
   Curly  -> "}"
