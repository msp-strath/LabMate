{-# LANGUAGE OverloadedStrings, LambdaCase #-}

module Lex where

import Data.Char
import Data.List
import Control.Monad
import Control.Applicative
import Control.Arrow ((***))
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as Map

import Bwd
import Hide

data Kin
  = Nom -- identifiers
  | Blk -- keywords opening a block
  | Key -- keywords that don't open blocks
  | Sym -- symbols/operators
  | Grp Grouping (Hide [Tok])  -- anything composite
  | Spc -- whitespace not newline
  | Dig -- sequence of digits
  | Ret -- return character
  | Nop -- token to be filtered from a Grp, keeping its raw text
  | Urk -- unrecognized
  | Non Nonce -- nonces
  deriving (Show, Eq)

type Nonce = Int

non :: Int -> Tok
non n = Tok ("$" ++ show n) (Non n) dump

data Tok = Tok
  { raw :: String
  , kin :: Kin
  , pos :: Hide Pos
  } deriving (Show, Eq)

data Grouping = Literal
              | Comment
              | Directive
              | Response
              | Generated
              | Block
              | Bracket Bracket
              | Line LineTerminator
              | Error
  deriving (Show, Eq)

data Bracket = Round | Square | Curly
  deriving (Show, Eq)

brackets :: Bracket -> (String, String)
brackets Round = ("(", ")")
brackets Square = ("[", "]")
brackets Curly = ("{", "}")

data LineTerminator = RET | Semicolon
  deriving (Show, Eq)

type Pos = (Int, Int) -- line, column with 0 origin

dump :: Hide Pos
dump = Hide (0,0)

sym :: String -> Tok
sym s = Tok s Sym dump

type Doc = (T.Text, Pos)

lexer :: T.Text -> [Tok]
lexer = lex4 . lex3 . lex2 . lex1 . lex0

-- basic lexing
lex0 :: T.Text -> [Tok]
lex0 t = unfoldr tok (t, (0, 0)) where
  tok :: Doc -> Maybe (Tok, Doc)
  tok d@(_, p) = case munch d symbols of
    Just (s, d) -> return (Tok s Sym (Hide p), d)
    Nothing -> peek d >>= \case
      (c, d)
        | isAlpha c ->
          let (s, d') = spand (\ c -> isAlphaNum c || c == '_') d
              x = c : s
              k = case Map.lookup x keywords of
                Just False -> Key
                Just True  -> Blk
                _          -> Nom
          in  return (Tok x k (Hide p), d')
        | isNL c -> return (Tok [c] Ret (Hide p), d)
        | isSpace c -> let (s, d') = spand (\ c -> isSpace c && not (isNL c)) d in
            return (Tok (c : s)  Spc (Hide p), d')
        | isDigit c -> let (s, d') = spand isDigit d in
            return (Tok (c : s) Dig (Hide p), d')
        | otherwise -> return (Tok [c] Urk (Hide p), d)


-- grouping character literals (surrounded by `'`), end of line comments (`%`),
-- ellipsis comments (...) and multiline comments (`%{` and `%}`)
lex1 :: [Tok] -> [Tok]
lex1 = normal False False where
  normal :: Bool -- have we seen any non-space characters on the current line?
         -> Bool -- can we transpose?
         -> [Tok] -> [Tok]
  normal _ _ [] = []
  normal nsp xp (t:ts)
    | t == sym "%{" && not nsp && blankToEOL ts
      = mlcomment True (B0 :< (B0 :< t)) ts
    | t == sym "'" && not xp = charlit (B0 :< t) ts
    | t `elem` [sym "%", sym "%{", sym "%}"]
      = lcomment (typeOfComment ts) (B0 :< t) ts
    | t == sym "..." = ecomment (B0 :< t) ts
    | t == sym "%<{" && not nsp
      = generatedCode False (B0 :< t {kin = Nop}) ts
    | otherwise    = t : normal (updateNSP nsp t) (setXP t) ts

  charlit acc [] = grpCons Error acc []
  charlit acc (t:ts)
    -- We have already made ".'" a token, even in string
    -- literals. It's okay to put it on the accumulator as is, because
    -- the parser for string literals uses the raw text anyway.
    | t `elem` [sym ".'", sym "'"] =
      case ts of
        (t':ts) | t' == sym "'" -> charlit (acc :< t :< t') ts
        _ -> grpCons Literal (acc :< t) $ normal True False ts
    | kin t == Ret = grpCons Error acc $ normal True False (t:ts)
    | otherwise = charlit (acc :< t) ts

  lcomment grp acc [] = fixup $ grpCons grp acc []
  lcomment grp acc (t:ts)
    | kin t == Ret = fixup $ grpCons grp acc $ normal True False (t:ts)
    | otherwise = lcomment grp (acc :< t) ts

  fixup (t@Tok { kin = Grp g (Hide (a0:a1:as)) }:ts) | g `elem` [Directive, Response]
    = t { kin = Grp g (Hide (a0:a1:lex1 as))} : ts
  fixup ts = ts

  -- ellipsis comments include the line break in the comment
  ecomment acc [] = grpCons Comment acc []
  ecomment acc (t:ts)
    | kin t == Ret = grpCons Comment (acc :< t) $ normal False False ts
    | otherwise = ecomment (acc :< t) ts

  mlcomment _ B0 _ = error "stack should never be empty"
  mlcomment nsp (az :< a) [] = let c0 = grp Error a in
    case az of
      B0 -> [c0]
      az :< a -> mlcomment nsp (az :< (a :< c0)) []
  mlcomment nsp acc@(az :< a) (t:ts)
    | t == sym "%{" && not nsp && blankToEOL ts
      = mlcomment True (acc :< (B0 :< t)) ts
    | t == sym "%}" && not nsp && blankToEOL ts
      = let c0 = grp Comment (a :< t) in
        case az of
          B0 -> c0 : normal False False ts
          az :< a -> mlcomment True (az :< (a :< c0)) ts
    | otherwise    = mlcomment (updateNSP nsp t) (az :< (a :< t)) ts

  generatedCode :: Bool -- have we seen the closing delimiter yet?
                -> Bwd Tok -- accumulator
                -> [Tok] -> [Tok]
  generatedCode _ acc [] = grpCons Generated acc []
  generatedCode b acc (t:ts)
    | t == sym "%<}" && not b = generatedCode True (acc :< t {kin = Nop}) ts
    | kin t == Ret && b =  grpCons Generated (acc :< t) (normal True False ts)
    | otherwise = generatedCode b (acc :< t) ts

  blankToEOL :: [Tok] -> Bool
  blankToEOL [] = True
  blankToEOL (t:ts)
    | kin t == Ret = True
    | kin t == Spc = blankToEOL ts
    | otherwise = False

  updateNSP :: Bool -> Tok -> Bool
  updateNSP nsp t
    | kin t == Spc = nsp
    | kin t == Ret = False
    | otherwise    = True

  setXP :: Tok -> Bool
  setXP t = kin t == Nom || t `elem` map sym [")", "]", "}", "'", ".'"]

  typeOfComment :: [Tok] -> Grouping
  typeOfComment (t:ts) | t == sym ">" = Directive
  typeOfComment (t:ts) | t == sym "<" = Response
  typeOfComment _ = Comment

-- finds blocks delimited by a Blk keyword and `end`
lex2 :: [Tok] -> [Tok]
lex2 = helper B0 where
  helper B0 [] = []
  helper (az :< a) [] = helper az $ grpCons Block a []
  helper az (t : ts)
    | kin t == Blk  = helper (az :< (B0 :< t)) ts
    | t == end && endsABlock az ts = case az of
        az :< a -> helper az $ grpCons Block (a :< t) ts
  helper B0 (t : ts) = gen t : helper B0 ts
  helper (az :< a) (t : ts) = helper (az :< (a :< gen t)) ts

  gen (t@Tok { kin = Grp Generated (Hide ss) }) = t { kin = Grp Generated (Hide $ lex2 ss) }
  gen t | t == end =  t { kin = Nom} -- An 'end' in an expression, not a block delimiter
  gen t = t

  endsABlock B0 ts = False
  endsABlock (_ :< a) ts = junkUntilNL ts && junkUntilNL (revz a)

  junkUntilNL [] = True
  junkUntilNL (t:ts)
    | kin t == Ret || t == sym ";" = True
    | kin t == Spc || isComment t = junkUntilNL ts
    | otherwise = False

  end = Tok "end" Key dump

-- finds brackets inside blocks and directives, but not vice versa
lex3 :: [Tok] -> [Tok]
lex3 = helper B0 where
  helper B0 [] = []
  helper (az :< (_, a)) [] = helper az $ grpCons Error a []
  helper az (t : ts)
    | Just b <- opener t = helper (az :< (b, B0 :< t {kin = Nop})) ts
  helper (az :< (b, a)) (t : ts)
    | t == closer b = helper az $ grpCons (Bracket b) (a :< t {kin = Nop}) ts
    | otherwise = helper (az :< (b, a :< t)) ts
  helper B0 (Tok s (Grp g ss) p : ts) | g `elem` [Block, Directive, Generated] =
    Tok s (Grp g $ Hide $ lex3 $ unhide ss) p : helper B0 ts
  helper B0 (t : ts)  = t : helper B0 ts

-- finds and groups lines
lex4 :: [Tok] -> [Tok]
lex4 = helper B0 where
  helper acc [] = grpCons (Line RET) acc []
  helper acc (Tok s (Grp k ss) p : ts)
    | k `elem` blocky =
      helper (acc :< Tok s (Grp k $ Hide $ lex4 $ unhide ss) p) ts
    | k `elem` passedthrough =
      helper (acc :< Tok s (Grp k $ Hide $ map sublex4 $ unhide ss) p) ts
  helper acc (t : ts)
    | kin t == Ret = ending (acc :< t) RET B0 ts
    | t == semicolon = ending (acc :< t) Semicolon B0 ts
    | otherwise = helper (acc :< t) ts

  ending :: Bwd Tok -> LineTerminator -> Bwd Tok -> [Tok] -> [Tok]
  ending acc e wh (t : ts)
    | kin t == Ret = ending (acc <> wh :< t) e B0 ts
    | t == semicolon = ending (acc <> wh :< t) Semicolon B0 ts
    | kin t `elem` [Spc, Grp Comment (Hide [])] = ending acc e (wh :< t) ts
  ending acc e wh ts = grpCons (Line e) acc $ lex4 (wh <>> ts)

  semicolon = sym ";"

  blocky = [Block, Bracket Square, Bracket Curly, Generated]
  passedthrough = [Bracket Round, Directive]

  sublex4 :: Tok -> Tok
  sublex4 (Tok s (Grp k ss) p)
    | k `elem` blocky = Tok s (Grp k $ Hide $ lex4 $ unhide ss) p
  sublex4 (Tok s (Grp k ss) p)
    | k `elem` passedthrough = Tok s (Grp k $ Hide $ map sublex4 $ unhide ss) p
  sublex4 t = t

grp :: Grouping -> Bwd Tok -> Tok
grp g tz = case tz <>> [] of
  ts@(t:_) -> Tok (ts >>= raw)
    (Grp g $ Hide (filter ((Nop /=) . kin) ts)) (pos t)
  [] -> error "should not make empty group"

grpCons :: Grouping -> Bwd Tok -> [Tok] -> [Tok]
grpCons g B0 ts = ts
grpCons g tz ts = grp g tz : ts

-- only use after lex1
isComment :: Tok -> Bool
isComment (Tok { kin = Grp Comment _ }) = True
isComment _ = False

unix :: T.Text -> T.Text
unix t = case T.uncons t of
  Nothing -> t
  Just (c,t) -> case c of
    '\r' -> case T.uncons t of
      Just ('\n', _) -> unix t
      _ -> T.cons '\n' (unix t)
    _ | T.null t && c /= '\n' -> T.pack [c, '\n']
      | otherwise -> T.cons c (unix t)

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

data Table = Table Bool (Map.Map Char Table) deriving Show

empT :: Table
empT = Table False Map.empty

insT :: String -> Table -> Table
insT [] (Table _ m) = Table True m
insT (c : s) (Table b m) = Table b (Map.alter go c m) where
  go Nothing  = Just (insT s empT)
  go (Just t) = Just (insT s t)

munch :: Doc -> Table -> Maybe (String, Doc)
munch d (Table b m) = (do
  (c, d') <- peek d
  t <- Map.lookup c m
  (s, d) <- munch d' t
  return (c : s, d)
  ) <|> ("", d) <$ guard b

keywords :: Map.Map String Bool -- whether the keyword begins a block ending with `end`
keywords = Map.fromList (map (, True) ["if", "function", "for", "while", "switch"])
         <> Map.fromList (map (, False) ["else", "elseif", "case", "otherwise", "end",
                                       "break", "return", "continue"])

{-
%>  directive
%<  response
%<{
    generated code
%<}
-}

binOps :: [String]
binOps =
  [ "+", "-", ".*", "*", "./", "/", ".\\", "\\", ".^", "^"
  , "==", "~=", ">", ">=", "<", "<="
  , "&", "|", "&&", "||", "~", ":"
  ]


symbols :: Table
symbols = foldr insT empT $ binOps ++
  [ ".'", "'"
  , "@"
  , "."
  , "..."
  , "%", "%{", "%}"
  , "%<{", "%<}" -- generated code delimiters
  , "!", "?"
  , "\"", "\"\""
  , "="
  , ".?"
  , "(", ")", "[", "]", "{", "}", ",", ";"
  ]

opener :: Tok -> Maybe Bracket
opener = flip lookup $ map (sym *** id) [("(", Round), ("[", Square), ("{", Curly)]

closer :: Bracket -> Tok
closer b = sym $ case b of
   Round  -> ")"
   Square -> "]"
   Curly  -> "}"

seeToks :: [Tok] -> IO ()
seeToks ts = go 0 ts where
  go i [] = return ()
  go i ts = case span (\ t -> case kin t of {Grp _ _ -> False; _ -> True}) ts of
    (ss, us) -> do
      putStr (replicate i ' ')
      mapM_ (\ t -> putStr (show (kin t) ++ " " ++ raw t ++ " ")) ss
      putStrLn ""
      case us of
        Tok {kin = Grp g (Hide ts)} : us -> do
          putStr (replicate i ' '); print g
          go (i + 2) ts
          go i us
        _ -> return ()

groupString :: Grouping -> String -> String
groupString g s = prefix g ++ s ++ suffix g
  where
    prefix g = case g of
      Bracket b -> fst (brackets b)
      Generated -> "%<{"
      _ -> ""
    suffix g = case g of
      Bracket b -> snd (brackets b)
      Generated -> "%<}"
      _ -> ""

groupRaw :: Grouping -> [Tok] -> String
groupRaw g ts = groupString g (ts >>= raw)

nonceExpand :: Map Nonce String -> Tok -> String
nonceExpand table t | Non n <- kin t = case Map.lookup n table of
  Just ts -> ts
  Nothing -> error $ "should be impossible: " ++ show n
nonceExpand table t | Grp g (Hide ts) <- kin t = groupString g (ts >>= nonceExpand table)
nonceExpand _ t = raw t

type Source = (Nonce, Hide [Tok])

data WithSource a = (:<=:) { what :: a , source :: Source }
  deriving (Functor, Show)

nonce :: WithSource a -> Nonce
nonce = fst . source

{-
instance Show a => Show (WithSource a) where
  show (a :<=: (n, src)) = "$" ++ show n ++ " = `" ++ (src >>= showEaten) ++ "`" ++ show a
    where
      showEaten t
        | Non n <- kin t = "$" ++ show n
        | otherwise = raw t
-}
