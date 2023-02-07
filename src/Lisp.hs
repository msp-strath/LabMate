{-# LANGUAGE PatternGuards #-}
module Lisp where

import Hide
import Lex

import BRect

data Lisp = List [Lisp] | Atom Tok
  deriving (Eq)

showCdr :: [Lisp] -> String
showCdr [] = ""
showCdr (t:ts) = " " ++ show t ++ showCdr ts

instance Show Lisp where
  show (List ts) = "[" ++ showCdr ts ++ "]"
  show (Atom t) = raw t

tokenStreamToLisp :: [Tok] -> Lisp
tokenStreamToLisp = List . tokenStreamToListLisp

tokenStreamToListLisp :: [Tok] -> [Lisp]
tokenStreamToListLisp [] = []
tokenStreamToListLisp (t:ts)
  | discard t = tokenStreamToListLisp ts
  | Just ss <- unpack t = tokenStreamToLisp ss : tokenStreamToListLisp ts
  | otherwise = Atom t : tokenStreamToListLisp ts

  where
    discard :: Tok -> Bool
    discard t = case kin t of
      Spc -> True
      Ret -> True
      Grp k _ -> k `elem` [Comment, Response, Generated, Error]
      Urk -> True
      Sym -> raw t `elem` ["[", "]"]
      _   -> False

    unpack :: Tok -> Maybe [Tok]
    unpack t | Grp g (Hide ts) <- kin t = case g of
                 Literal -> Nothing
                 Bracket Square -> Just (sym "Square" : ts)
                 _ -> Just ts
    unpack _ = Nothing

brectLisp :: Lisp -> BRect
brectLisp (Atom t) = word (raw t)
brectLisp (List []) = word ""
brectLisp (List (t:ts)) = par $ foldl (\ b s -> b `tackOn` brectLisp s) (brectLisp t) ts

pretty :: Int -> Lisp -> String
pretty k = brect k . brectLisp
