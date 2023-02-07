{-# LANGUAGE PatternGuards #-}
module Lisp where

import Hide
import Lex

data Lisp = Cons Lisp Lisp | Nil | Atom Tok
  deriving (Eq)

showCdr :: Lisp -> String
showCdr Nil = ""
showCdr (Atom t) = "| " ++ raw t
showCdr (Cons s t) = " " ++ show s ++ showCdr t

instance Show Lisp where
  show (Cons s t) = "[" ++ show s ++ showCdr t ++ "]"
  show Nil = "[]"
  show (Atom t) = raw t

tokenStreamToLisp :: [Tok] -> Lisp
tokenStreamToLisp [] = Nil
tokenStreamToLisp (t:ts)
  | discard t = tokenStreamToLisp ts
  | Just ss <- unpack t = Cons (tokenStreamToLisp ss) (tokenStreamToLisp ts)
  | otherwise = Cons (Atom t) (tokenStreamToLisp ts)

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

