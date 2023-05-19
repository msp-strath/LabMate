module Parse.InputFormat(pdescription) where

import Parse
import Syntax
import Lex
import Hide
--mgen
import Description
import Dimension

import Control.Monad
import Control.Applicative
import Data.Foldable
import Data.Char

pkey :: Parser a -> Parser a
pkey p = psym "@" *> p

pinteger :: Parser Int
pinteger = maybe id (const negate) <$> optional psign <*> ppositive
  where
    psign = psym "-" <* pospc
    ppositive = read . concat <$> some (prawif Dig)

pcomment :: Parser [String]
pcomment = pgreedy . ptok $ \t -> raw t <$ guard (t /= sym "@" && t /= sym ":")

pheader :: Parser (Int, String)
pheader = pnom' <* pospc <* psym ":"
 where
   pnom' = ptok $ \ t -> (snd . unhide. pos $ t, raw t) <$ guard (kin t == Nom)

pwithheader :: (Int -> String -> Parser a) -> Parser (Int, a)
pwithheader p = pheader <* pcomment >>= \(n, s) -> (n,) <$> p n s

pline' :: Parser a -> Parser a
pline' p = pgrp isLine (p <* pjunk True)
  where
    isLine :: Grouping -> Bool
    isLine (Line _) = True
    isLine _ = False

pblock :: Int -> Parser (Int, a) -> Parser (Int, [a])
pblock n p = do
  (n', x) <- pline' p
  guard (n' > n)
  (ns, xs) <- unzip <$> pgreedy (pline' p)
  guard $ all (== n') ns
  pure (n', x : xs)

pderivedunit :: Parser DerivedUnitNF
pderivedunit = undefined

pdescription :: Parser InputBody
pdescription = pgreedy (pline' pcomment) *> (snd <$> pobject)
  where
    pobject = do
      (n, h) <- pline' (pospc *> pheader <* pcomment)
      (_, body) <- pblock n (pospc *> pdesc)
      pure (n, Object h body)

    pdesc :: Parser (Int, InputBody)
    pdesc = parray <|> parraylit <|> pfield <|> pobject


    pfieldtype = pkey (Nat <$ asum (pkin Nom <$> ["number", "Number", "int", "Int"]))
                   -- <|> Quantity <$> pderivedunit)

    pfield = pwithheader $ \ _ h -> Field h <$> pfieldtype <* pcomment

    parray = pwithheader $ \ _ h -> Array h <$> pindex <* pcomment <*> ptypes <* pcomment
      where
        pindex = pkey (Lit <$> pinteger <|> FieldAccess <$> psep1 (psym ".") pnom)
        ptypes = psep1 (punc ",") pfieldtype


    parraylit = pwithheader $ \n h -> ArrayLit h <$> liftA2 (<$) (pfieldtype <* pcomment) (go n)
      where
        go n = snd <$> pblock n (pospc *> psym' "-" <* pcomment)
        psym' s = ptok $ \ t -> (snd . unhide . pos $ t, ()) <$ guard (kin t == Sym && raw t == s)
