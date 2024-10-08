module Machine.Reassemble where
import Machine
import Bwd

import Control.Monad
import Lex
import Parse
import Parse.Matlab
import Syntax
import Term
import Hide

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.List as L
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Writer
import Data.Foldable (traverse_)

import Debug.Trace

track = const id

data RenameGripe
  = Captured  -- the new name is already in scope
  | Capturing -- the new name prevents a subsequent declaration
  | TooManyNames
  deriving (Show, Eq, Ord)

renameGripeResponse :: RenameGripe -> String
renameGripeResponse g = "Error: renaming not possible: " ++ case g of
  Captured -> "the new name was already taken."
  Capturing -> "the new name will be needed later."
  TooManyNames -> "too many new names for the same old name."

type RenameProblems = Set (ResponseLocation, RenameGripe)

reassemble :: Nonce -> MachineState -> String
reassemble n ms =
  let (ms', probs) = runWriter (renamePass ms)
      tab = nonceTable ms
      tab' = foldr (\((n, c), grp) rs -> Map.insertWith (++) n (concat ["\n", replicate c ' ', "%< ", renameGripeResponse grp]) rs) tab probs
  in fromMaybe [] $ Map.lookup n (updateNonceTable tab' (resetCursor (position $ if Set.null probs then ms' else ms)))

updateNonceTable :: Map Nonce String -> Cursor Frame -> Map Nonce String
updateNonceTable table (fz :<+>: []) = table
updateNonceTable table (fz :<+>: Fork frk : fs) =
  updateNonceTable (updateNonceTable table (fz :<+>: fs)) (fz :<+>: either fframes fframes frk)
updateNonceTable table (fz :<+>: Source (n, Hide ts) : fs) =
  let m = updateNonceTable table (fz :<+>: fs)
      ts' = ts >>= nonceExpand m
  in Map.insert (track ("UNT " ++ show n ++ " " ++ ts') n) ts' m
updateNonceTable table (fz :<+>: f : fs) = updateNonceTable table (fz :< f :<+>: fs)

renamePass :: MachineState -> Writer RenameProblems MachineState
renamePass ms = inbound ms
  where
    inbound :: MachineState -> Writer RenameProblems MachineState
    inbound ms@(MS { position = fz :<+>: fs, problem = p }) =
      case outsource (fz <>< fs :<+>: [], p) of
        (fz :< Source (n, Hide [t]) :<+>: fs, Done (FreeVar x)) | kin t == Nom -> do
          ~True <- track ("HIT" ++ show (x, n)) $ pure True
          x' <- renamer fz x False
          outbound mempty ms{ position = fz :<+>: Source (n, Hide [t{ raw = x' }]) : fs }
        (fz :< Source (l, Hide (s:ss)) :< Source (n, Hide ts) :< Source (m, Hide (t':ts')) :<+>: fs, Done (Atom ""))
          | raw t' == "rename", Grp Directive dss <- kin s ->
            outbound mempty ms{
              position = fz :<+>:
                  Source (l, Hide (s{kin = Grp Response dss} : ss))
                : Source (n, Hide (respond ts))
                : Source (m, Hide (t'{raw = "renamed"} : ts'))
                : fs
              }
        (cur, p) -> outbound mempty ms{ position = cur }

    outsource :: (Cursor Frame, Problem) -> (Cursor Frame, Problem)
    outsource cur@(_ :< Source _ :<+>: _, _) = cur
    -- our expectations of where `Done (Freevar x)` is w.r.t to the
    -- Source Frame have become more liberal,
    outsource cur@(fz :< Fork (Left MkFork{..}) :<+>: fs, p)
      | any sourceFrameEh fframes = cur
      | p'@(Done (FreeVar x)) <- fprob = outsource (fz :<+>: Fork -- TODO: worry about fstatus
                                                    (Right MkFork{fprob = p, fframes = fs, fstatus = mempty}) : fframes, p')
    outsource cur@(fz :< Fork (Right MkFork{..}) :<+>: fs, p)
      | any sourceFrameEh fframes = cur
      | p'@(Done (FreeVar x)) <- fprob = outsource (fz :<+>: Fork -- TODO: worry about fstatus
                                                    (Left MkFork{fprob = p, fframes = fs, fstatus = mempty}) : fframes, p')
    outsource (fz :< f :<+>: fs, p) = outsource (fz :<+>: f : fs, p)
    outsource cur@(B0 :<+>: _, _) = cur

    outbound :: ForkCompleteStatus -> MachineState -> Writer RenameProblems MachineState
    outbound stat ms@(MS { position = B0 :<+>: _ }) = pure ms
    outbound stat ms@(MS { position = fz :< f :<+>: fs, problem = p }) = case f of
      Fork (Left MkFork{..}) -> inbound ms{ position = fz :< Fork (Right MkFork{fstatus = stat, fframes = fs, fprob= p})
                                                       :<+>: fframes
                                          , problem = fprob }
      Fork (Right MkFork{..}) -> outbound (fstatus <> stat) ms{ position = fz :<+>: Fork (Left MkFork{fstatus = stat, fframes = fs, fprob= p}) : fframes
                                            , problem = fprob }
      _ -> outbound stat ms { position = fz :<+>: f : fs }

    sourceFrameEh :: Frame -> Bool
    sourceFrameEh (Source _) = True
    sourceFrameEh _ = False

    renamer
      :: Bwd Frame
      -> Name
      -> Bool  -- have we found FunctionLocale yet?
      -> Writer RenameProblems String
    renamer B0 n b = error "ScriptLocale disappeared in renamer!"
    renamer (fz :< Locale (FunctionLocale _)) n b = renamer fz n True
    renamer (fz :< Locale ScriptLocale) n True = error "Declaration disappeared in renamer!"
    renamer (fz :< Declaration n' d@UserDecl{capturable}) n b = do
      s <- newName d
      if n == n' then do
          when capturable $ do
            cap <- captured fz b s
            when cap $ tellGripes Captured d
          pure s
      else do
        s <- renamer fz n b
        s' <- newName d
        when (s == s') $ tellGripes Captured d
        pure s
    renamer (fz :< f) n b = renamer fz n b

    captured
      :: Bwd Frame
      -> Bool -- have we found a FunctionLocale yet?
      -> String
      -> Writer RenameProblems Bool
    captured B0 b s = pure False
    captured (fz :< Locale (FunctionLocale _)) b s = captured fz True s
    captured (fz :< Locale ScriptLocale) True s = pure False
    captured (fz :< Declaration _ d) b s = do
      s' <- newName d
      if s == s'
        then do
          tellGripes Capturing d
          pure True
        else captured fz b s
    captured (fz :< f) b s = captured fz b s

    newName :: DeclarationType a -> Writer RenameProblems String
    newName UserDecl{ currentName = old, newNames = [] } = pure old
    newName UserDecl{ newNames } | [new] <- L.nub (map fst newNames) = pure new
    newName d@UserDecl{ currentName = old } = old <$ tellGripes TooManyNames d

    respond :: [Tok] -> [Tok]
    respond (t : ts) | Grp (Line e) (Hide ss) <- kin t, Just ss <- inner ss =
      t { kin = Grp (Line e) (Hide ss) } : ts
     where
       inner :: [Tok] -> Maybe [Tok]
       inner (t:ts)
         | raw t == ">" = Just $ t{ raw = "<" } : ts
         | otherwise = (t :) <$> inner ts
       inner [] = Nothing
    respond (t : ts) = t : respond ts
    respond [] = []

    tellGripes :: RenameGripe -> DeclarationType a -> Writer RenameProblems ()
    tellGripes grp UserDecl{ newNames } = traverse_ (\(_, src) -> tell $ Set.singleton (src, grp)) newNames

-- Plan:
-- 1. Try to do renaming, computing Either Gripe MachineState, turning directives into responses
-- 2. If we succeed, reassemble
-- 3. If we fail, do another pass, turning directives into responses explaining what the problem was
-- 4. Avoid code duplication by doing the above in "one pass", Oxford style
