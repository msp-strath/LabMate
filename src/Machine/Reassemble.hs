module Machine.Reassemble where
import Machine
import Bwd

import Control.Monad
import Lex
import Parse
import Parse.Matlab
import Syntax
import Hide

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.List as L
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Writer
import Data.Foldable (traverse_)

data RenameGripe
  = Captured  -- the new name is already in scope
  | Capturing -- the new name prevents a subsequent declaration
  | TooManyNames
  deriving (Show, Eq, Ord)

renameGripeResponse :: RenameGripe -> String
renameGripeResponse g = "Renaming not possible: " ++ case g of
  Captured -> "the new name was already taken."
  Capturing -> "the new name will be needed later."
  TooManyNames -> "too many new names for the same old name."

type RenameProblems = Set (Source, RenameGripe)

reassemble :: (Nonce, Map Nonce String) -> MachineState -> String
reassemble (n, tab) ms =
  let (ms', probs) = runWriter (renamePass ms)
      responses = foldr (\((n, _), grp) rs -> Map.insertWith (++) n [renameGripeResponse grp] rs) Map.empty probs in
  fromMaybe [] $ Map.lookup n (nonceTable responses tab (resetCursor (position $ if Set.null probs then ms' else ms)))



nonceTable :: Map Nonce [String] -> Map Nonce String -> Cursor Frame -> Map Nonce String
nonceTable responses table (fz :<+>: []) = table
nonceTable responses table (fz :<+>: Fork _ fs' e : fs) = nonceTable responses (nonceTable responses table (fz :<+>: fs)) (fz :<+>: fs')
nonceTable responses table (fz :<+>: Source (n, Hide ts) : fs) =
  let m = nonceTable responses table (fz :<+>: fs) in
  Map.insert n (L.intercalate "\n%< " $ (ts >>= nonceExpand m) : Map.findWithDefault [] n responses) m
nonceTable responses table (fz :<+>: f : fs) = nonceTable responses table (fz :< f :<+>: fs)

renamePass :: MachineState -> Writer RenameProblems MachineState
renamePass ms = inbound ms
  where
    inbound :: MachineState -> Writer RenameProblems MachineState
    inbound ms@(MS { position = fz :<+>: fs, problem = p }) =
      case (fz <>< fs, p) of
        (fz :< Source (n, Hide [t]), Done (FreeVar x)) | kin t == Nom -> do
          x' <- renamer fz x False
          outbound ms{ position = fz :<+>: [Source (n, Hide [t{ raw = x' }])] }
        (fz :< Source (n, Hide (t:ts)) :< Source (m, Hide (t':ts')), Done (Atom ""))
          | raw t' == "rename", Grp Directive (Hide dirts) <- kin t ->
            outbound ms{
              position = fz :<+>:
                [Source (n, Hide (t{ kin = Grp Response (Hide $ respond dirts) } : ts))
                ,Source (m, Hide (t'{raw = "renamed"} : ts'))]}
        (fz, p) -> outbound ms{ position = fz :<+>: [] }

    outbound :: MachineState -> Writer RenameProblems MachineState
    outbound ms@(MS { position = B0 :<+>: _}) = pure ms
    outbound ms@(MS { position = fz :< f :<+>: fs, problem = p}) = case f of
     Fork (Left frk) fs' p' -> inbound ms{ position = fz :< Fork (Right frk) fs p :<+>: fs' , problem = p' }
     Fork (Right frk) fs' p' -> outbound ms{ position = fz :<+>: Fork (Left frk) fs p : fs', problem = p' }
     _ -> outbound ms { position = fz :<+>: f : fs }

    renamer :: Bwd Frame
            -> Name
            -> Bool  -- have we found FunctionLocale yet?
            -> Writer RenameProblems String
    renamer B0 n b = error "ScriptLocale disappeared in renamer!"
    renamer (fz :< Locale FunctionLocale) n b = renamer fz n True
    renamer (fz :< Locale ScriptLocale) n True = error "Declaration disappeared in renamer!"
    renamer (fz :< Declaration n' d) n b = do
      s <- newName d
      if n == n' then case d of
        UserDecl _ _ _ capturable -> do
          when capturable $ do
            cap <- captured fz b s
            when cap $ tellGripes Captured d
          pure s
        _ -> error "Impossible: renaming LabRat var"
      else do
        s <- renamer fz n b
        s' <- newName d
        when (s == s') $ tellGripes Captured d
        pure s
    renamer (fz :< f) n b = renamer fz n b

    captured :: Bwd Frame
             -> Bool -- have we found a FunctionLocale yet?
             -> String
             -> Writer RenameProblems Bool
    captured B0 b s = pure False
    captured (fz :< Locale FunctionLocale) b s = captured fz True s
    captured (fz :< Locale ScriptLocale) True s = pure False
    captured (fz :< Declaration _ d) b s = do
      s' <- newName d
      if s == s'
        then do
          tellGripes Capturing d
          pure True
        else captured fz b s
    captured (fz :< f) b s = captured fz b s

    newName :: DeclarationType -> Writer RenameProblems String
    newName (UserDecl old seen [] capturable) = pure old
    newName (UserDecl old seen names capturable)
      | [new] <- L.nub (map fst names) = pure new
    newName d@(UserDecl old _ _ _) = old <$ tellGripes TooManyNames d

    respond :: [Tok] -> [Tok]
    respond (t:ts)
      | raw t == ">" = t{ raw = "<" } : ts
      | otherwise = t: respond ts
    respond [] = []

    tellGripes :: RenameGripe -> DeclarationType -> Writer RenameProblems ()
    tellGripes grp = \case
       UserDecl _ _ newNames _ -> traverse_ (\(_, src) -> tell $ Set.singleton (src, grp)) newNames
       _ -> pure ()

-- Plan:
-- 1. Try to do renaming, computing Either Gripe MachineState, turning directives into responses
-- 2. If we succeed, reassemble
-- 3. If we fail, do another pass, turning directives into responses explaining what the problem was
-- 4. Avoid code duplication by doing the above in "one pass", Oxford style
