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

reassemble :: (Nonce, Map Nonce String) -> MachineState -> String
reassemble (n, tab) ms =
  case either (const ms) id $ renamePass ms of
    ms -> case Map.lookup n (nonceTable tab (resetCursor (position ms))) of
      Just ts -> ts
      Nothing -> []


nonceTable :: Map Nonce String -> Cursor Frame -> Map Nonce String
nonceTable table (fz :<+>: []) = table
nonceTable table (fz :<+>: Fork _ fs' e : fs) = nonceTable (nonceTable table (fz :<+>: fs)) (fz :<+>: fs')
nonceTable table (fz :<+>: Source (n, ts) : fs) = let m = nonceTable table (fz :<+>: fs) in Map.insert n (ts >>= nonceExpand m) m
nonceTable table (fz :<+>: f : fs) = nonceTable table (fz :< f :<+>: fs)

renamePass :: MachineState -> Either Gripe MachineState
renamePass ms = inbound ms
  where
    inbound :: MachineState -> Either Gripe MachineState
    inbound ms@(MS { position = fz :<+>: fs, problem = p }) =
      case (fz <>< fs, p) of
        (fz :< Source (n, [t]), Done (FreeVar x)) | kin t == Nom ->
          case renamer fz x False of
            Nothing -> Left $ "Inconsistent renaming of " ++ raw t ++ "."
            Just x' -> outbound ms{ position = fz :<+>: [Source (n, [t{ raw = x' }])] }
        (fz :< Source (n, t:ts) :< Source (m, t':ts'), Done (Atom ""))
          | raw t' == "rename", Grp Directive (Hide dirts) <- kin t ->
            outbound ms{
              position = fz :<+>:
                [Source (n, t{ kin = Grp Response (Hide $ respond dirts) } : ts)
                ,Source (m, t'{raw = "renamed"} : ts')]}
        (fz, p) -> outbound ms{ position = fz :<+>: [] }

    outbound :: MachineState -> Either Gripe MachineState
    outbound ms@(MS { position = B0 :<+>: _}) = Right ms
    outbound ms@(MS { position = fz :< f :<+>: fs, problem = p}) = case f of
     Fork (Left frk) fs' p' -> inbound ms{ position = fz :< Fork (Right frk) fs p :<+>: fs' , problem = p' }
     Fork (Right frk) fs' p' -> outbound ms{ position = fz :<+>: Fork (Left frk) fs p : fs', problem = p' }
     _ -> outbound ms { position = fz :<+>: f : fs }

    renamer :: Bwd Frame
            -> Name
            -> Bool  -- have we found FunctionLocale yet?
            -> Maybe String
    renamer B0 n b = error "ScriptLocale disappeared in renamer!"
    renamer (fz :< Locale FunctionLocale) n b = renamer fz n True
    renamer (fz :< Locale ScriptLocale) n True = error "Declaration disappeared in renamer!"
    renamer (fz :< Declaration n' d) n b =
      if n == n' then case (d, newName d) of
        (UserDecl _ _ _ capturable, Just s) ->
          if capturable && captured fz b s then Nothing else pure s
        _ -> Nothing
      else do
        s <- renamer fz n b
        s' <- newName d
        s <$ guard (s /= s')
    renamer (fz :< f) n b = renamer fz n b

    captured :: Bwd Frame -> Bool -> String -> Bool
    captured B0 b s = False
    captured (fz :< Locale FunctionLocale) b s = captured fz True s
    captured (fz :< Locale ScriptLocale) True s = False
    captured (fz :< Declaration _ d) b s | newName d == Just s = True
    captured (fz :< f) b s = captured fz b s

    newName :: DeclarationType -> Maybe String
    newName (UserDecl old seen [] capturable) = Just old
    newName (UserDecl old seen [new] capturable) = Just new
    newName _ = Nothing

    respond :: [Tok] -> [Tok]
    respond (t:ts)
      | raw t == ">" = t{raw = "<"} : ts
      | otherwise = t: respond ts
    respond [] = []

-- Plan:
-- 1. Try to do renaming, computing Either Gripe MachineState, turning directives into responses
-- 2. If we succeed, reassemble
-- 3. If we fail, do another pass, turning directives into responses explaining what the problem was
-- 4. Avoid code duplication by doing the above in "one pass", Oxford style
