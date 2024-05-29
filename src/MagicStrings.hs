module MagicStrings where

-- core types
pattern SType = "Type"
pattern SOne  = "One"
pattern STwo  = "Two"
pattern SAbel = "Abel"
pattern SList = "List"
pattern SAtom = "Atom"
pattern SChar = "Char"
pattern SEnum = "Enum"
pattern SPi   = "Pi"
pattern SSig  = "Sigma"
pattern SDest     = "Destination"
pattern SMatrix   = "Matrix"
pattern SQuantity = "Quantity"

-- eliminators
pattern Sfst  = "fst"
pattern Ssnd  = "snd"
-- constructors
pattern Splus = "plus"
pattern Sone = "one"
pattern Shjux = "hjux"
pattern Svjux = "vjux"

pattern Sand = "and"

-- Labmate user types
pattern Lint = "int"
pattern Lstring = "string"
