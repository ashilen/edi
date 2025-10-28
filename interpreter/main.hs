data Syn
  = Leaf String
  | Branch Syn Syn

data Sem
  = Lex Ty String
  | Comb Ty Mode Sem Sem
  deriving (Show)

data EffX
  = SX -- computations with indeterminate results
  | RX Ty -- computations that query an environment of type Ty
  | WX Ty -- computations that store information of type Ty
  | CX Ty -- computations that quantify over Ty contexts
  -- and so on for other effects, as desired
  deriving (Eq, Show)

functor, applicative :: EffX -> Bool
functor _ = True
applicative (WX s) = monoid s
applicative f = functor f && True

monoid :: Ty -> Bool
monoid T = True
monoid _ = False

data Ty
  = E
  | T
  | V -- primitive types
  | Ty :-> Ty -- function types
  | Comp EffX Ty -- computation types
  deriving (Eq, Show)

data Mode
  = FA
  | BA
  | PM -- etc
  | FC
  | MR Mode
  | ML Mode -- map right and map left
  | AP Mode -- structured application
  | UR Mode
  | UL Mode
  deriving (Show)

modes :: Ty -> Ty -> [(Mode, Ty)]
modes l r = case (l, r) of
  (a :-> b, _) | r == a -> [(FA, b)]
  (_, a :-> b) | l == a -> [(BA, b)]
  (a :-> T, b :-> T) | a == b -> [(PM, a :-> T)]
  (c :-> d, a :-> b) | b == c -> [(FC, a :-> d)]
  -- ... ==...
  _ -> []

type Lexicon = String -> [Ty]

synsem :: Lexicon -> Syn -> [Sem]
synsem lex syn = case syn of
  (Leaf w) -> [Lex t w | t <- lex w]
  (Branch lsyn rsyn) ->
    [ Comb ty op lsem rsem
      | lsem <- synsem lex lsyn,
        rsem <- synsem lex rsyn,
        (op, ty) <- combine (getType lsem) (getType rsem)
    ]
  where
    getType (Lex ty _) = ty
    getType (Comb ty _ _ _) = ty

combine :: Ty -> Ty -> [(Mode, Ty)]
combine l r =
  modes l r
    ++ addMR l r
    ++ addML l r
    -- if both daughters are applicative, try structured application ++ addAP l r
    -- if the left daughter closes an applicative effect,
    -- try to purify the right daughter
    ++ addUR l r
    -- if the right daughter closes an applicative effect,
    -- try to purify the left daughter
    ++ addUL l r

addAP :: Ty -> Ty -> [(Mode, Ty)]
addAP l r = case (l, r) of
  (Comp f s, Comp g t)
    | f == g,
      applicative f ->
        [(AP op, Comp f u) | (op, u) <- combine s t]
  _ -> []

addUR :: Ty -> Ty -> [(Mode, Ty)]
addUR l r = case l of
  Comp f s :-> s'
    | applicative f ->
        [(UR op, u) | (op, u) <- combine (s :-> s') r]
  _ -> []

addUL :: Ty -> Ty -> [(Mode, Ty)]
addUL l r = case r of
  Comp f t :-> t'
    | applicative f ->
        [(UL op, u) | (op, u) <- combine l (t :-> t')]
  _ -> []

addMR :: Ty -> Ty -> [(Mode, Ty)]
addMR l r = case r of
  Comp f t | functor f -> [(MR op, Comp f u) | (op, u) <- combine l t]
  _ -> []

addML :: Ty -> Ty -> [(Mode, Ty)]
addML l r = case l of
  Comp f s | functor f -> [(ML op, Comp f u) | (op, u) <- combine s r]
  _ -> []