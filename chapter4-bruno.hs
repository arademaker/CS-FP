-- [Computational Semantics with Functional Programming](http://www.computational-semantics.eu), by Jan van Eijck and Christina Unger.
-- @odanoburu's solutions -- in public domain

import Data.List

--
-- propositional logic
data Form =  P String | Ng Form | Cnj [Form] | Dsj [Form] 
            deriving Eq

instance Show Form where 
 show (P name) = name 
 show (Ng  f)  = '¬': show f
 show (Cnj fs) = '∧': show fs
 show (Dsj fs) = '∨': show fs

form1, form2 :: Form
form1 = Cnj [P "p", Ng (P "p")]
form2 = Dsj [Ng (Cnj [P "p", Ng (P "p")]), P "p2", P "p3", Cnj [P "p", Ng (P "p")]]

-- c4e12
opsNr :: Form -> Int
opsNr (P _) = 0
opsNr (Ng form) = 1 + opsNr form
opsNr (Dsj forms) = 1 + sum (map opsNr forms)
opsNr (Cnj forms) = 1 + sum (map opsNr forms)

-- c4e13
--- is depth the maximum number of operations among branches?
depth :: Form -> Int
depth (P _) = 0
depth (Ng form) = 1 + depth form
depth (Dsj forms) = 1 + maximum (map depth forms)
depth (Cnj forms) = 1 + maximum (map depth forms)

-- c4e14
propNames' :: Form -> [String]
propNames' (P pname) = [pname]
propNames' (Ng form) = propNames' form
propNames' (Dsj forms) = concat $ map propNames' forms
propNames' (Cnj forms) = concat $ map propNames' forms

propNames :: Form -> [String]
propNames = sort . nub . propNames'

--
-- FOL
type Name     = String 
type Index    = [Int]
data Variable = Variable Name Index deriving (Eq,Ord)

instance Show Variable where 
  show (Variable name [])  = name
  show (Variable name [i]) = name ++ show i
  show (Variable name is ) = name ++ showInts is
     where showInts []     = "" 
           showInts [i]    = show i  
           showInts (i:is) = show i ++ "_" ++ showInts is

x, y, z :: Variable
x = Variable "x" []
y = Variable "y" []
z = Variable "z" []

data Formula a = Atom String [a]
               | Eq a a
               | Neg  (Formula a)
               | Impl (Formula a) (Formula a) 
               | Equi (Formula a) (Formula a)
               | Conj [Formula a]
               | Disj [Formula a] 
               | Forall Variable (Formula a)
               | Exists Variable (Formula a)
               deriving Eq

instance Show a => Show (Formula a) where 
  show (Atom s [])   = s
  show (Atom s xs)   = s ++ show xs 
  show (Eq t1 t2)    = show t1 ++ "==" ++ show t2
  show (Neg form)    = '¬' : (show form)
  show (Impl f1 f2)  = "(" ++ show f1 ++ "⇒" 
                           ++ show f2 ++ ")"
  show (Equi f1 f2)  = "(" ++ show f1 ++ "⇔" 
                           ++ show f2 ++ ")"
  show (Conj [])     = "true" 
  show (Conj fs)     = "conj" ++ show fs 
  show (Disj [])     = "false" 
  show (Disj fs)     = "disj" ++ show fs 
  show (Forall v f)  = "∀ " ++  show v ++ (' ' : show f)
  show (Exists v f)  = "∃ " ++  show v ++ (' ' : show f)

formula0 = Atom "R" [x,y]
formula1 = Forall x (Atom "R" [x,x])
formula2 = Forall x 
            (Forall y
              (Impl (Atom "R" [x,y]) (Atom "R" [y,x])))
formula3 = Forall x 
            (Forall y
              (Impl (Atom "R" [x,y,z]) (Atom "R" [y,x,z])))

-- c4e18
freeVars' :: Formula Variable -> [Variable]
freeVars' (Atom _ vs) = vs
freeVars' (Eq v v') = [v, v']
freeVars' (Neg f) = freeVars' f
freeVars' (Impl f f') = freeVars' f ++ freeVars' f'
freeVars' (Equi f f') = freeVars' f ++ freeVars' f'
freeVars' (Conj fs) = concat $ map freeVars' fs
freeVars' (Disj fs) = concat $ map freeVars' fs
freeVars' (Forall v f) = filter (\v' -> v /= v') $ freeVars' f
freeVars' (Exists v f) = filter (\v' -> v /= v') $ freeVars' f

freeVars :: Formula Variable -> [Variable]
freeVars = nub . freeVars'

closedForm :: Formula Variable -> Bool
closedForm f = if null $ freeVars f then True else False

-- c4e19
rmIDs :: Formula Variable -> Formula Variable
rmIDs (Neg f) = Neg $ rmIDs f
rmIDs (Impl f f') = Disj [Neg $ rmIDs f, rmIDs f']
rmIDs (Equi f f') = Conj [rmIDs (Impl f f'), rmIDs (Impl f' f)]
rmIDs (Conj fs) = Conj $ map rmIDs fs
rmIDs (Disj fs) = Disj $ map rmIDs fs
rmIDs (Forall v f) = (Forall v $ rmIDs f)
rmIDs (Exists v f) = (Exists v $ rmIDs f)
rmIDs f = f

-- c4e20
nnf' :: Formula Variable -> Formula Variable
nnf' (Neg (Conj fs)) = Disj $ map (\f -> nnf' $ (Neg f)) fs
nnf' (Neg (Disj fs)) = Conj $ map (\f -> nnf' $ (Neg f)) fs
nnf' (Neg (Neg f)) = nnf' f
nnf' (Neg (Forall v f)) = (Exists v $ nnf' $ (Neg f))
nnf' (Neg (Exists v f)) = (Forall v $ nnf' $ (Neg f))
nnf' (Conj fs) = Conj $ map nnf' fs
nnf' (Disj fs) = Disj $ map nnf' fs
nnf' (Forall v f) = (Forall v $ nnf' f)
nnf' (Exists v f) = (Exists v $ nnf' f)
nnf' f = f

nnf :: Formula Variable -> Formula Variable
nnf = nnf' . rmIDs

--
-- formulas with structured terms
data Term = Var Variable | Struct String [Term] 
            deriving (Eq,Ord)

instance Show Term where 
  show (Var v)       = show v 
  show (Struct s []) = s
  show (Struct s ts) = s ++ show ts

tx, ty, tz :: Term 
tx = Var x
ty = Var y
tz = Var z

tformula0 = Atom "R" [tx,ty]
tformula1 = Forall x (Atom "R" [tx,tx])
tformula2 = Forall x 
            (Forall y
              (Impl (Atom "R" [tx,ty]) (Atom "R" [ty,tx])))
tformula3 = Forall x 
            (Forall y
              (Impl (Atom "R" [tx,ty,tz]) (Atom "R" [ty,tx,tz])))

isVar :: Term -> Bool
isVar (Var _) = True
isVar _       = False

varsInTerm :: Term -> [Variable]
varsInTerm (Var v)       = [v]
varsInTerm (Struct s ts) = varsInTerms ts

varsInTerms :: [Term] -> [Variable]
varsInTerms = nub . concat . map varsInTerm

-- c4e22
termsInForm' :: Formula Term -> [Term]
termsInForm' (Atom _ ts) = ts
termsInForm' (Eq t t') = [t, t']
termsInForm' (Neg f) = termsInForm' f
termsInForm' (Impl f f') = termsInForm' f ++ termsInForm' f'
termsInForm' (Equi f f') = termsInForm' f ++ termsInForm' f'
termsInForm' (Conj fs) = concat $ map termsInForm' fs
termsInForm' (Disj fs) = concat $ map termsInForm' fs
termsInForm' (Forall v f) = termsInForm' f
termsInForm' (Exists v f) = termsInForm' f

varsInForm :: Formula Term -> [Variable]
varsInForm = varsInTerms . termsInForm'

-- c4e23
boundVarsInForm :: Formula Term -> [Variable]
boundVarsInForm (Neg f) = boundVarsInForm f
boundVarsInForm (Impl f f') = boundVarsInForm f ++ boundVarsInForm f'
boundVarsInForm (Equi f f') = boundVarsInForm f ++ boundVarsInForm f'
boundVarsInForm (Conj fs) = concat $ map boundVarsInForm fs
boundVarsInForm (Disj fs) = concat $ map boundVarsInForm fs
boundVarsInForm (Forall v f) = v : (boundVarsInForm f)
boundVarsInForm (Exists v f) = v : (boundVarsInForm f)
boundVarsInForm _ = []

freeVarsInForm :: Formula Term -> [Variable]
freeVarsInForm f = varsInForm f \\ boundVarsInForm f 

-- c4e24
openForm :: Formula Term -> Bool
openForm = not . null . freeVarsInForm
