-- [Computational Semantics with Functional Programming](http://www.computational-semantics.eu), by Jan van Eijck and Christina Unger.
-- @odanoburu's solutions -- in public domain

-- c3e12
minList :: Ord a => [a] -> a
minList [x] = x
minList (x1:x2:xt) = minList ((min x1 x2):xt)

-- c3e13
delete :: Eq a => a -> [a] -> [a]
delete _ [] = []
delete y (x:xt)
  | x /= y = x : (delete y xt)
  | otherwise = xt -- delete y xt

-- c3e14
srt :: Ord a => [a] -> [a]
srt [] = []
srt xs = let xm = minList xs in xm : srt (delete xm xs)

-- c3e17
prefix :: Eq a => [a] -> [a] -> Bool
prefix [] ys = True
prefix xs [] = True
prefix (x:xs) (y:ys) = (x==y) && prefix xs ys

sublist :: Eq a => [a] -> [a] -> Bool
sublist [] [] = True
sublist _ [] = False
sublist xs ys@(_:yt) | prefix xs ys = True
                     | sublist xs yt = True
                     | otherwise = False

-- c3e19

data Feature = F Attr Value deriving (Eq,Show)

data Attr    = Back | High | Round | Cons deriving (Eq,Show)
data Value   = Plus | Minus               deriving (Eq,Show)

type Phoneme = [Feature]

yawelmaniVowels = [i,a,o,u,e]

i = [F Cons Minus,  F High Plus,  
     F Round Minus, F Back Minus]
a = [F Cons Minus,  F High Minus, 
     F Round Minus, F Back Plus ]
o = [F Cons Minus,  F High Minus, 
     F Round Plus,  F Back Plus ]
u = [F Cons Minus,  F High Plus , 
     F Round Plus,  F Back Plus ]
e = [F Cons Minus,  F High Minus, 
     F Round Minus, F Back Minus]

c = [F Cons Plus]

realize :: Phoneme -> Char
realize x | x == i = 'i'
          | x == a = 'a'
          | x == o = 'o'
          | x == u = 'u'
          | x == e = 'e'
          | x == c = 'c'

fValue :: Attr -> Phoneme -> Value
fValue attr [] = error "feature not found"
fValue attr ((F a v):fs) | attr == a = v
                         | otherwise = fValue attr fs

fMatch :: Attr -> Value -> Phoneme -> Phoneme
fMatch attr value fs = map (match attr value) fs
   where match a v f@(F a' v') | a == a'   = F a' v
                               | otherwise = f

appendSuffixY :: [Phoneme] -> [Phoneme] -> [Phoneme]
appendSuffixY stem suffix = stem ++ (map (harmonize stemV) suffix)
  where isVowel = (\c -> elem c yawelmaniVowels)
        getVowel = head . filter isVowel -- only gets first vowel
        stemV = getVowel stem
        harmonize' stemVowel = (\c -> fMatch Round (fValue Round stemVowel) (fMatch Back (fValue Back stemVowel) c))
        harmonize stemVowel = (\c -> if isVowel c && (fValue High stemVowel) == (fValue High c) then harmonize' stemVowel c else c)
