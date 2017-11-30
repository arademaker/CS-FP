module Model2 where 

import Data.List
import Model

snowWhite' :: Entity
snowWhite' = T

girl', boy', princess', dwarf', giant', 
  child', person', man', woman', thing' :: OnePlacePred
girl'     = list2OnePlacePred [S,T,A,D,G]
boy'      = list2OnePlacePred [M,Y]
princess' = list2OnePlacePred [E,S]
dwarf'    = list2OnePlacePred [B,R]
giant'    = list2OnePlacePred []
wizard'   = list2OnePlacePred [W,V]
child'    = \ x -> (girl' x  || boy' x)
person'   = \ x -> (child' x || princess' x || dwarf' x 
                             || giant' x    || wizard' x) 
man'      = \ x -> (dwarf' x || giant' x    || wizard' x) 
woman'    = \ x -> princess' x 
thing'    = \ x -> not (person' x || x == Unspec)

laugh', cheer', shudder' :: OnePlacePred
laugh'   = list2OnePlacePred [A,G,E,T]
cheer'   = list2OnePlacePred [M,D]
shudder' = list2OnePlacePred []

{-
iSent (Sent SnowWhite (VP3 Wanted To (INF Catch (NP1 Some Girl)))) W1
iNP SnowWhite (iVP (VP3 Wanted To (INF Catch (NP1 Some Girl)))) W1
(\ p -> p iSnowWhite) (iAV Wanted (iINF (INF Catch (NP1 Some Girl)))) W1
(\ p -> p iSnowWhite) (iAV Wanted  (\ s -> iNP (NP1 Some Girl) (\ o -> iTINF Catch s o))) W1
(\ p -> p iSnowWhite) (iAV Wanted  (\ s -> iNP (NP1 Some Girl) (\ o -> iTINF Catch s o))) W1
(\ p -> p iSnowWhite) (\ x i -> and [ p x j | j <- worlds, iAttit Wanted x j ]) (\ s -> iNP (NP1 Some Girl) (\ o -> iTINF Catch s o)) W1
(\ p -> p iSnowWhite) (\ x i -> and [ p x j | j <- worlds, elem j [W2,W3]]) (\ s -> iNP (NP1 Some Girl) (\ o -> iTINF Catch s o)) W1
(\ p -> p iSnowWhite) (and [ p (\ s -> iNP (NP1 Some Girl) (\ o -> iTINF Catch s o)) j | j <- worlds, elem j [W2,W3]])
(\ p -> p iSnowWhite) (and [ p (\ s -> (\ i -> any (\x -> q (\j -> x) i) (filter (\x -> p (\j -> x) i) entities)) (\ o -> iTINF Catch s o)) j | j <- worlds, elem j [W2,W3]])
-}
