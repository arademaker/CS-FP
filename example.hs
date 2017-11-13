
lfVP (VP1 tv np) =
\ subj -> lfNP np (\ obj -> lfTV tv (subj,obj))


lfVP (VP1 tv np) =
\ subj -> lfNP np (\ obj -> lfTV (\ (t1,t2) -> Atom "love" [t1,t2]) (subj,obj))



-- :t Sent Alice (VP1 Loved Goldilocks)

LfSent ( Sent Alice (VP1 Loved Goldilocks) ) = (lfNP Alice) (lfVP (VP1 Loved Goldilocks))
 = (\p -> p (Struct "alice" [])) \ subj -> Atom "love" [subj,(Struct "Goldilocks" [])]
 = \ subj -> Atom "love" [subj,(Struct "Goldilocks" [])] (Struct "alice" [])
 =  Atom "love" [(Struct "alice" []),(Struct "Goldilocks" [])]

  
(lfNP Alice) = (\p -> p (Struct "alice" [])) 

(lfVP (VP1 Loved Goldilocks)) = \ subj -> lfNP Goldilocks (\ obj -> lfTV Loved (subj,obj)) =

  = \ subj -> lfNP Goldilocks (\ obj -> (\ (t1,t2) -> Atom "love" [t1,t2]) (subj,obj))
  = \ subj -> lfNP Goldilocks (\ obj -> Atom "love" [subj,obj])
  = \ subj -> \p -> p (Struct "Goldilocks" []) (\ obj -> Atom "love" [subj,obj])
  = \ subj -> (\ obj -> Atom "love" [subj,obj]) (Struct "Goldilocks" [])
  = \ subj -> (\ obj -> Atom "love" [subj,obj]) (Struct "Goldilocks" [])
  = \ subj -> Atom "love" [subj,(Struct "Goldilocks" [])]


