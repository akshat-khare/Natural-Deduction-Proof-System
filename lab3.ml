open List;;
type prop = T| F | L of string
			| Not of prop
			| And of prop * prop
			| Or of prop * prop
			| Impl of prop * prop
		;;
let rec isSameProp a b = match (a,b) with
| (T,T) -> true
| (F,F) -> true
| (L(c), L(d)) -> if(c=d) then true else false
| (Not(c), Not(d)) -> (isSameProp c d)
| (And(c, d), And(e, f)) -> (isSameProp c e) && (isSameProp d f)
| (Or(c, d), Or(e, f)) -> (isSameProp c e) && (isSameProp d f)
| (Impl(c, d), Impl(e, f)) -> (isSameProp c e) && (isSameProp d f)
| _ -> false
;;
let rec isMember a l = match l with
| [] -> false
| x::xs -> if((isSameProp x a)) then true else (isMember a xs)
;;
let rec isContained l1 l2 = match l1 with
| [] -> true
| x::xs -> if(isMember x l2) then (isContained xs l2) else false
type gamma = prop list;;
type rule = Hyp
			| 