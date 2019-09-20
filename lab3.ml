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
;;
let isSameList l1 l2 = (isContained l1 l2) && (isContained l2 l1)
;;
type gamma = prop list;;
type rule = Hyp | Itrue | Iimplies | Eimplies | Eint | Classical | Iand | Eleftand | Erightand | Ileftor | Irightor | Eor;;
type ndprooftree = Rule of gamma * prop* rule * ndprooftree list;;
let extractgamma proof = match proof with
| Rule (gamma, prop, rule, childproof) -> gamma;;
let extractprop proof = match proof with
| Rule (gamma, prop, rule, childproof) -> prop;;
let rec valid_ndprooftree proof = match proof with
| Rule (gamma, prop, rule, childproof) -> (match rule with
											| Hyp -> (isMember prop gamma)
											| Itrue -> (isSameProp prop T)
											| Iimplies -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let childprop = extractprop child in
																	(
																		match prop with
																		| Impl(p, q) -> (
																							let sameGamma = isSameList (p::gamma) childgamma in
																							if sameGamma=true then 
																							(
																								let sameprop = isSameProp prop (Impl(p,childprop)) in
																								sameprop && (valid_ndprooftree child)
																							) else false
																						)
																		| _ -> false
																	)
																)
															else false
															)
											| Eimplies -> (let childlen = length childproof in
															if (childlen=2)
																then (
																	let child1 = hd childproof in
																	let child2 = hd (tl childproof) in
																	let childgamma1 = extractgamma child1 in
																	let checkgamma1 = (isSameList childgamma1 gamma) in
																	let childgamma2 = extractgamma child2 in
																	let checkgamma2 = (isSameList childgamma2 gamma) in
																	let childprop1 = extractprop child1 in
																	let childprop2 = extractprop child2 in
																	(
																		match childprop1 with
																		| Impl(p, q) -> (
																							let sameGamma = (checkgamma1 && checkgamma2) in
																							if sameGamma=true then 
																							(
																								let sameprop = isSameProp childprop1 (Impl(childprop2,prop)) in
																								sameprop && (valid_ndprooftree child1) && (valid_ndprooftree child2)
																							) else false
																						)
																		| _ -> false
																	)
																)
															else false
															)
											| Eint -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let checkgamma = (isSameList childgamma gamma) in
																	let childprop = extractprop child in
																	let checkchildprop = (isSameProp F childprop) in
																	checkgamma && checkchildprop && (valid_ndprooftree child)
																)
															else false
															)
											| Classical -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let checkgamma = (isSameList childgamma ((Not prop)::gamma)) in
																	let childprop = extractprop child in
																	let checkchildprop = (isSameProp F childprop) in
																	checkgamma && checkchildprop && (valid_ndprooftree child)
																)
															else false
															)
											| Iand -> (let childlen = length childproof in
															if (childlen=2)
																then (
																	let child1 = hd childproof in
																	let child2 = hd (tl childproof) in
																	let childgamma1 = extractgamma child1 in
																	let checkgamma1 = (isSameList childgamma1 gamma) in
																	let childgamma2 = extractgamma child2 in
																	let checkgamma2 = (isSameList childgamma2 gamma) in
																	let childprop1 = extractprop child1 in
																	let childprop2 = extractprop child2 in
																	let checkchildprop = isSameProp prop (And(childprop1, childprop2)) in
																	checkchildprop && checkgamma1 && checkgamma2 && (valid_ndprooftree child1) && (valid_ndprooftree child2)
																)
															else false
															)
											| Eleftand -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let checkgamma = (isSameList childgamma gamma) in
																	let childprop = extractprop child in
																	let checkchildprop = (match childprop with
																								| And(p,q) -> isSameProp p prop
																								| _ -> false
																							) in
																	checkgamma && checkchildprop && (valid_ndprooftree child)
																)
															else false
															)
											| Erightand -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let checkgamma = (isSameList childgamma gamma) in
																	let childprop = extractprop child in
																	let checkchildprop = (match childprop with
																								| And(p,q) -> isSameProp q prop
																								| _ -> false
																							) in
																	checkgamma && checkchildprop && (valid_ndprooftree child)
																)
															else false
															)
											| Ileftor -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let checkgamma = (isSameList childgamma ((Not prop)::gamma)) in
																	let childprop = extractprop child in
																	let checkchildprop = (match prop with
																								| Or(p,q) -> isSameProp p childprop
																								| _ -> false
																							) in
																	checkgamma && checkchildprop && (valid_ndprooftree child)
																)
															else false
															)
											| Irightor -> (let childlen = length childproof in
															if (childlen=1)
																then (
																	let child = hd childproof in
																	let childgamma = extractgamma child in
																	let checkgamma = (isSameList childgamma ((Not prop)::gamma)) in
																	let childprop = extractprop child in
																	let checkchildprop = (match prop with
																								| Or(p,q) -> isSameProp q childprop
																								| _ -> false
																							) in
																	checkgamma && checkchildprop && (valid_ndprooftree child)
																)
															else false
															)
											| Eor -> (let childlen = length childproof in
															if (childlen=3)
																then (
																	let child1 = hd childproof in
																	let child2 = hd (tl childproof) in
																	let child3 = hd ( tl (tl childproof)) in
																	let childprop1 = extractprop child1 in
																	let childprop2 = extractprop child2 in
																	let childprop3 = extractprop child3 in
																	let checkchildprop2 = isSameProp childprop2 prop in
																	let checkchildprop3 = isSameProp childprop3 prop in
																	let childgamma1 = extractgamma child1 in
																	let childgamma2 = extractgamma child2 in
																	let childgamma3 = extractgamma child3 in
																	let checkgamma1 = (isSameList childgamma1 gamma) in
																	(match childprop1 with
																	| Or(p, q) -> (
																					let checkgamma2 = (isSameList childgamma2 (p::gamma)) in
																					let checkgamma3 = (isSameList childgamma3 (q::gamma)) in
																					checkchildprop2 && checkchildprop3 && checkgamma1 && checkgamma2 && checkgamma3 && (valid_ndprooftree child1) && (valid_ndprooftree child2) && (valid_ndprooftree child3)
																				)
																	| _ -> false)
																)
															else false
															)
										)
;;
let rec mergeList g delta = match delta with
| [] -> g
| x::xs -> if(isMember x g) then (mergeList g xs) else (mergeList (g@[x]) xs)
;;

let rec pad delta proof = match proof with
| Rule (gamma, prop, rule, childproof) -> Rule((mergeList gamma delta), prop, rule, (map (pad delta) childproof))
;;

exception InvalidProof;;


let rec minimalgaama l proof = match proof with
| Rule (gamma, prop, rule, childproof) -> (
											match rule with
											| Hyp -> prop::l
											| _ -> (fold_left (fun acc x -> minimalgaama acc x) l childproof)
											)
;;


let rec setGamma minGaama proof = match proof with
| Rule (gamma, prop, rule, childproof) -> (match rule with
											| Iimplies -> (match prop with
															| Impl(p,q) -> (Rule (minGaama, prop, rule, (map (setGamma (p::minGaama)) childproof)))
															| _ -> (raise InvalidProof)
															)
											| Classical -> (Rule(minGaama, prop, rule, (map (setGamma ((Not prop)::minGaama)) childproof)))
											| _ -> (Rule(minGaama, prop, rule, (map (setGamma minGaama) childproof)))
										)
;;

let prune proof = let minGaama = minimalgaama [] proof in
					setGamma minGaama proof
				;;

exception Wronggraft;;

let rec findProp prop prooflist = match prooflist with
| [] -> raise Wronggraft
| x::xs -> (match x with
			 Rule (gamma, propproof, rule, childproof) -> (
														if (isSameProp prop propproof) then x else (findProp prop xs)
														)
		)
;;

let rec addGaamaToProof p proof = match proof with
| Rule (gaama, prop, rule, childproof) -> Rule (p::gaama, prop, rule, (map (addGaamaToProof p) childproof))
;;

let addGaama p prooflist = (map (addGaamaToProof p) prooflist)
;;

let rec graftAndReplace finGaama prooflist proof= match proof with
| Rule (gamma, prop, rule, childproof) -> (
											match rule with
											| Hyp -> (findProp prop prooflist)
											| Iimplies -> (
															match prop with
															| Impl(p,q) -> (let newprooflist = (addGaama p prooflist) in
																				(Rule (finGaama, prop, rule, 
																					(map (graftAndReplace (p::finGaama) newprooflist) childproof)
																				))
																				)
															| _ -> (raise Wronggraft)
														)
											| Classical -> (
															let newprooflist = (addGaama (Not prop) prooflist) in
															(Rule (finGaama, prop, rule,
																(map (graftAndReplace ((Not prop)::finGaama) newprooflist) childproof)))
															)
											| _ -> Rule( finGaama, prop, rule, (map (graftAndReplace finGaama prooflist) childproof))
											)
;;

let graft proof prooflist = let finGaama = (match (hd prooflist) with
											| Rule (gamma, prop, rule, childproof) -> gamma
										) in
							graftAndReplace finGaama prooflist proof
							;;





