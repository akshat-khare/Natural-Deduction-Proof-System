#use "lab3.ml";;
let proof1 = Rule([L("p");L("q")], L("p"), Hyp, []);;
let isValidproof1 = valid_ndprooftree proof1;;
let prunedproof1 = prune proof1;;
