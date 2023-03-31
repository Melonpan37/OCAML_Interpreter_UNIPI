(*definizione del tipo di dato set*)
type 't set = Empty | Elements of 't list | Singleton of 't;;

type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp |
	Letrec of ide * exp * exp | 
	(*definizione regole per set*)
	Eset of info | 
	Eadd of exp * exp | Eremove of exp * exp | IsIn of exp * exp | IsEmpty of exp | 
	Subset of exp * exp | Max of exp | Min of exp |
	Eunion of exp * exp | Esub of exp * exp | Eintersect of exp * exp |
	Forall of exp * exp | Exists of exp * exp | Filter of exp * exp | Map of exp * exp
	
	and info = Item of exp * info | Null
	;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun |
(*definizione del tipo set esprimibile dal linguaggio*)
	Set of evT set
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

let rec setTypecheck (s : string) (v : evT) : bool = match v with
	Set(Empty) -> true |
	Set(Singleton(e)) -> typecheck s e |
	Set(Elements(lis)) -> listypecheck s lis |
	_ -> failwith("not a set")
and	listypecheck str l = match l with 
		[] -> true |
		some::rest -> if(typecheck str some) then listypecheck str rest else false
;;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*==========================================utilities su liste======================================*)

(*rimuove un elemento dalla lista*)
let rec remList lis x = match lis with
	[] -> [] |
	a::rest -> if(a <> x) then a::(remList rest x) else rest;;
(*controlla che un elemento non sia presente in una lista*)
let rec checkNotInList l x : bool = match l with
	[] -> true |
	a::rest -> if(a = x) then false else checkNotInList rest x;;

let rec existList p l = match l with
	[] -> false |
	a::rest -> if(p a) then true else existList p rest;;

let rec subList l1 l2 = match l1 with
	[] -> true |
	a::rest -> if(true <> (checkNotInList l2 a)) then subList rest l2 else false;; 

(*=========================================utilities su set=========================================*)

(*attenzione, ritorna true se non trova l'elemento, false altrimenti*)
let rec checkNotInSet (s : evT) (x : evT) : bool = 
	if(false = (typecheck "int" x)) then failwith("not an int") else
	match s with
	Set(Empty) -> true |
	Set(Singleton(a)) -> if (a = x) then false else true |
	Set(Elements(lis)) -> (match lis with
		l::rest -> if(l <> x) then (checkNotInList rest x) else false) |
	_ -> failwith("not a set");;

(*controlla che tutti gli elementi di una lista siano in un set*)
let rec recIsInSet lis s = match lis with
	[] -> true |
	some::rest -> if(false <> checkNotInSet s some) then false else recIsInSet rest s;;

(*controlla che non esistano set di elements contenenti una lista con meno di due elementi*)
let rec reduceSet s = match s with
	Set(Elements(lis)) -> (match lis with
		[] -> Set(Empty) |
		some::rest -> if(rest = []) then Set(Singleton(some)) else s	
	);;

(*========================================primitive su set==========================================*)

let add (s : evT) (x : evT) : evT = if ((setTypecheck "int"  s) && (typecheck "int" x)) 
	then (if(checkNotInSet s x) 
		then (match s with
			Set(Empty) -> Set(Singleton(x)) |
			Set(Singleton(a)) -> Set(Elements(x::[a])) |
			Set(Elements(l)) -> Set(Elements(x::l))
			)
		else (match s with
			Set(Empty) -> Set(Empty) |
			Set(Singleton(a)) -> Set(Singleton(a)) |
			Set(Elements(l)) -> Set(Elements(l))
		)
	)
	else failwith("Type error");;

let remove (s : evT) (x : evT) : evT = 
	if((setTypecheck "int" s) && (typecheck "int" x))
	then (
		if(true <> (checkNotInSet s x))
		then(
			match s with 
				Set(Singleton(a)) -> Set(Empty) |
				Set(Elements(lis)) -> reduceSet (Set(Elements(remList lis x)))	
		)
		else s
	)
	else failwith("Type error");;

let isEmpty (s : evT) = match s with
	Set(Empty) -> Bool(true) |
	Set(Singleton(x)) -> Bool(false) |
	Set(Elements(l)) -> Bool(false) |
	_ -> failwith("not a set")
	;;

let isIn (s: evT) (x: evT) = match checkNotInSet s x with
	true -> Bool(false) |
	false -> Bool(true);;
	


let subset (s1 : evT) (s2 : evT) = if((true <> (setTypecheck "int" s1)) || (true <> (setTypecheck "int" s2))) 
	then failwith("not a set") else	match s1 with
	Set(Empty) -> Bool(true) |
	Set(Singleton(x)) -> isIn s2 x |
	Set(Elements(lis)) -> (match s2 with
		Set(Empty) -> Bool(false) |
		Set(Singleton(y)) -> Bool(false) |
		Set(Elements(lst)) -> Bool(recIsInSet lis s2)
	)
	;;

let rec max s = if(true <> (setTypecheck "int" s)) then failwith("not a set") else match s with
	Set(Empty) -> Int(-32000)|
	Set(Singleton(x)) -> x |
	Set(Elements((Int some)::rest)) -> maxlis rest some 
and maxlis l fst = match l with
	[] -> Int fst |
	(Int some)::rest -> if(some > fst) then maxlis rest some else maxlis rest fst
	;;

let rec min s = if(true <> (setTypecheck "int" s)) then failwith("not a set") else match s with
	Set(Empty) -> Int(32000) |
	Set(Singleton(x)) -> x |
	Set(Elements((Int some)::rest)) -> minlis rest some
and minlis l fst = match l with
	[] -> Int fst |
	(Int some)::rest -> if(some < fst) then minlis rest some else minlis rest fst
	;;

(*=====================================operazioni elementari su insiemi=====================================*)

(*operazione su insiemi X U Y*)
let rec union (s1 : evT) (s2 : evT) = 
if(true <> ((setTypecheck "int" s1)&&(setTypecheck "int" s2))) then failwith("type error") else match s1 with
	Set(Empty) -> s2 |
	Set(Singleton(x)) -> add s2 x |
	Set(Elements(lis)) -> 
		match lis with
			[] -> s2 |
			some::rest -> union (remove s1 some) (add s2 some)
	;;

(*operazione su insiemi X \ Y*)
(*sottrae a s1 gli elementi di s2*)
let rec sub (s1 : evT) (s2 : evT) = 
if(true <> ((setTypecheck "int" s1)&&(setTypecheck "int" s2))) then failwith("type error") else match s2 with
	Set(Empty) -> s1 |
	Set(Singleton(x)) -> remove s1 x |
	Set(Elements(lis)) -> match lis with
		[] -> s1 |
		some::rest -> sub (remove s1 some) (remove s2 some)
	;;

let rec intersection (s1 : evT) (s2 : evT) = 
if(true <> ((setTypecheck "int" s1)&&(setTypecheck "int" s2))) then failwith("type error") else match s1 with
	Set(Empty) -> Set(Empty) |
	Set(Singleton(a)) -> if(true <> (checkNotInSet s2 a)) then Set(Singleton(a)) else Set(Empty) |
	Set(Elements(lis)) -> aux lis s2
and aux l s = match l with 
	[] -> Set(Empty) |
	some::rest -> if(true <> (checkNotInSet s some)) then (add (aux rest s) some) else aux rest s
	;;
	

(*===========================================interprete========================================*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
        Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def")) |
	Eset(i) -> (match i with
		Null -> Set(Empty) |
		Item(fst, nxt) -> recAdd fst nxt r ) |
	
	(*primitive su set*)
	Eadd(a, b) -> add (eval a r) (eval b r) |
	Eremove(a, b) -> remove (eval a r) (eval b r) |
	IsIn(a, b) -> isIn (eval a r) (eval b r) |
	IsEmpty(a) -> isEmpty (eval a r) |
	Subset(a, b) -> subset (eval a r) (eval b r) |
	
	(*op elementari su set*)
	Eunion(a, b) -> union (eval a r) (eval b r) |
	Esub(a, b) -> sub (eval a r) (eval b r) |
	Eintersect(a, b) -> intersection (eval a r) (eval b r) |
	
	Max(a) -> max (eval a r) |
	Min(a) -> min (eval a r) |
	
	(*funzioni di ordine superiore su set*)
	Exists(a, p) -> (
		if(setTypecheck "int" (eval a r)) then
		exists (eval a r) p r
		else failwith("type error")
	) |
	
	Forall(a, p) -> (
		if(setTypecheck "int" (eval a r)) then
		forall (eval a r) p r
		else failwith("type error")
	) |
	
	Filter(a, p) -> (
		if(setTypecheck "int" (eval a r)) then
		filter (eval a r) p r
		else failwith("type error")
	) |
	
	Map(a, f) -> (
		if(setTypecheck "int" (eval a r)) then
		map (eval a r) f r
		else failwith("type error")
	)
	
	and recAdd fst nxt r = match nxt with
		Null -> Set(Singleton(eval fst r)) |
		Item(a, b) -> add (recAdd a b r) (eval fst r)
	and exists s p r = match s with
		Set(Empty) -> Bool(false) |
		Set(Singleton(Int(x))) -> eval (FunCall(p, (Eint x))) r |
		Set(Elements((Int(some))::rest)) -> (match  eval (FunCall(p, (Eint some))) r with
			Bool(true) -> Bool(true) |
			Bool(false) -> exists (remove s (Int some)) p r
		)
	and forall s p r = match s with
		Set(Empty) -> Bool(false) |
		Set(Singleton((Int x))) -> eval (FunCall(p, (Eint x))) r |
		Set(Elements((Int(some))::rest)) -> (match eval (FunCall(p, (Eint some))) r with
			Bool(false) -> Bool(false) |
			Bool(true) -> forall (remove s (Int some)) p r
		)
	and filter s p r = match s with
		Set(Empty) -> s |
		Set(Singleton(Int x)) -> ( match ( eval (FunCall(p, (Eint x))) r ) with
				Bool(true) -> s |
				Bool(false) -> Set(Empty)
		) |	
		Set(Elements((Int some)::rest)) -> (
			match ( eval (FunCall(p, (Eint some))) r) with
				Bool(true) -> add (filter (remove s (Int some)) p r) (Int some) |
				Bool(false) -> filter (remove s (Int some)) p r   
		)
	and map s f r = match s with
		Set(Empty) -> s |
		Set(Singleton(Int x)) -> Set(Singleton(eval (FunCall(f, (Eint x))) r )) |
		Set(Elements(lis)) -> (
			let rec mapList l foo env = (match l with
				[] -> [] |
				(Int st)::rs -> (eval (FunCall(foo, (Eint st))) r)::(mapList rs foo env)
			) in Set(Elements( mapList lis f r ))
		)
;;

(*=====================================utilities per i test========================================*)
let printevt e = match e with
	Int(a) -> Printf.printf "%d " a |
	Bool(b) -> Printf.printf "%B " b;;

let rec printevtlist l = match l with 
	[] -> Printf.printf "\n" |
	some::rest -> printevt some ; printevtlist rest;;

let rec printevtset s = match s with
	Set(Empty) -> Printf.printf "empty\n" |
	Set(Singleton(a)) -> printevt a; Printf.printf "\n" |
	Set(Elements(lis)) -> printevtlist lis;;


(* =============================  TESTS  ================= *)



let s1 = Set(Empty);;
let s2 = Set(Empty);;
let s3 = Set(Singleton(Int(1)));;
let s4 = Set(Singleton(Int(3)));;
let s5 = Set(Elements([(Int(1)); (Int(2))]));;
let s6 = Set(Elements([(Int(3)); (Int(4))]));;
let s7 = Set(Elements([(Int(1)); (Int(2)); (Int(3))]));;
let s8 = Set(Elements([(Int 0); (Int 2);]));;

Printf.printf "\ninizializzazione dei seguenti set per i test: (saranno usati per tutti i test)\n";;
printevtset s1;;
printevtset s2;;
printevtset s3;;
printevtset s4;;
printevtset s5;;
printevtset s6;;
printevtset s7;;
printevtset s8;;

Printf.printf "\ntest valutazione espressione Eset:\n";;
let s1 = Eset(Null);;
let s2 = Eset(Null);;
let s3 = Eset(Item((Eint(1)), Null));;
let s4 = Eset(Item((Eint(3)), Null));;
let s5 = Eset(Item((Eint(1)), Item((Eint(2)), Null)));;
let s6 = Eset(Item((Eint(3)), Item((Eint(4)), Null)));;
let s7 = Eset(Item((Eint(1)), Item((Eint(2)), Item((Eint(3)), Null))));;
let s8 = Eset(Item((Eint 0), Item(((Eint 2), Null))));;

printevtset (eval s1 (emptyenv Unbound));;
printevtset (eval s2 (emptyenv Unbound));;
printevtset (eval s3 (emptyenv Unbound));;
printevtset (eval s4 (emptyenv Unbound));;
printevtset (eval s5 (emptyenv Unbound));;
printevtset (eval s6 (emptyenv Unbound));;
printevtset (eval s7 (emptyenv Unbound));;
printevtset (eval s8 (emptyenv Unbound));;

(*test isEmpty*)

Printf.printf "\ntest espressione IsEmpty: (devono risultare true, false, false)\n";;

let e1 = IsEmpty s1;;
let e2 = IsEmpty s3;;
let e3 = IsEmpty s5;;

(*empty -> sempre true*)
printevt (eval e1 (emptyenv Unbound));;
(*singleton -> sempre false*)
printevt (eval e2 (emptyenv Unbound));;
(*elements -> sempre false*)
printevt (eval e3 (emptyenv Unbound));;

(*test isIn*)

Printf.printf "\ntest espressione IsIn: (devono risultare false, true, false, true, false) \n";;
let e1 = IsIn(s1, (Eint(1)));;
let e2 = IsIn(s3, (Eint(1)));;
let e3 = IsIn(s3, (Eint(2)));;
let e4 = IsIn(s5, (Eint(1)));;
let e5 = IsIn(s5, (Eint(3)));;

(*empty = sempre false*)
printevt(eval e1 (emptyenv Unbound));;
(*singleton = true*)
printevt(eval e2 (emptyenv Unbound));;
(*singleton = false*)
printevt(eval e3 (emptyenv Unbound));;
(*elements = true*)
printevt(eval e4 (emptyenv Unbound));;
(*elements = false*)
printevt(eval e5 (emptyenv Unbound));;

(*test subset*)

Printf.printf "\ntest espressione Subset: 
(devono risultare true true true false false false true false true false) \n";;
let e1 = Subset(s1, s2);;
let e2 = Subset(s1, s3);;
let e3 = Subset(s1, s5);;
let e4 = Subset(s3, s1);;
let e5 = Subset(s5, s1);;
let e6 = Subset(s5, s3);;
let e7 = Subset(s3, s5);;
let e8 = Subset(s4, s5);;
let e9 = Subset(s5, s7);;
let e10 = Subset(s6, s7);;

(*empty -> empty = sempre true*)
printevt(eval e1 (emptyenv Unbound));;
(*empty -> singleton = sempre true*)
printevt(eval e2 (emptyenv Unbound));;
(*empty -> elements = sempre true*)
printevt(eval e3 (emptyenv Unbound));;
(*singleton -> empty = sempre false*)
printevt(eval e4 (emptyenv Unbound));;
(*elements -> empty = sempre false*)
printevt(eval e5 (emptyenv Unbound));;
(*elements -> singleton = sempre false*)
printevt(eval e6 (emptyenv Unbound));;
(*singleton -> elements = true*)
printevt(eval e7 (emptyenv Unbound));;
(*singleton -> elements = false*)
printevt(eval e8 (emptyenv Unbound));;
(*elements -> elements = true*)
printevt(eval e9 (emptyenv Unbound));;
(*elements -> elements = false*)
printevt(eval e10 (emptyenv Unbound));;

(*test union*)

Printf.printf "\ntest unione: \n";;

(*empty U empty -> empty*)
let e1 = Eunion(s1, s2);;
(*empty U singleton -> singleton*)
let e2 = Eunion(s1, s3);;
(*empty U elemenst -> elements*)
let e3 = Eunion(s1, s5);;
(*singleton U elemenst -> elements senza elmininazioni dovute a ripetizioni*)
let e4 = Eunion(s3, s6);;
(*singleton U elements -> elements con eliminazioni dovute a ripetizioni*)
let e5 = Eunion(s3, s5);;
(*elements U elements -> elements senza eliminazioni dovute a ripetizioni*)
let e6 = Eunion(s5, s6);;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;
printevtset( eval e4 (emptyenv Unbound));;
printevtset( eval e5 (emptyenv Unbound));;
printevtset( eval e6 (emptyenv Unbound));;

(*test subtraction*)

Printf.printf "\ntest sottrazione:\n";;

(*empty \ empty -> empty*)
let e1 = Esub(s1, s2);;
(*singletn \ empty -> singleton (sono disgiunti ovviamente)*)
let e2 = Esub(s3, s1);;
(*singleton \ elements -> empty*)
let e3 = Esub(s3, s5);;
(*elements \ elements -> singleton*)
let e4 = Esub(s7, s5);;
(*elemtns \ elements -> elements (sono disgiunti)*)
let e5 = Esub(s5, s6);;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;
printevtset( eval e4 (emptyenv Unbound));;
printevtset( eval e5 (emptyenv Unbound));;

(*test intersezione*)

Printf.printf "\ntest intersezione:\n";;

(*vuota*)
let e1 = Eintersect(s1, s3);;
(*vuota*)
let e2 = Eintersect(s1, s5);;
(*vuota*)
let e3 = Eintersect(s3, s4);;
(*tutto s3*)
let e4 = Eintersect(s3, s5);;
(*tutto s5*)
let e4 = Eintersect(s5, s7);;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;
printevtset( eval e4 (emptyenv Unbound));;
printevtset( eval e5 (emptyenv Unbound));;

(*test exists*)
(*si controlla se esistono set contenenti il numero 2*)

Printf.printf "\ntest exists: (si controllano i set che rispettano il predicato exists un elemento = 2)\n"

let pred = Fun("x", Eq(Den "x", Eint(2)));;

(*empty -> false*)
let e1 = Exists(s1, pred);;
(*singleton -> false*)
let e2 = Exists(s3, pred);;
(*elements -> true*)
let e3 = Exists(s5, pred);;
(*elements -> false*)
let e4 = Exists(s6, pred);;

printevt( eval e1 (emptyenv Unbound));;
printevt( eval e2 (emptyenv Unbound));;
printevt( eval e3 (emptyenv Unbound));;
printevt( eval e4 (emptyenv Unbound));;

(*test forall*)
(*si controlla se esistono set contenenti solo i numeri 2 o 0*)

Printf.printf "\ntest forall: (si controllano i set contenenti solo elementi = 2 or = 0)\n";;

let pred = Fun("x", Or((Eq(Den "x", Eint 2)),(IsZero (Den "x"))));;

(*empty -> false*)
let e1 = Forall(s1, pred);;
(*singleton -> false*)
let e2 = Forall(s3, pred);;
(*elements -> false*)
let e3 = Forall(s5, pred);;
(*elements -> true*)
let e4 = Forall(s8, pred);;

printevt( eval e1 (emptyenv Unbound));;
printevt( eval e2 (emptyenv Unbound));;
printevt( eval e3 (emptyenv Unbound));;
printevt( eval e4 (emptyenv Unbound));;

(*test filter*)
(*filtra gli elementi uguali a 0 o 2 nei set*)

Printf.printf "\ntest filter: (si filtrano nei set gli elementi diversi da 2 o 0)\n"

let pred = Fun("x", Not(Or((Eq(Den "x", Eint 2)),(IsZero (Den "x")))));;

(*empty -> empty*)
let e1 = Filter(s1, pred);;
(*singleton -> singleton*)
let e2 = Filter(s3, pred);;
(*elements -> singleton*)
let e3 = Filter(s5, pred);;
(*elements -> elements*)
let e4 = Filter(s6, pred);;
(*elements -> empty*)
let e5 = Filter(s8, pred);;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;
printevtset( eval e4 (emptyenv Unbound));;
printevtset( eval e5 (emptyenv Unbound));;

(*test map*)
(*incrementa ogni elemento del set di 1*)

Printf.printf "\ntest map: (aumenta ogni elemento del set di 1)\n"

let foo = Fun("x", Sum(Den "x", Eint 1));;

(*empty*)
let e1 = Map(s1, foo);;
(*singleton*)
let e2 = Map(s3, foo);;
(*elements*)
let e3 = Map(s5, foo);;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;

Printf.printf "\ntest add\n"

(*1*)
let e1 = Eadd(s1, (Eint 1));;
(*1*)
let e2 = Eadd(s3, (Eint 1));;
(*1, 3*)
let e3 = Eadd(s3, (Eint 3));;
(*1, 2*)
let e4 = Eadd(s5, (Eint 1));;
(*1, 2, 3*)
let e5 = Eadd(s5, (Eint 3));;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;
printevtset( eval e4 (emptyenv Unbound));;
printevtset( eval e5 (emptyenv Unbound));;

Printf.printf "\ntest remove\n"

(*vuoto senza*)
let e1 = Eremove(s1, (Eint 1));;
(*vuoto con rimozione*)
let e2 = Eremove(s3, (Eint 1));;
(*singleton senza rimozione*)
let e3 = Eremove(s3, (Eint 3));;
(*elements -> singleton con rimozione*)
let e4 = Eremove(s5, (Eint 1));;
(*elments senza rimzione*)
let e5 = Eremove(s5, (Eint 3));;

printevtset( eval e1 (emptyenv Unbound));;
printevtset( eval e2 (emptyenv Unbound));;
printevtset( eval e3 (emptyenv Unbound));;
printevtset( eval e4 (emptyenv Unbound));;
printevtset( eval e5 (emptyenv Unbound));;

Printf.printf "\ntest max\n"

(*max di vuoto*)
let e1 = Max(s1);;
(*max di singleton -> 1*)
let e2 = Max(s3);;
(*max di elements -> 2*)
let e3 = Max(s5);;

printevt( eval e1 (emptyenv Unbound));;
printevt( eval e2 (emptyenv Unbound));;
printevt( eval e3 (emptyenv Unbound));;

Printf.printf "\ntest min\n"

(*max di vuoto*)
let e1 = Min(s1);;
(*max di singleton -> 1*)
let e2 = Min(s3);;
(*max di elements -> 2*)
let e3 = Min(s5);;

printevt( eval e1 (emptyenv Unbound));;
printevt( eval e2 (emptyenv Unbound));;
printevt( eval e3 (emptyenv Unbound));;

