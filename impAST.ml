type locatie = string

type op =
  | Plus
  | Mic
  | Minus
  | Mul
  | Div
  | MicS

let string_of_op = function
  | Plus -> "+"
  | Minus -> "-"
  | Mul -> "*"
  | Div -> "/"
  | MicS -> "<"
  | Mic -> "<="

let string_of_l s = "_loc" ^ string_of_int s ^ "_"

(* types of expressions *)
type tip = TInt | TFloat | TBool | TUnit 
  | TArrow of tip * tip 
  | TRef of tip
  | TProd of tip list
  | DefType of string
let rec string_of_tip = function
  | TInt -> "int"
  | TFloat -> "float"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TArrow (t1,t2) -> "(" ^ string_of_tip t1 ^ " -> " ^ string_of_tip t2 ^ ")"
  | TRef t -> string_of_tip t ^ " ref"
  | TProd(l) -> "(" ^ String.concat " * " (List.map string_of_tip l) ^ ")"
  | DefType s -> s


type expr =
  | IntOfFloat of locatie | FloatOfInt of locatie | Z of locatie
  | Bool of bool * locatie
  | Int of int * locatie
  | Float of float * locatie
  | Loc of int * locatie
  | Var of string * locatie
  | AnyVar of locatie
  | Op of expr * op * expr * locatie
  | Atrib of expr * expr * locatie
  | Ref of expr * locatie
  | Deref of expr * locatie
  | Secv of expr * expr * locatie
  | If of expr * expr * expr * locatie
  | While of expr * expr * locatie
  | For of expr * expr * expr * expr * locatie | Skip of locatie
  | Fun of expr * locatie
  | Function of expr list * locatie
  | TypedExpr of expr * tip * locatie
  | Let of expr * expr * expr * locatie
  | LetRec of string * tip * expr * expr * locatie
  | App of expr * expr * locatie
  | Tuple of expr list * locatie
  | Match of expr * expr list * locatie
  | Case of expr * expr * locatie
  | Decls of expr list * locatie
  | VarTypeDecl of string * expr list * locatie
  | VarTypeCase of string * tip * locatie
  | ConstTypeCase of string * locatie
  | Variant of string * expr * locatie
  | Const of string * locatie

let exps = function
 | IntOfFloat _ | FloatOfInt _ | Bool _ | Int _ | Float _ | Loc _
 | Var _ | Skip _ | Z _ | AnyVar _
   -> []
 | Ref (e,_) | Deref (e,_) | Fun(e,_) | TypedExpr (e,_,_)
   -> [e]
 | Atrib(e1,e2,_) | Op(e1,_,e2,_) | Secv(e1,e2,_) | While(e1,e2,_) 
 | App(e1,e2,_) | LetRec (_,_,e1,e2,_) | Case(e1,e2,_)
   -> [e1;e2]
 | Let (e1,e2,e3,_) | If(e1,e2,e3,_) -> [e1;e2;e3]
 | For(e1,e2,e3,e4,_) -> [e1;e2;e3;e4]
 | Tuple(l,_) -> l
 | Match(e,l,_) -> e::l
 | Function(l,_) -> l
 | Decls (l,_) 
 | VarTypeDecl (_,l,_) -> l
 | VarTypeCase _ 
 | ConstTypeCase _ 
 | Const _ -> []
 | Variant (_,e,_) -> [e]


let revExps = function
   | (e,[]) -> e
   | (Deref(_,loc),[e]) -> Deref(e,loc)
   | (Ref(_,loc),[e]) -> Ref(e,loc)
   | (Fun(_,loc),[e]) -> Fun(e,loc) 
   | (Atrib(_,_,loc),[e1;e2]) -> Atrib(e1,e2,loc)
   | (Op(_,op,_,loc),[e1;e2]) -> Op(e1,op,e2,loc) 
   | (Secv(_,_,loc),[e1;e2]) -> Secv(e1,e2,loc) 
   | (While(_,_,loc),[e1;e2]) -> While(e1,e2,loc) 
   | (App(_,_,loc),[e1;e2]) -> App(e1,e2,loc) 
   | (Let(_,_,_,loc),[e1;e2;e3]) -> Let(e1,e2,e3,loc) 
   | (LetRec(x,t,_,_,loc),[e1;e2]) -> LetRec(x,t,e1,e2,loc) 
   | (If(_,_,_,loc), [e1;e2;e3]) -> If(e1,e2,e3,loc)
   | (For(_,_,_,_,loc), [e1;e2;e3;e4]) -> For(e1,e2,e3,e4,loc)
   | (Tuple(_,loc), l) -> Tuple(l,loc)
   | (Function(_,loc), l) -> Function(l,loc)
   | (Match(_,_,loc), e::l) -> Match(e,l,loc)
   | (Case(_,_,loc), [e1;e2]) -> Case(e1,e2,loc)
   | (TypedExpr(_,t,loc), [e]) -> TypedExpr(e,t,loc)
   | (Decls (_,loc), l) -> Decls (l,loc) 
   | (VarTypeDecl (x,_,loc), l) -> VarTypeDecl(x,l,loc)
   | (Variant (x,_,loc), [e]) -> Variant(x,e,loc)
   | _ -> failwith "revExps: This should not happen. Missing match case?"

type 't preResult = More | Done of 't
 
let rec visit pre post exp = 
  match pre exp with
    | More -> post (exp, (List.map (visit pre post) (exps exp)))
    | Done result -> result

let postVisit post = visit (fun e -> More) post

let transform pre post = visit pre (fun p -> post (revExps p))

let rec remove x = function
  | [] -> []
  | h::t when h < x -> h::(remove x t) 
  | h::t when h = x -> t
  | l -> l

let rec remove_all xs l = match xs with
  | [] -> l
  | x::t -> remove_all t (remove x l)

let union l1 l2 = let rec punion = function
  | ([],l) -> l
  | (l,[]) -> l
  | (h1::t1,h2::t2) -> match compare h1 h2 with 
      |  0  -> h1::punion (t1,t2)
      | -1 -> h1::punion (t1,h2::t2)
      |  1  -> h2::punion (h1::t1,t2)
      | _ -> failwith "union: compare should return 0, -1, or 1"
 in punion (l1,l2)

let var e = 
  let var_fold = function
     | (Var (x,_),_) -> [x]
     | (Case _,[vs1;vs2]) -> remove_all vs1 vs2
     | (Let _, [vsp;vs1;vs2]) -> union vs1 (remove_all vsp vs2)
     | (LetRec (x,_,_,_,_), [vs1;vs2]) -> remove x (union vs1 vs2)
     | (_,vs_list) -> List.fold_left union [] vs_list
  in postVisit var_fold e

let pattern_vars e =
  let var_fold = function
     | (TypedExpr(Var(x,_),t,_),_) -> [x,t]
     | (_,vs_list) -> List.fold_left union [] vs_list
  in postVisit var_fold e
     

let vars = List.fold_left (fun l1  -> fun (_,(_,l2)) -> union l1 l2) []

let keys sigma = List.sort compare (List.fold_left (fun l -> fun (x,_) -> x::l) [] sigma)

(* intersection of two ascending sorted lists *)
let rec intersect l1 l2 = match (l1,l2) with
  | ([],_) -> []
  | (_,[]) -> []
  | (h1::t1,h2::t2) when h1 = h2 -> h1::intersect t1 t2
  | (h1::t1,h2::t2) when h1 < h2 -> intersect t1 l2
  | (_,_::t2) -> intersect l1 t2

let free_more n vlist = 
  let max = List.fold_left 
     (fun m -> fun x -> 
       if String.get x 0 <> 'x' 
       then m 
       else try let m' = int_of_string (String.sub x 1 (String.length x - 1))
            in max m m'
            with Failure _ -> m) 0 vlist 
  in let rec free i n = if i > n then [] else ("x" ^ (string_of_int (max+i)))::
                             free (i+1) n
    in free 1 n

let free vlist = List.hd (free_more 1 vlist)

let freesubst sigma vars capture =
  let freeVars = free_more (List.length capture) vars in
  let sigma' = List.map2 (fun x -> fun x' -> x,(Var (x',"new"), [x'])) capture freeVars in
  sigma' @ sigma

let rec invars x = function
  | [] -> false
  | h::t when h < x -> invars x t 
  | h::t when h = x -> true
  | _ -> false

let rec substitute sigma = 
  transform 
  (function 
     | Var (x,l) -> (try 
                      let (sx,_) = List.assoc x sigma in Done sx 
                    with Not_found -> Done (Var (x,l)))
     | Case (xe,e,l)
       -> let vs = union (vars sigma) (keys sigma) and vx = var xe in
            let capture = intersect vx vs in 
               let sigma' = freesubst sigma (union vs (var e)) capture in
                 Done (Case(substitute sigma' xe, substitute sigma' e, l))
     | _ -> More)
  (fun x -> x)


let addVars = List.map (fun ((x:string),e) -> (x,(e, var e)))

let subst x ex e = substitute [x,(ex, var ex)] e

let string_of_expr e = 
  let string_of_expr_fold = function
  | (Z _,_) -> "Z"
  | (IntOfFloat _,_) -> "int_of_float"
  | (FloatOfInt _,_) -> "float_of_int"
  | (Int (i,_),_) -> string_of_int i
  | (Float (f,_),_) -> string_of_float f
  | (Bool (b,_),_) -> string_of_bool b
  | (Loc (l,_),_) -> string_of_l l
  | (Ref _,[s]) -> "ref (" ^ s ^ ")"
  | (Deref _,[s]) -> "! (" ^ s ^ ")"
  | (Var (s,_),_) -> s
  | (AnyVar _,_) -> "_"
  | (Op (_,b, _,_),[s1;s2]) -> "(" ^ s1 ^ (string_of_op b) ^ s2 ^ ")"
  | (Atrib _,[s1;s2]) -> "(" ^ s1 ^ ":=" ^ s2 ^ ")"
  | (If _,[s1;s2;s3]) ->
    "(if " ^ s1 ^ "\nthen " ^ s2 ^ "\nelse " ^ s3 ^ ")"
  | (While _,[s1;s2]) ->
    "while " ^ s1 ^ " do \n" ^ s2 ^ "\ndone"
  | (For _,[s1;s2;s3;s4])
    -> "(for (" ^ s1 ^ "; " ^ s2 ^ "; " ^ s3 ^ ") \n" ^ s4 ^ "\n)"
  | (Secv _,[s1;s2]) ->
    "(" ^ s1 ^ ";\n" ^ s2 ^ ")"
  | (Skip _, _) -> "()"
  | (Fun _,[s]) -> 
    "(fun " ^ s ^ ")"
  | (TypedExpr(_,t,_),[s]) -> "(" ^ s ^ ":" ^ string_of_tip t ^ ")"
  | (Let _,[sx;s1;s2]) -> 
    "(let " ^ sx  ^ " = " ^ s1 ^ " in " ^ s2 ^ ")"
  | (LetRec (x,t,_,_,_),[s1;s2]) -> 
    "(let rec " ^ x ^ ":" ^ string_of_tip t ^ " = " ^ s1 ^ " in " ^ s2 ^ ")"
  | (App _, [s1;s2]) -> 
    "(" ^ s1 ^ " " ^ s2 ^ ")"
  | (Tuple _, ls) ->
    "(" ^ String.concat "," ls ^ ")"
  | (Match _, s::ls) ->
    "(" ^ "match " ^ s ^ " with " ^ String.concat " | " ls ^ ")"
  | (Function _, ls) ->
    "(" ^ "function " ^ String.concat " | " ls ^ ")"
  | (Case _, [s1;s2]) -> s1 ^ " -> " ^ s2
  | (Decls (_,_), sl) -> String.concat "\n\n" sl
  | (VarTypeDecl (x,_,_), sl) -> "type " ^ x ^ " = \n    " ^ String.concat "\n  | " sl
  | (Variant (x,_,_), [s]) -> x ^ " " ^ s 
  | (VarTypeCase (x,t,_),[]) -> x ^ " of " ^ string_of_tip t
  | (ConstTypeCase (x,_),[]) -> x
  | (Const (x,_),[]) -> x
  | _ -> failwith "string_of_expr: this should not happen. Missing match case?"
  in postVisit string_of_expr_fold e

let location = function
  | Z l
  | IntOfFloat l
  | FloatOfInt l
  | Int (_,l)
  | Float (_,l)
  | Bool (_,l)
  | Loc (_,l)
  | Ref (_,l)
  | Deref (_,l)
  | Var (_,l)
  | AnyVar l  
  | Op (_, _, _,l)
  | Atrib (_,_,l)
  | If (_, _, _,l)
  | While (_, _,l)
  | For (_, _, _, _,l)
  | Secv (_,_,l)
  | Skip l 
  | App (_,_,l)
  | Fun (_,l)
  | TypedExpr (_,_,l)
  | Let (_,_,_,l)
  | LetRec (_,_,_,_,l)
  | Tuple (_,l)
  | Function (_,l)
  | Match (_,_,l)
  | Case (_,_,l)
  | Decls (_,l) 
  | VarTypeDecl (_,_,l)
  | VarTypeCase (_,_,l) 
  | ConstTypeCase (_,l) 
  | Const (_,l)
  | Variant (_,_,l)
  -> l

