open Mem
open ImpAST

let is_fun = function
  | Fun _ | Function _ | IntOfFloat _ | FloatOfInt _ -> true 
  | _ -> false

let rec is_val = function
  | Bool _ | Int _ | Float _ | String _ | Loc _ | Skip _ | Const _ -> true
  | Tuple (l,_) -> List.fold_left (fun b -> fun e -> b && is_val e) true l 
  | Variant (x,e,_) -> is_val e
  | e -> is_fun e

let matchPattern p e any =
  let rec matchPattern pl el sigma = match (pl,el) with
    | ([],[]) -> sigma
    | (TypedExpr(p,_,_)::pt,el) -> matchPattern (p::pt) el sigma
    | (pl,TypedExpr(e,_,_)::et) -> matchPattern pl (e::et) sigma
    | (Tuple(tp::tpt,l)::pt, Tuple(te::tet,l')::et)
      -> matchPattern (tp::Tuple(tpt,l)::pt) (te::Tuple(tet,l')::et) sigma
    | (Tuple([],_)::pt,Tuple([],_)::et) -> matchPattern pt et sigma
    | (Int (n,_)::pt, Int(n',_)::et) when n=n' -> matchPattern pt et sigma
    | (Bool (n,_)::pt, Bool(n',_)::et) when n=n' -> matchPattern pt et sigma
    | (Float (n,_)::pt, Float(n',_)::et) when n=n' -> matchPattern pt et sigma
    | (String (n,_)::pt, String(n',_)::et) when n=n' -> matchPattern pt et sigma
    | (Loc (n,_)::pt, Loc(n',_)::et) when n=n' -> matchPattern pt et sigma
    | (Skip _::pt, Skip _::et) -> matchPattern pt et sigma
    | (Var (x,_)::pt, e::et) -> matchPattern pt et ((x,e)::sigma)
    | (AnyVar _::pt, e::et) when any -> matchPattern pt et sigma
    | (Const (c,_)::pt, Const (c',_)::et) when c = c' -> matchPattern pt et sigma
    | (Variant (v,p,_)::pt, Variant (v',e,_)::et) when v = v' -> matchPattern (p::pt) (e::et) sigma
    | _ -> raise Not_found
  in matchPattern [p] [e] []

let rec reduce = function
  | (Op(Int (n1,_),Plus,Int (n2,_),loc),s) -> Some (Int (n1+n2,loc),s)             (*Op+*)
  | (Op(Float (f1,_),Plus,Float (f2,_),loc),s) -> Some (Float (f1+.f2,loc),s)
  | (Op(Int (n1,_),Minus,Int (n2,_),loc),s) -> Some (Int (n1-n2,loc),s)             (*Op+*)
  | (Op(Float (f1,_),Minus,Float (f2,_),loc),s) -> Some (Float (f1-.f2,loc),s)
  | (Op(Int (n1,_),Mul,Int (n2,_),loc),s) -> Some (Int (n1*n2,loc),s)             (*Op+*)
  | (Op(Float (f1,_),Mul,Float (f2,_),loc),s) -> Some (Float (f1*.f2,loc),s)
  | (Op(Int (n1,_),Div,Int (n2,_),loc),s) when n2 <> 0 -> Some (Int (n1/n2,loc),s)             (*Op+*)
  | (Op(Float (f1,_),Div,Float (f2,_),loc),s) -> Some (Float (f1/.f2,loc),s)

  | (Op(Int (n1,_),Mic,Int (n2,_),loc),s) -> Some (Bool (n1<=n2,loc),s)            (*Op<=*)
  | (Op(Float (f1,_),Mic,Float (f2,_),loc),s) -> Some (Bool (f1<=f2,loc),s)            (*Op<=*)
  | (Op(Int (n1,_),MicS,Int (n2,_),loc),s) -> Some (Bool (n1<n2,loc),s)
  | (Op(v1,Equal,v2,loc),s) when is_val v1 && is_val v2 
    -> Some (Bool ((try (matchPattern v1 v2 false)  = []
                    with Not_found -> false),loc),s)
  | (Op(Float (f1,_),MicS,Float (f2,_),loc),s) -> Some (Bool (f1<f2,loc),s)
  | (Op(Int (n1,loc1),op,e2,loc),s) ->                                        (*OpD*)
    (match reduce (e2,s) with 
      | Some (e2',s') -> Some (Op(Int (n1,loc1),op,e2',loc),s')
      | None -> None
    )
  | (Op(Float (f1,loc1),op,e2,loc),s) ->                                        (*OpD*)
    (match reduce (e2,s) with 
      | Some (e2',s') -> Some (Op(Float (f1,loc1),op,e2',loc),s')
      | None -> None
    )
  | (Op(e1,op,e2,loc),s) ->                                            (*OpS*)
    (match reduce (e1,s) with Some (e1',s') -> Some (Op(e1',op,e2,loc),s')
      | None -> None)
  | (Deref (Loc (l,_), loc), s) -> Some (lookup l s, s)               (*Deref*)
  | (Deref (e, loc), s) ->                     (*DerefS*)
    (match reduce (e,s) with Some (e',s') -> Some (Deref(e',loc),s')
      | None -> None)

  | (Ref (v,loc), s) when is_val v ->            (*Ref*)
    let (l,s') = mem_add v s 
    in Some (Loc (l,loc), s')                    
  | (Ref (e, loc), s) ->                         (*RefS*)
    (match reduce (e,s) with Some (e',s') -> Some (Ref(e',loc),s')
      | None -> None)
  | (Atrib(Loc(l,_), v,loc),s) when is_val v ->                                         (*Atrib*)
      Some (Skip loc, update (l, v) s)
  | (Atrib(Loc(l,loc'),e,loc),s) ->                                          (*AtribD*)
    (match reduce (e,s) with 
      | Some (e',s') -> Some (Atrib(Loc(l,loc'),e',loc),s')
      | None -> None)
  | (Atrib(e1,e2,loc),s) ->
    (match reduce (e1,s) with 
      | Some (e1',s') -> Some (Atrib(e1',e2,loc),s')
      | None -> None)
  | (Secv(Skip _,e,_),s) -> Some (e,s)                                 (*Secv*)
  | (Secv(e1,e2,loc),s) ->                                             (*SecvS*)
    (match reduce (e1,s) with Some (e1',s') -> Some (Secv(e1',e2,loc),s')
      | None -> None)
  | (If(Bool (true,_),e1,e2,_),s) -> Some (e1,s)                         (*IfTrue*)
  | (If(Bool (false,_),e1,e2,_),s) -> Some (e2,s)                        (*IfFalse*)
  | (If(e,e1,e2,loc),s) ->                                             (*IfS*)
    (match reduce (e,s) with Some (e',s') -> Some (If(e',e1,e2,loc),s')
      | None -> None)
  | (While(e1,e2,loc),s) -> Some (If(e1,Secv(e2,While(e1,e2,loc),loc),Skip loc,loc),s) (*While*)
  | (For(init,cond,incr,body,l), s) 
    -> Some (Secv(init,While(cond,Secv(body,incr,l),l),l), s)    (*For*)
  | (App (IntOfFloat _, Float (f,_), loc), s)
    -> Some (Int (int_of_float f, loc), s)
  | (App (FloatOfInt _, Int (n,_), loc), s)
    -> Some (Float (float_of_int n, loc), s)
(*  Semantics for the Z combinator (removed in favor of variant constructors)
  | (App (App(Z loc, g, loc1), v, loc2), s)
    -> Some (App (App (g, App(Z loc, g, loc),loc1), v, loc2), s)
*)
  | (Match (v,cases,l), s) when is_val v
    -> reduce (App (Function(cases,l),v,l), s)
  | (Match (e,cases,l), s) 
    -> (match reduce (e,s) with 
         | Some (e',s') -> Some (Match (e',cases,l), s')
         | None -> None)
  | (App (Fun(Case(p,e,lc),lf),v,la),s) when is_val v 
    -> (try let sigma = matchPattern p v true in 
         Some (substitute (addVars sigma) e,s) 
        with Not_found -> None)
  | (Let (p,e2,e1,l),s) when is_val e2 
    -> reduce (App (Fun(Case(p,e1,l),l), e2, l), s)
  | (App (Function (case::cases,l), v, l'), s) when is_val v
    -> (match reduce (App (Fun (case,l), v,l'), s) with
           | Some e -> Some e
           | None -> Some (App (Function (cases,l), v, l'), s))
  | (App (e1, e2, loc), s) when is_fun e1
     -> (match reduce (e2,s) with Some (e2',s') -> Some (App(e1,e2',loc),s')
      | None -> None)
  | (App (e1, e2, loc), s) 
     -> (match reduce (e1,s) with Some (e1',s') -> Some (App(e1',e2,loc),s')
      | None -> None)
  | (Let (p, e2, e1, loc), s) 
     -> (match reduce (e2,s) with 
           |Some (e2',s') -> Some (Let (p,e2',e1,loc),s')
           | None -> None)
  | (LetRec (x, t, e2, e1, loc), s)
     -> Some (subst x (LetRec (x, t, e2, e2, loc)) e1, s)
 


(*  Normal Order
  | (App (Fun(x,_,e1,_),e2,_),s) -> Some (subst x e2 e1, s)
  | (App (App(Z loc, g, loc1), v, loc2), s)
    -> Some (App (App (g, App(Z loc, g, loc),loc1), v, loc2), s)
  | (App (e1, e2, loc), s) ->
    (match reduce (e1,s) with Some (e1',s') -> Some (App(e1',e2,loc),s')
      | None -> (match reduce (e2,s) with Some (e2',s') -> Some (App(e1,e2',loc),s')
      | None -> None))
   | (Fun (x,t,e,loc),s) ->
    (match reduce (e,s) with Some (e',s') -> Some (Fun (x,t,e',loc),s') 
      | None -> None)
*)

  | (Tuple (v::l, loc),s) when is_val v
    -> (match reduce (Tuple (l,loc), s) with
            | Some (Tuple (l',_), s') -> Some (Tuple(v::l',loc),s')
            | _ -> None)
  | (Tuple (e::l, loc),s) 
    -> (match reduce (e,s) with
            | Some (e',s') -> Some (Tuple(e'::l,loc), s')
            | None -> None)
  | (Decls(VarTypeDecl _::dt,loc), s) ->  Some (Decls(dt,loc), s)
  | (Decls([e],loc), s) ->  Some (e, s)
  | (Variant (x,e,loc),s)
   -> (match reduce (e,s) with
           | Some (e',s') -> Some (Variant (x,e',loc),s')
           | None -> None)
  | _ -> None                                                    (*default*)


let string_of_config (p,m) = "<" ^ string_of_expr p ^ ", {" ^ string_of_mem m ^ "} >"

(* evaluate basically computes the transitive closure ->* of the
   one step reduction relation. *)
let rec evaluate debug c = match (reduce c) with
  | Some c' -> if debug 
               then Printf.printf "%s\n" (string_of_config c) 
               else () ; 
               evaluate debug c'
  | None -> c

