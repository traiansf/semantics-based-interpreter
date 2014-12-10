open Mem
open ImpAST

exception TypeError of expr*tip*tip
exception VarNotFound of expr
exception AnyVarError of bool*string


let rec inferPatternType inPattern m = function
  | Int (n,_) -> TInt
  | Bool (b,_) -> TBool
  | Float (f,_) -> TFloat
  | Skip _ -> TUnit
  | Var (v,loc) -> (try 
           lookup v m 
     with Not_found -> raise (VarNotFound (Var(v, loc))))
  | AnyVar loc when inPattern -> raise (AnyVarError (true,loc))
  | TypedExpr (AnyVar _, t,_) when inPattern -> t
  | TypedExpr (e, t,_) when inPattern -> (match inferPatternType true m e with
          | t' when t'=t -> t
          | t' -> raise (TypeError(e,t,t')))
  | Tuple (l,_) when inPattern -> TProd (List.map (inferPatternType true m) l)
  | e -> failwith ("infertype: expression " ^ string_of_expr e ^ " not allowed in a " ^ if inPattern then "pattern." else "program.")

(* Type inference function *)
let rec infertype m = function
  | Op(e1,(Plus|Minus|Mul|Div),e2,_) 
    -> (match (infertype m e1, infertype m e2) with
     | (TInt, TInt) -> TInt
     | (TFloat, TFloat) -> TFloat
     | (TInt, t) -> raise (TypeError (e2, TInt, t))
     | (TFloat, t) -> raise (TypeError (e2, TFloat, t))
     | (t,_) -> raise (TypeError (e1, TInt, t)))
  | Op(e1,(Mic|MicS),e2,_) 
    -> (match (infertype m e1, infertype m e2) with
     | (TInt, TInt) | (TFloat, TFloat)  -> TBool
     | (TInt, t)  -> raise (TypeError (e2, TInt, t))
     | (TFloat, t) -> raise (TypeError (e2, TFloat, t))
     | (t,_) -> raise (TypeError (e1, TInt, t)))
  | If(e1,e2,e3,_) -> (match (infertype m e1, infertype m e2, infertype m e3) with
     | (TBool, t, t') when t=t' -> t
     | (TBool, t, t') -> raise (TypeError (e3, t, t'))
     | (t,_,_) -> raise (TypeError (e1, TBool, t)))
  | Deref (e,_)
    -> (match (infertype m e) with
          | TRef t -> t
          | t -> raise (TypeError (e, TRef t, t)))
  | Ref (e,_) -> TRef (infertype m e) 
  | AnyVar loc -> raise (AnyVarError (false, loc))
  | TypedExpr (e,t,_) -> (match infertype m e with
       | t' when t = t' -> t
       | t' -> raise (TypeError (e,t,t')))
  | Atrib(e1,e2,loc) -> (match (infertype m e1, infertype m e2) with
       | (TRef t1, t2) when t1 = t2 -> TUnit
       | (TRef t, t') -> raise (TypeError (e2, t, t'))
       | (t, t') -> raise (TypeError (e1, TRef t', t)))
  | Secv (e1,e2,_) -> (match (infertype m e1, infertype m e2) with
     | (TUnit,t) -> t
     | (t1,_) -> raise (TypeError (e1, TUnit, t1)))
  | While (cond,body,_) -> (match (infertype m cond, infertype m body) with
     | (TBool, TUnit) -> TUnit
     | (TBool, t) -> raise (TypeError (body, TUnit, t))
     | (t,_) -> raise (TypeError (cond, TBool, t)))
  | For (init,cond,incr,body,_) 
    -> (match (infertype m init, infertype m cond, infertype m incr, infertype m body) with
     | (TUnit, TBool, TUnit, TUnit) -> TUnit
     | (TUnit, TBool, TUnit, t) -> raise (TypeError (body, TUnit, t))
     | (TUnit, TBool, t, _) -> raise (TypeError (incr, TUnit, t))
     | (TUnit, t, _, _) -> raise (TypeError (cond, TBool, t))
     | (t, _, _, _) -> raise (TypeError (init, TUnit, t)))
  | App (e1, e2, _) -> (match (infertype m e1, infertype m e2) with
     | (TArrow(t1, t1'), t2) when t1 = t2 -> t1'
     | (TArrow(t1, t1'), t2) -> raise (TypeError (e2,t1,t2))
     | (t1,t2) -> raise (TypeError (e1,TArrow(t2,t2),t1)))
  | IntOfFloat _ -> TArrow(TFloat, TInt)
  | FloatOfInt _ -> TArrow(TInt, TFloat)
  | Z _ -> TArrow(TArrow(TArrow(TInt,TInt),TArrow(TInt,TInt)),TArrow(TInt,TInt))
  | Fun (e,_) -> infertype m e
  | Function (fstCase::choices,_) 
    -> let t = infertype m fstCase in
         List.iter (fun choice ->
              (match infertype m choice with
                 | t' when t' = t -> ()
                 | t' -> raise (TypeError (choice, t, t')))) choices ; t
  | Let (Var(x,_),e1,e2,_) 
    -> let t = infertype m e1 in
       infertype (update_or_add (x,t) m) e2
  | Let (p,e1,e2,l) -> infertype m (App (Fun (Case(p,e2,l),l),e1,l))
  | LetRec (x,t,e1,e2,_) 
    -> let infertype' = infertype (update_or_add (x,t) m)
       in (match (infertype' e1, infertype' e2) with
             | (t1,t2) when t1 = t -> t2
             | (t1,_) -> raise (TypeError (e1,t,t1)))
  | Match (e,choices,l) -> infertype m (App(Function(choices,l),e,l)) 
  | Case (p,e,_)
   -> let mp = pattern_vars p in 
      let tp = inferPatternType true mp p and m' = update_or_add_all mp m in
      TArrow(tp, infertype m' e)
  | Tuple (l,_) -> TProd (List.map (infertype m) l)
  | e -> inferPatternType false m e


let type_check e = try
     let _ = infertype [] e in true
  with 
    | TypeError (e,t1,t2) -> Printf.eprintf "%s\nError: Error: This expression has type %s but an expression was expected of type %s\n"  (location e) (string_of_tip t2) (string_of_tip t1) ; false
    | VarNotFound e -> Printf.eprintf "%s\nError: Variable %s unbound.\n"  (location e) (string_of_expr e) ; false
    | AnyVarError (true, loc) -> Printf.eprintf "%s\nError: Anonymous Variable untyped in pattern.\n" loc ; false
    | AnyVarError (false, loc) -> Printf.eprintf "%s\nError: Anonymous Variable not allowed here.\n"  loc ; false


