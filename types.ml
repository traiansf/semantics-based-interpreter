open Mem
open ImpAST

exception TypeError of expr*tip*tip
exception VarNotFound of expr
exception UntypedVarError of expr
exception AnyVarError of bool*string
exception VariantError of expr
exception InvalidExpression of expr * bool


let addVariants m t cases = List.fold_left (fun m -> function VarTypeCase(v,t',_) -> (v,TArrow(t',t))::m
                                                       | ConstTypeCase(v,_) -> (v,t)::m
                                                       | _ -> failwith ("addVariants: should only have variant decls here")
                                           ) m cases

let rec inferPatternType inPattern m = 
 let infertype =  if inPattern then inferPatternType true else infertype in
  function
  | Int _ -> TInt
  | Bool _ -> TBool
  | Float _ -> TFloat
  | String _ -> TString
  | Skip _ -> TUnit
  | Var (v,loc) as var -> if inPattern then raise (UntypedVarError var) else (try 
           lookup v m 
     with Not_found -> raise (VarNotFound var))
  | AnyVar loc -> raise (AnyVarError (inPattern,loc))
  | TypedExpr (Var _, t,_) when inPattern -> t
  | TypedExpr (AnyVar _, t,_) when inPattern -> t
  | TypedExpr (e, t,_) -> (match infertype m e with
          | t' when t'=t -> t
          | t' -> raise (TypeError(e,t,t')))
  | Tuple (l,_) -> TProd (List.map (infertype m) l)
  | Variant (v,e,_) as var -> (try (match (lookup v m, infertype m e) with
                              | (TArrow(t,t'),te) when t=te -> t'
                              | (TArrow(t,t'),te) -> raise (TypeError (e,t,te))
                              | _ -> failwith("inferPatternType - variant type should be an arrow type.")
                        ) with Not_found -> raise (VariantError var))
  | Const (v,_) as const -> (try lookup v m with Not_found -> raise (VariantError const))
  | e -> raise (InvalidExpression (e, inPattern)) 
and
(* Type inference function *)
  infertype m = function
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
  | Op(e1,Equal,e2,_)
    -> let (t,t') = (infertype m e1, infertype m e2) in
         if t = t' then TBool else raise (TypeError(e2,t,t'))
  | If(e1,e2,e3,_) -> (match (infertype m e1, infertype m e2, infertype m e3) with
     | (TBool, t, t') when t=t' -> t
     | (TBool, t, t') -> raise (TypeError (e3, t, t'))
     | (t,_,_) -> raise (TypeError (e1, TBool, t)))
  | Deref (e,_)
    -> (match (infertype m e) with
          | TRef t -> t
          | t -> raise (TypeError (e, TRef t, t)))
  | Ref (e,_) -> TRef (infertype m e) 
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
(* type of the Z combinator
  | Z _ -> TArrow(TArrow(TArrow(TInt,TInt),TArrow(TInt,TInt)),TArrow(TInt,TInt))
*)
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
      let m' = update_or_add_all mp m in
      let tp = inferPatternType true m' p in 
      TArrow(tp, infertype m' e)
  | Decls(VarTypeDecl(x,cases,_)::dt,loc)
    -> let m' = addVariants m (DefType x) cases in infertype m' (Decls(dt,loc))
  | Decls(LetDecl (e1,e2,loc)::dt,loc')
     -> infertype m (Let(e1,e2,Decls(dt,loc'),loc)) 
  | Decls(LetRecDecl (x,t,e,loc)::dt,loc')
     -> infertype m (LetRec(x,t,e,Decls(dt,loc'),loc)) 
  | Decls([e],_) -> infertype m e
  | Decls(e::t,_) -> raise (InvalidExpression (e,false))
  | e -> inferPatternType false m e


let type_check e = try
     let _ = infertype [] e in true
  with 
    | TypeError (e,t1,t2) -> Printf.eprintf "%s\nError: This expression has type %s but an expression was expected of type %s\n"  (location e) (string_of_tip t2) (string_of_tip t1) ; false
    | VarNotFound e -> Printf.eprintf "%s\nError: Variable %s unbound.\n"  (location e) (string_of_expr e) ; false
    | UntypedVarError e -> Printf.eprintf "%s\nError: Variable %s not typed in pattern.\n"  (location e) (string_of_expr e) ; false
    | AnyVarError (true, loc) -> Printf.eprintf "%s\nError: Anonymous Variable untyped in pattern.\n" loc ; false
    | AnyVarError (false, loc) -> Printf.eprintf "%s\nError: Anonymous Variable not allowed here.\n"  loc ; false
    | InvalidExpression (e,inPattern)  -> Printf.eprintf "%s\nError: Expression not allowed in %s.\n"  (location e) (if inPattern then "pattern" else "program") ; false
    | VariantError (Variant(x,_,loc)) -> Printf.eprintf "%s\nError: Constructor %s was not previously defined.\n"  loc x ; false
    | VariantError (Const(x,loc)) -> Printf.eprintf "%s\nError: Constructor %s was not previously defined.\n"  loc x ; false



