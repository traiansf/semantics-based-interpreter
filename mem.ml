let lookup = List.assoc

let mem_add n = function
  | [] -> (0,[0,n])
  | (x',n')::t -> let x = x'+1 in (x,(x,n)::(x',n')::t)

let rec update (x,n) = function
  | [] -> raise Not_found
  | (y,v)::s  when x=y -> ((x,n)::s)
  | h::t -> h::(update (x,n) t)

let update_or_add (x,v) m = (x,v)::List.remove_assoc x m

let string_of_mem = 
  let string_of_pair (x,v) = string_of_int x ^ " |-> " ^ ImpAST.string_of_expr v in
  let rec string_of_mem str = function
  | [] -> str
  | p::t -> string_of_mem (str ^ "; " ^ string_of_pair p) t
  in function [] -> "" | p::t -> string_of_mem (string_of_pair p) t
