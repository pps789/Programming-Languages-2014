(*
   SNU 4190.310 Programming Languages (Fall 2013)
 
   K- Interpreter
*)
(* Location : don't mention it *)
module type LOC =
sig
	type t
	val base : t
	val equal : t -> t -> bool
	val diff : t -> t -> int
	val increase : t -> int -> t
end

module Loc : LOC =
struct
	type t = Location of int
	let base = Location(0)
	let equal (Location(a)) (Location(b)) = (a = b)
	let diff (Location(a)) (Location(b)) = a - b
	let increase (Location(base)) n = Location(base+n)
end

(* Memory Signature *)
module type MEM = 
sig
	type 'a t
	exception Not_allocated
	exception Not_initialized
	val empty : 'a t (* get empty memory *)
	val load : 'a t -> Loc.t  -> 'a (* load value : Mem.load mem loc => value *)
	val store : 'a t -> Loc.t -> 'a -> 'a t (* save value : Mem.store mem loc value => mem' *)
	val alloc : 'a t -> Loc.t * 'a t (* get fresh memory cell : Mem.alloc mem => (loc, mem') *)
end

(* Environment Signature *)
module type ENV =
sig
	type ('a, 'b) t
	exception Not_bound
	val empty : ('a, 'b) t (* get empty environment *)
	val lookup : ('a, 'b) t -> 'a -> 'b (* lookup environment : Env.lookup env key => content *)
	val bind : ('a, 'b) t -> 'a -> 'b -> ('a, 'b) t  (* id binding : Env.bind env key content => env'*)
end

(* Memory Implementation *)
module Mem : MEM =
struct
	exception Not_allocated
	exception Not_initialized
	type 'a content = V of 'a | U
	type 'a t = M of Loc.t * 'a content list
	let empty = M(Loc.base,[])

	let rec replace_nth = fun l n c -> 
		match l with
		| h::t -> if n = 1 then c::t else h::(replace_nth t (n-1) c)
		| [] -> raise Not_allocated

	let load (M(boundary,storage)) loc =
		match (List.nth storage ((Loc.diff boundary loc) - 1)) with
		| V(v) -> v 
		| U -> raise Not_initialized

	let store (M(boundary,storage)) loc content =
		M(boundary, replace_nth storage (Loc.diff boundary loc) (V(content)))

	let alloc (M(boundary,storage)) = (boundary,M(Loc.increase boundary 1,U::storage))
end

(* Environment Implementation *)
module Env : ENV=
struct
	exception Not_bound
	type ('a, 'b) t = E of ('a -> 'b)
	let empty = E(fun x -> raise Not_bound)
	let lookup (E(env)) id = env id
	let bind (E(env)) id loc = E(fun x -> if x = id then loc else env x)
end

(*
 * K- Interpreter
 *)
module type KMINUS =
sig
	exception Error of string
	type id = string
	type exp =
	| NUM of int | TRUE | FALSE | UNIT
	| VAR of id
	| ADD of exp * exp
	| SUB of exp * exp
	| MUL of exp * exp
	| DIV of exp * exp
	| EQUAL of exp * exp
	| LESS of exp * exp
	| NOT of exp
 	| SEQ of exp * exp            (* sequence *)
 	| IF of exp * exp * exp       (* if-then-else *)
  	| WHILE of exp * exp          (* while loop *)
  	| LETV of id * exp * exp      (* variable binding *)
  	| LETF of id * id list * exp * exp (* procedure binding *)
  	| CALLV of id * exp list      (* call by value *)
  	| CALLR of id * id list       (* call by referenece *)
  	| RECORD of (id * exp) list   (* record construction *)
  	| FIELD of exp * id           (* access record field *)
  	| ASSIGN of id * exp          (* assgin to variable *)
	| ASSIGNF of exp * id * exp   (* assign to record field *)
  	| READ of id
	| WRITE of exp
    
	type program = exp
	type memory
	type env
	type value
	val emptyMemory : memory
	val emptyEnv : env
	val run : memory * env * program -> value
end

module K : KMINUS =
struct
	exception Error of string

	type id = string
	type exp =
	| NUM of int | TRUE | FALSE | UNIT
	| VAR of id
	| ADD of exp * exp
	| SUB of exp * exp
	| MUL of exp * exp
	| DIV of exp * exp
	| EQUAL of exp * exp
	| LESS of exp * exp
  	| NOT of exp
  	| SEQ of exp * exp            (* sequence *)
  	| IF of exp * exp * exp       (* if-then-else *)
  	| WHILE of exp * exp          (* while loop *)
  	| LETV of id * exp * exp      (* variable binding *)
  	| LETF of id * id list * exp * exp (* procedure binding *)
  	| CALLV of id * exp list      (* call by value *)
  	| CALLR of id * id list       (* call by referenece *)
  	| RECORD of (id * exp) list   (* record construction *)
  	| FIELD of exp * id           (* access record field *)
  	| ASSIGN of id * exp          (* assgin to variable *)
	| ASSIGNF of exp * id * exp   (* assign to record field *)
	| READ of id
	| WRITE of exp

	type program = exp

	type value =
	| Num of int
	| Bool of bool
	| Unit
	| Record of (id -> Loc.t)
    
	type memory = value Mem.t
	type env = (id, env_entry) Env.t
	and  env_entry = Addr of Loc.t | Proc of id list * exp * env

	let emptyMemory = Mem.empty
	let emptyEnv = Env.empty

	let value_int v = 
		match v with 
		| Num n -> n
		| Bool _ -> raise (Error "Bool type is used as Num type")
		| Unit -> raise (Error "Unit type is used as Num type")
		| Record _ -> raise (Error "Unit type is used as Num type")

	let value_bool v =
		match v with
		| Bool b -> b
		| Num _ -> raise (Error "Num type is used as Bool type")
		| Unit -> raise (Error "Unit type is used as Bool type")
		| Record _ -> raise (Error "Unit type is used as Bool type")

    let value_unit v =
		match v with 
		| Unit -> ()
		| Num _ -> raise (Error "Num type is used as Unit type")
		| Bool _ -> raise (Error "Bool type is used as Unit type")
		| Record _ -> raise (Error "Bool type is used as Unit type")

	let value_record v =
		match v with
		| Record r -> r
		| Num _ -> raise (Error "Num type is used as Record type")
		| Unit -> raise (Error "Unit type is used as Record type")
		| Bool _ -> raise (Error "Bool type is used as Record type")

	let env_loc e x =
		try
			(match Env.lookup e x with
			| Addr l -> l
			| Proc _ -> raise (Error "not allowed")) 
		with Env.Not_bound -> raise (Error "not bound")

	let env_proc e f =
		try
			(match Env.lookup e f with
  			| Addr _ -> raise (Error "not allowed") 
			| Proc (id, exp, env) -> (id, exp, env))
		with Env.Not_bound -> raise (Error "not bound")
		  
	let rec semantics : memory -> env -> exp -> (value * memory) = 
        let two_int mem env e1 e2 =            
            let (v1, m1) = semantics mem env e1 in
            let n1 = value_int v1 in
            let (v2, m2) = semantics m1 env e2 in
            let n2 = value_int v2 in
            (n1, n2, m2)
        in
		fun mem env e -> match e with
		| NUM(i) -> (Num i, mem)
        | TRUE -> (Bool true, mem)
        | FALSE -> (Bool false, mem)
        | UNIT -> (Unit, mem)
        | VAR(v) -> ((Mem.load mem (env_loc env v)), mem)
        | ADD(e1, e2) ->
                let (n1, n2, m) = two_int mem env e1 e2 in
                (Num (n1+n2), m)
        | SUB(e1, e2) ->
                let (n1, n2, m) = two_int mem env e1 e2 in
                (Num (n1-n2), m)
        | MUL(e1, e2) ->
                let (n1, n2, m) = two_int mem env e1 e2 in
                (Num (n1*n2), m)
        | DIV(e1, e2) ->
                let (n1, n2, m) = two_int mem env e1 e2 in
                (Num (n1/n2), m)
        | EQUAL(e1, e2) ->
                let (v1, m1) = semantics mem env e1 in
                let (v2, m) = semantics m1 env e2 in
                begin
                    match (v1, v2) with
                    | (Num i, Num j) -> if i=j then (Bool true, m) else (Bool false, m)
                    | (Bool i, Bool j) -> if i=j then (Bool true, m) else (Bool false, m)
                    | (Unit, Unit) -> (Bool true, m)
                    | _ -> (Bool false, m)
                end
        | LESS(e1, e2) ->
                let (n1, n2, m) = two_int mem env e1 e2 in
                if n1<n2 then (Bool true, m) else (Bool false, m)
        | NOT(e1) ->
                let (v, m) = semantics mem env e1 in
                let b = value_bool v in
                if b then (Bool false, m) else (Bool true, m)
        | SEQ(e1, e2) ->
                let (v1, m1) = semantics mem env e1 in
                let (v2, m) = semantics m1 env e2 in
                (v2, m)
        | IF(e1, e2, e3) ->
                let (v1, m1) = semantics mem env e1 in
                let b = value_bool v1 in
                if b then
                    let (v2, m2) = semantics m1 env e2 in
                    (v2, m2)
                else
                    let (v2, m2) = semantics m1 env e3 in
                    (v2, m2)
        | WHILE(e1, e2) ->
                let (v1, m1) = semantics mem env e1 in
                let b = value_bool v1 in
                if b then
                    let (v2, m2) = semantics m1 env e2 in
                    semantics m2 env e
                else (Unit, m1)
        | LETV(v_name, v_expr, v_scope) ->
                let (v_val, m1) = semantics mem env v_expr in
                let (loc, m_alloc) = Mem.alloc m1 in
                let m_stored = Mem.store m_alloc loc v_val in
                let env_binded = Env.bind env v_name (Addr loc) in
                semantics m_stored env_binded v_scope
        | LETF(p_name, p_list, p_body, p_scope) ->
                let env_binded = Env.bind env p_name (Proc (p_list, p_body, env)) in
                semantics mem env_binded p_scope
        | CALLV(p_name, p_exp_list) ->
                let get_v_list (_v_list, _mem) _expr =
                    let (_v, _m) = semantics _mem env _expr in
                    ((_v::_v_list), _m)
                in
                let (v_list, mn) = List.fold_left get_v_list ([], mem) p_exp_list in
                let (fun_para_list, fun_body, fun_env) = env_proc env p_name in
                let get_loc_list (_loc_list, _mem) _v =
                    let (_loc, _m_alloc) = Mem.alloc _mem in
                    let _m_stored = Mem.store _m_alloc _loc _v in
                    (((Addr _loc)::_loc_list), _m_stored)
                in
                let (loc_list, m_alloc) = List.fold_left get_loc_list ([], mn) v_list in
                let env_binded = List.fold_left2 Env.bind fun_env fun_para_list loc_list in
                semantics m_alloc (Env.bind env_binded p_name (Proc (fun_para_list, fun_body, fun_env))) fun_body
        | CALLR(p_name, p_para_name_list) ->
                let (fun_para_list, fun_body, fun_env) = env_proc env p_name in
                let env_binded = List.fold_left2 Env.bind fun_env fun_para_list (List.map (Env.lookup env) p_para_name_list) in
                semantics mem (Env.bind env_binded p_name (Proc (fun_para_list, fun_body, fun_env))) fun_body
        | RECORD([]) -> (Unit, mem)
        | RECORD(id_exp_list) ->
                let rec get_v_list _mem _id_exp_list =
                    match _id_exp_list with
                    | [] -> ([], _mem)
                    | (_, _exp)::tl ->
                            let (_v, _m) = semantics _mem env _exp in
                            let (ret_list, ret_mem) = get_v_list _m tl in
                            ((_v::ret_list), ret_mem)
                in
                let (v_list, mn) = get_v_list mem id_exp_list in
                let rec get_loc_list _mem _v_list =
                    match _v_list with
                    | [] -> ([], _mem)
                    | hd::tl ->
                            let (_loc, _mem_alloc) = Mem.alloc _mem in
                            let _mem_stored = Mem.store _mem_alloc _loc hd in
                            let (ret_list, ret_mem) = get_loc_list _mem_stored tl in
                            (_loc::ret_list, ret_mem)
                in
                let (loc_list, mem_stored) = get_loc_list mn v_list in
                let rec get_record _id_exp_list _loc_list =
                    match _id_exp_list with
                    | [] ->
                            let ker x = raise (Error "No id in record") in
                            ker
                    | (_id,_)::tl ->
                            let ret x =
                                if x=_id then (List.hd _loc_list)
                                else (get_record tl (List.tl _loc_list)) x
                            in
                            ret
                in
                (Record (get_record id_exp_list loc_list), mem_stored)
        | FIELD(e, name) ->
                let (v, m) = semantics mem env e in
                let rr = value_record v in
                ((Mem.load m (rr name)), m)
        | ASSIGN(name, e) ->
                let (v, m) = semantics mem env e in
                (v, (Mem.store m (env_loc env name) v))
        | ASSIGNF(e1, name, e2) ->
                let (v1, m1) = semantics mem env e1 in
                let (v2, m2) = semantics m1 env e2 in
                let r1 = value_record v1 in
                (v2, (Mem.store m2 (r1 name) v2))
        | READ(name) ->
                let n = read_int () in
                let v = Num n in
                (v, Mem.store mem (env_loc env name) v)
        | WRITE(e) ->
                let (v, m) = semantics mem env e in
                print_int (value_int v);
                (v, m)
		| _ -> raise (Error("not implemented")) (* implement it! *)

    let run (mem, env, pgm) =
		let (v,_) = semantics mem env pgm in
		v
end
