open M
module M_SimChecker : M_SimTypeChecker = struct
    type prim = String | Int | Bool

    type tvar =
        | Prim of prim
        | Arr of tvar * tvar
        | Pair of tvar * tvar
        | Loc of tvar
        | Var of string

    let rec ptvar (t:tvar) =
        match t with
        | Prim Int -> "int"
        | Prim Bool -> "bool"
        | Prim String -> "string"
        | Pair(a,b) -> "pair(" ^ (ptvar a) ^ "," ^ (ptvar b) ^ ")"
        | Arr(a,b) -> "arr(" ^ (ptvar a) ^ "," ^ (ptvar b) ^ ")"
        | Loc l -> "loc(" ^ (ptvar l) ^ ")"
        | Var v -> v

    let varcount = ref 0
    let newvar () =
        varcount := !varcount + 1 ;
        Var (string_of_int (!varcount))

    module Gamma = struct (* TyEnv : id -> type *)
        type id = string
        module G = Map.Make (
            struct
                type t = id
                let compare = compare
            end)

        let empty = G.empty
        let add = G.add
        let apply = G.find
    end

    module Subst = struct (* Subst : tvar -> tvar *)
        module S = Map.Make (
            struct
                type t = string
                let compare = compare
            end)

        let empty = S.empty
        let add = S.add
        let single = S.singleton

        let rec apply tvar subst : tvar =
            match tvar with
            | Prim x -> Prim x
            | Arr(t1,t2) -> Arr(apply t1 subst,apply t2 subst)
            | Pair(t1,t2) -> Pair(apply t1 subst,apply t2 subst)
            | Loc l -> Loc (apply l subst)
            | Var str ->
                    if S.mem str subst then S.find str subst else Var str

        let subst_g gamma subst =
            Gamma.G.map (fun v -> apply v subst) gamma

        let subst_s r subst = (* subst r *)
            let sr = S.map (fun v -> apply v subst) r in
            let f x a b =
                match (a,b) with
                | None,None -> None
                | Some a',None -> Some a'
                | None,Some b' -> Some b'
                | Some a',Some b' -> Some a'
            in
            S.merge f sr subst
    end

    let rec occur (Var v) t =
        match t with
        | Prim _ -> false
        | Arr(t1,t2) -> occur (Var v) t1 || occur (Var v) t2
        | Pair(t1,t2) -> occur (Var v) t1 || occur (Var v) t2
        | Loc l -> occur (Var v) l
        | Var str -> str = v

    let rec unify t1 t2 =
        (* print_endline ("unify : "^(ptvar t1)^" and "^(ptvar t2)); *)
        match (t1,t2) with
        | Prim x,Prim y -> if x=y then Subst.empty else raise (TypeError "prim fail")
        | Var v,x | x,Var v ->
                if ((Var v) <> x) && (occur (Var v) x) then raise (TypeError "occur check fail") else Subst.single v x
        | Pair(a,b),Pair(c,d) | Arr(a,b),Arr(c,d) ->
                let s = unify a c in
                let s' = unify (Subst.apply b s) (Subst.apply d s) in
                Subst.subst_s s s'
        | Loc a,Loc b -> unify a b
        | _ -> raise (TypeError "unify fail")

    (* algorithm M
     *
     * gamma exp type -> subst
     * to solve 'eq' and 'write' problem,
     * we need another parameter 'query'.
     * query determines which type will be(?) at eq, write. *)

    type eq_query = EQINT | EQSTRING | EQBOOL | EQLOC
    type wr_query = WRINT | WRSTRING | WRBOOL
    type query = (eq_query list) * (wr_query list)

    let pop_eq_query (q:query) : (tvar * query) =
        let (hd::tl,w) = q in
        let t =
            match hd with
            | EQINT -> Prim Int
            | EQSTRING -> Prim String
            | EQBOOL -> Prim Bool
            | EQLOC -> Loc (newvar ())
        in
        (t,(tl,w))

    let pop_wr_query (q:query) : (tvar * query) =
        let (e,hd::tl) = q in
        let t =
            match hd with
            | WRINT -> Prim Int
            | WRSTRING -> Prim String
            | WRBOOL -> Prim Bool
        in
        (t,(e,tl))

    let rec m gamma exp t (q:query) =
        match exp with
        | CONST(S _) -> (unify (Prim String) t,q)
        | CONST(N _) -> (unify (Prim Int) t,q)
        | CONST(B _) -> (unify (Prim Bool) t,q)
        | VAR id -> (unify (Gamma.apply id gamma) t,q)
        | FN(id,e) ->
                let a1 = newvar () in
                let a2 = newvar () in
                let s = unify (Arr(a1,a2)) t in
                let (s',q) = m (Gamma.add id (Subst.apply a1 s) (Subst.subst_g gamma s)) e (Subst.apply a2 s) q in
                (Subst.subst_s s s',q)
        | APP(e1,e2) ->
                let a = newvar () in
                let (s,q) = m gamma e1 (Arr(a,t)) q in
                let (s',q) = m (Subst.subst_g gamma s) e2 (Subst.apply a s) q in
                (Subst.subst_s s s',q)
        | LET(NREC(id,e),scope) ->
                let a = newvar () in
                let (s,q) = m gamma e a q in
                let (s',q) = m (Gamma.add id (Subst.apply a s) (Subst.subst_g gamma s)) scope (Subst.apply t s) q in
                (Subst.subst_s s s',q)
        | LET(REC(id,e),scope) ->
                let a = newvar () in
                let (s,q) = m (Gamma.add id a gamma) e a q in
                let (s',q) = m (Gamma.add id (Subst.apply a s) (Subst.subst_g gamma s)) scope (Subst.apply t s) q in
                (Subst.subst_s s s',q)
        | IF(cond,e1,e2) -> (* TODO : prove it! *)
                let (s,q) = m gamma cond (Prim Bool) q in
                let (s',q) = m (Subst.subst_g gamma s) e1 (Subst.apply t s) q in
                let (s'',q) = m (Subst.subst_g (Subst.subst_g gamma s) s') e2 (Subst.apply (Subst.apply t s) s') q in
                (Subst.subst_s (Subst.subst_s s s') s'',q)
        | BOP(ADD,e1,e2) | BOP(SUB,e1,e2) ->
                let s = unify t (Prim Int) in
                let (s',q) = m (Subst.subst_g gamma s) e1 (Prim Int) q in
                let (s'',q) = m (Subst.subst_g (Subst.subst_g gamma s) s') e2 (Prim Int) q in
                (Subst.subst_s (Subst.subst_s s s') s'',q)
        | BOP(AND,e1,e2) | BOP(OR,e1,e2) ->
                let s = unify t (Prim Bool) in
                let (s',q) = m (Subst.subst_g gamma s) e1 (Prim Bool) q in
                let (s'',q) = m (Subst.subst_g (Subst.subst_g gamma s) s') e2 (Prim Bool) q in
                (Subst.subst_s (Subst.subst_s s s') s'',q)
        | BOP(EQ,e1,e2) ->
                let (t',q) = pop_eq_query q in
                let s = unify t (Prim Bool) in
                let (s',q) = m (Subst.subst_g gamma s) e1 (Subst.apply t' s) q in
                let (s'',q) = m (Subst.subst_g (Subst.subst_g gamma s) s') e2 (Subst.apply (Subst.apply t' s) s') q in
                (Subst.subst_s (Subst.subst_s s s') s'',q)
        | READ -> (unify t (Prim Int),q)
        | WRITE e ->
                let (t',q) = pop_wr_query q in
                let s = unify t t' in
                let (s',q) = m (Subst.subst_g gamma s) e (Subst.apply t' s) q in
                (Subst.subst_s s s',q)
        | MALLOC e ->
                let a = newvar () in
                let s = unify t (Loc a) in
                let (s',q) = m (Subst.subst_g gamma s) e (Subst.apply a s) q in
                (Subst.subst_s s s',q)
        | ASSIGN(addr,e) ->
                let (s,q) = m gamma addr (Loc t) q in
                let (s',q) = m (Subst.subst_g gamma s) e (Subst.apply t s) q in
                (Subst.subst_s s s',q)
        | BANG e ->
                m gamma e (Loc t) q
        | SEQ(e1,e2) ->
                let a = newvar () in
                let (s,q) = m gamma e1 a q in
                let (s',q) = m (Subst.subst_g gamma s) e2 (Subst.apply t s) q in
                (Subst.subst_s s s',q)
        | PAIR(e1,e2) ->
                let a1 = newvar () in
                let a2 = newvar () in
                let s = unify t (Pair(a1,a2)) in
                let (s',q) = m (Subst.subst_g gamma s) e1 (Subst.apply a1 s) q in
                let (s'',q) = m (Subst.subst_g (Subst.subst_g gamma s) s') e2 (Subst.apply (Subst.apply a2 s) s') q in
                (Subst.subst_s (Subst.subst_s s s') s'',q)
        | SEL1 e ->
                let a = newvar () in
                m gamma e (Pair(t,a)) q
        | SEL2 e ->
                let a = newvar () in
                m gamma e (Pair(a,t)) q

    let rec cnt_eq exp =
        match exp with
        | CONST _ | VAR _ | READ -> 0
        | BOP(EQ,e1,e2) -> (cnt_eq e1)+(cnt_eq e2)+1
        | FN(_,e) | WRITE e | MALLOC e | BANG e | SEL1 e | SEL2 e -> cnt_eq e
        | APP(e1,e2) | LET(REC(_,e1),e2) | LET(NREC(_,e1),e2)
        | BOP(_,e1,e2) | ASSIGN(e1,e2) | SEQ(e1,e2) | PAIR(e1,e2) -> (cnt_eq e1)+(cnt_eq e2)
        | IF(e1,e2,e3) -> (cnt_eq e1)+(cnt_eq e2)+(cnt_eq e3)

    let rec cnt_wr exp =
        match exp with
        | CONST _ | VAR _ | READ -> 0
        | WRITE e -> (cnt_wr e)+1
        | FN(_,e) | MALLOC e | BANG e | SEL1 e | SEL2 e -> cnt_wr e
        | APP(e1,e2) | LET(REC(_,e1),e2) | LET(NREC(_,e1),e2)
        | BOP(_,e1,e2) | ASSIGN(e1,e2) | SEQ(e1,e2) | PAIR(e1,e2) -> (cnt_wr e1)+(cnt_wr e2)
        | IF(e1,e2,e3) -> (cnt_wr e1)+(cnt_wr e2)+(cnt_wr e3)

    let rec generate_eq res left : eq_query list list =
        if left <= 0 then res else
            let put_eq l =
                [EQINT::l;EQSTRING::l;EQBOOL::l;EQLOC::l]
            in
            generate_eq (List.flatten (List.map put_eq res)) (left-1)

    let rec generate_wr res left : wr_query list list =
        if left <= 0 then res else
            let put_wr l =
                [WRINT::l;WRSTRING::l;WRBOOL::l]
            in
            generate_wr (List.flatten (List.map put_wr res)) (left-1)

    let mycheck exp query =
        varcount := 0;
        let a = newvar () in
        try
            Some (Subst.apply a (fst (m Gamma.empty exp a query)))
        with
        | _ ->
                None (* debug *)

    let rec ormap f l =
        match l with
        | [] -> []
        | hd::tl ->
                let res = f hd in
                if res <> None then let Some r = res in [r]@(ormap f tl)
                else ormap f tl

    let process exp =
        let n_eq = cnt_eq exp in
        let n_wr = cnt_wr exp in
        let q_eq = generate_eq ([[EQINT];[EQSTRING];[EQBOOL];[EQLOC]]) (n_eq) in
        let q_wr = generate_wr ([[WRINT];[WRSTRING];[WRBOOL]]) (n_wr) in

        let f qeq =
            let g qwr = mycheck exp (qeq,qwr) in
            ormap g q_wr in
        List.flatten (List.map f q_eq)

    let rec make_type (t:tvar) : types =
        match t with
        | Prim Int -> TyInt
        | Prim Bool -> TyBool
        | Prim String -> TyString
        | Pair(a,b) -> TyPair(make_type a,make_type b)
        | Loc l -> TyLoc (make_type l)
        | Arr(a,b) -> TyArrow(make_type a,make_type b)
        | _ -> raise (TypeError "unreachable")

    let mko t =
        try Some (make_type t) with
        _ -> None

    let rec unique l =
        match l with
        | [] -> []
        | a::[] -> [a]
        | a::b -> if a = (List.hd b) then unique b else a::(unique b)

    let check exp =
        let res = List.map mko (process exp) in
        let res' = List.sort compare res in
        let res'' = unique (List.filter (fun v -> v <> None) res') in
        if (List.length res'') = 1 then let Some x = List.hd res'' in x else raise (TypeError "fail")
end
