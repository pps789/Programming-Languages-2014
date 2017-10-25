exception IMPOSSIBLE
type treasure = StarBox | NameBox of string
type key = Bar | Node of key * key
type map =
    End of treasure
    | Branch of map * map
    | Guide of string * map

(* DSU Implementation *)
module DSU =
struct
    type t = D of (string -> string)
    let empty = D(fun x -> x)

    let rec find (D(dsu)) id =
        if (dsu id) = id then id
        else find (D(dsu)) (dsu id)
    ;;

    let put dsu a b = (* a -> b *)
        let da = find dsu a in
        let db = find dsu b in
        let D(d) = dsu in
        D(fun x -> if x = da then db else d x)
    ;;
end

(* Pool Implementation *)
module Pool =
struct
    type content = Bar | Basis of string | Pair of string * string
    type t = P of (string -> content)

    let empty = P(fun x -> if x = "*" then Bar else Basis(x))

    let find dsu (P(pool)) id =
        let tid = DSU.find dsu id in
        pool tid
    ;;

    let rec __contains dsu pool x ty = (* x contains y?, y is basis *)
        let tx = find dsu pool x in
        match tx with
        | Bar -> false
        | Basis(x) -> x = ty
        | Pair(p1, p2) -> (__contains dsu pool p1 ty) || (__contains dsu pool p2 ty)
    ;;

    let contains dsu pool pair y =
        let Pair(a, b) = find dsu pool pair in
        let Basis(ty) = find dsu pool y in
        (__contains dsu pool a ty) || (__contains dsu pool b ty)
    ;;

    let union dsu pool basis pair = (* return (dsu . pool) *)
        if contains dsu pool pair basis then raise IMPOSSIBLE
        else ((DSU.put dsu basis pair), pool)
    ;;

    let rec unify dsu pool a b =
        let ta = find dsu pool a in
        let tb = find dsu pool b in
        match (ta, tb) with
        | (Pair(a1, a2), Pair(b1, b2)) ->
                let (d, p) = unify dsu pool a1 b1 in
                unify d p a2 b2
        | (Pair(_, _), Basis(basis)) ->
                union dsu pool basis a
        | (Basis(basis), Pair(_, _)) ->
                union dsu pool basis b
        | (Basis(b1), Basis(b2)) ->
                ((DSU.put dsu b1 b2), pool)
        | (Bar, Bar) -> (dsu, pool)
        | (Basis(basis), Bar) ->
                ((DSU.put dsu basis "*"), pool)
        | (Bar, Basis(basis)) ->
                ((DSU.put dsu basis "*"), pool)
        | _ -> raise IMPOSSIBLE
    ;;

    let basisTear dsu pool id =
        let Basis(tid) = find dsu pool id in
        let tid_1 = String.concat "" ["(";tid;"_1)"] in
        let tid_2 = String.concat "" ["(";tid;"_2)"] in
        let P(p) = pool in
        (dsu, (P(fun x -> if x = tid then Pair(tid_1, tid_2) else p x)), tid_1, tid_2)
    ;;

    let makePair dsu pool a b =
        let ta = DSU.find dsu a in
        let tb = DSU.find dsu b in
        let str = String.concat "" ["(";ta;".";tb;")"] in
        let P(p) = pool in
        (dsu, (P(fun x -> if x = str then Pair(ta,tb) else p x)), str)
    ;;

    let functionCall dsu pool gamma beta =
        let tgamma = find dsu pool gamma in
        match tgamma with
        | Bar -> raise IMPOSSIBLE
        | Pair(p1, p2) ->
                let (d, p) = unify dsu pool p1 beta in
                (d, p, p2)
        | Basis(basis) ->
                let (d, p, b1, b2) = basisTear dsu pool basis in
                let (d', p') = unify d p b1 beta in
                (d', p', b2)
    ;;

    let rec generateKey dsu pool id =
        let k = find dsu pool id in
        match k with
        | Pair(p1, p2) ->
                Node((generateKey dsu pool p1), (generateKey dsu pool p2))
        | Bar ->
                Bar
        | Basis(basis) ->
                Bar
    ;;
end

let rec travel dsu pool m =
    match m with
    | End(NameBox(name)) -> (dsu, pool, name)
    | End(StarBox) -> (dsu, pool, "*")
    | Guide(name, m') ->
            let (d, p, x) = travel dsu pool m' in
            Pool.makePair d p name x
    | Branch(m1, m2) ->
            let (d2, p2, beta) = travel dsu pool m2 in
            let (d', p', gamma) = travel d2 p2 m1 in
            Pool.functionCall d' p' gamma beta
;;

let rec getVariable m =
    match m with
    | End(NameBox(name)) -> [name]
    | End(StarBox) -> ["*"]
    | Guide(_, m') -> getVariable m'
    | Branch(m1, m2) -> (getVariable m1) @ (getVariable m2)
;;

let rec keySorter k1 k2 =
    match (k1, k2) with
    | (Bar, Bar) -> 0
    | (Node(_), Bar) -> 1
    | (Bar, Node(_)) -> -1
    | (Node(k11, k12), Node(k21, k22)) ->
            let left = keySorter k11 k21 in
            if left = 0 then keySorter k12 k22 else left
;;

let rec unique l =
    match l with
    | [] -> []
    | a::[] -> [a]
    | a::b ->
            if (keySorter a (List.hd b)) = 0 then unique b else a::(unique b)
;;

let getReady m =
    let varList = getVariable m in
    let (dsu, pool, x) = travel (DSU.empty) (Pool.empty) m in
    let keyList = List.map (Pool.generateKey dsu pool) varList in
    unique (List.sort keySorter keyList)
;;
