(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * Lambda Calculus
 *)

module Evaluator =
  struct
	exception Error of string

    let rec longest l =
        match l with
        | [] -> ""
        | hd::tl ->
                let res = longest tl in
                if (String.length hd) > (String.length res) then hd else res

    let newstr l = String.concat "" [(longest l); "0"]

    let (@?) l x = snd (List.find (fun y -> x = fst y) l)
    let (@!) l x = List.exists (fun y -> x = fst y) l
    let fsts l = List.map (fun y -> fst y) l
    let snds l = List.map (fun y -> snd y) l

    type subrule = (string * Lambda.lexp) list
    let emptyrule = []
    let addrule rule str exp = (str, exp)::rule

    let rec freevar exp =
        match exp with
        | Lambda.Id id -> [id]
        | Lambda.Lam (s, e) -> List.filter (fun y -> (not (s = y))) (freevar e)
        | Lambda.App (e1, e2) -> (freevar e1)@(freevar e2)
    
    let rec substitution sub exp =
        match exp with
        | Lambda.Id id ->
                if (sub @! id) then (sub @? id) else exp
        | Lambda.App (e1, e2) -> Lambda.App ((substitution sub e1), (substitution sub e2))
        | Lambda.Lam (s, e) ->
                let s' = newstr ((List.flatten (List.map freevar (snds sub))) @ (fsts sub) @ (freevar exp)) in
                Lambda.Lam (s', substitution (addrule sub s (Lambda.Id s')) e)

    let rec betareduction exp = (* return (exp', reduced?) *)
        match exp with
        | Lambda.App (Lambda.Lam (x, e1), e2) ->
                (substitution (addrule emptyrule x e2) e1, true)
        | Lambda.App (e1, e2) ->
                let (e1', det) = betareduction e1 in
                if det then (Lambda.App (e1', e2), true)
                else
                    let (e2', det2) = betareduction e2 in
                    if det2 then (Lambda.App (e1, e2'), true) else (exp, false)
        | Lambda.Id _ -> (exp, false)
        | Lambda.Lam (x, e) ->
                let (e', det) = betareduction e in
                if det then (Lambda.Lam (x, e'), true) else (exp, false)
 
	let rec reduce : Lambda.lexp -> Lambda.lexp
	= fun exp ->
        let (e', det) = betareduction exp in
        if det then reduce e' else exp

  end
