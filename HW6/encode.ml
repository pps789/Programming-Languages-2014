(*
 * SNU 4190.310 Programming Languages
 *
 * M0
 *)
open M
module Encoder =
  struct
  	exception Error of string

    let rec wrap : Lambda.lexp -> int -> Lambda.lexp -> Lambda.lexp (* f^n x *)
    = fun f n x ->
        if n = 0 then x
        else wrap f (n-1) (Lambda.App (f, x))

    let lambda_true = Lambda.Lam("a", Lambda.Lam("b", Lambda.Id "a"))
    let lambda_false = Lambda.Lam("a", Lambda.Lam("b", Lambda.Id "b"))

    let is_zero =
        Lambda.Lam("n",
        Lambda.App(
            Lambda.App(
                Lambda.Id "n", Lambda.Lam("x", lambda_false)), lambda_true))

    let lambda_add =
        Lambda.Lam("n",Lambda.Lam("m",Lambda.Lam("f",Lambda.Lam("x",
        Lambda.App(
            Lambda.App(Lambda.Id "n", Lambda.Id "f"),
            Lambda.App(Lambda.App(Lambda.Id "m", Lambda.Id "f"), Lambda.Id "x"))))))

    let lambda_pred =
        Lambda.Lam("n",Lambda.Lam("f",Lambda.Lam("x",
        Lambda.App(Lambda.App(Lambda.App(
            Lambda.Id "n",
            Lambda.Lam("g", Lambda.Lam("h", Lambda.App(Lambda.Id "h", Lambda.App(Lambda.Id "g", Lambda.Id "f"))))),
            Lambda.Lam("u", Lambda.Id "x")),
            Lambda.Lam("u", Lambda.Id "u")))))

    let lambda_sub =
        Lambda.Lam("m", Lambda.Lam("n", Lambda.App(Lambda.App(Lambda.Id "n", lambda_pred), Lambda.Id "m")))

    let lambda_mkpr =
        Lambda.Lam("x", Lambda.Lam("y", Lambda.Lam("f",
        Lambda.App(Lambda.App(
            Lambda.Id "f",
            Lambda.Id "x"),
            Lambda.Id "y"))))

    let lambda_fst = Lambda.Lam("p", Lambda.App(Lambda.Id "p", lambda_true))
    let lambda_snd = Lambda.Lam("p", Lambda.App(Lambda.Id "p", lambda_false))

    let z_combinator =
        let g =
            Lambda.Lam("x", Lambda.App(Lambda.Id "f",
            Lambda.Lam("v", Lambda.App(Lambda.App(Lambda.Id "x", Lambda.Id "x"), Lambda.Id "v")))) in
        Lambda.Lam("f", Lambda.App(g, g))

    let num : int -> Lambda.lexp
    = fun i ->
        Lambda.Lam ("f", Lambda.Lam ("x", wrap (Lambda.Id "f") i (Lambda.Id "x")))

	let rec encode : M.mexp -> Lambda.lexp
	= fun pgm ->
        match pgm with
        | M.Num n -> num n
        | M.Var id -> Lambda.Id id
        | M.Ifz(cond, t, f) ->
                let lambda_cond = Lambda.App(is_zero, encode cond) in
                let lambda_then = Lambda.Lam("if", encode t) in
                let lambda_else = Lambda.Lam("if", encode f) in
                Lambda.App(Lambda.App(Lambda.App(
                        lambda_cond, lambda_then), lambda_else),
                        Lambda.Id "if")
        | M.Add(m1, m2) -> Lambda.App(Lambda.App(lambda_add, encode m1), encode m2)
        | M.Sub(m1, m2) -> Lambda.App(Lambda.App(lambda_sub, encode m1), encode m2)
        | M.Pair(m1, m2) -> Lambda.App(Lambda.App(lambda_mkpr, encode m1), encode m2)
        | M.Fst m -> Lambda.App(lambda_fst, encode m)
        | M.Snd m -> Lambda.App(lambda_snd, encode m)
        | M.And(m1, m2) -> encode(
            M.Ifz(m1, M.Num 0, M.Ifz(m2, M.Num 0, M.Num 1)))
        | M.Fn(id, m) -> Lambda.Lam(id, encode m)
        | M.App(m1, m2) -> Lambda.App(encode m1, encode m2)
        | M.Rec(id, para, body) ->
                Lambda.App(z_combinator, Lambda.Lam(id, Lambda.Lam(para, encode body)))
  end
