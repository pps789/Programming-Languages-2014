(*
 * SNU 4190.310 Programming Languages (Fall 2014)
 *
 * SM5
 *)
open K
open Sm5
module Translator = struct

let rec trans : K.program -> Sm5.command
= fun pgm ->
  match pgm with
    | K.NUM n -> [Sm5.PUSH (Sm5.Val (Sm5.Z n))]
    | K.TRUE -> [Sm5.PUSH (Sm5.Val (Sm5.B true))]
    | K.FALSE -> [Sm5.PUSH (Sm5.Val (Sm5.B false))]
    | K.UNIT -> [Sm5.PUSH (Sm5.Val (Sm5.Unit))]
    | K.VAR v -> [Sm5.PUSH (Sm5.Id v); Sm5.LOAD]
    | K.ADD (e1, e2) -> (trans e1)@(trans e2)@[Sm5.ADD]
    | K.SUB (e1, e2) -> (trans e1)@(trans e2)@[Sm5.SUB]
    | K.MUL (e1, e2) -> (trans e1)@(trans e2)@[Sm5.MUL]
    | K.DIV (e1, e2) -> (trans e1)@(trans e2)@[Sm5.DIV]
    | K.EQUAL (e1, e2) -> (trans e1)@(trans e2)@[Sm5.EQ]
    | K.LESS (e1, e2) -> (trans e1)@(trans e2)@[Sm5.LESS]
    | K.NOT e -> (trans e)@[Sm5.NOT]
    | K.ASSIGN (id, e) -> (trans e)@[Sm5.PUSH (Sm5.Id id); Sm5.STORE]@(trans (K.VAR id))
    | K.SEQ (e1, e2) -> (trans e1)@[Sm5.POP]@(trans e2)
    | K.IF (e1, e2, e3) -> (trans e1)@[Sm5.JTR (trans e2, trans e3)]
    | K.WHILE (cond, body) ->
            trans (K.LETF ("while#", "while_para#", (K.IF (cond, K.SEQ(body, K.CALLV("while#", K.NUM 1)), K.UNIT)), K.CALLV("while#", K.NUM 1)))
    | K.FOR (id, e_lo, e_hi, body) ->
            trans (K.LETF ("eval#", "x#", K.SEQ (K.ASSIGN (id, K.VAR "x#"), body),
            K.LETV ("lo#", e_lo,
            K.LETV ("hi#", e_hi,
            K.LETF ("f#", "y#",
                K.IF (K.LESS (K.VAR "y#", K.ADD (K.VAR "hi#", K.NUM 1)),
                    K.SEQ (K.CALLV ("eval#", K.VAR "y#"), K.CALLV ("f#", K.ADD (K.VAR "y#", K.NUM 1))),
                    K.UNIT),
                K.CALLV ("f#", K.VAR "lo#"))))))
    | K.LETV (id, expr, scope) -> (trans expr)@[Sm5.MALLOC; Sm5.BIND id; Sm5.PUSH (Sm5.Id id); Sm5.STORE]@(trans scope)@[Sm5.UNBIND; Sm5.POP]
    | K.LETF (proc_id, para_id, body, scope) -> [Sm5.PUSH (Sm5.Fn (para_id,[Sm5.BIND proc_id]@(trans body))); Sm5.BIND proc_id]@(trans scope)@[Sm5.UNBIND; Sm5.POP]
    | K.CALLV (id, e) -> [Sm5.PUSH (Sm5.Id id); Sm5.PUSH (Sm5.Id id)]@(trans e)@[Sm5.MALLOC; Sm5.CALL]
    | K.CALLR (id, para) -> [Sm5.PUSH (Sm5.Id id); Sm5.PUSH (Sm5.Id id); Sm5.PUSH (Sm5.Id para); Sm5.LOAD; Sm5.PUSH (Sm5.Id para); Sm5.CALL]
    | K.READ id -> [Sm5.GET; Sm5.PUSH (Sm5.Id id); Sm5.STORE; Sm5.PUSH (Sm5.Id id); Sm5.LOAD]
    | K.WRITE e -> (trans e)@[Sm5.MALLOC; Sm5.BIND "write#"; Sm5.PUSH (Sm5.Id "write#"); Sm5.STORE; Sm5.PUSH (Sm5.Id "write#"); Sm5.LOAD; Sm5.PUSH (Sm5.Id "write#"); Sm5.LOAD; Sm5.PUT; Sm5.UNBIND; Sm5.POP]
end
