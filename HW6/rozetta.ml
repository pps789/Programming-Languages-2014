(*
 * SNU 4190.310 Programming Languages
 *
 * Sonata
 *)
open Sm5
open Sonata
module Rozetta = struct
  let rec mytrans : Sm5.command -> Sonata.command = fun command ->
      match command with
      | [] -> []
      | Sm5.PUSH obj::tl ->
              let here =
                  (match obj with
                  | Sm5.Val v ->
                          (match v with
                          | Sm5.Z z -> Sonata.PUSH (Sonata.Val (Sonata.Z z))
                          | Sm5.B b -> Sonata.PUSH (Sonata.Val (Sonata.B b))
                          | Sm5.Unit -> Sonata.PUSH (Sonata.Val Sonata.Unit)
                          | _ -> raise (Invalid_argument "rozetta")
                          )
                  | Sm5.Id str -> Sonata.PUSH (Sonata.Id str)
                  | Sm5.Fn (str, cmd) ->
                          let callback = [Sonata.PUSH (Sonata.Id ("cbf#"));
                          Sonata.UNBIND; Sonata.POP;
                          Sonata.PUSH (Sonata.Val (Sonata.Z (-1)));
                          Sonata.PUSH (Sonata.Val (Sonata.L (-1,-1)));
                          Sonata.CALL] in
                          Sonata.PUSH (Sonata.Fn (str, [Sonata.BIND "cbf#"]@(mytrans cmd)@callback))
                  ) in
              here::mytrans tl
      | Sm5.POP::tl -> Sonata.POP::mytrans tl
      | Sm5.STORE::tl -> Sonata.STORE::mytrans tl
      | Sm5.LOAD::tl -> Sonata.LOAD::mytrans tl
      | Sm5.JTR (c1,c2)::tl -> Sonata.JTR (mytrans c1,mytrans c2)::mytrans tl
      | Sm5.MALLOC::tl -> Sonata.MALLOC::mytrans tl
      | Sm5.BOX n::tl -> Sonata.BOX n::mytrans tl
      | Sm5.UNBOX str::tl -> Sonata.UNBOX str::mytrans tl
      | Sm5.BIND str::tl -> Sonata.BIND str::mytrans tl
      | Sm5.UNBIND::tl -> Sonata.UNBIND::mytrans tl
      | Sm5.GET::tl -> Sonata.GET::mytrans tl
      | Sm5.PUT::tl -> Sonata.PUT::mytrans tl
      | Sm5.ADD::tl -> Sonata.ADD::mytrans tl
      | Sm5.SUB::tl -> Sonata.SUB::mytrans tl
      | Sm5.MUL::tl -> Sonata.MUL::mytrans tl
      | Sm5.DIV::tl -> Sonata.DIV::mytrans tl
      | Sm5.EQ::tl -> Sonata.EQ::mytrans tl
      | Sm5.LESS::tl -> Sonata.LESS::mytrans tl
      | Sm5.NOT::tl -> Sonata.NOT::mytrans tl
      | Sm5.CALL::tl ->
              let callback_cmd =
                  (mytrans tl)@
                  [Sonata.PUSH (Sonata.Id "cbf#");
                          Sonata.UNBIND; Sonata.POP;
                          Sonata.PUSH (Sonata.Val (Sonata.Z (-1)));
                          Sonata.PUSH (Sonata.Val (Sonata.L (-1,-1)));
                          Sonata.CALL] in
              let callback_fun = Sonata.Fn ("cb#", callback_cmd) in
              [Sonata.PUSH (Sonata.Val (Sonata.L (-2,0))); Sonata.STORE;
              Sonata.PUSH (Sonata.Val (Sonata.L (-2,1))); Sonata.STORE;
              Sonata.PUSH (Sonata.Val (Sonata.L (-2,2))); Sonata.STORE;
              Sonata.PUSH callback_fun;
              Sonata.PUSH (Sonata.Val (Sonata.L (-2,2))); Sonata.LOAD;
              Sonata.PUSH (Sonata.Val (Sonata.L (-2,1))); Sonata.LOAD;
              Sonata.PUSH (Sonata.Val (Sonata.L (-2,0))); Sonata.LOAD;
              Sonata.CALL]

  let trans : Sm5.command -> Sonata.command = fun command ->
      [Sonata.PUSH (Sonata.Fn ("cb#", []));
      Sonata.BIND "cbf#"]
      @mytrans command
end
