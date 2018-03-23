(************************************************************************************************)
(* Constructors plugin.                                                                         *)
(* Copyright (c) 2010-2015 Matthieu Sozeau <mattam@mattam.org>.                                 *)
(************************************************************************************************)

(** Constructors - An example plugin and tactic for Coq

    This defines a tactic [constructors of c in id] that puts
    the list of constructors of the inductive type [c] in the
    (fresh) hypothesis [id]. We build a [list dynamic] where
    [dyn] is defined in a support file of the plugin
    (in theories/Dynamic.v) and is isomorphic to a sigma type.
*)

(* These are necessary for grammar extensions like the one at the end
   of the module *)

(*i camlp4deps: "parsing/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmo" i*)

DECLARE PLUGIN "constructors"

(* $$ *)

open Ltac_plugin     
open Term
open Names
open Universes
open Stdarg
   
(* Getting constrs (primitive Coq terms) from exisiting Coq libraries. *)

let find_constant contrib dir s =
  constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "constructors"
let init_constant dir s = find_constant contrib_name dir s

(* We also need booleans from the standard library. *)

let bool_path = ["Coq";"Init";"Datatypes"]
let coq_true = lazy (init_constant bool_path "true")
let coq_false = lazy (init_constant bool_path "false")

(* A clause specifying that the [let] should not try to fold anything the goal
   matching the list of constructors (see [letin_tac] below). *)

let nowhere = Locus.({ onhyps = Some []; concl_occs = NoOccurrences })

(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. There's currently no way to return a term
   through an extended tactic, hence the use of a let binding. *)

let isprop_tac gl c id =
  let open Proofview in
  let open Notations in
  let env = Goal.env gl in
  let sigma = Goal.sigma gl in
  let map, t = Typing.type_of env sigma c in
  let prop = EConstr.mkProp in
  let b = if t = prop then coq_true else coq_false in
  let b' = (EConstr.of_constr (Lazy.force b)) in
  let tac = V82.tactic (Refiner.tclEVARS (fst (Typing.type_of env sigma b'))) in
      tac <*> Tactics.letin_tac None (Name id) b' None nowhere

TACTIC EXTEND isprop_tac
| ["is_prop" constr(c) "in" ident(id) ] ->
  [ Proofview.Goal.enter begin fun gl ->
    let gl = Proofview.Goal.assume gl in
      isprop_tac gl c id
  end 
    ]
END
