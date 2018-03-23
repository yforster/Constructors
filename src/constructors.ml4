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

(* Some boilerplate that should go to a standard library eventually *)
   
let ltac_lcall tac args =
  Tacexpr.TacArg(Loc.tag @@ Tacexpr.TacCall (Loc.tag (Misctypes.ArgVar(Loc.tag @@ Names.Id.of_string tac),args)))

let to_ltac_val c = Tacinterp.Value.of_constr c

open Tacexpr
open Tacinterp
open Misctypes
open Tacarg

let ltac_apply (f : Value.t) (args: Tacinterp.Value.t list) =
  let fold arg (i, vars, lfun) =
    let id = Names.Id.of_string ("x" ^ string_of_int i) in
    let x = Reference (ArgVar (Loc.tag id)) in
    (succ i, x :: vars, Id.Map.add id arg lfun)
  in
  let (_, args, lfun) = List.fold_right fold args (0, [], Id.Map.empty) in
  let lfun = Id.Map.add (Id.of_string "F") f lfun in
  let ist = { (Tacinterp.default_ist ()) with Tacinterp.lfun = lfun; } in
  Tacinterp.eval_tactic_ist ist (ltac_lcall "F" args)

(* Getting constrs (primitive Coq terms) from exisiting Coq libraries. *)

let find_constant contrib dir s =
  constr_of_global (Coqlib.find_reference contrib dir s)

let contrib_name = "constructors"
let init_constant dir s = find_constant contrib_name dir s

let constructors_path = ["Constructors";"Dynamic"]

(* We use lazy as the Coq library is not yet loaded when we
   initialize the plugin, once [Constructors.Dynamic] is loaded
   in the interpreter this will resolve correctly. *)

let coq_dynamic_ind = lazy (init_constant constructors_path "dyn")
let coq_dynamic_constr = lazy (init_constant constructors_path "mkDyn")
let coq_dynamic_type = lazy (init_constant constructors_path "dyn_type")
let coq_dynamic_obj = lazy (init_constant constructors_path "dyn_value")

(* Reflect the constructor of [dyn] values *)

let mkDyn ty value =
  mkApp (Lazy.force coq_dynamic_constr, [| ty ; value |])

(* We also need lists from the standard library. *)

let list_path = ["Coq";"Init";"Datatypes"]
let coq_list_ind = lazy (init_constant list_path "list")
let coq_list_nil = lazy (init_constant list_path "nil")
let coq_list_cons = lazy (init_constant list_path "cons")

(* Now the real tactic. *)

let constructors env c =
  (* Decompose the application of the inductive type to params and arguments. *)
  let ind, args = Inductive.find_rectype env c in
  (* Find information about it (constructors, other inductives in the same block...) *)
  let mindspec = Global.lookup_pinductive ind in
  (* We fold on the constructors and build a [dyn] object for each one. *)
  CArray.fold_right_i (fun i v l ->
      (* Constructors are just referenced using the inductive type
	 and constructor number (starting at 1). *)
      let cd = mkConstructUi (ind, succ i) in
      let d = mkDyn v cd in
      (* Cons the constructor on the list *)
      mkApp (Lazy.force coq_list_cons, [| Lazy.force coq_dynamic_ind; d; l |]))
    (* An array of types for the constructors, with parameters abstracted too. *)
    (Inductive.type_of_constructors ind mindspec)
    (* Our init is just the empty list *)
    (mkApp (Lazy.force coq_list_nil, [| Lazy.force coq_dynamic_ind |]))


(* This adds an entry to the grammar of tactics, similar to what
   Tactic Notation does. There's currently no way to return a term
   through an extended tactic, hence the use of a let binding. *)

TACTIC EXTEND constructors_of_in
| ["constructors" "of" constr(c) "in" tactic(tac) ] ->
  [ Proofview.Goal.enter begin fun gl ->
      let env = Proofview.Goal.env gl in
      let v = constructors env (EConstr.to_constr (Proofview.Goal.sigma gl) c) in
      ltac_apply tac (List.map to_ltac_val [EConstr.of_constr v])
  end 
    ]
END
