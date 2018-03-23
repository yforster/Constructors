(************************************************************************************************)
(* Constructors plugin.                                                                         *)
(* Copyright (c) 2010-2015 Matthieu Sozeau <mattam@mattam.org>.                                 *)
(************************************************************************************************)

Declare ML Module "constructors".

(** A CPS version of the tactic that gives the constructor list directly
   to [tac]. *)

Ltac is_prop_cps ind tac :=
  let x := fresh "H" in 
  is_prop ind in x ;
  let cs := eval cbv in x in
    clear x; tac cs. 

Ltac e x := exact x.
Ltac isProp P := let x := constr:(ltac:(is_prop_cps P e)) in let y := eval cbn in x in y.
