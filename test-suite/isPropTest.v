Require Import isProp.isProp. 
  
Goal forall n : nat, forall P : Prop, n = n.
Proof.
  intros.
  let x := isProp n in pose (pn := x).
  let x := isProp P in pose (pP := x).
  reflexivity.
Qed.
