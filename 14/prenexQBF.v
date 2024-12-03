Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

(* Define PreForm *)
Inductive PreForm : Set :=
  | Var : nat -> PreForm
  | Bot : PreForm
  | Top : PreForm
  | Neg : PreForm -> PreForm
  | Arr : PreForm -> PreForm -> PreForm
  | Any : PreForm -> PreForm
  | Some : PreForm -> PreForm. 

Fixpoint lift_aux (n : nat) (t : PreForm) (k : nat) {struct t} : PreForm :=
   match t with
     | Bot => Bot
     | Top => Top
     | Var i => match (le_gt_dec k i) with
                  | left _ => (* k <= i *) Var (i + n)
                  | right _ => (* k > i *) Var i
                end
     | Neg s => Neg (lift_aux n s k)
     | Arr s r => Arr (lift_aux n s k) (lift_aux n r k)
     | Any s => Any (lift_aux n s (S k))
     | Some s => Some (lift_aux n s (S k))
   end.

Definition lift_n t n := lift_aux n t 0.

Definition lift t := lift_aux 1 t 0.

Fixpoint prnx (t : PreForm) : PreForm :=
  match t with 
   | Bot => Bot
   | Top => Top
   | Var i => Var i
   | Neg (Any A) => Some (Neg (prnx A))
   | Neg (Some A) => Any (Neg (prnx A))
   | Neg s => Neg (prnx s)
   | Arr A (Some B) => Some (Arr (lift (prnx A)) (prnx B)) 
   | Arr A (Any B) => Any (Arr (lift (prnx A)) (prnx B))
   | Arr (Some A) B  => Any (Arr (prnx A) (lift (prnx B)))
   | Arr (Any A) B => Some (Arr (prnx A) (lift (prnx B)))
   | Arr s r => Arr (prnx s) (prnx r) 
   | Any s => Any (prnx s)
   | Some s => Some (prnx s)
  end.

Fixpoint depth (t : PreForm) : nat :=
  match t with
  | Var i => 0
  | Bot | Top => 0
  | Neg s => S (depth s) 
  | Arr s r => 1 + (max (depth s) (depth r))
  | Any s => S (depth s)
  | Some s => S (depth s)
  end.

Fixpoint prnx_aux (n : nat) (t : PreForm) : PreForm :=
  match n with 
    | 0 => prnx t
    | S m => prnx (prnx_aux m t)
  end.

Definition prnx_full (t : PreForm) := prnx_aux (depth t) t.

Eval compute in prnx_full (Arr (Arr (Neg Top) (Some (Var 0))) (Some (Var 0))).


