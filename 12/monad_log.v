Require Import Coq.Lists.List Arith.
Import ListNotations.

(*Monads*)

(* Ternary Conditional Language*)
Inductive Term : Set :=
  | tt : Term
  | ff : Term
  | if_then_else : Term -> Term -> Term -> Term.

(*CBV Beta Reduction for run a program (cbn: call-by-name reduction strategy)*)
Fixpoint beta_red_cbn (t : Term) : Term :=
 match t with 
   | if_then_else p q r => 
       match p with
         | tt => beta_red_cbn q
         | ff => beta_red_cbn r
         | _  => if_then_else (beta_red_cbn p) (beta_red_cbn q) (beta_red_cbn r) 
       end
   | tt => tt
   | ff => ff
 end.

(*
******************************
Kivételek - Option/Maybe monád
******************************
*)

(*Példa: a beta_red_cbn redukciós stratégia nem garantál teljes redukciót (nem fut le a program feltétlenül), 
  de ha lefut, gyorsan fut le, mert csak a közvetlen tt ff eseteket értékeli ki. Tehát nincs mindenhol értelmezve. 
  Az ilyen nem mindenhol értelmezett függvények (kivételek) kezelésére való az option typeformer. Az option typeformer induktív definíciójához: Print option.*)

Definition beta_red_cbn_opt (t : Term) : option Term := 
  match (beta_red_cbn t) with
    | tt | ff => Some (beta_red_cbn t)
    | if_then_else _ _ _ => None
  end.

Eval compute in beta_red_cbn_opt 
  (if_then_else ff (if_then_else (if_then_else ff ff tt) ff tt) ff ).

Eval compute in beta_red_cbn_opt 
  (if_then_else (if_then_else (if_then_else ff ff tt) ff tt) ff ff ).

(*
***************************
Többértékűség - Lista monád
***************************
*)

  (*Van, amikor nem kivételek, hanem többértékűség van. Pl. amikor nem egyetlen adat, hanem egy egész számítástörténet a kimenet. A lista typeformer induktív definíciójához: Print list.*)

Fixpoint depth (t : Term) : nat :=
  match t with
  | tt => 0
  | ff => 0
  | if_then_else p q r => 
      1 + max (depth p) (max (depth q) (depth r))
  end.

Fixpoint beta_reduct_with_trace (steps : nat) (t : Term) : list Term :=
  match steps with
  | 0 => [t]  
  | S n => 
      t :: beta_reduct_with_trace n (beta_red_cbn t) 
  end.

Definition beta_reduct_full_with_trace (t : Term) : list Term :=
  beta_reduct_with_trace (depth t) t.

Definition example_term := if_then_else (if_then_else (if_then_else ff (if_then_else ff ff tt) tt) tt tt) tt ff.

Compute beta_reduct_full_with_trace example_term.

(*
************************************************************
Korai kilépés - call/cc (call by current continuation) monad
************************************************************

Az előző példában túl sok redukció történt, lehetne gyorsabban, ha elérünk a legmélyére korábban.   
*)

Fixpoint beta_reduct_with_trace_and_exit (steps : nat) (t : Term) : list Term :=
  match steps with
  | 0 => [t]  
  | S n =>
      if depth (beta_red_cbn t) =? 0 then
        [t; beta_red_cbn t]
      else
        t :: beta_reduct_with_trace_and_exit n (beta_red_cbn t)
  end.

Definition beta_reduct_full_with_trace_and_exit (t : Term) : list Term :=
  beta_reduct_with_trace_and_exit (depth t) t. 

Compute beta_reduct_full_with_trace_and_exit example_term.

(*
Az alábbi nagyon absztrakt megoldás egy "exit" lable-t tesz a kilépés helyére. Ehhez egy olyan függvényre van szükség, amelyik 
  az exit változó meghívásakor kiugrik a számításból, ha meg nincs meghívva exit, folytatja. 
*)

Definition call_cc {A : Type} (f : (A -> A) -> A) : A :=
  f (fun x => x).

Fixpoint beta_reduct_with_call_cc (steps : nat) (t : Term) : list Term :=
  match steps with
  | 0 => [t]
  | S n =>
      call_cc (fun exit =>
        if depth (beta_red_cbn t) =? 0 then
          exit [beta_red_cbn t]
        else
          (beta_red_cbn t) :: beta_reduct_with_call_cc n (beta_red_cbn t)  
      )
  end.

Definition beta_reduct_full_with_trace_and_call_cc (t : Term) : list Term :=
  [t] ++ (beta_reduct_with_call_cc (depth t) t). 

Compute beta_reduct_full_with_trace_and_call_cc example_term.

(*
*********************************************
Continuation passing style (cps) - continuation monád
*********************************************
*)

(*
Az előbbi megoldás lényegében olyan alakban ír fel egy függvényt hogy azt nézi, mit lehet vele csinálni. Ez egy általános programozási stílus
  az úgy nevezett kontinuáció. Ahelyett, hogy leprogramoznánk az f: A -> B függvényt, azt mondjuk meg, hogy ha őt egy g: (A -> B) -> C meghívná
  abból a célból, hogy egy C-beli értéket számítson ki, hogyan kell ezt megtenni. Tehát szükségünk van egy f_cont :  ((A -> B) -> C) -> C alakra, 
  amelyik megmondja, hogy ha egy g "tovább akarnak számolni f-fel", akkor azt hogy kell tennie. Ilyenkor g a kontinuáció, f_cont a continuation passing style alakja f-nek.
*)

Fixpoint depth_cps (t : Term) (k : nat -> list Term) : list Term :=
  match t with
  | tt => k 0
  | ff => k 0
  | if_then_else p q r =>
      depth_cps p (fun dp =>
      depth_cps q (fun dq =>
      depth_cps r (fun dr =>
      k (1 + max dp (max dq dr)))))
  end.

Definition beta_reduct_full_with_trace_c (t : Term) : list Term :=
  depth_cps t (fun k => beta_reduct_with_trace k t).


Compute beta_reduct_full_with_trace_c example_term.
   
(*
****************
  Már 13. hét
****************
*)
(*Monad in CS, Extension system*)
Structure Monad : Type := mk_monad
{
  (*sort*)
  M : Type -> Type;
  
  (*operators*)
  bind : forall {A B : Type}, (A -> M B) -> M A -> M B;
  ret : forall {A : Type}, A -> M A;

  (*equations*)  
  left_id_law : forall (A B : Type) (a : A) (f : A -> M B), 
                    bind f (ret a) = f a; 

  right_id_law : forall (A : Type) (ma : M A),
                    bind (ret) ma = ma; 

  assoc_law : forall (A B C : Type) (ma : M A) (g : A -> M B) (f : B -> M C),
                    bind f (bind g ma) = bind (fun x => bind f (g x)) ma
}.

Parameter Typev : Type -> Type.

Inductive MonadI  (A : Type) : Type :=
  | retI : A -> MonadI A
  | bindI : forall (B : Type), ((Typev B) -> MonadI A) -> MonadI B -> MonadI A.

Print MonadI_ind.

Definition ret_opt (A : Type) := fun (a : A) => Some a.

Definition bind_opt (A B: Type) := fun (f : A -> option B) (ma : option A) =>
                     match ma with
                       | Some a => f a
                       | None => None
                     end.


Theorem Option_is_a_Monad : Monad.
Proof.
apply mk_monad with (M := option) (bind := bind_opt) (ret := ret_opt).
  - intros; simpl; auto.
  - intros; induction ma; compute; auto.
  - intros; induction ma; compute; auto.
Qed.

Require Import List.
Import ListNotations.

Definition ret_list (A : Type) := fun (a : A) => [a].

Fixpoint bind_list (A B: Type) (f : A -> list B) (l : list A) {struct l} :=
                     match l with
                       | nil => nil
                       | a :: l' => (f a) ++ (bind_list A B f l')
                     end.

Theorem Option_is_a_List : Monad.
Proof.
apply mk_monad with (M := list) (bind := bind_list) (ret := ret_list).
  - intros; simpl; auto.
Abort.
  


