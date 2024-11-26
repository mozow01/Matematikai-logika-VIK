Inductive Term : Set :=
  | tt : Term
  | ff : Term
  | if_then_else : Term -> Term -> Term -> Term.

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

Definition beta_red_cbn_opt (t : Term) : option Term := 
  match (beta_red_cbn t) with
    | tt | ff => Some (beta_red_cbn t)
    | if_then_else _ _ _ => None
  end.

Definition ret {A : Type} (x : A) : option A := Some x.

Definition bind {A B : Type} (m : option A) (f : A -> option B) : option B :=
  match m with
  | Some x => f x
  | None => None
  end.

Definition return_ternary_ex (t: Term) : option Term :=
  match t with
  | tt | ff => Some t
  | if_then_else _ _ _ => None
  end.

Definition beta_red_cbn_mon (t : option Term) : option Term := 
  bind t (fun t' => 
  bind (ret (beta_red_cbn t')) (fun t'' =>
  bind (return_ternary_ex t'')
  ret )).

Eval compute in beta_red_cbn_mon 
  (Some (if_then_else (if_then_else (if_then_else ff ff tt) ff tt) ff ff)).

Definition double_beta_red (t : option Term) : option Term :=
  bind t (fun t' =>
  bind (ret (beta_red_cbn t')) (fun t'' =>
  bind (ret (beta_red_cbn t'')) (fun t''' =>
  bind (return_ternary_ex t'') 
  ret ))).

Eval compute in beta_red_cbn_mon  
  (Some (if_then_else (if_then_else (if_then_else ff ff tt) ff tt) ff ff)).

Eval compute in double_beta_red  
  (Some (if_then_else ff (if_then_else (if_then_else ff ff tt) ff tt) ff)).

Structure Monad : Type := mk_monad
{
  (*sort*)
  M : Type -> Type;

  (*operators*)
  bindM : forall {A B : Type}, M A -> (A -> M B) -> M B;
  retM : forall {A : Type}, A -> M A;

  (*equations*)  
  left_id_law : forall (A B : Type) (a : A) (f : A -> M B), 
                    bindM (retM a) f = f a; 

  right_id_law : forall (A : Type) (ma : M A),
                    bindM ma retM = ma; 

  assoc_law : forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
                    bindM (bindM ma f) g = bindM ma (fun x => bindM (f x) g)
}.


Theorem Option_is_a_Monad : Monad.
Proof.
apply mk_monad with (M := option) (bindM := @bind) (retM := @ret).
  - intros; simpl; auto.
  - intros; destruct ma; simpl; auto.
  - intros; destruct ma; simpl; auto.
Qed.
