Require Import List.
Import ListNotations.

Inductive Typ : Set :=
  | At : nat -> Typ
  | Top : Typ
  | Imp : Typ -> Typ -> Typ
  | Cnj : Typ -> Typ -> Typ.

Inductive Trm : Set :=
  | top : Trm
  | hyp : nat -> Trm
  | lam : Typ -> Trm -> Trm
  | app : Trm -> Trm -> Trm
  | cnj : Trm -> Trm -> Trm
  | proj_1 : Trm -> Trm
  | proj_2 : Trm -> Trm.

Definition Cntxt := list Typ.

Inductive Tyty : Cntxt -> Trm -> Typ -> Prop :=
  | STT_top : forall Γ, Tyty Γ top Top
  | STT_hypO : forall Γ A, Tyty (A :: Γ) (hyp 0) A
  | STT_hypS :
      forall Γ A B i,
      Tyty Γ (hyp i) A -> Tyty (B :: Γ) (hyp (S i)) A
  | STT_lam :
      forall Γ t A B,
      Tyty (A :: Γ) t B -> Tyty Γ (lam A t) (Imp A B)
  | STT_app :
      forall Γ t s A B,
      Tyty Γ t (Imp A B) -> Tyty Γ s A -> Tyty Γ (app t s) B
  | STT_cnj :
      forall Γ t s A B,
      Tyty Γ t A -> Tyty Γ s B -> Tyty Γ (cnj t s) (Cnj A B)
  | STT_proj1 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_1 t) A
  | STT_proj2 :
      forall Γ t A B,
      Tyty Γ t (Cnj A B) -> Tyty Γ (proj_2 t) B.

Notation "Γ '⊢' t '[:]' A" := (Tyty Γ t A) (at level 70, no associativity) : type_scope.

Notation "'⊢' t '[:]' A" := (Tyty nil t A) (at level 70, no associativity) : type_scope.

Notation "A ⊃ B" := (Imp A B) (at level 70, right associativity) :
type_scope.

Class Category := cat_mk {
  Obj : Type;
  uHom := Type : Type;
  Hom : Obj -> Obj -> uHom;
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;
}.

Notation "x → y" := (Hom x y) (at level 70, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 71, left associativity) :
type_scope.

Definition Obj_STT := Typ.

Definition Hom_STT (x y : Obj_STT) := { t : Trm | ⊢ t [:] (x ⊃ y)}.

Definition Id_STT_term (x : Obj_STT) := (lam x (hyp 0)).

Lemma Id_STT_type (x : Obj_STT) : ⊢ (Id_STT_term x) [:] (x ⊃ x).
Proof.
unfold Id_STT_term.
apply STT_lam.
apply STT_hypO.
Defined.

Definition Id_STT (x : Typ) : {t : Trm | ⊢ t [:] (x ⊃ x)} :=
  exist (fun t => ⊢ t [:] (x ⊃ x)) (Id_STT_term x) (Id_STT_type x).

Lemma weakening_weak : forall Γ Δ t A,
  Γ ⊢ t [:] A -> (Γ ++ Δ) ⊢ t [:] A.
Proof.
  assert (K : forall (T : Type) (l : list T) (a : T), a :: l = [a] ++ l).
  simpl; auto.
  intros Γ Δ t A H.
  induction H.
  all: try rewrite K; try rewrite <- app_assoc; try rewrite <- K.
  - apply STT_top.
  - apply STT_hypO.
  - apply STT_hypS.
    auto.
  - apply STT_lam.
    rewrite K in IHTyty.
    rewrite <- app_assoc in IHTyty.
    rewrite <- K in IHTyty.
    auto.
  - apply STT_app with (A := A).
    all: auto.
  - apply STT_cnj.
    all: auto.
  - apply STT_proj1 with (Γ := Γ ++ Δ ) (B:=B).
    auto.
 - apply STT_proj2 with (Γ := Γ ++ Δ ) (A:=A).
    auto.
Defined.

Definition Compose_STT_term {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) := lam x (app (proj1_sig f) (app (proj1_sig g) (hyp 0))).

Definition Compose_STT_type {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : ⊢ (Compose_STT_term f g) [:] (x ⊃ z).
Proof.
unfold Compose_STT_term.
apply STT_lam.
assert (Kf : ⊢ (proj1_sig f) [:] (y ⊃ z)).
 { exact (proj2_sig f). }
assert (Kg : ⊢ (proj1_sig g) [:] (x ⊃ y)).
 { exact (proj2_sig g). }
assert (Kfx : [x] ⊢ (proj1_sig f) [:] (y ⊃ z)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig f); auto. }
assert (Kgx : [x] ⊢ (proj1_sig g) [:] (x ⊃ y)).
 { apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig g); auto. }
apply STT_app with (A:=y). auto.
apply STT_app with (A:=x). auto.
apply STT_hypO.
Defined.

Definition Compose_STT {x y z : Obj_STT} (f : Hom_STT y z) (g : Hom_STT x y) : {t : Trm | ⊢ t [:] (x ⊃ z)} :=
  exist (fun t => ⊢ t [:] (x ⊃ z)) (Compose_STT_term f g) (Compose_STT_type f g).

Axiom ProofIrrelevance : forall (Γ : Cntxt) (A : Typ) (x y : { t : Trm | Γ ⊢ t [:] A}), x = y.

Instance STT_as_a_Cat : Category. 
Proof.
apply cat_mk with (Obj := Obj_STT) (Hom := Hom_STT) (Id := Id_STT) (Compose := @Compose_STT).
all: intros; unfold Compose_STT; unfold Compose_STT_term; simpl; unfold Compose_STT_type; simpl; apply ProofIrrelevance.
Defined.

Class CartClosedCat (C : Category) := CartClosedCat_mk {
  Top_obj : Obj;
  Top_mor : forall {x}, x → Top_obj;
  Prod_obj : Obj -> Obj -> Obj;
  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;
  First {x y} : (Prod_obj x y) → x;
  Second {x y} : (Prod_obj x y) → y;
  Exp_obj : Obj -> Obj -> Obj;
  Exp_app : forall {y z}, (Prod_obj (Exp_obj z y) y) → z;
  Lam : forall {x y z} (g : (Prod_obj x y) → z), x → (Exp_obj z y);

  unique_top : forall {x} (f : x → Top_obj), f = Top_mor;
  prod_ax_1 : forall {x y z} (f : x → y) (g : x → z), 
    ((First ∘ (Prod_mor f g)) = f);
  prod_ax_2 : forall {x y z} (f : x → y) (g : x → z),((Second ∘ (Prod_mor f g)) = g);
  unique_prod : forall {x y z} (f : x → y) (g : x → z) (h : x → Prod_obj y z),
    ((First ∘ h) = f) /\ ((Second ∘ h) = g) -> h = (Prod_mor f g);
  exp_ax : forall {x y z} (g : ((Prod_obj x y) → z)), 
    (Exp_app ∘ (Prod_mor (Compose (Lam g) First) (Compose (Id y) Second))) = g;
  unique_exp : forall {x y z} (h : x → Exp_obj z y),
    Lam (Exp_app ∘ (Prod_mor (Compose h First) (Compose (Id y) Second))) = h
}.

(*
Lemma pr_1 (x y z : Typ) (t s) : (⊢ t [:] (Imp x y)) -> (⊢ s [:] ( Imp x z)) -> (⊢ lam x (cnj (app (hyp 0)) (app (hyp 0) )[:] (Imp x (Cnj y z)). 
*)


Definition Prodmor_STT_term (x y z : Obj_STT) (f : {t : Trm | ⊢ t [:] (Imp x y)} ) (g : {t : Trm | ⊢ t [:] ( Imp x z)} ) := lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g)(hyp 0) )).

Lemma Prodmor_STT_type (x y z : Obj_STT) (f : {t : Trm | ⊢ t [:] (Imp x y)} ) (g : {t : Trm | ⊢ t [:] ( Imp x z)} ) : ⊢ lam x (cnj (app (proj1_sig f) (hyp 0)) (app (proj1_sig g)(hyp 0) )) [:] (Imp x (Cnj y z)).
Proof.
apply STT_lam.
apply STT_cnj.
apply STT_app with (A:=x).
apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig f).
exact (proj2_sig f).
apply STT_hypO.
apply STT_app with (A:=x).
apply weakening_weak with (Γ := nil) (Δ := [x]) (t := proj1_sig g).
exact (proj2_sig g).
apply STT_hypO.
Defined.

Definition Prodmor_STT (x y z : Obj_STT) (f : {t : Trm | ⊢ t [:] (Imp x y)} ) (g : {t : Trm | ⊢ t [:] ( Imp x z)} ) : {t : Trm | ⊢ t [:]  (Imp x (Cnj y z))} :=
  exist (fun t => ⊢ t [:] (Imp x (Cnj y z))) (Prodmor_STT_term x y z f g) (Prodmor_STT_type x y z f g).



Definition Topmor_STT_term (A : Obj_STT) := (lam A top).

Lemma Topmor_STT_type (A : Obj_STT) : ⊢ (lam A top) [:] (Imp A Top).
Proof.
intros.
apply STT_lam.
apply STT_top.
Defined.

Definition Topmor_STT (x : Typ) : {t : Trm | ⊢ t [:] (Imp x Top)} :=
  exist (fun t => ⊢ t [:] ((Imp x Top))) (Topmor_STT_term x) (Topmor_STT_type x).

Lemma First_STT_type (x y : Obj_STT) : ⊢ (lam (Cnj x y) (proj_1 (hyp 0))) [:] (Imp (Cnj x y) x).
Proof.
apply STT_lam.
apply STT_proj1 with (A:=x) (B:=y).
apply STT_hypO.
Defined.

Definition First_STT_term (x y : Obj_STT) := (lam (Cnj x y) (proj_1 (hyp 0))). 

Definition First_STT (x y : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj x y) x)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj x y) x)) (First_STT_term x y) (First_STT_type x y).

Lemma Second_STT_type (x y : Obj_STT) : ⊢ (lam (Cnj x y) (proj_2 (hyp 0))) [:] (Imp (Cnj x y) y).
Proof.
apply STT_lam.
apply STT_proj2 with (A:=x) (B:=y).
apply STT_hypO.
Defined.

Definition Second_STT_term (x y : Obj_STT) := (lam (Cnj x y) (proj_2 (hyp 0))). 

Definition Second_STT (x y : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj x y) y)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj x y) y)) (Second_STT_term x y) (Second_STT_type x y).

Lemma Expapp_STT_type (y z : Typ) : ⊢ lam (Cnj (Imp y z) y) (app (proj_1 (hyp 0)) (proj_2 (hyp 0)) ) [:] (Imp (Cnj (Imp y z) y) z).
Proof.
apply STT_lam.
assert (K0 : [Cnj (y ⊃ z) y] ⊢ (hyp 0) [:] (Cnj (y ⊃ z) y)).
apply STT_hypO.
assert (K1 : [Cnj (y ⊃ z) y] ⊢ (proj_1 (hyp 0)) [:] (y ⊃ z)).
apply STT_proj1 in K0.
auto.
assert (K2 : [Cnj (y ⊃ z) y] ⊢ (proj_2 (hyp 0)) [:] y).
apply STT_proj2 in K0.
auto.
apply STT_app with (A:=y) (B:=z).
all: auto.
Defined.

Definition Expapp_STT_term (y z : Obj_STT) := lam (Cnj (Imp y z) y) (app (proj_1 (hyp 0)) (proj_2 (hyp 0)) ). 

Definition Expapp_STT (y z : Typ) : {t : Trm | ⊢ t [:] (Imp (Cnj (Imp y z) y) z)} :=
  exist (fun t => ⊢ t [:] (Imp (Cnj (Imp y z) y) z)) (Expapp_STT_term y z) (Expapp_STT_type y z).

Lemma Lam_STT_type (x y z : Obj_STT) (g : {t : Trm | ⊢ t [:] (Imp (Cnj x y) z)}) : ⊢ (lam x (lam y (app (proj1_sig g) (cnj (hyp 1) (hyp 0))))) [:] Imp x (Imp y z).
Proof.
apply STT_lam.
apply STT_lam.
assert (K1 : ⊢ (proj1_sig g) [:] (Cnj x y ⊃ z)).
exact (proj2_sig g).
assert (K2 : [y; x] ⊢ (cnj (hyp 1) (hyp 0)) [:] (Cnj x y)).
apply STT_cnj.
apply STT_hypS.
apply STT_hypO.
apply STT_hypO.
apply STT_app with (A:=(Cnj x y)) (B:=z).
all: auto.
apply weakening_weak with (Γ:=nil) (Δ:=[y; x]).
auto.
Defined.

Definition Lam_STT_term (x y z : Obj_STT) (g : {t : Trm | ⊢ t [:] (Imp (Cnj x y) z)}) := (lam x (lam y (app (proj1_sig g) (cnj (hyp 1) (hyp 0))))). 

Definition Lam_STT (x y z : Typ) (g : {t : Trm | ⊢ t [:] (Imp (Cnj x y) z)}) : {t : Trm | ⊢ t [:] (Imp x (Imp y z))} :=
  exist (fun t => ⊢ t [:] (Imp x (Imp y z))) (Lam_STT_term x y z g) (Lam_STT_type x y z g).

Instance STT_as_a_CCC : CartClosedCat STT_as_a_Cat. 
Proof.
apply CartClosedCat_mk with (Top_obj := Top) (Top_mor := Topmor_STT) (Prod_obj := Cnj) (Prod_mor := Prodmor_STT) (Exp_obj := (fun A B => Imp B A)) (First := First_STT) (Second := Second_STT) (Exp_app := Expapp_STT) (Lam := Lam_STT).
all: intros; simpl Obj in *; simpl Hom in *;
simpl Compose in *; apply ProofIrrelevance.
Defined.

Structure VAL (C : Category) (CC : CartClosedCat C) : Type := makeVAL 
  { V :> Typ -> Obj;
    VAL_top : V Top = Top_obj;
    VAL_imp : forall {A B}, V (Imp A B) = Exp_obj (V B) (V A);
    VAL_cnj : forall {A B}, V (Cnj A B) = Prod_obj (V A) (V B);
  }.

Fixpoint VAL_Cntxt (C : Category) (CC : CartClosedCat C) (v : VAL C CC) (Γ : list Typ) := 
  match Γ with 
    | nil => Top_obj
    | A :: Γ' => Prod_obj (VAL_Cntxt C CC v Γ') (v A) 
  end.

Notation "[[ Γ ]]_ C CC v" := (VAL_Cntxt C CC v Γ) (at level 200, no associativity) :
type_scope.

Lemma Soundness_ver (C : Category) (CC : CartClosedCat C) : 
forall v Γ A, (exists t, (Γ ⊢ t [:] A)) -> inhabited (Hom (VAL_Cntxt C CC v Γ) (v A)).
Proof.
  intros v Γ A H.
  elim H.
  intros. 
  induction H0.
  - apply inhabits.
  rewrite VAL_top.
  exact (Top_mor).
  - apply inhabits; simpl.
  exact (@Second C CC (VAL_Cntxt C CC v Γ) (v A) ).
  - assert (H1 : (exists t : Trm, Γ ⊢ t [:] A)). 
    { exists (hyp i). exact H0. } 
  apply IHTyty in H1.
  induction H1; apply inhabits.
  exact (Compose X (@First C CC (VAL_Cntxt C CC v Γ) (v B))).
  - assert (Inh : inhabited ((VAL_Cntxt C CC v (A :: Γ)) → v B)). 
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t. 
  rewrite VAL_imp; simpl in Inh. 
  induction Inh; apply inhabits. 
  exact (@Lam C CC (VAL_Cntxt C CC v Γ) (v A) (v B) X). 
  - assert (Inh1 : inhabited ((VAL_Cntxt C CC v Γ) → v (Imp A B))).
    { apply IHTyty1; exists t; exact H0_. } clear IHTyty1 H0_.
  assert (Inh2 : inhabited ((VAL_Cntxt C CC v Γ) → v A)).
  { apply IHTyty2; exists s; exact H0_0. } clear IHTyty2 H0_0 H t s.
  rewrite VAL_imp in Inh1.
  induction Inh1, Inh2; apply inhabits.
  assert (Y : ((VAL_Cntxt C CC v Γ) → (Prod_obj (Exp_obj (v B) (v A))) (v A ))).
  { exact (@Prod_mor C CC ((VAL_Cntxt C CC v Γ)) (Exp_obj (v B) (v A)) (v A) X X0 ). }
  assert (Z : (Prod_obj (Exp_obj (v B) (v A)) (v A)) → v B ).
  { exact (@Exp_app C CC (v A) (v B)). }
  exact (Compose Z Y).
  - assert (Inh1 : inhabited ((VAL_Cntxt C CC v Γ) → v A)).
    { apply IHTyty1; exists t; exact H0_. } clear IHTyty1 H0_.
  assert (Inh2 : inhabited ((VAL_Cntxt C CC v Γ) → v B)).
  { apply IHTyty2; exists s; exact H0_0. } clear IHTyty2 H0_0 H t s.
  induction Inh1, Inh2; apply inhabits.
  rewrite VAL_cnj.
  exact (@Prod_mor C CC (VAL_Cntxt C CC v Γ) (v A) (v B) X X0).
  - assert (Inh : inhabited ((VAL_Cntxt C CC v Γ) → v (Cnj A B))).
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t.
  induction Inh; apply inhabits.
  rewrite VAL_cnj in X.
  assert (Y : (Prod_obj (v A) (v B) ) → v A).
  { exact (@First C CC (v A) (v B)). }
  exact (Compose Y X).
  - assert (Inh : inhabited ((VAL_Cntxt C CC v Γ) → v (Cnj A B))).
    { apply IHTyty; exists t; exact H0. } clear IHTyty H0 H t.
  induction Inh; apply inhabits.
  rewrite VAL_cnj in X.
  assert (Y : (Prod_obj (v A) (v B) ) → v B).
  { exact (@Second C CC (v A) (v B)). }
  exact (Compose Y X).
Defined.

Theorem Soundness : (forall A Γ, (exists t, (Γ ⊢ t [:] A)) -> (forall (C : Category) (CC : CartClosedCat C) v, inhabited (Hom (VAL_Cntxt C CC v Γ) (v A)))).
Proof. 
assert (S : (forall (C : Category) (CC : CartClosedCat C) v Γ A, (exists t, (Γ ⊢ t [:] A)) -> inhabited (Hom (VAL_Cntxt C CC v Γ) (v A))) -> (forall A Γ, (exists t, (Γ ⊢ t [:] A)) -> (forall (C : Category) (CC : CartClosedCat C) v, inhabited (Hom (VAL_Cntxt C CC v Γ) (v A))))).
auto.
apply S.
apply Soundness_ver.
Defined. 

Fixpoint Cnj_Cntxt (Γ : list Typ) := 
  match Γ with 
    | nil => Top
    | A :: Γ' => Cnj (Cnj_Cntxt Γ') A 
  end.

Definition V_STT : VAL STT_as_a_Cat STT_as_a_CCC.
Proof.
apply (makeVAL STT_as_a_Cat STT_as_a_CCC) with (V := (fun A : Typ => A)).
all: simpl; auto.
Defined.

Lemma cntx_1 : forall Γ, VAL_Cntxt STT_as_a_Cat STT_as_a_CCC V_STT Γ = Cnj_Cntxt Γ.
Proof.
intros.
induction Γ.
simpl; auto.
simpl.
rewrite IHΓ.
auto.
Defined.

Lemma imp_cntx_1 : forall A B t, (⊢ t
     [:] (B ⊃ A)) -> [ B ] ⊢ (app t (hyp 0)) [:] A.
Proof. 
  intros A B t H.
  assert (K : [B] ⊢ t [:] (B ⊃ A)).
  apply weakening_weak with (Γ := nil) (Δ := [B]) (t := t).
  auto.
  assert (L : [B] ⊢ (hyp 0) [:] B).
  apply STT_hypO.
  apply STT_app with (A:=B) (B:=A).
  all: auto.
Defined.

Lemma val_1 : forall A, V_STT A = A.
Proof.
intros.
compute.
auto.
Defined.

Theorem Completeness : 
forall A Γ, (forall (C : Category) (CC : CartClosedCat C) v, inhabited (Hom (VAL_Cntxt C CC v Γ) (v A))) -> (exists t, ( [ Cnj_Cntxt Γ ] ⊢ t [:] A)).
Proof.
intros.
assert (K : inhabited (Hom (VAL_Cntxt STT_as_a_Cat STT_as_a_CCC V_STT Γ) (V_STT A))).
apply H.
elim K.
intros L.
simpl Obj in *; simpl Hom in *.
rewrite cntx_1 with (Γ := Γ) in L.
assert (L1 : ⊢ proj1_sig L
  [:] ((Cnj_Cntxt Γ) ⊃ V_STT A)).
exact (proj2_sig L).
assert (L2 : [ Cnj_Cntxt Γ ] ⊢ (app (proj1_sig L) (hyp 0))
     [:] (V_STT A)).
apply imp_cntx_1 with ( B := Cnj_Cntxt Γ) (A := V_STT A).
auto.
rewrite val_1 in L2. 
exists (app (proj1_sig L) (hyp 0)).
auto.
Defined.








