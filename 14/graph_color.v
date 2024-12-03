Require Import Coq.Lists.List.
Import ListNotations.

Structure Graph := mk_Graph {
V : Type;
E : V -> V -> bool;
edge_symmetry : forall u v, (E u v) = true -> (E v u) = true }.

Definition has_edge {G : Graph} (u v : V G) : bool :=
  if (E G u v) then true else false.

Definition is_triangle {G : Graph}  (a b c : V G) : bool :=
  has_edge a b && has_edge b c && has_edge c a.

Fixpoint has_triangle {G : Graph} (vertices : list (V G)) : bool :=
  match vertices with
  | [] => false
  | x :: xs => 
    existsb (fun y => existsb (fun z => is_triangle x y z) xs) xs || has_triangle xs
  end.

Inductive Vertex2 := a | b | c.

Definition example_edges2 (u v : Vertex2) : bool :=
  match u, v with
  | a, b | b, a => true
  | b, c | c, b => true
  | a, c | c, a => true
  | _, _ => false
  end.

Lemma example_edge_symmetry2 : forall u v, (example_edges2 u v) = true -> (example_edges2 v u = true).
Proof.
  intros u v H. destruct u, v; simpl in H; auto.
Qed.

Definition example_graph2 : Graph :=
  mk_Graph Vertex2 example_edges2 example_edge_symmetry2.

Inductive Color := Red | Green | Blue.

Definition has_different_color (color1 color2 : Color) : bool :=
  match color1, color2 with
  | Red, Green | Red, Blue | Green, Red | Green, Blue | Blue, Red | Blue, Green => true
  | _, _ => false
  end.

Fixpoint is_valid_coloring {G : Graph} (vertices : list (V G)) (coloring : V G -> Color) : bool :=
  match vertices with
  | [] => true
  | v :: vs =>
      forallb (fun u => if has_edge v u then has_different_color (coloring v) (coloring u) else true) vs
      && is_valid_coloring vs coloring
  end.

Definition example_coloring2 (v : Vertex2) : Color :=
  match v with
  | a => Red
  | b => Green
  | c => Blue
  end.

Compute @is_valid_coloring example_graph2 [a; b; c] example_coloring2.

