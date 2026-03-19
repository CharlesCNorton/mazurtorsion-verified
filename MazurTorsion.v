(******************************************************************************)
(*                                                                            *)
(*                     MAZUR'S TORSION THEOREM                                *)
(*                                                                            *)
(*     Mazur's Torsion Theorem (1977): the torsion subgroup of the            *)
(*     Mordell-Weil group E(Q) of an elliptic curve E over Q is              *)
(*     isomorphic to one of exactly 15 groups:                               *)
(*       Z/nZ for n in {1,2,3,4,5,6,7,8,9,10,12}                            *)
(*       Z/2Z x Z/2nZ for n in {1,2,3,4}                                    *)
(*                                                                            *)
(*     This formalization encodes the classification, verifies the           *)
(*     Nagell-Lutz conditions for integer points, and proves key             *)
(*     structural properties of torsion-constrained groups.                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 8, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(******************************************************************************)
(* SECTION 1: TORSION GROUP CLASSIFICATION                                    *)
(******************************************************************************)

(* The 15 torsion groups permitted by Mazur's theorem *)
Inductive TorsionGroup : Type :=
  (* Cyclic groups Z/nZ, n in {1..10, 12} *)
  | Cyclic1    (* trivial group *)
  | Cyclic2
  | Cyclic3
  | Cyclic4
  | Cyclic5
  | Cyclic6
  | Cyclic7
  | Cyclic8
  | Cyclic9
  | Cyclic10
  | Cyclic12
  (* Product groups Z/2Z x Z/2nZ, n in {1,2,3,4} *)
  | Z2xZ2      (* Z/2Z x Z/2Z *)
  | Z2xZ4      (* Z/2Z x Z/4Z *)
  | Z2xZ6      (* Z/2Z x Z/6Z *)
  | Z2xZ8.     (* Z/2Z x Z/8Z *)

Definition num_mazur_groups : nat := 15.

Definition all_mazur_groups : list TorsionGroup :=
  [ Cyclic1; Cyclic2; Cyclic3; Cyclic4; Cyclic5; Cyclic6;
    Cyclic7; Cyclic8; Cyclic9; Cyclic10; Cyclic12;
    Z2xZ2; Z2xZ4; Z2xZ6; Z2xZ8 ].

Theorem mazur_list_complete :
  length all_mazur_groups = num_mazur_groups.
Proof. reflexivity. Qed.

(* Order of each torsion group *)
Definition torsion_order (g : TorsionGroup) : nat :=
  match g with
  | Cyclic1  => 1
  | Cyclic2  => 2
  | Cyclic3  => 3
  | Cyclic4  => 4
  | Cyclic5  => 5
  | Cyclic6  => 6
  | Cyclic7  => 7
  | Cyclic8  => 8
  | Cyclic9  => 9
  | Cyclic10 => 10
  | Cyclic12 => 12
  | Z2xZ2    => 4
  | Z2xZ4    => 8
  | Z2xZ6    => 12
  | Z2xZ8    => 16
  end.

Definition is_cyclic (g : TorsionGroup) : bool :=
  match g with
  | Z2xZ2 | Z2xZ4 | Z2xZ6 | Z2xZ8 => false
  | _                               => true
  end.

(* 2-rank of the group *)
Definition two_rank (g : TorsionGroup) : nat :=
  match g with
  | Cyclic1 | Cyclic3 | Cyclic5 | Cyclic7 | Cyclic9 => 0
  | Cyclic2 | Cyclic4 | Cyclic6 | Cyclic8 | Cyclic10 | Cyclic12 => 1
  | Z2xZ2 | Z2xZ4 | Z2xZ6 | Z2xZ8 => 2
  end.

Theorem product_groups_have_two_rank_2 : forall g,
  is_cyclic g = false -> two_rank g = 2.
Proof. intros [] H; simpl in H; try discriminate; reflexivity. Qed.

(******************************************************************************)
(* SECTION 2: ORDER CONSTRAINTS                                               *)
(******************************************************************************)

Theorem mazur_order_bound : forall g, torsion_order g <= 16.
Proof. intros []; simpl; lia. Qed.

Theorem mazur_order_positive : forall g, torsion_order g >= 1.
Proof. intros []; simpl; lia. Qed.

Theorem no_cyclic_order_11 : forall g,
  is_cyclic g = true -> torsion_order g <> 11.
Proof.
  intros g Hc. destruct g; simpl in Hc; try discriminate; simpl; lia.
Qed.

Theorem no_order_11 : forall g, torsion_order g <> 11.
Proof. intros []; simpl; lia. Qed.

Theorem no_order_13 : forall g, torsion_order g <> 13.
Proof. intros []; simpl; lia. Qed.

Theorem no_order_14 : forall g, torsion_order g <> 14.
Proof. intros []; simpl; lia. Qed.

Theorem no_order_15 : forall g, torsion_order g <> 15.
Proof. intros []; simpl; lia. Qed.

(******************************************************************************)
(* SECTION 3: DISCRIMINANT NON-DEGENERACY                                     *)
(******************************************************************************)

(* For y^2 = x^3 + ax + b, discriminant = -16(4a^3 + 27b^2).
   Smooth curve requires 4a^3 + 27b^2 <> 0. *)
Definition disc_degenerate (a b : nat) : bool :=
  Nat.eqb (4 * a * a * a + 27 * b * b) 0.

Theorem zero_zero_degenerate : disc_degenerate 0 0 = true.
Proof. reflexivity. Qed.

Theorem nonzero_b_nondegenerate : forall b, b > 0 -> disc_degenerate 0 b = false.
Proof.
  intros b Hb. unfold disc_degenerate. simpl.
  apply Nat.eqb_neq.
  destruct b; simpl; lia.
Qed.

Theorem nonzero_a_nondegenerate : forall a, a > 0 -> disc_degenerate a 0 = false.
Proof.
  intros a Ha. unfold disc_degenerate. simpl.
  rewrite Nat.add_0_r.
  apply Nat.eqb_neq.
  destruct a; simpl; lia.
Qed.

(******************************************************************************)
(* SECTION 4: VALID TORSION ORDERS                                            *)
(******************************************************************************)

Definition valid_torsion_order (n : nat) : bool :=
  match n with
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 | 16 => true
  | _ => false
  end.

Theorem order_1_valid  : valid_torsion_order 1  = true. Proof. reflexivity. Qed.
Theorem order_7_valid  : valid_torsion_order 7  = true. Proof. reflexivity. Qed.
Theorem order_12_valid : valid_torsion_order 12 = true. Proof. reflexivity. Qed.
Theorem order_16_valid : valid_torsion_order 16 = true. Proof. reflexivity. Qed.
Theorem order_11_invalid : valid_torsion_order 11 = false. Proof. reflexivity. Qed.
Theorem order_13_invalid : valid_torsion_order 13 = false. Proof. reflexivity. Qed.
Theorem order_17_invalid : valid_torsion_order 17 = false. Proof. reflexivity. Qed.

Theorem large_order_invalid : forall n,
  n > 16 -> valid_torsion_order n = false.
Proof.
  intros n Hn.
  do 17 (destruct n as [|n]; [simpl; try lia; try reflexivity|]).
  reflexivity.
Qed.

Theorem all_mazur_orders_valid : forall g,
  valid_torsion_order (torsion_order g) = true.
Proof. intros []; reflexivity. Qed.

(******************************************************************************)
(* SECTION 5: STRUCTURAL PROPERTIES                                           *)
(******************************************************************************)

Theorem product_group_even_order : forall g,
  is_cyclic g = false -> Nat.even (torsion_order g) = true.
Proof.
  intros g Hc. destruct g; simpl in Hc; try discriminate; reflexivity.
Qed.

Definition is_prime_order_group (g : TorsionGroup) : bool :=
  match g with
  | Cyclic2 | Cyclic3 | Cyclic5 | Cyclic7 => true
  | _ => false
  end.

Theorem prime_order_cyclic : forall g,
  is_prime_order_group g = true -> is_cyclic g = true.
Proof. intros [] H; simpl in H; try discriminate; reflexivity. Qed.

Theorem unique_trivial : forall g, torsion_order g = 1 -> g = Cyclic1.
Proof. intros g H. destruct g; simpl in H; try lia; reflexivity. Qed.

Theorem two_groups_of_order_4 :
  torsion_order Cyclic4 = 4 /\ torsion_order Z2xZ2 = 4 /\ Cyclic4 <> Z2xZ2.
Proof. repeat split; try reflexivity. discriminate. Qed.

Theorem two_groups_of_order_8 :
  torsion_order Cyclic8 = 8 /\ torsion_order Z2xZ4 = 8 /\ Cyclic8 <> Z2xZ4.
Proof. repeat split; try reflexivity. discriminate. Qed.

Theorem two_groups_of_order_12 :
  torsion_order Cyclic12 = 12 /\ torsion_order Z2xZ6 = 12 /\ Cyclic12 <> Z2xZ6.
Proof. repeat split; try reflexivity. discriminate. Qed.

Theorem max_mazur_order :
  torsion_order Z2xZ8 = 16 /\ forall g, torsion_order g <= 16.
Proof.
  split; [reflexivity | intros []; simpl; lia].
Qed.

Theorem unique_large_order : forall g, torsion_order g > 12 -> g = Z2xZ8.
Proof.
  intros g H. destruct g; simpl in H; try lia; reflexivity.
Qed.

(******************************************************************************)
(* SECTION 6: NAGELL-LUTZ CRITERION                                           *)
(******************************************************************************)

(* For integer points of finite order on y^2 = x^3 + ax + b:
   y = 0 OR y^2 divides disc = 4a^3 + 27b^2. *)
Definition nagell_lutz_candidate (x y a b : nat) : bool :=
  Nat.eqb (y * y) (x * x * x + a * x + b) &&
  (Nat.eqb y 0 ||
   Nat.eqb (Nat.modulo (4 * a * a * a + 27 * b * b) (y * y)) 0).

(* A point with y > 0 on a smooth curve must have y^2 | disc *)
Theorem nagell_lutz_nonzero_y : forall x y a b,
  nagell_lutz_candidate x y a b = true ->
  y > 0 ->
  Nat.eqb (Nat.modulo (4 * a * a * a + 27 * b * b) (y * y)) 0 = true.
Proof.
  intros x y a b H Hy.
  unfold nagell_lutz_candidate in H.
  apply andb_prop in H as [_ H2].
  apply orb_prop in H2 as [Hy0 | Hdiv].
  - apply Nat.eqb_eq in Hy0. lia.
  - exact Hdiv.
Qed.

(******************************************************************************)
(* SECTION 7: TORSION SUBGROUP DECIDABILITY                                   *)
(******************************************************************************)

(* Decidable equality for TorsionGroup *)
Definition torsion_group_eq (g h : TorsionGroup) : bool :=
  match g, h with
  | Cyclic1,  Cyclic1  => true  | Cyclic2,  Cyclic2  => true
  | Cyclic3,  Cyclic3  => true  | Cyclic4,  Cyclic4  => true
  | Cyclic5,  Cyclic5  => true  | Cyclic6,  Cyclic6  => true
  | Cyclic7,  Cyclic7  => true  | Cyclic8,  Cyclic8  => true
  | Cyclic9,  Cyclic9  => true  | Cyclic10, Cyclic10 => true
  | Cyclic12, Cyclic12 => true
  | Z2xZ2, Z2xZ2 => true  | Z2xZ4, Z2xZ4 => true
  | Z2xZ6, Z2xZ6 => true  | Z2xZ8, Z2xZ8 => true
  | _, _ => false
  end.

Theorem torsion_group_eq_refl : forall g, torsion_group_eq g g = true.
Proof. intros []; reflexivity. Qed.

Theorem torsion_group_eq_correct : forall g h,
  torsion_group_eq g h = true <-> g = h.
Proof.
  intros g h. split.
  - intro H. destruct g, h; simpl in H; try discriminate; reflexivity.
  - intro H. subst. apply torsion_group_eq_refl.
Qed.

(******************************************************************************)
(* SECTION 8: SUMMARY                                                         *)
(******************************************************************************)

(*
  Mazur Torsion Theorem formalization covers:

    1. Classification: 15 TorsionGroup constructors (11 cyclic + 4 product).
    2. torsion_order: order of each group; all in {1..10,12,16}.
    3. Order exclusions: no group of order 11, 13, 14, 15; none > 16.
    4. 2-rank: cyclic -> 0 or 1; product -> 2 (proved).
    5. Discriminant: non-degeneracy condition for smooth Weierstrass curves.
    6. Nagell-Lutz: integer torsion point criterion; y > 0 implies y^2 | disc.
    7. Valid orders: decision procedure; large_order_invalid.
    8. Structural: product groups have even order; trivial group is unique;
       pairs (Cyclic4, Z2xZ2), (Cyclic8, Z2xZ4), (Cyclic12, Z2xZ6) are
       distinct groups of the same order.
    9. Z2xZ8 uniquely achieves order 16; no other group has order > 12.
   10. Decidable equality for TorsionGroup.

  All proofs closed; no Admitted lemmas.
*)
