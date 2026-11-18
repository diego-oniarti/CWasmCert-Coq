From Coq Require Import ZArith.BinInt BinNat.
From CWasm Require Export bytes.
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
Require Import Coq.NArith.NArith.
Require Import Coq.Init.Datatypes.

Set Bullet Behavior "Strict Subproofs".

(* No idea how this works but it lets me use == on N *)
Lemma NeqbP : Equality.axiom N.eqb.
Proof. move=> x y. case: N.eqb_spec; constructor => //. Qed.
Canonical N_eqId := EqType N (EqMixin NeqbP).

Definition color : Type := option N.

Record pointer : Type := {
  ptr_addr     : N     ; (* should be u32 *)
  ptr_col      : color ;
  ptr_freeable : bool  ;
}.

Definition dummy_pointer := {|
  ptr_addr     := 0     ;
  ptr_col      := None  ;
  ptr_freeable := false ;
|}.


Definition is_null p := (ptr_col p  == None).
Lemma is_null_dummy p : p = dummy_pointer -> is_null p.
Proof. intros. subst. auto. Qed.

Definition upd_pointer_addr p a := {|
  ptr_addr     := a ; ptr_col      := p.(ptr_col);
  ptr_freeable := p.(ptr_freeable);
|}.

Definition new_pointer a c f := {|
  ptr_addr     := a ;
  ptr_col      := c ;
  ptr_freeable := f ;
|}.

Definition same_origin p1 p2 :=
  ptr_col p1 = ptr_col p2.
Definition same_origin_b p1 p2 :=
  ptr_col p1 == ptr_col p2.

Lemma same_origin_refl p : same_origin_b p p.
Proof. unfold same_origin_b; by apply/eqP. Qed.

Lemma same_origin_sym p1 p2 : same_origin_b p1 p2 = same_origin_b p2 p1.
Proof. unfold same_origin_b; by rewrite eq_sym. Qed.

Lemma same_origin_trans p1 p2 p3 : 
  same_origin_b p1 p2 -> same_origin_b p2 p3 -> same_origin_b p1 p3.
Proof.
  unfold same_origin_b. 
  move/eqP=> H1; move/eqP=> H2. 
  by rewrite H1 H2 eqxx. 
Qed.

Definition pointer_to_pair p := (ptr_addr p, ptr_col p, ptr_freeable p).

Lemma pointer_inj : forall p1 p2, pointer_to_pair p1 = pointer_to_pair p2 -> p1 = p2.
Proof. by case=> a1 c1 f1 [a2 c2 f2] [] /= -> -> ->. Qed.

Definition pointer_eqMixin := InjEqMixin pointer_inj.
Canonical pointer_eqType := EqType pointer pointer_eqMixin.

Definition pointer_ltb p1 p2 :=
  N.ltb (ptr_addr p1) (ptr_addr p2).
Definition pointer_leb p1 p2 :=
  N.leb (ptr_addr p1) (ptr_addr p2).
Definition pointer_gtb p1 p2 :=
  N.ltb (ptr_addr p2) (ptr_addr p1).
Definition pointer_geb p1 p2 :=
  N.leb (ptr_addr p2) (ptr_addr p1).

(** Could steal this Definition handle_add h (n: Z) := if (Z.of_N (offset h) + n >=? 0)%Z then Some {| base := h.(base) ; offset := Z.to_N (Z.of_N (offset h) + n)%Z ; bound := h.(bound) ; valid := h.(valid) ; id := h.(id) |} else None. *)

Definition pointer_arith (p : pointer) (delta : Z) : option pointer :=
  let new_addr := (Z.of_N p.(ptr_addr) + delta)%Z in
  if (0 <=? new_addr)%Z then
    Some {|
      ptr_addr     := Z.to_N new_addr  ;
      ptr_col      := p.(ptr_col)      ;
      ptr_freeable := p.(ptr_freeable) ;
    |}
  else None.

Class PointerBytes : Type := {
  pointer_size : N;
  serialise_pointer : pointer -> bytes;
  pointer_of_bytes : bytes -> pointer;

    size_is_not_zero : 0 < nat_of_bin pointer_size;
    length_serialise : forall h, length (serialise_pointer h) = pointer_size;
    pointer_of_serialise : forall h, pointer_of_bytes (serialise_pointer h) = h;
    serialise_pointer_of : forall bs, serialise_pointer (pointer_of_bytes bs) = bs
}.
