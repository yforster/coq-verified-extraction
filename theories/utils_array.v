Require Import ssreflect.

Require Import ZArith Array.PArray List Floats Lia.
Import ListNotations.

Require Import Malfunction.Malfunction Malfunction.SemanticsSpec.
From Coq Require Import Uint63.

Fixpoint Array_of_List' {A} count (l : list A) (a : array A) :=
  match l with
  | [] => a
  | x :: l => Array_of_List' (S count) l (PArray.set a (int_of_nat count) x)
  end.

Definition Array_of_list {A} (def : A) (l : list A) :=
  Array_of_List' 0 l (PArray.make (int_of_nat (List.length l)) def).

Definition Array_init {A} (size : int) f :=
  let g := fun x => (f (int_of_nat x)) in
  @Array_of_list A (g 0) (map g (seq 0 (Z.to_nat (Int63.to_Z size)))).


Lemma Array_of_list'_get {A} s l (a : array A) i :
  i < s + List.length l ->
  (s + List.length l < Z.to_nat Int63.wB) ->
  s + List.length l <= int_to_nat (PArray.length a) ->
  PArray.get (Array_of_List' s l a) (int_of_nat i) =
    if (i <? s)%nat then
      a.[int_of_nat i]
    else
      nth (i - s) l (a.[int_of_nat i]).
Proof.
  intros Hl Hs Ha.
  induction l as [ | ? ? IHl] in s, i, a, Hl, Hs, Ha |- *.
  - destruct (Nat.ltb_spec i s).
    + cbn. reflexivity.
    + cbn. destruct (i - s); reflexivity.
  - rewrite IHl. 
    + cbn in Hl. lia.
    + cbn [Datatypes.length] in Hs. lia.
    + rewrite PArray.length_set. cbn [Datatypes.length] in Ha. lia.
    + fold (int_of_nat s). destruct (Nat.ltb_spec i s) as [H | H].
      * destruct (Nat.ltb_spec i (S s)) as [H0 | H0]; try lia.
        rewrite get_set_other.
        -- intros E. eapply (f_equal int_to_nat) in E.
           rewrite !int_to_of_nat in E.
           all:assert (H1 : s < Z.to_nat Int63.wB) by lia.
           all:eapply inj_lt in H1.
           all:rewrite Z2Nat.id in H1. all:lia. 
        -- reflexivity.
      * destruct (Nat.ltb_spec i (S s)); try lia.
        -- assert (i = s) by lia. subst.
           rewrite get_set_same.
           ++ eapply Int63.ltb_spec.
              1:eapply Z2Nat.inj_lt.
              1:eapply Int63.to_Z_bounded.
              1:eapply Int63.to_Z_bounded. 
              fold (int_to_nat (int_of_nat s)).
              rewrite int_to_of_nat. 1:lia.
              unfold int_to_nat in Ha. lia.
           ++ cbn. destruct s. 1:reflexivity.
              rewrite Nat.sub_diag. reflexivity.
        -- cbn. destruct (i - s) as [ | n] eqn:E.
           ++ lia.
           ++ assert (H1 : i - S s = n) by lia. rewrite H1.
              eapply nth_indep.
              cbn in Hl. lia.
Qed.

Lemma Array_of_list_get {A} (a : A) l i :
  (i < Z.to_nat Int63.wB) ->
  (List.length l < Z.to_nat Int63.wB) ->
  List.length l <= int_to_nat max_length ->
  i < List.length l ->
  (Array_of_list a l).[int_of_nat i] = nth i l a.

Proof.
  unfold Array_of_list. intros Hs Hl1 Hl Hi.
  rewrite Array_of_list'_get.
  + assumption.
  + lia. 
  + rewrite PArray.length_make.
    fold (int_of_nat (Datatypes.length l)).
    destruct (Int63.lebP (int_of_nat (Datatypes.length l)) max_length) as [ | n ].
    * rewrite int_to_of_nat.
      1:eapply Z2Nat.inj_lt. all: lia. 
    * destruct n.
      epose proof (int_to_of_nat (Datatypes.length l) _) as H.
      eapply Z2Nat.inj_le.
      1:eapply Int63.to_Z_bounded.
      1:eapply Int63.to_Z_bounded.
      unfold int_to_nat in H. rewrite H.
      unfold int_to_nat in Hl. exact Hl.
      Unshelve. all:lia.
  + destruct (Nat.ltb_spec i 0); try lia.
    rewrite Nat.sub_0_r.
    eapply nth_indep. lia.
Qed.


Lemma Array_of_list_get_again {A : Set} i s (l : list A) a :
  i >= s + List.length l ->
  s + List.length l < Z.to_nat Int63.wB ->
  i < Z.to_nat Int63.wB ->
  (Array_of_List' s l a).[int_of_nat i]  = PArray.get a (int_of_nat i).
Proof.
  induction l as [ | ? l IHl ] in s, i, a |- *; intros Hi Hs Ha.
  - cbn. reflexivity.
  - cbn. rewrite IHl. 
    + cbn in Hi. lia.
    + cbn [List.length] in Hs. lia. 
    + cbn [List.length] in Hs. lia.
    + rewrite get_set_other. 2:reflexivity.
      fold (int_of_nat s).
      intros H. eapply (f_equal int_to_nat) in H.
      rewrite !int_to_of_nat in H.
      * eapply inj_lt in Hs.
        rewrite Z2Nat.id in Hs. 1:cbn; lia.
        rewrite <- Hs.
        eapply inj_lt. cbn. lia.
      * eapply inj_lt in Ha.
        rewrite Z2Nat.id in Ha. 1:cbn; lia.
        lia.
      * subst. cbn in Hi. lia.
Qed.


Lemma Array_of_list_S A default n a (l:list A) : 
  n < Datatypes.length l ->
  S (Datatypes.length l) <= int_to_nat max_length ->
  (Array_of_list default (a :: l)).[int_of_nat (S n)] = 
  (Array_of_list default l).[int_of_nat n].
Proof.
  intros. 
  repeat rewrite Array_of_list_get; cbn in *; try lia; eauto.
Qed.

Lemma Array_of_list'_length A k (l:list A) a :
  PArray.length (Array_of_List' k l a) =
  PArray.length a.
Proof. 
  revert k a. induction l; [reflexivity|].
  intros; cbn. rewrite IHl. now rewrite PArray.length_set.
Qed.

Lemma Array_of_list_length A default (l:list A) :
  Datatypes.length l < int_to_nat max_length -> 
  int_to_nat (PArray.length (Array_of_list default l)) =
  List.length l.
Proof.
  unfold Array_of_list. rewrite Array_of_list'_length.
  rewrite PArray.length_make. intro H. 
  assert (Hl: (int_of_nat (Datatypes.length l) ≤? max_length)%uint63 = true).
  { apply leb_spec. rewrite Int63.of_Z_spec. rewrite Z.mod_small; [cbn in *; lia |].
    cbn in *; lia. }
  rewrite Hl. apply int_to_of_nat. cbn in *; lia. 
Qed.