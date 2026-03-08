(******************************************************************************)
(*                                                                            *)
(*                 Mīšarum: Debt Remission in Old Babylonian Law              *)
(*                                                                            *)
(*     Old Babylonian mīšarum edicts: qualifying agrarian debts are           *)
(*     remitted, debt-servants released, pledged holdings restored, and       *)
(*     merchant-credit obligations preserved as explicit exceptions.          *)
(*                                                                            *)
(*     "dannum enšam ana lā ḫabālim"                                          *)
(*     "That the strong might not oppress the weak."                          *)
(*     - Old Babylonian legal prologue, c. 18th century BCE                   *)
(*                                                                            *)
(*     Author: Repository maintainer                                          *)
(*     Date: March 8, 2026                                                    *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

Require Import Bool.
Require Import List.
Require Import PeanoNat.

Import ListNotations.

Set Implicit Arguments.

Inductive DebtKind :=
| AgrarianBarley
| AgrarianSilver
| RentArrear
| TaxArrear
| MerchantLoan
| TradePartnership.

Inductive HoldingKind :=
| Field
| Orchard
| House.

Inductive ObligationStatus :=
| Enforceable
| Remitted.

Inductive BondageStatus :=
| Bound
| Released.

Inductive PledgeStatus :=
| Held
| Restored.

Inductive CollectionStatus :=
| Retained
| Refunded.

Record Obligation := {
  obligation_id : nat;
  obligation_creditor : nat;
  obligation_debtor : nat;
  obligation_kind : DebtKind;
  obligation_amount : nat;
  obligation_status : ObligationStatus
}.

Record Bondage := {
  bondage_household : nat;
  bondage_obligation : nat;
  bondage_status : BondageStatus
}.

Record Pledge := {
  pledge_holder : nat;
  pledge_debtor : nat;
  pledge_obligation : nat;
  pledge_holding_kind : HoldingKind;
  pledge_status : PledgeStatus
}.

Record Collection := {
  collection_obligation : nat;
  collection_amount : nat;
  collection_before_edict : bool;
  collection_status : CollectionStatus
}.

Record CaseState := {
  state_obligations : list Obligation;
  state_bondages : list Bondage;
  state_pledges : list Pledge;
  state_collections : list Collection
}.

Definition debt_kind_eqb (x y : DebtKind) : bool :=
  match x, y with
  | AgrarianBarley, AgrarianBarley => true
  | AgrarianSilver, AgrarianSilver => true
  | RentArrear, RentArrear => true
  | TaxArrear, TaxArrear => true
  | MerchantLoan, MerchantLoan => true
  | TradePartnership, TradePartnership => true
  | _, _ => false
  end.

Definition obligation_is_remissible_kind (k : DebtKind) : bool :=
  match k with
  | AgrarianBarley => true
  | AgrarianSilver => true
  | RentArrear => true
  | TaxArrear => true
  | MerchantLoan => false
  | TradePartnership => false
  end.

Definition obligation_is_remissible (o : Obligation) : bool :=
  match obligation_status o with
  | Enforceable => obligation_is_remissible_kind (obligation_kind o)
  | Remitted => false
  end.

Definition obligation_is_commercial_exception (o : Obligation) : bool :=
  negb (obligation_is_remissible_kind (obligation_kind o)).

Definition mark_remitted (o : Obligation) : Obligation :=
  if obligation_is_remissible o then
    {| obligation_id := obligation_id o;
       obligation_creditor := obligation_creditor o;
       obligation_debtor := obligation_debtor o;
       obligation_kind := obligation_kind o;
       obligation_amount := obligation_amount o;
       obligation_status := Remitted |}
  else o.

Definition remitted_ids (st : CaseState) : list nat :=
  map obligation_id (filter obligation_is_remissible (state_obligations st)).

Definition id_in (n : nat) (ids : list nat) : bool :=
  existsb (Nat.eqb n) ids.

Definition release_if_remitted (ids : list nat) (b : Bondage) : Bondage :=
  match bondage_status b with
  | Released => b
  | Bound =>
      if id_in (bondage_obligation b) ids then
        {| bondage_household := bondage_household b;
           bondage_obligation := bondage_obligation b;
           bondage_status := Released |}
      else b
  end.

Definition restore_if_remitted (ids : list nat) (p : Pledge) : Pledge :=
  match pledge_status p with
  | Restored => p
  | Held =>
      if id_in (pledge_obligation p) ids then
        {| pledge_holder := pledge_holder p;
           pledge_debtor := pledge_debtor p;
           pledge_obligation := pledge_obligation p;
           pledge_holding_kind := pledge_holding_kind p;
           pledge_status := Restored |}
      else p
  end.

Definition refund_if_remitted (ids : list nat) (c : Collection) : Collection :=
  match collection_status c with
  | Refunded => c
  | Retained =>
      if collection_before_edict c && id_in (collection_obligation c) ids then
        {| collection_obligation := collection_obligation c;
           collection_amount := collection_amount c;
           collection_before_edict := collection_before_edict c;
           collection_status := Refunded |}
      else c
  end.

Definition apply_misharum (st : CaseState) : CaseState :=
  let ids := remitted_ids st in
  {| state_obligations := map mark_remitted (state_obligations st);
     state_bondages := map (release_if_remitted ids) (state_bondages st);
     state_pledges := map (restore_if_remitted ids) (state_pledges st);
     state_collections := map (refund_if_remitted ids) (state_collections st) |}.

Lemma debt_kind_eqb_refl : forall k,
  debt_kind_eqb k k = true.
Proof.
  destruct k.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.


Lemma obligation_is_commercial_exception_spec : forall o,
  obligation_is_commercial_exception o = true <->
  obligation_is_remissible_kind (obligation_kind o) = false.
Proof.
  intros o.
  unfold obligation_is_commercial_exception.
  rewrite Bool.negb_true_iff.
  tauto.
Qed.

Lemma mark_remitted_status : forall o,
  obligation_status (mark_remitted o) =
  if obligation_is_remissible o then Remitted else obligation_status o.
Proof.
  intros o.
  unfold mark_remitted.
  destruct (obligation_is_remissible o).
  - reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_remits : forall o,
  obligation_is_remissible o = true ->
  obligation_status (mark_remitted o) = Remitted.
Proof.
  intros o H.
  rewrite mark_remitted_status.
  rewrite H.
  reflexivity.
Qed.

Lemma mark_remitted_preserves_commercial_exception : forall o,
  obligation_is_commercial_exception o = true ->
  mark_remitted o = o.
Proof.
  intros [oid creditor debtor kind amount status] H.
  unfold obligation_is_commercial_exception in H.
  unfold mark_remitted.
  destruct status.
  - destruct kind.
    + discriminate H.
    + discriminate H.
    + discriminate H.
    + discriminate H.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma id_in_intro : forall n ids,
  In n ids ->
  id_in n ids = true.
Proof.
  intros n ids Hin.
  unfold id_in.
  apply existsb_exists.
  exists n.
  split.
  - exact Hin.
  - apply Nat.eqb_refl.
Qed.

Lemma remitted_ids_contains : forall st o,
  In o (state_obligations st) ->
  obligation_is_remissible o = true ->
  id_in (obligation_id o) (remitted_ids st) = true.
Proof.
  intros st o Hin Hrem.
  unfold remitted_ids.
  apply id_in_intro.
  apply in_map.
  apply filter_In.
  split.
  - exact Hin.
  - exact Hrem.
Qed.

Lemma release_if_remitted_bound : forall ids b,
  bondage_status b = Bound ->
  id_in (bondage_obligation b) ids = true ->
  bondage_status (release_if_remitted ids b) = Released.
Proof.
  intros ids [household obligation status] Hbound Hid.
  simpl in *.
  subst status.
  unfold release_if_remitted.
  simpl.
  rewrite Hid.
  reflexivity.
Qed.

Lemma restore_if_remitted_held : forall ids p,
  pledge_status p = Held ->
  id_in (pledge_obligation p) ids = true ->
  pledge_status (restore_if_remitted ids p) = Restored.
Proof.
  intros ids [holder debtor obligation kind status] Hheld Hid.
  simpl in *.
  subst status.
  unfold restore_if_remitted.
  simpl.
  rewrite Hid.
  reflexivity.
Qed.

Lemma refund_if_remitted_retained : forall ids c,
  collection_status c = Retained ->
  collection_before_edict c = true ->
  id_in (collection_obligation c) ids = true ->
  collection_status (refund_if_remitted ids c) = Refunded.
Proof.
  intros ids [obligation amount before status] Hretained Hbefore Hid.
  simpl in *.
  subst status before.
  unfold refund_if_remitted.
  simpl.
  rewrite Hid.
  reflexivity.
Qed.

Theorem apply_misharum_remits_every_eligible_obligation : forall st o,
  In o (state_obligations st) ->
  obligation_is_remissible o = true ->
  In (mark_remitted o) (state_obligations (apply_misharum st)).
Proof.
  intros st o Hin _.
  unfold apply_misharum.
  simpl.
  apply in_map.
  exact Hin.
Qed.

Theorem apply_misharum_preserves_lengths : forall st,
  length (state_obligations (apply_misharum st)) = length (state_obligations st) /\
  length (state_bondages (apply_misharum st)) = length (state_bondages st) /\
  length (state_pledges (apply_misharum st)) = length (state_pledges st) /\
  length (state_collections (apply_misharum st)) = length (state_collections st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  repeat split.
  - apply map_length.
  - apply map_length.
  - apply map_length.
  - apply map_length.
Qed.

Lemma obligation_is_remissible_mark_remitted_false : forall o,
  obligation_is_remissible (mark_remitted o) = false.
Proof.
  intros [oid creditor debtor kind amount status].
  destruct status.
  - destruct kind.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_idempotent : forall o,
  mark_remitted (mark_remitted o) = mark_remitted o.
Proof.
  intros o.
  unfold mark_remitted at 1.
  rewrite obligation_is_remissible_mark_remitted_false.
  reflexivity.
Qed.

Lemma release_if_remitted_nil : forall b,
  release_if_remitted [] b = b.
Proof.
  intros [household obligation status].
  destruct status.
  - reflexivity.
  - reflexivity.
Qed.

Lemma restore_if_remitted_nil : forall p,
  restore_if_remitted [] p = p.
Proof.
  intros [holder debtor obligation kind status].
  destruct status.
  - reflexivity.
  - reflexivity.
Qed.

Lemma refund_if_remitted_nil : forall c,
  refund_if_remitted [] c = c.
Proof.
  intros [obligation amount before status].
  destruct status.
  - destruct before.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma map_mark_remitted_idempotent : forall obs,
  map mark_remitted (map mark_remitted obs) = map mark_remitted obs.
Proof.
  induction obs as [|o obs IH].
  - reflexivity.
  - simpl.
    rewrite mark_remitted_idempotent.
    rewrite IH.
    reflexivity.
Qed.

Lemma map_release_if_remitted_nil : forall ids bondages,
  map (release_if_remitted []) (map (release_if_remitted ids) bondages) =
  map (release_if_remitted ids) bondages.
Proof.
  intros ids bondages.
  induction bondages as [|b bondages IH].
  - reflexivity.
  - simpl.
    rewrite release_if_remitted_nil.
    rewrite IH.
    reflexivity.
Qed.

Lemma map_restore_if_remitted_nil : forall ids pledges,
  map (restore_if_remitted []) (map (restore_if_remitted ids) pledges) =
  map (restore_if_remitted ids) pledges.
Proof.
  intros ids pledges.
  induction pledges as [|p pledges IH].
  - reflexivity.
  - simpl.
    rewrite restore_if_remitted_nil.
    rewrite IH.
    reflexivity.
Qed.

Lemma map_refund_if_remitted_nil : forall ids collections,
  map (refund_if_remitted []) (map (refund_if_remitted ids) collections) =
  map (refund_if_remitted ids) collections.
Proof.
  intros ids collections.
  induction collections as [|c collections IH].
  - reflexivity.
  - simpl.
    rewrite refund_if_remitted_nil.
    rewrite IH.
    reflexivity.
Qed.

Lemma remitted_ids_after_marking : forall obs,
  map obligation_id (filter obligation_is_remissible (map mark_remitted obs)) = [].
Proof.
  induction obs as [|o obs IH].
  - reflexivity.
  - simpl.
    rewrite obligation_is_remissible_mark_remitted_false.
    exact IH.
Qed.

Lemma remitted_ids_after_apply_misharum : forall st,
  remitted_ids (apply_misharum st) = [].
Proof.
  intros [obs bondages pledges collections].
  unfold remitted_ids, apply_misharum.
  simpl.
  apply remitted_ids_after_marking.
Qed.

Theorem apply_misharum_preserves_commercial_exceptions : forall st o,
  In o (state_obligations st) ->
  obligation_is_commercial_exception o = true ->
  In o (state_obligations (apply_misharum st)).
Proof.
  intros st o Hin Hcommercial.
  unfold apply_misharum.
  simpl.
  rewrite <- (mark_remitted_preserves_commercial_exception o Hcommercial).
  apply in_map.
  exact Hin.
Qed.

Theorem apply_misharum_releases_attached_bondages : forall st b,
  In b (state_bondages st) ->
  In (release_if_remitted (remitted_ids st) b) (state_bondages (apply_misharum st)).
Proof.
  intros st b Hin.
  unfold apply_misharum.
  simpl.
  apply in_map.
  exact Hin.
Qed.

Theorem apply_misharum_restores_attached_pledges : forall st p,
  In p (state_pledges st) ->
  In (restore_if_remitted (remitted_ids st) p) (state_pledges (apply_misharum st)).
Proof.
  intros st p Hin.
  unfold apply_misharum.
  simpl.
  apply in_map.
  exact Hin.
Qed.

Theorem apply_misharum_refunds_attached_collections : forall st c,
  In c (state_collections st) ->
  In (refund_if_remitted (remitted_ids st) c) (state_collections (apply_misharum st)).
Proof.
  intros st c Hin.
  unfold apply_misharum.
  simpl.
  apply in_map.
  exact Hin.
Qed.

Theorem apply_misharum_idempotent : forall st,
  apply_misharum (apply_misharum st) = apply_misharum st.
Proof.
  intros [obs bondages pledges collections].
  set (ids :=
    remitted_ids
      {| state_obligations := obs;
         state_bondages := bondages;
         state_pledges := pledges;
         state_collections := collections |}).
  change (
    apply_misharum
      {| state_obligations := map mark_remitted obs;
         state_bondages := map (release_if_remitted ids) bondages;
         state_pledges := map (restore_if_remitted ids) pledges;
         state_collections := map (refund_if_remitted ids) collections |} =
    {| state_obligations := map mark_remitted obs;
       state_bondages := map (release_if_remitted ids) bondages;
       state_pledges := map (restore_if_remitted ids) pledges;
       state_collections := map (refund_if_remitted ids) collections |}).
  unfold apply_misharum.
  simpl.
  assert
    (Hids :
      remitted_ids
        {| state_obligations := map mark_remitted obs;
           state_bondages := map (release_if_remitted ids) bondages;
           state_pledges := map (restore_if_remitted ids) pledges;
           state_collections := map (refund_if_remitted ids) collections |} = []).
  {
    subst ids.
    change
      (remitted_ids
         (apply_misharum
            {| state_obligations := obs;
               state_bondages := bondages;
               state_pledges := pledges;
               state_collections := collections |}) = []).
    apply remitted_ids_after_apply_misharum.
  }
  rewrite Hids.
  simpl.
  f_equal.
  - apply map_mark_remitted_idempotent.
  - apply map_release_if_remitted_nil.
  - apply map_restore_if_remitted_nil.
  - apply map_refund_if_remitted_nil.
Qed.

Lemma mark_remitted_preserves_id : forall o,
  obligation_id (mark_remitted o) = obligation_id o.
Proof.
  intros [oid creditor debtor kind amount status].
  unfold mark_remitted.
  destruct status.
  - destruct kind.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_preserves_creditor : forall o,
  obligation_creditor (mark_remitted o) = obligation_creditor o.
Proof.
  intros [oid creditor debtor kind amount status].
  unfold mark_remitted.
  destruct status.
  - destruct kind.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_preserves_debtor : forall o,
  obligation_debtor (mark_remitted o) = obligation_debtor o.
Proof.
  intros [oid creditor debtor kind amount status].
  unfold mark_remitted.
  destruct status.
  - destruct kind.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_preserves_kind : forall o,
  obligation_kind (mark_remitted o) = obligation_kind o.
Proof.
  intros [oid creditor debtor kind amount status].
  unfold mark_remitted.
  destruct status.
  - destruct kind.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_preserves_amount : forall o,
  obligation_amount (mark_remitted o) = obligation_amount o.
Proof.
  intros [oid creditor debtor kind amount status].
  unfold mark_remitted.
  destruct status.
  - destruct kind.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_status_exact : forall o,
  obligation_status (mark_remitted o) = Remitted <->
  obligation_status o = Remitted \/ obligation_is_remissible o = true.
Proof.
  intros [oid creditor debtor kind amount status].
  destruct status.
  - destruct kind.
    + split; intro H.
      * right. reflexivity.
      * reflexivity.
    + split; intro H.
      * right. reflexivity.
      * reflexivity.
    + split; intro H.
      * right. reflexivity.
      * reflexivity.
    + split; intro H.
      * right. reflexivity.
      * reflexivity.
    + split; intro H.
      * discriminate H.
      * destruct H as [H | H].
        -- discriminate H.
        -- discriminate H.
    + split; intro H.
      * discriminate H.
      * destruct H as [H | H].
        -- discriminate H.
        -- discriminate H.
  - split; intro H.
    + left. reflexivity.
    + reflexivity.
Qed.

Lemma release_if_remitted_status_exact : forall ids b,
  bondage_status (release_if_remitted ids b) = Released <->
  bondage_status b = Released \/
  (bondage_status b = Bound /\ id_in (bondage_obligation b) ids = true).
Proof.
  intros ids [household obligation status].
  destruct status.
  - split; intro H.
    + right.
      split.
      * reflexivity.
      * unfold release_if_remitted in H.
        simpl in H.
        destruct (id_in obligation ids) eqn:Hid.
        -- exact Hid.
        -- discriminate H.
    + destruct H as [H | [H Hid]].
      * discriminate H.
      * subst.
        unfold release_if_remitted.
        simpl.
        simpl in Hid.
        rewrite Hid.
        reflexivity.
  - split; intro H.
    + left. reflexivity.
    + reflexivity.
Qed.

Lemma restore_if_remitted_status_exact : forall ids p,
  pledge_status (restore_if_remitted ids p) = Restored <->
  pledge_status p = Restored \/
  (pledge_status p = Held /\ id_in (pledge_obligation p) ids = true).
Proof.
  intros ids [holder debtor obligation kind status].
  destruct status.
  - split; intro H.
    + right.
      split.
      * reflexivity.
      * unfold restore_if_remitted in H.
        simpl in H.
        destruct (id_in obligation ids) eqn:Hid.
        -- exact Hid.
        -- discriminate H.
    + destruct H as [H | [H Hid]].
      * discriminate H.
      * subst.
        unfold restore_if_remitted.
        simpl.
        simpl in Hid.
        rewrite Hid.
        reflexivity.
  - split; intro H.
    + left. reflexivity.
    + reflexivity.
Qed.

Lemma refund_if_remitted_status_exact : forall ids c,
  collection_status (refund_if_remitted ids c) = Refunded <->
  collection_status c = Refunded \/
  (collection_status c = Retained /\
   collection_before_edict c = true /\
   id_in (collection_obligation c) ids = true).
Proof.
  intros ids [obligation amount before status].
  destruct status.
  - destruct before.
    + split; intro H.
      * right.
        split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ unfold refund_if_remitted in H.
              simpl in H.
              destruct (id_in obligation ids) eqn:Hid.
              ** exact Hid.
              ** discriminate H.
      * destruct H as [H | [Hstatus [Hbefore Hid]]].
        -- discriminate H.
        -- subst.
           unfold refund_if_remitted.
           simpl.
           simpl in Hid.
           rewrite Hid.
           reflexivity.
    + split; intro H.
      * discriminate H.
      * destruct H as [H | [Hstatus [Hbefore Hid]]].
        -- discriminate H.
        -- discriminate Hbefore.
  - split; intro H.
    + left. reflexivity.
    + reflexivity.
Qed.

Lemma obligations_all_nonremissible_after_marking : forall obs,
  Forall (fun o => obligation_is_remissible o = false) (map mark_remitted obs).
Proof.
  induction obs as [|o obs IH].
  - constructor.
  - simpl.
    constructor.
    + apply obligation_is_remissible_mark_remitted_false.
    + exact IH.
Qed.

Theorem apply_misharum_exhausts_remissible_obligations : forall st,
  Forall (fun o => obligation_is_remissible o = false)
    (state_obligations (apply_misharum st)).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  apply obligations_all_nonremissible_after_marking.
Qed.

Theorem apply_misharum_preserves_obligation_ids : forall st,
  map obligation_id (state_obligations (apply_misharum st)) =
  map obligation_id (state_obligations st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  induction (state_obligations st) as [|o obs IH].
  - reflexivity.
  - simpl.
    rewrite mark_remitted_preserves_id.
    rewrite IH.
    reflexivity.
Qed.

Theorem apply_misharum_preserves_obligation_parties : forall st,
  map (fun o => (obligation_creditor o, obligation_debtor o))
      (state_obligations (apply_misharum st)) =
  map (fun o => (obligation_creditor o, obligation_debtor o))
      (state_obligations st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  induction (state_obligations st) as [|o obs IH].
  - reflexivity.
  - simpl.
    rewrite mark_remitted_preserves_creditor.
    rewrite mark_remitted_preserves_debtor.
    rewrite IH.
    reflexivity.
Qed.

Theorem apply_misharum_preserves_obligation_economics : forall st,
  map (fun o => (obligation_kind o, obligation_amount o))
      (state_obligations (apply_misharum st)) =
  map (fun o => (obligation_kind o, obligation_amount o))
      (state_obligations st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  induction (state_obligations st) as [|o obs IH].
  - reflexivity.
  - simpl.
    rewrite mark_remitted_preserves_kind.
    rewrite mark_remitted_preserves_amount.
    rewrite IH.
    reflexivity.
Qed.

Lemma release_if_remitted_preserves_household : forall ids b,
  bondage_household (release_if_remitted ids b) = bondage_household b.
Proof.
  intros ids [household obligation status].
  destruct status.
  - unfold release_if_remitted.
    simpl.
    destruct (id_in obligation ids).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma release_if_remitted_preserves_obligation : forall ids b,
  bondage_obligation (release_if_remitted ids b) = bondage_obligation b.
Proof.
  intros ids [household obligation status].
  destruct status.
  - unfold release_if_remitted.
    simpl.
    destruct (id_in obligation ids).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma restore_if_remitted_preserves_debtor : forall ids p,
  pledge_debtor (restore_if_remitted ids p) = pledge_debtor p.
Proof.
  intros ids [holder debtor obligation kind status].
  destruct status.
  - unfold restore_if_remitted.
    simpl.
    destruct (id_in obligation ids).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma restore_if_remitted_preserves_obligation : forall ids p,
  pledge_obligation (restore_if_remitted ids p) = pledge_obligation p.
Proof.
  intros ids [holder debtor obligation kind status].
  destruct status.
  - unfold restore_if_remitted.
    simpl.
    destruct (id_in obligation ids).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma restore_if_remitted_preserves_holding_kind : forall ids p,
  pledge_holding_kind (restore_if_remitted ids p) = pledge_holding_kind p.
Proof.
  intros ids [holder debtor obligation kind status].
  destruct status.
  - unfold restore_if_remitted.
    simpl.
    destruct (id_in obligation ids).
    + reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma refund_if_remitted_preserves_obligation : forall ids c,
  collection_obligation (refund_if_remitted ids c) = collection_obligation c.
Proof.
  intros ids [obligation amount before status].
  destruct status.
  - destruct before.
    + unfold refund_if_remitted.
      simpl.
      destruct (id_in obligation ids).
      * reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma refund_if_remitted_preserves_amount : forall ids c,
  collection_amount (refund_if_remitted ids c) = collection_amount c.
Proof.
  intros ids [obligation amount before status].
  destruct status.
  - destruct before.
    + unfold refund_if_remitted.
      simpl.
      destruct (id_in obligation ids).
      * reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma refund_if_remitted_preserves_before_edict : forall ids c,
  collection_before_edict (refund_if_remitted ids c) = collection_before_edict c.
Proof.
  intros ids [obligation amount before status].
  destruct status.
  - destruct before.
    + unfold refund_if_remitted.
      simpl.
      destruct (id_in obligation ids).
      * reflexivity.
      * reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Definition obligation_ids (st : CaseState) : list nat :=
  map obligation_id (state_obligations st).

Definition state_referential_integrity (st : CaseState) : Prop :=
  Forall (fun b => In (bondage_obligation b) (obligation_ids st)) (state_bondages st) /\
  Forall (fun p => In (pledge_obligation p) (obligation_ids st)) (state_pledges st) /\
  Forall (fun c => In (collection_obligation c) (obligation_ids st)) (state_collections st).

Theorem apply_misharum_preserves_bondage_links : forall st,
  map bondage_obligation (state_bondages (apply_misharum st)) =
  map bondage_obligation (state_bondages st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  induction (state_bondages st) as [|b bondages IH].
  - reflexivity.
  - simpl.
    rewrite release_if_remitted_preserves_obligation.
    rewrite IH.
    reflexivity.
Qed.

Theorem apply_misharum_preserves_pledge_links : forall st,
  map pledge_obligation (state_pledges (apply_misharum st)) =
  map pledge_obligation (state_pledges st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  induction (state_pledges st) as [|p pledges IH].
  - reflexivity.
  - simpl.
    rewrite restore_if_remitted_preserves_obligation.
    rewrite IH.
    reflexivity.
Qed.

Theorem apply_misharum_preserves_collection_links : forall st,
  map collection_obligation (state_collections (apply_misharum st)) =
  map collection_obligation (state_collections st).
Proof.
  intros st.
  unfold apply_misharum.
  simpl.
  induction (state_collections st) as [|c collections IH].
  - reflexivity.
  - simpl.
    rewrite refund_if_remitted_preserves_obligation.
    rewrite IH.
    reflexivity.
Qed.

Lemma Forall_release_if_remitted_preserves_refs :
  forall ids refs bondages,
    Forall (fun b => In (bondage_obligation b) refs) bondages ->
    Forall (fun b => In (bondage_obligation b) refs)
      (map (release_if_remitted ids) bondages).
Proof.
  intros ids refs bondages H.
  induction H as [|b bondages Hb Htail IH].
  - constructor.
  - simpl.
    constructor.
    + rewrite release_if_remitted_preserves_obligation.
      exact Hb.
    + exact IH.
Qed.

Lemma Forall_restore_if_remitted_preserves_refs :
  forall ids refs pledges,
    Forall (fun p => In (pledge_obligation p) refs) pledges ->
    Forall (fun p => In (pledge_obligation p) refs)
      (map (restore_if_remitted ids) pledges).
Proof.
  intros ids refs pledges H.
  induction H as [|p pledges Hp Htail IH].
  - constructor.
  - simpl.
    constructor.
    + rewrite restore_if_remitted_preserves_obligation.
      exact Hp.
    + exact IH.
Qed.

Lemma Forall_refund_if_remitted_preserves_refs :
  forall ids refs collections,
    Forall (fun c => In (collection_obligation c) refs) collections ->
    Forall (fun c => In (collection_obligation c) refs)
      (map (refund_if_remitted ids) collections).
Proof.
  intros ids refs collections H.
  induction H as [|c collections Hc Htail IH].
  - constructor.
  - simpl.
    constructor.
    + rewrite refund_if_remitted_preserves_obligation.
      exact Hc.
    + exact IH.
Qed.

Theorem apply_misharum_preserves_referential_integrity : forall st,
  state_referential_integrity st ->
  state_referential_integrity (apply_misharum st).
Proof.
  intros st [Hbondages [Hpledges Hcollections]].
  unfold state_referential_integrity in *.
  repeat split.
  - unfold obligation_ids.
    rewrite apply_misharum_preserves_obligation_ids.
    simpl.
    apply Forall_release_if_remitted_preserves_refs.
    exact Hbondages.
  - unfold obligation_ids.
    rewrite apply_misharum_preserves_obligation_ids.
    simpl.
    apply Forall_restore_if_remitted_preserves_refs.
    exact Hpledges.
  - unfold obligation_ids.
    rewrite apply_misharum_preserves_obligation_ids.
    simpl.
    apply Forall_refund_if_remitted_preserves_refs.
    exact Hcollections.
Qed.

Inductive EdictClause :=
| ClauseDebtRemission
| ClauseBondageRelease
| ClausePledgeRestoration
| ClauseCollectionRefund
| ClauseCommercialException
| ClauseAdministrativeClosure.

Inductive ClauseWitness :=
| WitnessDebtRemissionFormula
| WitnessDebtServitudeFormula
| WitnessPledgeRestorationFormula
| WitnessCollectionRefundFormula
| WitnessCommercialExceptionFormula
| WitnessAdministrativeClosureFormula.

Definition clause_witness (cl : EdictClause) : ClauseWitness :=
  match cl with
  | ClauseDebtRemission => WitnessDebtRemissionFormula
  | ClauseBondageRelease => WitnessDebtServitudeFormula
  | ClausePledgeRestoration => WitnessPledgeRestorationFormula
  | ClauseCollectionRefund => WitnessCollectionRefundFormula
  | ClauseCommercialException => WitnessCommercialExceptionFormula
  | ClauseAdministrativeClosure => WitnessAdministrativeClosureFormula
  end.

Definition classify_obligation_clause (o : Obligation) : EdictClause :=
  if obligation_is_remissible o then ClauseDebtRemission
  else if obligation_is_commercial_exception o then ClauseCommercialException
  else ClauseAdministrativeClosure.

Definition classify_bondage_clause (ids : list nat) (b : Bondage) : EdictClause :=
  match bondage_status b with
  | Released => ClauseAdministrativeClosure
  | Bound =>
      if id_in (bondage_obligation b) ids then
        ClauseBondageRelease
      else ClauseAdministrativeClosure
  end.

Definition classify_pledge_clause (ids : list nat) (p : Pledge) : EdictClause :=
  match pledge_status p with
  | Restored => ClauseAdministrativeClosure
  | Held =>
      if id_in (pledge_obligation p) ids then
        ClausePledgeRestoration
      else ClauseAdministrativeClosure
  end.

Definition classify_collection_clause (ids : list nat) (c : Collection) : EdictClause :=
  match collection_status c with
  | Refunded => ClauseAdministrativeClosure
  | Retained =>
      if collection_before_edict c && id_in (collection_obligation c) ids then
        ClauseCollectionRefund
      else ClauseAdministrativeClosure
  end.

Theorem classify_obligation_clause_exact : forall o,
  match classify_obligation_clause o with
  | ClauseDebtRemission =>
      obligation_is_remissible o = true /\
      obligation_status (mark_remitted o) = Remitted /\
      clause_witness (classify_obligation_clause o) = WitnessDebtRemissionFormula
  | ClauseCommercialException =>
      obligation_is_commercial_exception o = true /\
      mark_remitted o = o /\
      clause_witness (classify_obligation_clause o) =
      WitnessCommercialExceptionFormula
  | ClauseAdministrativeClosure =>
      obligation_status o = Remitted /\
      mark_remitted o = o /\
      clause_witness (classify_obligation_clause o) =
      WitnessAdministrativeClosureFormula
  | _ => False
  end.
Proof.
  intros [oid creditor debtor kind amount status].
  destruct status.
  - destruct kind.
    all: simpl; repeat split; reflexivity.
  - destruct kind.
    all: simpl; repeat split; reflexivity.
Qed.

Theorem classify_bondage_clause_exact : forall ids b,
  match classify_bondage_clause ids b with
  | ClauseBondageRelease =>
      bondage_status b = Bound /\
      id_in (bondage_obligation b) ids = true /\
      bondage_status (release_if_remitted ids b) = Released /\
      clause_witness (classify_bondage_clause ids b) =
      WitnessDebtServitudeFormula
  | ClauseAdministrativeClosure =>
      (bondage_status b = Released \/
       (bondage_status b = Bound /\
        id_in (bondage_obligation b) ids = false)) /\
      release_if_remitted ids b = b /\
      clause_witness (classify_bondage_clause ids b) =
      WitnessAdministrativeClosureFormula
  | _ => False
  end.
Proof.
  intros ids [household obligation status].
  destruct status.
  - unfold classify_bondage_clause.
    simpl.
    destruct (id_in obligation ids) eqn:Hid.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ apply release_if_remitted_bound.
              ** reflexivity.
              ** exact Hid.
           ++ reflexivity.
    + split.
      * right.
        split.
        -- reflexivity.
        -- reflexivity.
      * split.
        -- unfold release_if_remitted.
           simpl.
           rewrite Hid.
           reflexivity.
        -- reflexivity.
  - simpl.
    split.
    + left. reflexivity.
    + split.
      * reflexivity.
      * reflexivity.
Qed.

Definition distress_obligation_agric : Obligation :=
  {| obligation_id := 1;
     obligation_creditor := 100;
     obligation_debtor := 200;
     obligation_kind := AgrarianBarley;
     obligation_amount := 60;
     obligation_status := Enforceable |}.

Definition distress_obligation_trade : Obligation :=
  {| obligation_id := 2;
     obligation_creditor := 101;
     obligation_debtor := 200;
     obligation_kind := MerchantLoan;
     obligation_amount := 90;
     obligation_status := Enforceable |}.

Definition distress_bondage : Bondage :=
  {| bondage_household := 200;
     bondage_obligation := 1;
     bondage_status := Bound |}.

Definition distress_pledge : Pledge :=
  {| pledge_holder := 100;
     pledge_debtor := 200;
     pledge_obligation := 1;
     pledge_holding_kind := Field;
     pledge_status := Held |}.

Definition distress_collection_agric : Collection :=
  {| collection_obligation := 1;
     collection_amount := 20;
     collection_before_edict := true;
     collection_status := Retained |}.

Definition distress_collection_trade : Collection :=
  {| collection_obligation := 2;
     collection_amount := 15;
     collection_before_edict := true;
     collection_status := Retained |}.

Definition distress_case : CaseState :=
  {| state_obligations := [distress_obligation_agric; distress_obligation_trade];
     state_bondages := [distress_bondage];
     state_pledges := [distress_pledge];
     state_collections := [distress_collection_agric; distress_collection_trade] |}.

Definition distress_case_after : CaseState :=
  {| state_obligations :=
       [ {| obligation_id := 1;
            obligation_creditor := 100;
            obligation_debtor := 200;
            obligation_kind := AgrarianBarley;
            obligation_amount := 60;
            obligation_status := Remitted |};
         distress_obligation_trade ];
     state_bondages :=
       [ {| bondage_household := 200;
            bondage_obligation := 1;
            bondage_status := Released |} ];
     state_pledges :=
       [ {| pledge_holder := 100;
            pledge_debtor := 200;
            pledge_obligation := 1;
            pledge_holding_kind := Field;
            pledge_status := Restored |} ];
     state_collections :=
       [ {| collection_obligation := 1;
            collection_amount := 20;
            collection_before_edict := true;
            collection_status := Refunded |};
         distress_collection_trade ] |}.

Example distress_case_exec :
  apply_misharum distress_case = distress_case_after.
Proof.
  reflexivity.
Qed.

Example distress_case_clause_trace :
  map classify_obligation_clause (state_obligations distress_case) =
    [ClauseDebtRemission; ClauseCommercialException].
Proof.
  reflexivity.
Qed.

Example distress_case_integrity :
  state_referential_integrity distress_case.
Proof.
  unfold state_referential_integrity, obligation_ids, distress_case.
  simpl.
  repeat split.
  - constructor.
    + simpl.
      left.
      reflexivity.
    + constructor.
  - constructor.
    + simpl.
      left.
      reflexivity.
    + constructor.
  - constructor.
    + simpl.
      left.
      reflexivity.
    + constructor.
      * simpl.
        right.
        left.
        reflexivity.
      * constructor.
Qed.

Example distress_case_integrity_after :
  state_referential_integrity (apply_misharum distress_case).
Proof.
  apply apply_misharum_preserves_referential_integrity.
  apply distress_case_integrity.
Qed.

Definition late_collection_obligation : Obligation :=
  {| obligation_id := 3;
     obligation_creditor := 110;
     obligation_debtor := 210;
     obligation_kind := AgrarianSilver;
     obligation_amount := 40;
     obligation_status := Enforceable |}.

Definition late_collection : Collection :=
  {| collection_obligation := 3;
     collection_amount := 10;
     collection_before_edict := false;
     collection_status := Retained |}.

Definition late_collection_case : CaseState :=
  {| state_obligations := [late_collection_obligation];
     state_bondages := [];
     state_pledges := [];
     state_collections := [late_collection] |}.

Definition late_collection_case_after : CaseState :=
  {| state_obligations :=
       [ {| obligation_id := 3;
            obligation_creditor := 110;
            obligation_debtor := 210;
            obligation_kind := AgrarianSilver;
            obligation_amount := 40;
            obligation_status := Remitted |} ];
     state_bondages := [];
     state_pledges := [];
     state_collections := [late_collection] |}.

Example late_collection_case_exec :
  apply_misharum late_collection_case = late_collection_case_after.
Proof.
  reflexivity.
Qed.

Example late_collection_clause_trace :
  classify_collection_clause (remitted_ids late_collection_case) late_collection =
  ClauseAdministrativeClosure.
Proof.
  reflexivity.
Qed.

Definition closed_obligation : Obligation :=
  {| obligation_id := 4;
     obligation_creditor := 120;
     obligation_debtor := 220;
     obligation_kind := TaxArrear;
     obligation_amount := 12;
     obligation_status := Remitted |}.

Definition closed_bondage : Bondage :=
  {| bondage_household := 220;
     bondage_obligation := 4;
     bondage_status := Released |}.

Definition closed_pledge : Pledge :=
  {| pledge_holder := 120;
     pledge_debtor := 220;
     pledge_obligation := 4;
     pledge_holding_kind := Orchard;
     pledge_status := Restored |}.

Definition closed_collection : Collection :=
  {| collection_obligation := 4;
     collection_amount := 12;
     collection_before_edict := true;
     collection_status := Refunded |}.

Definition closed_case : CaseState :=
  {| state_obligations := [closed_obligation];
     state_bondages := [closed_bondage];
     state_pledges := [closed_pledge];
     state_collections := [closed_collection] |}.

Example closed_case_exec :
  apply_misharum closed_case = closed_case.
Proof.
  reflexivity.
Qed.

Example closed_case_clause_trace :
  map classify_obligation_clause (state_obligations closed_case) =
    [ClauseAdministrativeClosure].
Proof.
  reflexivity.
Qed.

Record TimedObligation := {
  timed_obligation_payload : Obligation;
  obligation_incurred_on : nat
}.

Record TimedCollection := {
  timed_collection_payload : Collection;
  collection_recorded_on : nat
}.

Record TimedCaseState := {
  timed_edict_day : nat;
  timed_state_obligations : list TimedObligation;
  timed_state_bondages : list Bondage;
  timed_state_pledges : list Pledge;
  timed_state_collections : list TimedCollection
}.

Definition obligation_predates_edict (edict_day : nat) (o : TimedObligation) : bool :=
  obligation_incurred_on o <? edict_day.

Definition timed_obligation_is_remissible (edict_day : nat) (o : TimedObligation) : bool :=
  obligation_predates_edict edict_day o &&
  obligation_is_remissible (timed_obligation_payload o).

Definition mark_remitted_timed (edict_day : nat) (o : TimedObligation) : Obligation :=
  if timed_obligation_is_remissible edict_day o then
    mark_remitted (timed_obligation_payload o)
  else timed_obligation_payload o.

Definition timed_remitted_ids (st : TimedCaseState) : list nat :=
  map (fun o => obligation_id (timed_obligation_payload o))
    (filter (timed_obligation_is_remissible (timed_edict_day st))
      (timed_state_obligations st)).

Definition normalize_timed_collection (edict_day : nat) (c : TimedCollection)
  : Collection :=
  let payload := timed_collection_payload c in
  {| collection_obligation := collection_obligation payload;
     collection_amount := collection_amount payload;
     collection_before_edict := collection_recorded_on c <? edict_day;
     collection_status := collection_status payload |}.

Definition refund_timed_if_remitted (edict_day : nat) (ids : list nat)
    (c : TimedCollection)
  : Collection :=
  refund_if_remitted ids (normalize_timed_collection edict_day c).

Definition apply_timed_misharum (st : TimedCaseState) : CaseState :=
  let ids := timed_remitted_ids st in
  {| state_obligations :=
       map (mark_remitted_timed (timed_edict_day st)) (timed_state_obligations st);
     state_bondages := map (release_if_remitted ids) (timed_state_bondages st);
     state_pledges := map (restore_if_remitted ids) (timed_state_pledges st);
     state_collections :=
       map (refund_timed_if_remitted (timed_edict_day st) ids)
         (timed_state_collections st) |}.

Lemma mark_remitted_timed_post_edict : forall edict_day o,
  obligation_predates_edict edict_day o = false ->
  mark_remitted_timed edict_day o = timed_obligation_payload o.
Proof.
  intros edict_day [payload incurred] H.
  unfold obligation_predates_edict in H.
  unfold mark_remitted_timed, timed_obligation_is_remissible, obligation_predates_edict.
  simpl in *.
  rewrite H.
  reflexivity.
Qed.

Lemma mark_remitted_timed_remits : forall edict_day o,
  timed_obligation_is_remissible edict_day o = true ->
  obligation_status (mark_remitted_timed edict_day o) = Remitted.
Proof.
  intros edict_day [payload incurred] H.
  unfold mark_remitted_timed, timed_obligation_is_remissible, obligation_predates_edict in *.
  simpl in *.
  apply andb_true_iff in H as [Htime Hrem].
  rewrite Htime.
  simpl.
  rewrite Hrem.
  simpl.
  apply mark_remitted_remits.
  exact Hrem.
Qed.

Lemma normalize_timed_collection_before_edict : forall edict_day c,
  collection_before_edict (normalize_timed_collection edict_day c) =
  (collection_recorded_on c <? edict_day).
Proof.
  intros edict_day [payload recorded].
  reflexivity.
Qed.

Lemma refund_timed_if_remitted_post_edict : forall edict_day ids c,
  collection_recorded_on c <? edict_day = false ->
  refund_timed_if_remitted edict_day ids c =
  normalize_timed_collection edict_day c.
Proof.
  intros edict_day ids [payload recorded] H.
  unfold refund_timed_if_remitted, normalize_timed_collection.
  simpl in *.
  destruct payload as [obligation amount before status].
  simpl in *.
  destruct status.
  - rewrite H.
    reflexivity.
  - reflexivity.
Qed.

Lemma mark_remitted_timed_status_exact : forall edict_day o,
  obligation_status (mark_remitted_timed edict_day o) = Remitted <->
  obligation_status (timed_obligation_payload o) = Remitted \/
  timed_obligation_is_remissible edict_day o = true.
Proof.
  intros edict_day [payload incurred].
  unfold mark_remitted_timed, timed_obligation_is_remissible.
  simpl.
  destruct (obligation_predates_edict edict_day
    {| timed_obligation_payload := payload;
       obligation_incurred_on := incurred |} && obligation_is_remissible payload)
    eqn:Hremiss.
  - split; intro H.
    + right.
      reflexivity.
    + apply mark_remitted_remits.
      apply andb_true_iff in Hremiss as [Htime Hrem].
      exact Hrem.
  - split; intro H.
    + left.
      exact H.
    + destruct H as [H | H].
      * exact H.
      * discriminate H.
Qed.

Lemma mark_remitted_timed_remissible_exact : forall edict_day o,
  timed_obligation_is_remissible edict_day o = true ->
  obligation_predates_edict edict_day o = true /\
  obligation_is_remissible (timed_obligation_payload o) = true.
Proof.
  intros edict_day [payload incurred] H.
  unfold timed_obligation_is_remissible, obligation_predates_edict in H.
  simpl in H.
  apply andb_true_iff in H as [Htime Hrem].
  split.
  - exact Htime.
  - exact Hrem.
Qed.

Lemma timed_obligation_is_remissible_intro : forall edict_day o,
  obligation_predates_edict edict_day o = true ->
  obligation_is_remissible (timed_obligation_payload o) = true ->
  timed_obligation_is_remissible edict_day o = true.
Proof.
  intros edict_day o Hpred Hrem.
  unfold timed_obligation_is_remissible.
  rewrite Hpred.
  rewrite Hrem.
  reflexivity.
Qed.

Lemma mark_remitted_timed_status_exact_expanded : forall edict_day o,
  obligation_status (mark_remitted_timed edict_day o) = Remitted <->
  obligation_status (timed_obligation_payload o) = Remitted \/
  (obligation_predates_edict edict_day o = true /\
   obligation_is_remissible (timed_obligation_payload o) = true).
Proof.
  intros edict_day o.
  rewrite mark_remitted_timed_status_exact.
  split; intro H.
  - destruct H as [H | H].
    + left.
      exact H.
    + right.
      apply mark_remitted_timed_remissible_exact.
      exact H.
  - destruct H as [H | H].
    + left.
      exact H.
    + right.
      destruct H as [Htime Hrem].
      apply timed_obligation_is_remissible_intro.
      * exact Htime.
      * exact Hrem.
Qed.

Lemma refund_timed_if_remitted_status_exact : forall edict_day ids c,
  collection_status (refund_timed_if_remitted edict_day ids c) = Refunded <->
  collection_status (timed_collection_payload c) = Refunded \/
  (collection_status (timed_collection_payload c) = Retained /\
   collection_recorded_on c <? edict_day = true /\
   id_in (collection_obligation (timed_collection_payload c)) ids = true).
Proof.
  intros edict_day ids [payload recorded].
  unfold refund_timed_if_remitted, normalize_timed_collection.
  destruct payload as [obligation amount before status].
  simpl.
  apply refund_if_remitted_status_exact.
Qed.

Lemma mark_remitted_timed_preserves_id : forall edict_day o,
  obligation_id (mark_remitted_timed edict_day o) =
  obligation_id (timed_obligation_payload o).
Proof.
  intros edict_day [payload incurred].
  unfold mark_remitted_timed.
  simpl.
  destruct (timed_obligation_is_remissible edict_day
    {| timed_obligation_payload := payload;
       obligation_incurred_on := incurred |}).
  - apply mark_remitted_preserves_id.
  - reflexivity.
Qed.

Lemma refund_timed_if_remitted_preserves_obligation : forall edict_day ids c,
  collection_obligation (refund_timed_if_remitted edict_day ids c) =
  collection_obligation (timed_collection_payload c).
Proof.
  intros edict_day ids [payload recorded].
  unfold refund_timed_if_remitted.
  rewrite refund_if_remitted_preserves_obligation.
  unfold normalize_timed_collection.
  destruct payload as [obligation amount before status].
  reflexivity.
Qed.

Lemma refund_timed_if_remitted_preserves_before_edict : forall edict_day ids c,
  collection_before_edict (refund_timed_if_remitted edict_day ids c) =
  (collection_recorded_on c <? edict_day).
Proof.
  intros edict_day ids c.
  unfold refund_timed_if_remitted.
  rewrite refund_if_remitted_preserves_before_edict.
  apply normalize_timed_collection_before_edict.
Qed.

Definition timed_obligation_ids (st : TimedCaseState) : list nat :=
  map (fun o => obligation_id (timed_obligation_payload o))
    (timed_state_obligations st).

Definition timed_state_referential_integrity (st : TimedCaseState) : Prop :=
  Forall (fun b => In (bondage_obligation b) (timed_obligation_ids st))
    (timed_state_bondages st) /\
  Forall (fun p => In (pledge_obligation p) (timed_obligation_ids st))
    (timed_state_pledges st) /\
  Forall
    (fun c => In (collection_obligation (timed_collection_payload c))
      (timed_obligation_ids st))
    (timed_state_collections st).

Theorem apply_timed_misharum_preserves_obligation_ids : forall st,
  map obligation_id (state_obligations (apply_timed_misharum st)) =
  timed_obligation_ids st.
Proof.
  intros [edict_day obligations bondages pledges collections].
  simpl.
  induction obligations as [|o obligations IH].
  - reflexivity.
  - simpl.
    rewrite mark_remitted_timed_preserves_id.
    rewrite IH.
    reflexivity.
Qed.

Lemma Forall_refund_timed_if_remitted_preserves_refs :
  forall edict_day ids refs collections,
    Forall
      (fun c => In (collection_obligation (timed_collection_payload c)) refs)
      collections ->
    Forall (fun c => In (collection_obligation c) refs)
      (map (refund_timed_if_remitted edict_day ids) collections).
Proof.
  intros edict_day ids refs collections H.
  induction H as [|c collections Hc Htail IH].
  - constructor.
  - simpl.
    constructor.
    + rewrite refund_timed_if_remitted_preserves_obligation.
      exact Hc.
    + exact IH.
Qed.

Theorem apply_timed_misharum_preserves_referential_integrity : forall st,
  timed_state_referential_integrity st ->
  state_referential_integrity (apply_timed_misharum st).
Proof.
  intros st [Hbondages [Hpledges Hcollections]].
  unfold timed_state_referential_integrity in *.
  unfold state_referential_integrity.
  repeat split.
  - unfold obligation_ids.
    rewrite apply_timed_misharum_preserves_obligation_ids.
    simpl.
    apply Forall_release_if_remitted_preserves_refs.
    exact Hbondages.
  - unfold obligation_ids.
    rewrite apply_timed_misharum_preserves_obligation_ids.
    simpl.
    apply Forall_restore_if_remitted_preserves_refs.
    exact Hpledges.
  - unfold obligation_ids.
    rewrite apply_timed_misharum_preserves_obligation_ids.
    simpl.
    apply Forall_refund_timed_if_remitted_preserves_refs.
    exact Hcollections.
Qed.

Theorem apply_timed_misharum_normalizes_collection_timing : forall st,
  map collection_before_edict (state_collections (apply_timed_misharum st)) =
  map (fun c => collection_recorded_on c <? timed_edict_day st)
    (timed_state_collections st).
Proof.
  intros [edict_day obligations bondages pledges collections].
  simpl.
  induction collections as [|c collections IH].
  - reflexivity.
  - simpl.
    rewrite refund_timed_if_remitted_preserves_before_edict.
    f_equal.
    exact IH.
Qed.

Definition timed_pre_edict_obligation : TimedObligation :=
  {| timed_obligation_payload :=
       {| obligation_id := 5;
          obligation_creditor := 130;
          obligation_debtor := 230;
          obligation_kind := RentArrear;
          obligation_amount := 25;
          obligation_status := Enforceable |};
     obligation_incurred_on := 3 |}.

Definition timed_post_edict_obligation : TimedObligation :=
  {| timed_obligation_payload :=
       {| obligation_id := 6;
          obligation_creditor := 131;
          obligation_debtor := 230;
          obligation_kind := AgrarianSilver;
          obligation_amount := 55;
          obligation_status := Enforceable |};
     obligation_incurred_on := 12 |}.

Definition timed_pre_edict_collection : TimedCollection :=
  {| timed_collection_payload :=
       {| collection_obligation := 5;
          collection_amount := 7;
          collection_before_edict := false;
          collection_status := Retained |};
     collection_recorded_on := 4 |}.

Definition timed_post_edict_collection : TimedCollection :=
  {| timed_collection_payload :=
       {| collection_obligation := 6;
          collection_amount := 11;
          collection_before_edict := true;
          collection_status := Retained |};
     collection_recorded_on := 14 |}.

Definition timed_case : TimedCaseState :=
  {| timed_edict_day := 10;
     timed_state_obligations :=
       [timed_pre_edict_obligation; timed_post_edict_obligation];
     timed_state_bondages := [];
     timed_state_pledges := [];
     timed_state_collections :=
       [timed_pre_edict_collection; timed_post_edict_collection] |}.

Definition timed_case_after : CaseState :=
  {| state_obligations :=
       [ {| obligation_id := 5;
            obligation_creditor := 130;
            obligation_debtor := 230;
            obligation_kind := RentArrear;
            obligation_amount := 25;
            obligation_status := Remitted |};
         {| obligation_id := 6;
            obligation_creditor := 131;
            obligation_debtor := 230;
            obligation_kind := AgrarianSilver;
            obligation_amount := 55;
            obligation_status := Enforceable |} ];
     state_bondages := [];
     state_pledges := [];
     state_collections :=
       [ {| collection_obligation := 5;
            collection_amount := 7;
            collection_before_edict := true;
            collection_status := Refunded |};
         {| collection_obligation := 6;
            collection_amount := 11;
            collection_before_edict := false;
            collection_status := Retained |} ] |}.

Example timed_case_exec :
  apply_timed_misharum timed_case = timed_case_after.
Proof.
  reflexivity.
Qed.

Theorem classify_pledge_clause_exact : forall ids p,
  match classify_pledge_clause ids p with
  | ClausePledgeRestoration =>
      pledge_status p = Held /\
      id_in (pledge_obligation p) ids = true /\
      pledge_status (restore_if_remitted ids p) = Restored /\
      clause_witness (classify_pledge_clause ids p) =
      WitnessPledgeRestorationFormula
  | ClauseAdministrativeClosure =>
      (pledge_status p = Restored \/
       (pledge_status p = Held /\
        id_in (pledge_obligation p) ids = false)) /\
      restore_if_remitted ids p = p /\
      clause_witness (classify_pledge_clause ids p) =
      WitnessAdministrativeClosureFormula
  | _ => False
  end.
Proof.
  intros ids [holder debtor obligation kind status].
  destruct status.
  - unfold classify_pledge_clause.
    simpl.
    destruct (id_in obligation ids) eqn:Hid.
    + split.
      * reflexivity.
      * split.
        -- reflexivity.
        -- split.
           ++ apply restore_if_remitted_held.
              ** reflexivity.
              ** exact Hid.
           ++ reflexivity.
    + split.
      * right.
        split.
        -- reflexivity.
        -- reflexivity.
      * split.
        -- unfold restore_if_remitted.
           simpl.
           rewrite Hid.
           reflexivity.
        -- reflexivity.
  - simpl.
    split.
    + left. reflexivity.
    + split.
      * reflexivity.
      * reflexivity.
Qed.

Theorem classify_collection_clause_exact : forall ids c,
  match classify_collection_clause ids c with
  | ClauseCollectionRefund =>
      collection_status c = Retained /\
      collection_before_edict c = true /\
      id_in (collection_obligation c) ids = true /\
      collection_status (refund_if_remitted ids c) = Refunded /\
      clause_witness (classify_collection_clause ids c) =
      WitnessCollectionRefundFormula
  | ClauseAdministrativeClosure =>
      (collection_status c = Refunded \/
       (collection_status c = Retained /\
        (collection_before_edict c = false \/
         id_in (collection_obligation c) ids = false))) /\
      refund_if_remitted ids c = c /\
      clause_witness (classify_collection_clause ids c) =
      WitnessAdministrativeClosureFormula
  | _ => False
  end.
Proof.
  intros ids [obligation amount before status].
  destruct status.
  - destruct before.
    + unfold classify_collection_clause.
      simpl.
      destruct (id_in obligation ids) eqn:Hid.
      * split.
        -- reflexivity.
        -- split.
           ++ reflexivity.
           ++ split.
              ** reflexivity.
              ** split.
                 --- apply refund_if_remitted_retained.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ exact Hid.
                 --- reflexivity.
      * split.
        -- right.
           split.
           ++ reflexivity.
           ++ right. reflexivity.
        -- split.
           ++ unfold refund_if_remitted.
              simpl.
              rewrite Hid.
              reflexivity.
           ++ reflexivity.
    + unfold classify_collection_clause.
      simpl.
      split.
      * right.
        split.
        -- reflexivity.
        -- left. reflexivity.
      * split.
        -- reflexivity.
        -- reflexivity.
  - simpl.
    split.
    + left. reflexivity.
    + split.
      * reflexivity.
      * reflexivity.
Qed.
