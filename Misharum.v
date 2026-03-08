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
