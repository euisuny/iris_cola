From iris.bi Require Import bi.
From iris.proofmode Require Import proofmode.

Section bi_cola.

  (* Definition from Pous' coinduction library *)
  Class CompleteLattice (X: Type) := {
    weq: relation X;
    leq: relation X;
    sup': forall I, (I -> Prop) -> (I -> X) -> X;
    inf': forall I, (I -> Prop) -> (I -> X) -> X;
    cup: X -> X -> X;
    cap: X -> X -> X;
    bot: X;
    top: X;
    CL_props:
    (* PreOrder_leq:> *) PreOrder leq /\
    (* weq_spec: *) (forall x y, weq x y <-> (leq x y /\ leq y x)) /\
    (* sup_spec: forall P z, sup P <= z <-> forall x, P x -> x <= z; *)
    (* inf_spec: forall P z, z <= inf P <-> forall x, P x -> z <= x; *)
    (* sup_spec: *) (forall I P f z, leq (@sup' I P f) z <-> forall i, P i -> leq (f i) z) /\
    (* inf_spec: *) (forall I P f z, leq z (@inf' I P f) <-> forall i, P i -> leq z (f i)) /\
    (* cup_spec: *) (forall x y z, leq (cup x y) z <-> (leq x z /\ leq y z)) /\
    (* cap_spec: *) (forall x y z, leq z (cap x y) <-> (leq z x /\ leq z y)) /\
    (* leq_bx: *) (forall x, leq bot x) /\
    (* leq_xt: *) (forall x, leq x top)
  }.

  Context {PROP : bi} `{!BiAffine PROP}.

  Definition bi_weq (x y : PROP) : Prop := (x ⊣⊢ y).
  Definition bi_leq (x y : PROP) : Prop := (x ⊢ y)%I.
  Definition bi_sup' (I : Type) (f : I -> Prop) (f': I -> PROP) : PROP :=
    (∃ (i : I), ⌜f i⌝ ∗ f' i).
  Definition bi_inf' (I : Type) (f : I -> Prop) (f': I -> PROP) : PROP :=
    (∀ (i : I), ⌜f i⌝ -∗ f' i).
  Definition bi_cup (x y : PROP) := (x ∨ y)%I.
  Definition bi_cap (x y : PROP) := (x ∧ y)%I.
  Definition bi_bot := (⌜False⌝ : PROP)%I.
  Definition bi_top := (⌜True⌝ : PROP)%I.

  Program Instance CompleteLattice_bi : CompleteLattice PROP := {|
      weq:=bi_weq;
      leq:=bi_leq;
      sup' := bi_sup';
      inf' := bi_inf';
      cup:=bi_cup;
      cap:=bi_cap;
      bot:=bi_bot;
      top:=bi_top |}.
  Next Obligation.
    split.
    { constructor.
      - iIntros (?).
        by iIntros "H".
      - rewrite /Transitive.
        iIntros (?????). iIntros "H".
        iDestruct (H with "H") as "H".
        by iDestruct (H0 with "H") as "H". }
    split.
    { iIntros (??). split.
      - intros H. unfold bi_weq, bi_leq.
        split; iIntros "x";
        by iPoseProof (H with "x") as "H".
      - intros (?&?).
        rewrite /bi_weq.
        iSplit; first iApply H; iApply H0. }
    split.
    { iIntros (????). split; intros.
      - rewrite /bi_leq /bi_sup' in H.
        rewrite /bi_leq.
        iIntros "H".
        iPoseProof H as "Hi".
        iApply "Hi".
        iExists i; by iFrame.
      - rewrite /bi_leq. iIntros "H".
        iDestruct "H" as (?) "H".
        iDestruct "H" as "(%H' & H)".
        specialize (H _ H').
        by iPoseProof (H with "H") as "H". }
    split.
    { iIntros (????). split; intros.
      - iIntros "HP".
        iPoseProof (H with "HP") as "H".
        rewrite /bi_inf'.
        by iSpecialize ("H" $! _ H0).
      - iIntros "H".
        iIntros (??).
        specialize (H _ H0).
        iApply (H with "H"). }
    split.
    { iIntros (???). rewrite /bi_leq /bi_cup; split; intros.
      - split; iIntros "H"; iApply H; [ by iLeft | by iRight].
      - destruct H.
        iIntros "[H | H]".
        by iApply H.
        by iApply H0. }
    split.
    { intros. split.
      - rewrite /bi_leq; intros. split;
        iIntros "H'"; iPoseProof (H with "H'") as "H".
        iDestruct "H" as "(H1 & _)"; iFrame.
        iDestruct "H" as "(_ & H2)"; iFrame.
      - intros. destruct H. rewrite /bi_leq /bi_cap.
        iApply bi.and_intro; auto. }
    split.
    { iIntros (?). iIntros (?). done. }
    iIntros (?). iIntros "H". done.
  Qed.

End bi_cola.


Section bi_cola_bi.

  Context {PROP : bi} `{!BiAffine PROP}.

  Class Reflexive {A} (R : A -> A -> PROP) :=
    { Refl: (⊢ ∀ a, R a a)%I;}.

  Class Transitive {A} (R : A -> A -> PROP) :=
    { Trans: (forall x y z, R x y -∗ R y z -∗ R x z);}.

  Class PreOrder {A} (R : A -> A -> PROP) : Prop := {
    #[global] PreOrder_Reflexive :: Reflexive R  | 2;
    #[global] PreOrder_Transitive :: Transitive R | 2 }.

  Class CompleteLattice_ (X : Type) := {
    _weq: X -> X -> PROP;
    _leq: X -> X -> PROP;
    _sup': forall I, (I -> PROP) -> (I -> X) -> X;
    _inf': forall I, (I -> PROP) -> (I -> X) -> X;
    _cup: X -> X -> X;
    _cap: X -> X -> X;
    _bot: X;
    _top: X;
    _CL_props:
      ((* PreOrder_leq:> *) PreOrder _leq /\
      (* weq_spec: *) (forall x y, _weq x y ⊣⊢ (_leq x y ∗ _leq y x)) /\
      (* sup_spec: *) (forall I P f z, _leq (@_sup' I P f) z ⊣⊢ □ (∀ i, □ P i -∗ _leq (f i) z)) /\
      (* inf_spec: *) (forall I P f z, _leq z (@_inf' I P f) ⊣⊢ □ (∀ i, □ P i -∗ _leq z (f i))) /\
      (* _cup_spec: *) (forall x y z, _leq (_cup x y) z ⊣⊢ (_leq x z ∧ _leq y z)) /\
      (* cap_spec: *) (forall x y z, _leq z (_cap x y) ⊣⊢ (_leq z x ∧ _leq z y)) /\
      (* _leq_bx: *) (∀ x, ⊢ _leq _bot x) /\
      (* _leq_xt: *) (∀ x, ⊢ _leq x _top))%I
  }.

  Definition ofe_weq (x y : PROP) := (□ (x ∗-∗ y))%I.
  Definition ofe_leq (x y : PROP) := (□ (x -∗ y))%I.
  Definition ofe_sup' (I : Type) (f : I -> PROP) (f': I -> PROP) : PROP :=
    (∃ (i : I), □ f i ∗ f' i).
  Definition ofe_inf' (I : Type) (f : I -> PROP) (f': I -> PROP) : PROP :=
    (∀ (i : I), □ f i -∗ f' i).
  Definition ofe_cup (x y : PROP) := (x ∨ y)%I.
  Definition ofe_cap (x y : PROP) := (x ∧ y)%I.
  Definition ofe_bot := (⌜False⌝ : PROP)%I.
  Definition ofe_top := (⌜True⌝ : PROP)%I.

  Program Instance CompleteLattice__bi: CompleteLattice_ PROP := {|
      _weq:=ofe_weq;
      _leq:=ofe_leq;
      _sup' := ofe_sup';
      _inf' := ofe_inf';
      _cup:=ofe_cup;
      _cap:=ofe_cap;
      _bot:=ofe_bot;
      _top:=ofe_top |}.
  Next Obligation.
    split.
    { constructor.
      - constructor.
        iIntros (?). iModIntro.
        by iIntros "H".
      - constructor.
        iIntros (???) "#H1 #H2". iModIntro. iIntros "H".
        iSpecialize ("H1" with "H").
        iApply "H2". done. }
    split.
    { iIntros (??). iSplit.
      - iIntros "#H". unfold ofe_weq, ofe_leq.
        iSplitL; iModIntro; iIntros "x"; by iApply "H".
      - iIntros "(#H1 & #H2)".
        rewrite /ofe_weq.
        iModIntro.
        iSplit; iIntros "x".
        by iApply "H1".
        by iApply "H2". }
    split.
    { iIntros (????). iSplit.
      - iIntros "#H".
        iModIntro.
        iIntros (?) "#HP".
        rewrite /ofe_sup'.
        iModIntro. iIntros "Hf".
        iApply "H"; iExists i; by iFrame.
      - iIntros "#H".
        rewrite /ofe_leq.
        iModIntro. rewrite /ofe_sup'.
        iIntros "HP".
        iDestruct "HP" as (?) "(HP & Hf)".
        iSpecialize ("H" with "HP").
        by iSpecialize ("H" with "Hf"). }
    split.
    { iIntros (????). iSplit.
      - iIntros "#H".
        iModIntro.
        iIntros (?) "#HP".
        rewrite /ofe_sup'.
        iModIntro. iIntros "Hf".
        by iApply ("H" with "Hf").
      - iIntros "#H".
        rewrite /ofe_leq.
        iModIntro. rewrite /ofe_sup'.
        iIntros "z".
        iIntros (?) "HP".
        by iSpecialize ("H" with "HP z"). }
    split.
    { iIntros (???). iSplit; iIntros "#H".
      - rewrite /ofe_leq.
        iSplitL; iModIntro; try iModIntro;
        iIntros "H'"; iApply "H"; [ by iLeft | by iRight].
      - iDestruct "H" as "(H1 & H2)".
        iModIntro. iIntros "[H | H]".
        by iApply "H1".
        by iApply "H2". }
    split.
    { intros. iSplit.
      - rewrite /ofe_leq. iIntros "#H".
        iSplitL; repeat iModIntro; iIntros "H'"; iSpecialize ("H" with "H'").
        iDestruct "H" as "(H1 & _)"; iFrame.
        iDestruct "H" as "(_ & H2)"; iFrame.
      - iStopProof.
        iApply bi.entails_wand'.
        rewrite /ofe_leq.
        rewrite -bi.intuitionistically_and.
        iApply bi.intuitionistically_intro'.
        rewrite /ofe_cap.
        iApply bi.wand_intro_r.
        etransitivity.
        rewrite bi.intuitionistically_and.
        iApply bi.sep_and_r.
        iApply bi.and_mono;
        iIntros "(H1 & H2)"; by iSpecialize ("H1" with "H2"). }
    split.
    { iIntros (?). iModIntro. iIntros (?). done. }
    iIntros (?). iModIntro. iIntros "H". done.
  Qed.

End bi_cola_bi.

