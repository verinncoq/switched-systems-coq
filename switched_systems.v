From Coq Require Import Reals List Sorting Lia Lra.
Import ListNotations.
From Coquelicot Require Import Coquelicot.
From CoqE2EAI Require Import matrix_extensions.

Open Scope R_scope.

(*---------------------------------------------------------------------------*)

Section SwitchedSystem.

Definition previous_switch_spec
  (t: R)
  (switch: R * nat)
  (is_switch: (R * nat) -> Prop)
  :=
  let (t_prev, m_prev) := switch in
  is_switch switch /\
  t_prev < t /\
  forall t' m',
  is_switch (t', m') ->
    (t' <= t_prev \/ t' >= t).

Structure InductiveSwitchingSignal := BuildSwitchingSignal {
  is_switch_descriptor: (R * nat) -> Prop;
  one_switch_per_time:
    forall t m1 m2,
      is_switch_descriptor (t, m1) ->
      is_switch_descriptor (t, m2) ->
      m1 = m2;
  switch_count: R -> nat;
  switch_count_increase:
    forall t1 m1 t2 m2,
      is_switch_descriptor (t1, m1) ->
      is_switch_descriptor (t2, m2) ->
      previous_switch_spec t2 (t1, m1) is_switch_descriptor ->
      S (switch_count t1) = switch_count t2;    
  switch_count_const:
    forall t1 t2,
      t1 < t2 ->
      (forall t m,
        is_switch_descriptor (t, m) ->
        t < t1 \/ t >= t2) ->
      forall t' t'',
        t1 <= t' <= t2 ->
        t1 <= t'' <= t2 ->
        switch_count t' = switch_count t'';
  compute_prev_switch: R -> (R * nat);
  compute_prev_switch_correct: 
    forall t,
      (exists switch, 
        previous_switch_spec t switch is_switch_descriptor) ->
      forall result,
        previous_switch_spec t result is_switch_descriptor <->
        compute_prev_switch t = result;
  t0: R;
  signal_respects_t0:
    forall t,
      t <= t0 -> switch_count t = 0%nat
}.

Structure SwitchedSystem : Type := BuildSwitchedSystem {
  dimension: nat;                                
  modes: list (colvec dimension -> colvec dimension);
  switching_signal: InductiveSwitchingSignal;
  signal_selects_modes: 
    forall t m, 
      (is_switch_descriptor switching_signal) (t,m) -> (m < length modes)%nat; 
}.

Fixpoint generate_switches (count: nat) (t:R) (s: SwitchedSystem) :=
  let prev_switch_f := (compute_prev_switch (switching_signal s)) in
  match count with
  | 0 => []
  | S n => 
    let (t_prev, m_prev) := prev_switch_f t in
    (t_prev, m_prev) :: generate_switches n t_prev s
  end.

Definition switches_until (t: R) (s: SwitchedSystem) :=
  generate_switches ((switch_count (switching_signal s)) t) t s.

End SwitchedSystem.

(*---------------------------------------------------------------------------*)

Section ModeSolvers.

Definition RInt_multi {dim: nat} (f: R -> colvec dim) t_from t_to :=
    mk_colvec dim (fun i => RInt (fun t => coeff_colvec 0 (f t) i) t_from t_to).

Definition is_mode_solution
  (s: SwitchedSystem)
  (mode_idx: nat)
  (t_from: R)
  (x_t_from: colvec (dimension s))
  (solution: R -> colvec (dimension s)) :=
  forall mode t d,
    (mode_idx < length (modes s))%nat ->
    mode = nth mode_idx (modes s) d ->
    t_from <= t ->
    solution t = 
        Mplus (RInt_multi (fun tau => mode (solution tau)) t_from t) x_t_from.

Definition ModeSolver (s:SwitchedSystem) :=
    {solver : nat -> R -> colvec (dimension s) -> (R -> colvec (dimension s)) |
        forall mode_idx t_from x_t_from,
        is_mode_solution s mode_idx t_from x_t_from (solver mode_idx t_from x_t_from)}.

End ModeSolvers.

(*---------------------------------------------------------------------------*)

Section CaratheodoryTrajectory.

Fixpoint trajectory_on_switches
  (s: SwitchedSystem)
  (switches: list (R * nat))
  (x_init: colvec (dimension s))
  (solver: ModeSolver s): colvec (dimension s)
  :=
  match switches with
  | nil => x_init
  | (t2, m2) :: tail =>
      match tail with
      | nil => x_init
      | (t1, m1) :: _ =>
          match solver with
          | exist solver_f _  =>
              let traj_at_t1 := (trajectory_on_switches s tail x_init solver) in
              (solver_f m1 t1 traj_at_t1) t2                                             
          end
      end
  end.

Definition trajectory
  (s: SwitchedSystem)
  (x_init: colvec (dimension s))
  (solver: ModeSolver s)
  (t:R) : colvec (dimension s) :=
  let latest_switches := switches_until t s in
  match latest_switches with
  | nil => x_init
  | (latest_t, latest_m) :: tail =>
      let traj_at_last_switch := trajectory_on_switches s latest_switches x_init solver in
      match solver with
      | exist solver_func _ =>
          (solver_func latest_m latest_t traj_at_last_switch) t 
     end
  end.

End CaratheodoryTrajectory.

Section SwitchedSystemProperties.

Definition next_switch_prop 
  (t: R) 
  (switch: R * nat) 
  (s: SwitchedSystem)
  :=
  let (t1, m1) := switch in
  let is_switch := (is_switch_descriptor (switching_signal s)) in
  is_switch (t1, m1) /\
  t < t1 /\
  forall t2 m2,
   is_switch (t2, m2) ->
    (t2 <= t \/ t2 >= t1).

Lemma switches_next_previous:
forall t m t_next m_next s,
  is_switch_descriptor (switching_signal s) (t, m) ->
  next_switch_prop t (t_next, m_next) s ->
  previous_switch_spec t_next (t, m) 
    (is_switch_descriptor (switching_signal s)).
Proof.
  intros t m t_next m_next s Hdesc Hnext.
  unfold previous_switch_spec.
  unfold next_switch_prop in Hnext.
  split; try split; auto; apply Hnext.
Qed.

Lemma compute_prev_switch_next:
  forall s t m t_next m_next,
    is_switch_descriptor (switching_signal s) (t, m) ->
    next_switch_prop t (t_next, m_next) s ->
    compute_prev_switch (switching_signal s) t_next = (t, m).
Proof.
  intros s t m t_next m_next Htm_switch Hnext.
  pose proof compute_prev_switch_correct (switching_signal s) as Hcompute.
  specialize (Hcompute t_next).
  assert (Hexists: exists switch, previous_switch_spec t_next switch 
    (is_switch_descriptor (switching_signal s))). {
    exists (t, m).
    apply (switches_next_previous t m) in Hnext.
    apply Hnext.
    apply Htm_switch.
  }
  specialize (Hcompute Hexists (t, m)).
  destruct Hcompute as [Hcompute1 Hcompute2].
  apply Hcompute1.
  apply (switches_next_previous t m t_next m_next).
  apply Htm_switch.
  all: apply Hnext.
Qed.

Lemma trajectory_induction_lemma: 
  forall t t_next s initial_point mode_solver,
  (exists m m_next,
  is_switch_descriptor (switching_signal s) (t, m) /\
  next_switch_prop t (t_next, m_next) s) -> 
  let traj_f := trajectory s initial_point mode_solver in
  trajectory_on_switches s (switches_until t_next s) 
    initial_point mode_solver = traj_f t.
Proof.
  intros t t_next s initial_point mode_solver Hmmn.
  destruct Hmmn as [m Hmn].
  destruct Hmn as [m_next Hm].
  destruct Hm as [Hm1 Hm2].
  simpl.
  unfold switches_until.
  unfold trajectory.
  unfold switches_until.
  rewrite <- ((switch_count_increase (switching_signal s)) t m t_next m_next);
  auto.
  * unfold generate_switches; fold generate_switches.
    rewrite (compute_prev_switch_next _ t m t_next m_next); auto.
    unfold next_switch_prop in Hm2. apply Hm2.
  *  apply (switches_next_previous t m t_next m_next); auto.
Qed.

End SwitchedSystemProperties.

(*---------------------------------------------------------------------------*)

Section SwitchedSystemController.

Structure PeriodicController := MakePeriodicController {
  control_func: R -> nat;
  period: R;
  period_greater_zero: period > 0;
  start: R;
}.

Definition periodic_controller_switches_descriptor 
  (controller: PeriodicController)
  (switch: (R * nat)): Prop 
  :=
  exists n, 
    let t := (start controller) + (period controller) * INR n in
      (fst switch) = t /\
      (snd switch) = (control_func controller) t.

Theorem periodic_controller_one_switch_per_time:
  forall pc t m1 m2, 
    periodic_controller_switches_descriptor pc (t, m1) ->
    periodic_controller_switches_descriptor pc (t, m2) ->
    m1 = m2.
Proof.
  intros pc t m1 m2 Hm1 Hm2.
  unfold periodic_controller_switches_descriptor in Hm1.
  unfold periodic_controller_switches_descriptor in Hm2.
  destruct Hm1 as [tn1 Hm1].
  destruct Hm2 as [tn2 Hm2].
  destruct Hm1 as [H1 H2].
  destruct Hm2 as [H3 H4].
  simpl in H1; simpl in H2; simpl in H3; simpl in H4.
  rewrite <- H1 in H2. rewrite H3 in H2.
  rewrite H2. rewrite H4. reflexivity.    
Qed.

Definition periodic_controller_switch_count 
  (controller: PeriodicController)
  (t: R) 
  :=
  if Rle_lt_dec t (start controller) then
      0%nat
  else
      S (Z.abs_nat (floor1 ((t - (start controller))/(period controller)))).

Theorem periodic_controller_switch_count_increase:
  forall pc t1 m1 t2 m2,
    periodic_controller_switches_descriptor pc (t1, m1) ->
    periodic_controller_switches_descriptor pc (t2, m2) ->
    previous_switch_spec t2 (t1, m1) 
      (periodic_controller_switches_descriptor pc) ->
    S (periodic_controller_switch_count pc t1) = 
      periodic_controller_switch_count pc t2.
Proof.
  intros pc t1 m1 t2 m2 Hswitch1 Hswitch2 Hprevious.
  unfold previous_switch_spec in Hprevious.
  destruct Hprevious as [Hprevious1 Hprevious].
  destruct Hprevious as [Hprevious2 Hprevious3].
  unfold periodic_controller_switch_count.
  destruct Hswitch1 as [n1 Hswitch1].
  destruct Hswitch2 as [n2 Hswitch2].
  simpl in Hswitch1; simpl in Hswitch2.
  pose proof (Nat.lt_total (S n1) n2) as Hsplit.
  destruct Hsplit as [HSn1n2_lt|Hsplit]; 
  try destruct Hsplit as [HSn1n2_eq|Hn2Sn1_lt].
  * destruct n1; destruct n2; try lia.
    - specialize (Hprevious3 
        (start pc + period pc * INR 1) 
        ((control_func pc) (start pc + period pc * INR 1))).
      assert (Hmain: periodic_controller_switches_descriptor pc 
        ((start pc + period pc * INR 1), 
        ((control_func pc) (start pc + period pc * INR 1)))). {
          unfold periodic_controller_switches_descriptor.
          exists 1%nat.
          split; reflexivity.
      }
      apply Hprevious3 in Hmain.
      apply lt_INR in HSn1n2_lt.
      assert (lra_help1: INR 1 = 1). reflexivity.
      assert (lra_help0: INR 0 = 0). reflexivity.
      destruct Hmain; nra.
    - specialize (Hprevious3 (start pc + period pc * INR (S (S n1)))).
      specialize (Hprevious3 
        ((control_func pc) (start pc + period pc * INR (S (S n1))))).
      assert (Hmain: periodic_controller_switches_descriptor pc 
        ((start pc + period pc * INR (S (S n1))),
        (control_func pc) (start pc + period pc * INR (S (S n1))))). {
          unfold periodic_controller_switches_descriptor.
          exists (S (S n1)).
          split; reflexivity.
      }
      apply Hprevious3 in Hmain.
      rewrite S_INR in Hmain.
      apply lt_INR in HSn1n2_lt.
      rewrite S_INR in HSn1n2_lt at 1.
      nra.
  * destruct n1; symmetry in HSn1n2_eq.
    - rewrite HSn1n2_eq in Hswitch2.
      destruct Hswitch1 as [Ht1 Hm1].
      destruct Hswitch2 as [Ht2 Hm2].
      rewrite Ht1. rewrite Ht2. simpl.
      pose proof (period_greater_zero pc).
      do 2 (destruct Rle_lt_dec; try nra).
      rewrite Rmult_1_r.
      unfold Rminus.
      rewrite Rplus_assoc.
      rewrite (Rplus_comm (period _)).
      rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r.
      rewrite Rplus_0_l.
      unfold Rdiv.
      rewrite Rinv_r; try lra.
      rewrite (floor1_tech _ 0%Z); try lra.
      reflexivity.
    - rewrite HSn1n2_eq in Hswitch2.
      destruct Hswitch1 as [Ht1 Hm1].
      destruct Hswitch2 as [Ht2 Hm2].
      pose proof (period_greater_zero pc).
      destruct Rle_lt_dec; destruct Rle_lt_dec;
      try (
        rewrite S_INR in Ht1;
        rewrite S_INR in Ht2;
        pose proof (pos_INR n1);
        pose proof (pos_INR (S n1));
        nra
      ).
      rewrite Ht1. rewrite Ht2.
      unfold Rminus.
      do 2 rewrite Rplus_assoc.
      do 2 rewrite (Rplus_comm _ (- start _)).
      do 2 rewrite <- Rplus_assoc.
      rewrite Rplus_opp_r.
      do 2 rewrite Rplus_0_l.
      unfold Rdiv.
      do 2 rewrite (Rmult_comm (period _)).
      do 2 rewrite Rmult_assoc.
      rewrite Rinv_r; try lra.
      do 2 rewrite Rmult_1_r.
      do 2 rewrite abs_floor_INR.
      reflexivity.
  * destruct n1; destruct n2.
    - lra.
    - lia.
    - pose proof (pos_INR (S n1)).
      pose proof (period_greater_zero pc).
      simpl in Hswitch2.
      nra.
    - destruct Hswitch1 as [Ht1 Hm1].
      destruct Hswitch2 as [Ht2 Hm2].
      rewrite Ht1 in Hprevious2.
      rewrite Ht2 in Hprevious2.
      pose proof (period_greater_zero pc).
      pose proof (pos_INR (S n1)).
      pose proof (pos_INR (S n2)).
      apply lt_n_Sm_le in Hn2Sn1_lt.
      apply le_INR in Hn2Sn1_lt.
      nra.
Qed.

Theorem periodic_controller_switch_count_const:
  forall pc t1 t2,
    t1 < t2 ->
    (forall t m,
      periodic_controller_switches_descriptor pc (t, m) ->
      t < t1 \/ t >= t2) ->
    forall t' t'',
      t1 <= t' <= t2 ->
      t1 <= t'' <= t2 ->
      periodic_controller_switch_count pc t' = 
        periodic_controller_switch_count pc t''.
Proof.
  intros pc t1 t2 Ht1t2 Hinterval t' t'' Ht' Ht''.
  assert (Ht2_spec: t2 <= 
      (start pc) + INR (S (Z.abs_nat 
         (floor1 ((t1 - (start pc))/(period pc))))
        ) * (period pc)). 
  {
    unfold periodic_controller_switches_descriptor in Hinterval.
    specialize (Hinterval ((start pc) + (period pc) * (INR (S (Z.abs_nat 
      (floor1 ((t1 - (start pc))/(period pc))))
    )))).
    specialize (Hinterval ((control_func pc) ((start pc) + (period pc) * 
    INR (S (Z.abs_nat 
    (floor1 ((t1 - (start pc))/(period pc))))
    )))).
    destruct Hinterval.
    * exists (S (Z.abs_nat (floor1 ((t1 - (start pc))/(period pc))))).
      split; reflexivity.
    * remember (Z.abs_nat (floor1 ((t1 - (start pc))/(period pc)))) 
        as absnat.
      pose proof (abs_floor_Sn absnat) as Habsfloor.
      pose proof Heqabsnat as Heqabsnat_copy.
      apply Habsfloor in Heqabsnat.
      pose proof (period_greater_zero pc).
      apply Rle_div_l in Heqabsnat; try nra.
    * lra.
  }
  unfold periodic_controller_switch_count.
  destruct (Rle_lt_dec t1 (start pc)); destruct (Rle_lt_dec t2 (start pc)).
  - destruct Rle_lt_dec; destruct Rle_lt_dec; try nra; reflexivity.
  - specialize (Hinterval (start pc) ((control_func pc) (start pc))).
    assert (Htrivial_switch: periodic_controller_switches_descriptor pc 
      ((start pc), ((control_func pc) (start pc)))). {
      unfold periodic_controller_switches_descriptor.
      exists 0%nat. simpl.
      repeat rewrite Rmult_0_r.
      repeat rewrite Rplus_0_r.
      split; reflexivity.
    }
    apply Hinterval in Htrivial_switch.
    destruct Rle_lt_dec; destruct Rle_lt_dec; try lra.
  - lra.
  - assert (Hpositive_helper: 
      (t1 - start  pc) / period  pc > 0). {
        apply Rlt_div_l; try lra.
        apply Rlt_gt.
        apply Rinv_0_lt_compat.
        pose proof (period_greater_zero pc) as Hperiodgt0.
        apply Hperiodgt0.
    }
    assert (Ht1_spec: (start pc) + INR (Z.abs_nat 
            (floor1 ((t1 - (start pc))/(period pc)))) * (period pc) < t1). 
    {
      unfold periodic_controller_switches_descriptor in Hinterval.
      remember (Z.abs_nat (floor1 ((t1 - (start pc))/(period pc)))) 
        as absnat.
      specialize (Hinterval ((start pc) + INR (Z.abs_nat 
        (floor1 ((t1 - (start pc))/(period pc)))) * (period pc))).
      specialize (Hinterval ((control_func pc) 
        ((start pc) + INR (Z.abs_nat 
        (floor1 ((t1 - (start pc))/(period pc)))) * (period pc)))).
      destruct Hinterval.
      - exists (Z.abs_nat (floor1 ((t1 - (start pc))/(period pc)))); simpl.
        rewrite <- Heqabsnat.
        rewrite (Rmult_comm (INR absnat)).
        split; reflexivity.
      - rewrite Heqabsnat. apply H.
      - rewrite Rplus_comm.
        apply Rlt_minus_r.
        pose proof (period_greater_zero pc) as Hperiodgt0.
        rewrite Rlt_div_r; try lra.
        apply abs_floor_monotone; try apply Heqabsnat.
        apply Hpositive_helper.
  }
    destruct Rle_lt_dec; destruct Rle_lt_dec; try lra.
    do 2 f_equal.
    assert (Hrounding: forall num, num > 0 -> INR (Z.abs_nat (floor1 num)) = 
                                      IZR (floor1 num)). {
      intros num Hnum.
      rewrite INR_IZR_INZ.
      rewrite Zabs2Nat.id_abs.
      pose proof (floor1_positive num Hnum).
      apply Z.ge_le in H.
      apply Z.abs_eq_iff in H.
      rewrite H.
      reflexivity.
    }
    rewrite S_INR in Ht2_spec.
    rewrite (floor1_tech ((t' - start pc) / period pc) 
      (floor1 ((t1 - start pc) / period pc))).
    rewrite (floor1_tech ((t'' - start pc) / period pc) 
      (floor1 ((t1 - start pc) / period pc))).
    reflexivity.
    all: (
      rewrite <- Hrounding; try apply Hpositive_helper;
      remember (Z.abs_nat _) as floor1_t1;
      apply abs_floor_monotone in Heqfloor1_t1; try apply Hpositive_helper
    ).
    * nra.
    * apply Rle_div_l; try lra.
    * apply Rlt_div_r; try lra.
    * apply Rle_div_l; try lra.
Qed.

Definition periodic_controller_compute_prev_switch 
  (controller: PeriodicController) 
  (t: R) 
  :=
  if Rle_dec t (start controller) then 
    ((start controller), (control_func controller) (start controller))
  else  
    let switch_t := (start controller) + (period controller) *
    INR (Z.abs_nat (floor1 ((t - start controller) / period controller)))
    in
    (switch_t, (control_func controller) switch_t).

Theorem periodic_controller_compute_prev_switch_correct: 
forall pc t,
    (exists switch, previous_switch_spec t switch 
        (periodic_controller_switches_descriptor pc)) ->
    forall result,
      previous_switch_spec t result 
      (periodic_controller_switches_descriptor pc) <->
      periodic_controller_compute_prev_switch pc t = result.
Proof.
  intros pc t Hexists_prev result.
  induction result as [t_result m_result].
  pose proof (period_greater_zero pc) as Hperiodgt0.
  split.
  * intros Hprevious.
    unfold previous_switch_spec in Hprevious.
    unfold periodic_controller_compute_prev_switch.
    destruct (Rlt_dec t (start pc)) as [Ht_lt_start|Ht_ge_start].
    - destruct Hexists_prev as [exists_switch Hexists_prev]. 
      unfold previous_switch_spec in Hexists_prev.
      induction exists_switch as [t_exists m_exists].
      destruct Hexists_prev as [Hexists_prev1 Hexists_prev].
      destruct Hexists_prev as [Hexists_prev2 Hexists_prev3].
      unfold periodic_controller_switches_descriptor in Hexists_prev1.
      destruct Hexists_prev1 as [n_exists Hexists_prev1].
      destruct n_exists.
      * simpl in Hexists_prev1. rewrite Rmult_0_r in Hexists_prev1. lra.
      * pose proof (pos_INR (S n_exists)). 
        unfold fst in Hexists_prev1. nra. 
    - apply Rnot_lt_ge in Ht_ge_start.
      destruct Hprevious as [Hprevious1 Hprevious].
      unfold periodic_controller_switches_descriptor in Hprevious1.
      destruct Hprevious1 as [n_exists Hprevious1].
      destruct Rle_dec as [Ht_le_1|Ht_gt_1].
      * induction n_exists.
        - apply pair_equal_spec in Hprevious1. symmetry. 
          rewrite Rmult_0_r in Hprevious1.
          rewrite Rplus_0_r in Hprevious1.
          apply Hprevious1.
        - unfold fst in Hprevious1.
          rewrite S_INR in Hprevious1.
          pose proof (pos_INR n_exists).
          nra.
      * apply Rnot_le_gt in Ht_gt_1.
        pose proof (Nat.lt_total n_exists 
          (Z.abs_nat (floor1 
            ((t - start pc) / period pc)))) as Hsplit.
        destruct Hsplit as [Hn_lt_floor|Hsplit]; 
        try destruct Hsplit as [Hn_is_floor|Hfloor_lt_n].
        - destruct Hprevious as [Hprevious2 Hprevious3].
          remember (Z.abs_nat (floor1 
          ((t - start pc) / period pc))) as absnat.
          specialize (Hprevious3 ((start pc) + (period pc) * INR absnat)).
          specialize (Hprevious3 ((control_func pc) 
          ((start pc) + (period pc) * INR absnat))).
          assert (Hisswitch: periodic_controller_switches_descriptor pc (
          ((start pc) + (period pc) * INR absnat),
          ((control_func pc) 
          ((start pc) + (period pc) * INR absnat)))). {
            unfold periodic_controller_switches_descriptor.
            exists (Z.abs_nat (floor1 
            ((t - start pc) / period pc))).
            split; rewrite <- Heqabsnat; reflexivity.
          }
          apply Hprevious3 in Hisswitch.
          unfold fst in Hprevious1; unfold snd in Hprevious1.
          apply lt_INR in Hn_lt_floor.
          destruct Hisswitch; try lra.
          * apply abs_floor_monotone in Heqabsnat; try nra.
          * apply abs_floor_monotone in Heqabsnat.
            - destruct Heqabsnat as [Heq1 Heq2].
              apply Rlt_div_r in Heq2; try lra.
            - apply Rlt_div_l; try lra.
              apply Rlt_gt.
              apply Rinv_0_lt_compat.
              apply Hperiodgt0.  
        - unfold fst in Hprevious1; unfold snd in Hprevious1.
          destruct Hprevious1 as [Ht_result Hm_result].
          rewrite Hm_result; rewrite Ht_result.
          rewrite Hn_is_floor.
          reflexivity.
        - unfold fst in Hprevious1; unfold snd in Hprevious1.
          destruct Hprevious as [Hprevious2 Hprevious3].
          apply lt_le_S in Hfloor_lt_n.
          remember (Z.abs_nat _) as absnat.
          destruct Hprevious1 as [Ht_result Hm_result].
          apply le_INR in Hfloor_lt_n.
          pose proof Heqabsnat as Ht_lt_Sabsnat.
          apply abs_floor_Sn in Ht_lt_Sabsnat.
          apply (Rplus_eq_compat_l (Ropp (start pc))) in Ht_result.
          rewrite <- Rplus_assoc in Ht_result.
          rewrite Rplus_opp_l in Ht_result.
          rewrite Rplus_0_l in Ht_result.
          rewrite Rplus_comm in Ht_result.
          apply (Rmult_eq_compat_l (/ period pc)) in Ht_result.
          rewrite <- Rmult_assoc in Ht_result.
          rewrite Rinv_l in Ht_result; try lra.
          rewrite Rmult_1_l in Ht_result.
          rewrite Rmult_comm in Ht_result.
          rewrite <- Ht_result in Hfloor_lt_n.
          apply Rle_ge in Hfloor_lt_n.
          apply (Rmult_ge_compat_r (period pc)) in Hfloor_lt_n; try lra.
          apply (Rmult_le_compat_r (period pc)) in Ht_lt_Sabsnat; try lra.
          rewrite Rmult_assoc in Hfloor_lt_n.
          rewrite Rinv_l in Hfloor_lt_n; try lra.
          unfold Rdiv in Ht_lt_Sabsnat.
          rewrite Rmult_assoc in Ht_lt_Sabsnat.
          rewrite Rinv_l in Ht_lt_Sabsnat; try lra.
  * intros Hresult.
    unfold periodic_controller_compute_prev_switch in Hresult.
    destruct Rle_dec as [Ht_le_start | Ht_gt_start].
    - destruct Hexists_prev as [switch_prev Hexists_prev].
      unfold previous_switch_spec in Hexists_prev.
      induction switch_prev as [t_prev m_prev].
      destruct Hexists_prev as [Hprev1 Hprev].
      destruct Hprev as [Hprev2 Hprev3].
      unfold periodic_controller_switches_descriptor in Hprev1.
      destruct Hprev1 as [n Hexists_n].
      unfold fst in Hexists_n.
      pose proof (pos_INR n).
      nra.
    - apply pair_equal_spec in Hresult.
      destruct Hresult as [Ht_result Hm_result].
      apply Rnot_le_gt in Ht_gt_start.
      unfold previous_switch_spec.
      remember (Z.abs_nat (floor1 
          ((t - start pc) / period pc))) as absnat.
      split; try split.
      * unfold periodic_controller_switches_descriptor.
        exists absnat.
        unfold fst; unfold snd. split.
        - symmetry; apply Ht_result.
        - symmetry; apply Hm_result.
      * apply abs_floor_monotone in Heqabsnat.
        - destruct Heqabsnat as [Heq1 Heq2].
          apply (Rplus_eq_compat_l (Ropp (start pc))) in Ht_result.
          rewrite <- Rplus_assoc in Ht_result.
          rewrite Rplus_opp_l in Ht_result.
          rewrite Rplus_0_l in Ht_result.
          rewrite Rplus_comm in Ht_result.
          apply (Rmult_eq_compat_l (/ period pc)) in Ht_result.
          rewrite <- Rmult_assoc in Ht_result.
          rewrite Rinv_l in Ht_result; try lra.
          rewrite Rmult_1_l in Ht_result.
          rewrite Rmult_comm in Ht_result.
          rewrite Ht_result in Heq2.
          unfold Rminus in Heq2; unfold Rdiv in Heq2.
          apply (RIneq.Rplus_lt_reg_r (Ropp (start pc))).
          nra.
        - apply Rlt_div_l; try lra.
          apply Rlt_gt.
          apply Rinv_0_lt_compat.
          apply Hperiodgt0.
      * intros t' m' Hswitch'.
        unfold periodic_controller_switches_descriptor in Hswitch'.
        destruct Hswitch' as [n Hn].
        unfold fst in Hn; unfold snd in Hn.
        destruct Hn as [Ht' Hm'].
        destruct (Rle_lt_dec (INR n) (INR absnat))
          as [Hle|Hlt].
        * nra.
        * right.
          apply INR_lt in Hlt.
          apply lt_le_S in Hlt.
          apply le_INR in Hlt.
          apply abs_floor_Sn in Heqabsnat.
          apply (Rplus_eq_compat_l (Ropp (start pc))) in Ht'.
          rewrite <- Rplus_assoc in Ht'.
          rewrite Rplus_opp_l in Ht'.
          rewrite Rplus_0_l in Ht'.
          rewrite Rplus_comm in Ht'.
          apply (Rmult_eq_compat_l (/ period pc)) in Ht'.
          rewrite <- Rmult_assoc in Ht'.
          rewrite Rinv_l in Ht'; try lra.
          rewrite Rmult_1_l in Ht'.
          rewrite Rmult_comm in Ht'.
          apply Rle_ge.
          apply (Rplus_le_reg_r (Ropp (start pc))).
          apply (Rmult_le_reg_r (/ period pc)).
          - apply Rinv_0_lt_compat.
            apply Hperiodgt0.
          - nra.
Qed.

Theorem periodic_controller_respects_start:
  forall ps t,
      t <= (start ps) -> 
      (periodic_controller_switch_count ps) t = 0%nat.
Proof.
  intros ps t Ht.
  unfold periodic_controller_switch_count.
  destruct Rle_lt_dec; try lra.
  reflexivity.
Qed.

Definition periodic_controller_to_switching_signal 
  (controller: PeriodicController): InductiveSwitchingSignal
  :=
  BuildSwitchingSignal  
    (periodic_controller_switches_descriptor controller)
    (periodic_controller_one_switch_per_time controller)
    (periodic_controller_switch_count controller)
    (periodic_controller_switch_count_increase controller)
    (periodic_controller_switch_count_const controller)
    (periodic_controller_compute_prev_switch controller)
    (periodic_controller_compute_prev_switch_correct controller)
    (start controller)
    (periodic_controller_respects_start controller).

Theorem periodic_controller_modes_helper:
  forall ps mode_count,
    (forall t, ((control_func ps) t < mode_count)%nat) ->
    forall t m, 
      (is_switch_descriptor 
          (periodic_controller_to_switching_signal ps)) (t,m) -> 
      (m < mode_count)%nat.
Proof.
  intros ps mode_count Hcontrol_func t m Hswitch.
  simpl in Hswitch.
  unfold periodic_controller_switches_descriptor in Hswitch.
  destruct Hswitch as [n Hswitch].
  unfold fst in Hswitch; unfold snd in Hswitch.
  destruct Hswitch as [Ht Hm].
  rewrite Hm.
  apply Hcontrol_func.
Qed.
  
End SwitchedSystemController.

(*---------------------------------------------------------------------------*)

Section SwitchedSystemExample.

Definition mode0 (x: colvec 2) := [[2], [1]].

Definition mode1 (x: colvec 2) := [[-2], [-1]].

Definition example_modes := [mode0; mode1].

Parameter observable_trajectory: R -> colvec 2.

Definition example_control_func (current_x: colvec 2): nat :=
  let x1 := coeff_colvec 0 current_x 0 in
  let x2 := coeff_colvec 0 current_x 1 in  
  match cond_positivity (x2 + 2 * x1) with
    | true  => 1%nat
    | false => 0%nat
  end.

Definition example_period := 1.

Definition example_t0 := 0.

Theorem example_period_greater_zero:
  1 > 0.
Proof.
  lra.
Qed.

Definition example_controller :=
  MakePeriodicController 
    (fun t => example_control_func (observable_trajectory t))   
    example_period example_period_greater_zero example_t0.

Definition example_switching_signal :=
  periodic_controller_to_switching_signal example_controller.

Theorem example_signal_selects_modes: 
  forall t m, 
    (is_switch_descriptor example_switching_signal) (t,m) -> 
    (m < length example_modes)%nat.
Proof.
  apply periodic_controller_modes_helper.
  intros t.
  unfold control_func.
  unfold example_controller.
  unfold example_control_func.
  destruct cond_positivity; compute; try lia.
Qed.

Definition example_switched_system :=
    BuildSwitchedSystem 2 
      example_modes 
      example_switching_signal
      example_signal_selects_modes.

End SwitchedSystemExample.

Section ExampleModeSolver.

Definition mode0_solution (t: R) (x_init: colvec 2): colvec 2 := 
  [[2*t + coeff_colvec 0 x_init 0], [t + coeff_colvec 0 x_init 1]].

Definition mode1_solution (t: R) (x_init: colvec 2): colvec 2 := 
  [[-2*t + coeff_colvec 0 x_init 0], [-t + coeff_colvec 0 x_init 1]].

Definition example_mode_solver_implementation
  (mode_idx: nat)
  (t_from: R)
  (x_t_from: colvec 2): R -> colvec 2 :=
  match mode_idx with
  | 0 => (fun t => mode0_solution (t - t_from) x_t_from)
  | 1 => (fun t => mode1_solution (t - t_from) x_t_from)
  | _ => (fun t => null_vector 2)
  end.

Theorem example_mode_solver_correct: 
  forall mode_idx t_from x_t_from,
    is_mode_solution
      example_switched_system mode_idx t_from x_t_from
      (example_mode_solver_implementation mode_idx t_from x_t_from).
Proof.
  unfold is_mode_solution.
  intros mode_idx t_from x_t_from mode t d Hmodeidx Hmode Ht.
  unfold example_mode_solver_implementation.
  destruct mode_idx.
  * rewrite <- (mk_matrix_bij 0 (mode0_solution _ _)).
    unfold mode0_solution.
    apply mk_matrix_ext.
    intros i j Hi Hj. 
    rewrite Hmode.
    unfold example_switched_system.
    unfold modes.
    unfold example_modes. 
    unfold mode0.
    unfold RInt_multi.
    simpl.
    unfold coeff_colvec.
    unfold mk_colvec.
    simpl in Hi.
    rewrite coeff_mat_bij.
    rewrite RInt_const.
    destruct i. destruct j; try lia.
    - compute. rewrite Rmult_comm. reflexivity.
    destruct i; destruct j; try lia.
    - rewrite <- (Rmult_1_r (t - t_from)) at 1.
      compute. rewrite Rmult_1_r. reflexivity.
      compute in Hi. lia.
      apply Hj.
  * destruct mode_idx.
    rewrite <- (mk_matrix_bij 0 (mode1_solution _ _)).
    unfold mode1_solution.
    apply mk_matrix_ext.
    intros i j Hi Hj.
    unfold RInt_multi.
    rewrite Hmode.
    unfold example_switched_system.
    unfold modes.
    unfold example_modes. 
    unfold mode1.
    unfold coeff_colvec.
    unfold mk_colvec.
    simpl. simpl in Hi.
    rewrite coeff_mat_bij.
    rewrite RInt_const.
    destruct i; destruct j; try lia.
    - compute. rewrite Rmult_comm. reflexivity.
    destruct i; try lia.
    - rewrite <- (Rmult_1_r (- (t - t_from))).
      compute. 
      rewrite <- Ropp_mult_distr_l.
      rewrite <- Ropp_mult_distr_r.
      reflexivity. lia. lia. 
    simpl in Hmodeidx. lia.
Qed.

Definition example_mode_solver: ModeSolver example_switched_system := 
  exist _ example_mode_solver_implementation example_mode_solver_correct.    

End ExampleModeSolver.

Section ExampleTrajectoryProofs.

Definition initial_point: colvec 2 := [[1], [0.5]].  

Theorem trajectory_until_0: 
    forall t, (t < 0) ->
      trajectory example_switched_system initial_point example_mode_solver t 
        = initial_point.
Proof.
    intros t Ht_lt_0.
    unfold trajectory.
    unfold switches_until. simpl.
    unfold periodic_controller_switch_count.
    unfold start. unfold example_controller. simpl.
    unfold example_t0.
    destruct Rle_lt_dec; try lra.
    reflexivity.
Qed.

Theorem trajectory_0_1: 
  forall t,
    let traj_f := 
      trajectory example_switched_system 
        initial_point example_mode_solver in
    observable_trajectory = traj_f ->
    (0 <= t <= 1) ->
    traj_f t = [[-2 * t + 1], [-t + 0.5]].
Proof.
  intros t traj_t Hobservable Ht.
  unfold traj_t.
  unfold trajectory.
  unfold switches_until.
  unfold example_switched_system; simpl.
  unfold periodic_controller_switch_count; simpl.
  unfold example_t0; simpl.
  destruct Rle_lt_dec.
  * rewrite (Rle_antisym t 0); try lra.
    unfold generate_switches.
    unfold initial_point.
    do 3 f_equal; lra.
  * assert (Habs: Z.abs_nat (floor1 t) = 0%nat). {
        unfold Z.abs_nat.
        rewrite (floor1_tech _ 0%Z); try lra.
        reflexivity.
    }
    rewrite Rminus_0_r.
    rewrite Rdiv_1.
    rewrite Habs. simpl.
    unfold periodic_controller_compute_prev_switch; simpl.
    unfold example_t0; simpl.
    destruct Rle_dec; try lra.
    unfold example_mode_solver_implementation.
    unfold mode1_solution.
    simpl.
    rewrite Rminus_0_r.
    rewrite Rplus_0_l.
    rewrite Rdiv_1.
    rewrite Rmult_1_l.
    unfold example_control_func.
    unfold cond_positivity.
    destruct Rle_dec as [Hle|Hnle].
    * rewrite Habs. rewrite Rminus_0_r. 
      reflexivity.
    * rewrite Habs in Hnle.
      simpl in Hnle.
      rewrite Hobservable in Hnle.
      unfold traj_t in Hnle.
      unfold trajectory in Hnle.
      unfold switches_until in Hnle.
      pose proof (
        signal_respects_t0 (switching_signal example_switched_system)
      ) as Ht0.
      specialize (Ht0 0).
      assert (Hzero_t0: 0 <= t0 (switching_signal example_switched_system)). {
        simpl.
        unfold example_t0.
        lra.
      }
      apply Ht0 in Hzero_t0.
      rewrite Hzero_t0 in Hnle.
      unfold generate_switches in Hnle.
      unfold initial_point in Hnle.
      compute in Hnle.
      lra.
Qed.

Theorem trajectory_1_2: 
    forall t,
      let traj_t := trajectory example_switched_system
            initial_point example_mode_solver in
      observable_trajectory = traj_t ->
      (1 < t <= 2) ->
      traj_t t = [[2 * t - 3], [t - 1.5]].
Proof.
    intros t traj_t Hobservable Ht.
    unfold traj_t. unfold trajectory.
    unfold switches_until at 1. simpl.
    unfold periodic_controller_switch_count. simpl.
    unfold example_t0.
    repeat (destruct Rle_lt_dec; try lra).
    assert (Habs: Z.abs_nat (floor1 t) = 1%nat). {
      unfold Z.abs_nat. 
      rewrite (floor1_tech _ 1); try lra.
      compute. reflexivity. 
    }
    rewrite Rminus_0_r. rewrite Rdiv_1.
    rewrite Habs. unfold generate_switches. simpl.
    unfold periodic_controller_compute_prev_switch. simpl.
    unfold example_t0.
    destruct Rle_dec; try lra.
    unfold example_mode_solver_implementation.
    assert (Hobstraj_pos: cond_positivity 
      (coeff_colvec 0 (observable_trajectory 1) 1 + 
      2 * coeff_colvec 0 (observable_trajectory 1) 0) = false). {
      unfold cond_positivity.
      destruct Rle_dec as [Hn|Hr]; try reflexivity. 
      * exfalso.
        rewrite Hobservable in Hn.
        unfold traj_t in Hn.
        rewrite trajectory_0_1 in Hn.
        compute in Hn; try lra.
        apply Hobservable. lra. 
    }
    repeat (rewrite Rminus_0_r; rewrite Rplus_0_l;
    rewrite Rmult_1_l; rewrite Rdiv_1).
    rewrite Habs. simpl.
    unfold example_control_func.
    rewrite Hobstraj_pos.
    unfold switches_until. simpl.
    unfold periodic_controller_switch_count; simpl.
    unfold example_t0.
    destruct Rle_lt_dec; try lra.
    rewrite Rminus_0_r. rewrite Rdiv_1.
    rewrite Habs. unfold generate_switches. simpl.
    unfold periodic_controller_compute_prev_switch.
    unfold example_controller. simpl.
    unfold example_t0.
    repeat (rewrite Rminus_0_r; rewrite Rplus_0_l;
    rewrite Rmult_1_l; rewrite Rdiv_1).
    rewrite Hobservable.
    unfold traj_t.
    unfold example_control_func.
    rewrite trajectory_0_1; try apply Hobservable; try lra.
    unfold initial_point. unfold coeff_colvec. unfold mk_colvec. 
    repeat (rewrite coeff_mat_bij; try simpl; try lia).
    destruct Rle_dec; try lra.
    repeat rewrite Habs.
    rewrite trajectory_0_1; try apply Hobservable; try lra.
    unfold INR; fold INR.
    destruct Rle_dec; try lra.
    rewrite Rminus_0_r. rewrite Rdiv_1.
    rewrite Rplus_0_l. 
    destruct cond_positivity; try lra.
    assert (Hrev_INR: 1 = INR 1). reflexivity.
    rewrite Hrev_INR. rewrite abs_floor_INR. simpl.
    rewrite Rmult_0_r.
    rewrite trajectory_0_1; try apply Hobservable; try lra.
    unfold initial_point. unfold coeff_colvec. unfold mk_colvec. 
    repeat (rewrite coeff_mat_bij; try simpl; try lia).
    unfold cond_positivity.
    destruct Rle_dec.
    * unfold example_mode_solver_implementation.
      unfold mode0_solution.
      unfold mode1_solution.
      f_equal. f_equal. compute. lra.
      f_equal. f_equal. compute. lra.
    * compute in n2; lra.
    simpl; lra. 
Qed.

Definition limit_cycle_point: colvec 2 := 
  [[-1], [-0.5]].  

Lemma example_induction_support: 
  forall n,
    exists m m_next : nat,
      is_switch_descriptor (switching_signal example_switched_system) 
        (INR n, m) /\
      next_switch_prop (INR n) (INR (S n), m_next) 
        example_switched_system.
Proof.
  intros n.
  exists (example_control_func (observable_trajectory (INR n))).
  exists (example_control_func (observable_trajectory (INR (S n)))).
  split.
  * simpl.
    unfold periodic_controller_switches_descriptor; simpl.
    exists n.
    split; unfold example_t0; unfold example_period; try lra.
    rewrite Rplus_0_l. rewrite Rmult_1_l. reflexivity.
  * unfold next_switch_prop.
    split; try split.
    - simpl.
      exists (S n).
      unfold example_controller.
      unfold start; unfold period; unfold control_func; simpl.
      split; unfold example_t0; unfold example_period; try lra.
      rewrite Rplus_0_l. rewrite Rmult_1_l. reflexivity.
    - apply lt_INR; lia.
    - intros t2 m2 Hswitch.
      simpl in Hswitch.
      unfold periodic_controller_switches_descriptor in Hswitch.
      destruct Hswitch as [n_x Hswitch].    
      unfold fst in Hswitch; unfold snd in Hswitch.
      destruct Hswitch as [Ht2 Hm2].
      rewrite Ht2.
      unfold example_controller; unfold start; unfold period.
      unfold example_t0; unfold example_period.
      rewrite Rplus_0_l; rewrite Rmult_1_l.
      pose proof (Nat.le_gt_cases n_x n) as Hsplit.
      destruct Hsplit.
      - left. apply le_INR. lia.
      - right. apply Rle_ge. apply le_INR. lia.
Qed.

Theorem example_limit_cycle:
  forall i,
    let traj_t := trajectory example_switched_system 
          initial_point example_mode_solver in
    observable_trajectory = traj_t ->
    (traj_t (INR (2 * i)%nat) = initial_point /\
     traj_t (INR (2 * i + 1)%nat) = limit_cycle_point).
Proof.
  Arguments INR _ : simpl nomatch.
  intros i traj_t Hobs_traj. unfold traj_t.
  induction i.
  * split; 
    (
      rewrite trajectory_0_1; try (simpl; lra);
      try unfold initial_point; try unfold limit_cycle_point;
      unfold mk_colvec;
      try (rewrite Hobs_traj; reflexivity);
      do 3 (try f_equal);
      compute; lra
    ).
  * destruct IHi as [IH1 IH2].
    assert (Halg: (2 * S i = S (2 * i + 1))%nat). lia.
    assert (Halg2: forall i, (S (i + S (i + 0) + 1) = 2 * S i + 1)%nat). lia.
    assert (Halg3: forall i, (S (i + S (i + 0)) = 2 * S i)%nat). lia.
    assert (Hgoal1: traj_t (INR (2 * S i)) = initial_point). {
      unfold traj_t.
      rewrite Halg.
      destruct i.
      - rewrite trajectory_1_2; try apply Hobs_traj; try (simpl; lra).
        unfold initial_point.
        do 3 (try f_equal); compute; lra.
      - unfold trajectory.
        unfold switches_until at 1.
        unfold example_switched_system at 2; simpl.
        rewrite <- S_INR.
        unfold periodic_controller_switch_count.
        destruct Rle_lt_dec.
        * rewrite S_INR in r.
          pose proof (pos_INR (S (i + S (i + 0) + 1))).
          simpl in r; unfold example_t0 in r. 
          lra.
        * simpl.
          unfold example_t0; unfold example_period.
          rewrite Rdiv_1; rewrite Rminus_0_r.
          rewrite <- S_INR.
          rewrite abs_floor_INR.
          unfold periodic_controller_compute_prev_switch.
          destruct Rle_dec.
          - rewrite Nat.add_1_r in r0.
            rewrite Nat.add_0_r in r0.
            repeat rewrite S_INR in r0.
            simpl in r0; unfold example_t0 in r0.
            pose proof (pos_INR (i + S i)).
            lra.
          - simpl.
            unfold example_t0; unfold example_period.
            rewrite Rplus_0_l; rewrite Rmult_1_l; rewrite Rdiv_1;
            rewrite Rminus_0_r; rewrite <- S_INR.
            rewrite abs_floor_INR.
            rewrite (trajectory_induction_lemma (INR (2 * S i + 1)));
            try apply example_induction_support.
            rewrite Hobs_traj.
            unfold traj_t.
            rewrite Halg2.
            rewrite IH2. 
            assert (Hcontr: example_control_func limit_cycle_point = 0%nat). {
              unfold example_control_func.
              unfold limit_cycle_point.
              unfold coeff_colvec. unfold mk_colvec.
              repeat (rewrite coeff_mat_bij; try lia).
              unfold cond_positivity. 
              destruct Rle_dec.
              * compute in r0; lra.
              * reflexivity.
            }
            rewrite Hcontr.
            unfold example_mode_solver_implementation.
            unfold mode0_solution.
            unfold limit_cycle_point.
            unfold coeff_colvec. unfold mk_colvec. 
            repeat (rewrite coeff_mat_bij; try lia).
            unfold initial_point.
            do 3 (try f_equal); compute; lra.
    }
    unfold traj_t in Hgoal1.
    split.
    * apply Hgoal1.
    * unfold trajectory.
      rewrite Nat.add_1_r.
      unfold switches_until at 1; simpl.
      rewrite Halg3.
      unfold periodic_controller_switch_count.
      destruct Rle_lt_dec.
      - unfold start in r; unfold example_controller in r.
        unfold example_t0 in r.
        pose proof (pos_INR (2 * S i)); lra.
      - simpl.
        unfold periodic_controller_compute_prev_switch.
        rewrite Halg3.
        destruct Rle_dec.
        * rewrite Halg in r0.
          repeat (rewrite S_INR in r0).
          pose proof (pos_INR (2 * i + 1)).
          unfold start in r0; unfold example_controller in r0;
          unfold example_t0 in r0; lra. 
        * simpl.
          unfold example_t0; unfold example_period.
          rewrite Rplus_0_l; rewrite Rmult_1_l; rewrite Rdiv_1;
          rewrite Rminus_0_r; rewrite <- S_INR.
          rewrite abs_floor_INR.
          rewrite Halg3.
          rewrite (trajectory_induction_lemma (INR (2 * S i)));
            try apply example_induction_support.
          rewrite Hobs_traj.
          unfold traj_t.
          rewrite Hgoal1.
          assert (Hcontr: example_control_func initial_point = 1%nat). {
            unfold example_control_func.
            unfold initial_point.
            unfold cond_positivity.
            destruct Rle_dec.
            * reflexivity.
            * compute in n0; lra.
          }
          rewrite Hcontr.
          unfold example_mode_solver_implementation.
          unfold mode1_solution.
          unfold limit_cycle_point.
          unfold initial_point.
          do 3 (try f_equal).
          all: rewrite S_INR; compute; lra.
Qed.

End ExampleTrajectoryProofs.


  

