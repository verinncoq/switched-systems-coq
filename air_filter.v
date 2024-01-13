From Coq Require Import List Reals Lia Lra.
Import ListNotations.
From Coquelicot Require Import Coquelicot.
From CoqSwitchedSystems Require Import matrix_extensions switched_systems.

Open Scope R_scope.
Import MatrixNotations.

Section VerifiedAirFilterControl.

Definition toReal (c: colvec 1): R := coeff_colvec 0 c 0.
Definition toColvec (c: R): colvec 1 := [[c]].

Variables (Inflow: R) (Outflow: R) (Filtered: R).

Definition air_filter_model (C: colvec 1) (FullOutflow: R): colvec 1
    := toColvec (Inflow - FullOutflow * toReal C).

Definition mode_filter_off (C: colvec 1): colvec 1 
    := air_filter_model C Outflow.
Definition mode_filter_on (C: colvec 1): colvec 1
    := air_filter_model C (Outflow + Filtered).

Parameter Cobserved: R -> colvec 1.

Variable (Target: R).

Definition air_filter_controller_func (C: colvec 1): nat :=
    if cond_positivity (Target - toReal C) then 0 (*off*) else 1 (*on*).

Definition period := 0.1. (*6 minutes*)

Lemma period_gt_0:
    period > 0.
Proof.
    unfold period; lra.
Qed.

Definition air_filter_controller :=
    MakePeriodicController
        (fun t => air_filter_controller_func (Cobserved t))
        period period_gt_0 0.  

Definition air_filter_switching_signal :=
    periodic_controller_to_switching_signal air_filter_controller.

Theorem air_filter_switching_signal_selects_modes: 
    forall t m, 
        (is_switch_descriptor air_filter_switching_signal) (t,m) -> 
        (m < length example_modes)%nat.
Proof.
    apply periodic_controller_modes_helper.
    intros t.
    unfold control_func.
    unfold air_filter_controller.
    unfold air_filter_controller_func.
    destruct cond_positivity; compute; try lia.
Qed.

Definition air_filter_switched_system: SwitchedSystem :=
    BuildSwitchedSystem 1
      [mode_filter_off; mode_filter_on] 
      air_filter_switching_signal
      air_filter_switching_signal_selects_modes.

Definition general_mode_solution 
    (t: R) (t_init: R) (C_init: colvec 1) (FullOutflow: R)
    : colvec 1 
    := 
    toColvec (((toReal C_init - Inflow/FullOutflow)/exp (- FullOutflow * t_init )) * 
                exp (- FullOutflow * t) + (Inflow/FullOutflow)).

Definition mode_off_solution (t: R) (t_init: R) (C_init: colvec 1): colvec 1 := 
    general_mode_solution t t_init C_init Outflow.

Definition mode_on_solution (t: R) (t_init: R) (C_init: colvec 1): colvec 1 := 
    general_mode_solution t t_init C_init (Outflow + Filtered).

Definition air_filter_mode_solver_implementation
    (mode_idx: nat) (t_from: R) (x_t_from: colvec 1)
    : R -> colvec 1 
    :=
    match mode_idx with
    | 0 => (fun t => mode_off_solution t t_from x_t_from)
    | 1 => (fun t => mode_on_solution t t_from x_t_from)
    | _ => (fun t => null_vector 1)
    end.

Hypothesis (Hin_gt_0: Inflow > 0).
Hypothesis (Hout_gt_0: Outflow > 0).
Hypothesis (Hfiltered_gt0: Filtered > 0).
Hypothesis (Hfilter_useful: Inflow / (Outflow + Filtered) <= Target).

Lemma integration_air_filter_model:
    forall outflow t t_from x_t_from,
        outflow > 0 ->
        general_mode_solution t t_from x_t_from outflow =
            (RInt_multi 
                (fun tau =>
                    air_filter_model 
                        (general_mode_solution tau t_from x_t_from outflow)
                        outflow
            ) t_from t + x_t_from)%M.
Proof.
    intros outflow t t_from x_t_from Houtflow.
    unfold general_mode_solution.
    unfold air_filter_model.
    unfold toColvec; unfold toReal.
    unfold RInt_multi.
    unfold Mplus.
    unfold mk_colvec; unfold mk_matrix; unfold mk_Tn.
    do 2 (apply pair_equal_spec; split; try reflexivity).
    unfold coeff_colvec; unfold coeff_mat; unfold coeff_Tn; simpl.
    apply (Rplus_eq_reg_r (Ropp (fst (fst x_t_from)))).
    rewrite (Rplus_comm (plus (RInt _ _ _) _) (Ropp (fst _))).
    rewrite (plus_comm (G:=R_AbsRing) (RInt _ _ _) _).
    rewrite (plus_assoc (G:=R_AbsRing) (Ropp _) (fst _) (RInt _ _ _)).
    rewrite Rplus_opp_l.
    rewrite (plus_zero_l (G:=R_AbsRing)).
    symmetry; apply is_RInt_unique.
    rewrite <- (Rplus_0_l (_ + _ + _)).
    rewrite <- (Rplus_opp_r (scal (t - t_from) Inflow)).
    rewrite Rplus_assoc.
    unfold Rminus.
    apply (is_RInt_plus (V:=R_CompleteNormedModule)).
    * apply (is_RInt_const (V:=R_CompleteNormedModule)).
    rewrite <- (Ropp_involutive (- scal _ _ + _)).
    apply (is_RInt_opp (V:=R_CompleteNormedModule)).
    rewrite <- (Rmult_1_l (Ropp (Ropp _ + _))).
    rewrite <- (Rinv_r outflow); try lra.
    rewrite Rmult_assoc.
    apply (is_RInt_scal (V:=R_CompleteNormedModule)).
    rewrite Ropp_plus_distr.
    rewrite Ropp_involutive.
    rewrite Rmult_plus_distr_l.
    assert (Hhelp: forall (r r1 r2:R), r * scal r1 r2 = scal r1 (r2 * r)). {
    intros r r1 r2. unfold scal; simpl; unfold mult; simpl; lra.
    }
    rewrite Hhelp.
    rewrite (Rplus_comm (scal _ _) _).
    apply (is_RInt_plus (V:=R_CompleteNormedModule)).
    * rewrite Ropp_mult_distr_r_reverse.
    rewrite Ropp_mult_distr_l.
    assert (Hhelp2: forall (r1 r2 r3: R), r1 + r2 + Ropp r3 = r1 - (r3 - r2)). 
    intros r1 r2 r3. unfold Rminus. lra.
    rewrite Hhelp2.
    rewrite <- (Rmult_1_r (Rminus (fst _) (Inflow/outflow))).
    unfold Rminus at 2.
    rewrite <- (Rinv_l (exp (- outflow * t_from))); try apply exp_neq_0.
    rewrite <- Rmult_assoc.
    unfold Rdiv.
    rewrite <- Rmult_minus_distr_l.
    rewrite <- Rmult_assoc.
    rewrite (Rmult_comm (- / _) _).
    assert (Hhelp3: forall (r1 r2 r3 r4:R), r1 * r2 * r3 * r4 = r1 * r2 * (r3 * r4)). 
        intros r1 r2 r3 r4. lra.
    rewrite Hhelp3.
    apply (is_RInt_scal (V:=R_CompleteNormedModule)); try apply exp_neq_0.
    rewrite Rmult_minus_distr_l.
    apply (is_RInt_derive (V:=R_CompleteNormedModule)
            (fun t => - / outflow * exp (- outflow * t))).
    - intros x Hx.
        auto_derive.
        * reflexivity.
        * rewrite Rmult_1_r.
        rewrite <- Rmult_assoc.
        rewrite <- Rinv_opp.
        rewrite Rinv_l; try lra.
    - intros x Hx.
      apply continuous_exp_comp.
      assert (Hhelp4: Rmult (- outflow) = scal (- outflow)).
        unfold scal. simpl. unfold mult. simpl. reflexivity.
      rewrite Hhelp4. 
      apply (continuous_scal_r (K:=R_AbsRing) _ (fun (y:R) => y)).
      apply continuous_id.
    * apply (is_RInt_const (V:=R_CompleteNormedModule)).
Qed. 

Theorem air_filter_mode_solver_correct: 
    forall mode_idx t_from x_t_from,
        is_mode_solution
        air_filter_switched_system mode_idx t_from x_t_from
        (air_filter_mode_solver_implementation mode_idx t_from x_t_from).
Proof.
    unfold is_mode_solution.
    intros mode_idx t_from x_t_from mode t d Hmodeidx Hmode Htfrom.
    unfold air_filter_mode_solver_implementation.
    destruct mode_idx.
    * rewrite Hmode; simpl.
      unfold mode_filter_off.
      unfold mode_off_solution.
      apply integration_air_filter_model; try lra.
    destruct mode_idx.
    * rewrite Hmode; simpl.
      unfold mode_filter_on.
      unfold mode_on_solution.
      apply integration_air_filter_model; try lra.
    * simpl in Hmodeidx. lia. 
Qed.

Definition air_filter_mode_solver: ModeSolver air_filter_switched_system := 
  exist _ air_filter_mode_solver_implementation air_filter_mode_solver_correct.

Definition in_invariant_region (x: colvec 1) : Prop :=
    toReal x <= toReal (mode_off_solution period 0 (toColvec Target)).

Lemma in_invariant_region_mode_off:
    forall C_prev t_prev t,
        t_prev >= 0 ->
        t_prev <= t ->
        t <= t_prev + period ->
        toReal C_prev <= Target ->
        in_invariant_region (C_prev) ->
        in_invariant_region (mode_off_solution t t_prev C_prev).
Proof.
    intros C_prev t_prev t Ht_prev Ht2 Ht Htarget HC_prev.
    unfold in_invariant_region.
    unfold in_invariant_region in HC_prev.
    remember (toReal C_prev) as C_prev_R.
    destruct (Rle_dec C_prev_R (Inflow/Outflow));
    destruct (Rle_dec Target (Inflow/Outflow)).
    * unfold mode_off_solution.
      unfold general_mode_solution.
      rewrite <- HeqC_prev_R; unfold toReal; unfold toColvec.
      unfold coeff_colvec; unfold coeff_mat; unfold coeff_Tn; simpl.
      apply Rplus_le_compat_r.
      unfold Rdiv.
      repeat rewrite <- exp_Ropp.
      repeat rewrite Rmult_assoc.
      repeat rewrite <- exp_plus.
      repeat rewrite Ropp_mult_distr_r.
      repeat rewrite <- Rmult_plus_distr_l.
      apply Ropp_le_cancel.
      repeat rewrite Ropp_mult_distr_l.
      apply Rmult_le_compat.
      - lra.
      - left. apply exp_pos.
      - lra.
      - rewrite Rplus_comm.
        rewrite Ropp_0.
        rewrite Rplus_0_r.
        destruct Ht.
        - left. 
          apply exp_increasing.
          repeat rewrite <- Ropp_mult_distr_l.
          apply Ropp_lt_contravar.
          apply Rmult_lt_compat_l; try lra.
        - right.
          f_equal.
          apply Rmult_eq_compat_l.
          lra. 
    * unfold mode_off_solution.
      unfold general_mode_solution.
      rewrite <- HeqC_prev_R; unfold toReal; unfold toColvec.
      unfold coeff_colvec; unfold coeff_mat; unfold coeff_Tn; simpl.
      apply Rplus_le_compat_r.
      unfold Rdiv.
      repeat rewrite <- exp_Ropp.
      repeat rewrite Rmult_assoc.
      repeat rewrite <- exp_plus.
      repeat rewrite Ropp_mult_distr_r.
      repeat rewrite <- Rmult_plus_distr_l.
      apply (Rle_trans _ 0 _).
      - apply Rmult_le_0_r.
        * lra.
        * left; apply exp_pos.
      - apply Rmult_le_pos.
        * lra.
        * left; apply exp_pos.
    * lra.
    * apply (Rle_trans _ C_prev_R _); try apply HC_prev.
      unfold mode_off_solution.
      unfold general_mode_solution.
      rewrite <- HeqC_prev_R; unfold toReal; unfold toColvec.
      unfold coeff_colvec; unfold coeff_mat; unfold coeff_Tn; simpl.
      apply Rle_minus_r.
      unfold Rdiv.
      repeat rewrite <- exp_Ropp.
      repeat rewrite Rmult_assoc.
      repeat rewrite <- exp_plus.
      repeat rewrite Ropp_mult_distr_r.
      repeat rewrite <- Rmult_plus_distr_l.
      assert (Hhelp: forall r1 r2, 
          r1 > 0 -> r2 <= 1 -> r1 * r2 <= r1). 
          intros r1 r2 H1. nra.
      apply Hhelp.
      - lra.
      - rewrite <- exp_0.
        destruct Ht2.
        * left.
          apply exp_increasing.
          nra.
        * right.
          f_equal.
          nra.  
Qed.

Lemma in_invariant_region_mode_on:
    forall C_prev t_prev t,
        t_prev >= 0 ->
        t_prev <= t ->
        t <= t_prev + period ->
        Target < toReal C_prev ->
        in_invariant_region C_prev ->
        in_invariant_region (mode_on_solution t t_prev C_prev).
Proof.
    intros C_prev t_prev t Ht_prev Ht2 Ht Htarget HC_prev.
    unfold in_invariant_region in HC_prev.
    unfold in_invariant_region.
    apply (Rle_trans _ (toReal C_prev) _); try apply HC_prev.
    unfold mode_on_solution.
    unfold general_mode_solution.
    remember (toReal C_prev) as C_prev_R.
    unfold toColvec; unfold toReal;
    unfold coeff_colvec; unfold coeff_mat; unfold coeff_Tn; simpl.
    apply Rle_minus_r.
    unfold Rdiv.
    rewrite Rmult_assoc.
    rewrite <- exp_Ropp.
    rewrite <- exp_plus.
    rewrite Ropp_mult_distr_r.
    rewrite <- Rmult_plus_distr_l.
    assert (Hhelp: forall r1 r2, 
          r1 > 0 -> r2 <= 1 -> r1 * r2 <= r1). 
          intros r1 r2 H1. nra.
    apply Hhelp.
    * lra.
    * rewrite <- exp_0.
      destruct Ht2.
      - left.
        apply exp_increasing.
        nra.
      - right.
        f_equal.
        nra.
Qed.

Lemma air_filter_controller_func_helper_degenerate:
    forall c x,
        (S (S c)) = air_filter_controller_func x -> False.
Proof.
    intros c x.
    pose proof air_filter_switching_signal_selects_modes as Hselects.
    unfold air_filter_controller_func.
    destruct cond_positivity; intros H; inversion H.
Qed.

Lemma air_filter_induction_support: 
    forall n,
        exists m m_next : nat,
        is_switch_descriptor (switching_signal air_filter_switched_system) 
            (period * INR n, m) /\
        next_switch_prop (period * INR n) (period * INR (S n), m_next) 
            air_filter_switched_system.
Proof.
    intros n.
    exists (air_filter_controller_func (Cobserved (period * INR n))).
    exists (air_filter_controller_func (Cobserved (period * INR (S n)))).
    split.
    * simpl.
        unfold periodic_controller_switches_descriptor; simpl.
        exists n.
        split; unfold period; try lra.
        rewrite Rplus_0_l. reflexivity.
    * unfold next_switch_prop.
        split; try split.
        - unfold is_switch_descriptor.
          unfold switching_signal.
          unfold air_filter_switched_system.
          unfold air_filter_switching_signal.
          unfold periodic_controller_to_switching_signal.
          unfold periodic_controller_switches_descriptor.
          exists (S n).
          unfold fst; unfold snd. unfold air_filter_controller.
          unfold start; unfold switched_systems.period; unfold control_func.
          split; unfold period; try lra.
          rewrite Rplus_0_l. reflexivity.
        - apply Rmult_lt_compat_l; try (unfold period; lra).
          apply lt_INR; lia.
        - intros t2 m2 Hswitch.
          simpl in Hswitch.
          unfold periodic_controller_switches_descriptor in Hswitch.
          destruct Hswitch as [n_x Hswitch].    
          unfold fst in Hswitch; unfold snd in Hswitch.
          destruct Hswitch as [Ht2 Hm2].
          rewrite Ht2.
          unfold air_filter_controller; unfold start;
          unfold switched_systems.period; unfold period.
          rewrite Rplus_0_l.
          pose proof (Nat.le_gt_cases n_x n) as Hsplit.
          destruct Hsplit.
        - left. apply Rmult_le_compat_l; try lra. apply le_INR. lia.
        - right. apply Rle_ge. apply Rmult_le_compat_l; try lra. apply le_INR. lia.
Qed.

Lemma air_filter_switches_invariant_specialization:
    forall i C_init,
    let filter_traj_t := 
        trajectory air_filter_switched_system C_init 
        air_filter_mode_solver in
        Cobserved = filter_traj_t ->
        in_invariant_region C_init ->
            (in_invariant_region (filter_traj_t (period * INR i))).
Proof.
    assert (Halg1: forall r1 r2, r1 > 0 -> r1 * r2 / r1 = r2). {
        intros r1 r2 Hr1. unfold Rdiv. rewrite Rmult_comm.
        rewrite <- Rmult_assoc. rewrite Rinv_l. rewrite Rmult_1_l. 
        reflexivity. lra.
    }
    intros i C_init filter_traj_t Hobserved Hinit.
    induction i.
    * unfold filter_traj_t.
      unfold trajectory.
      unfold switches_until.
      rewrite Rmult_0_r; simpl.
      unfold air_filter_controller; simpl.
      unfold periodic_controller_switch_count; simpl.
      destruct Rle_lt_dec; try lra.
      unfold generate_switches.
      apply Hinit.
    * unfold filter_traj_t.
      unfold trajectory.
      rewrite (trajectory_induction_lemma (period * INR i)); 
          try apply air_filter_induction_support.
      fold filter_traj_t.
      unfold switches_until.
      unfold switch_count.
      unfold switching_signal.
      unfold air_filter_switched_system at 1.
      unfold air_filter_switching_signal.
      unfold periodic_controller_to_switching_signal.
      unfold periodic_controller_switch_count.
      unfold start; unfold air_filter_controller.
      unfold switched_systems.period.
      destruct Rle_lt_dec as [Hl|Hr].
      - unfold period in Hl.
        rewrite S_INR in Hl. 
        pose proof (pos_INR (i)) as Hpos.
        lra.
      - unfold generate_switches.
        unfold compute_prev_switch at 1.
        unfold air_filter_switched_system at 1.
        unfold switching_signal.
        unfold air_filter_switching_signal.
        unfold periodic_controller_to_switching_signal.
        unfold periodic_controller_compute_prev_switch.
        unfold start. unfold air_filter_controller.
        unfold switched_systems.period.
        unfold control_func.
        destruct Rle_dec; try lra.
        rewrite Rplus_0_l.
        rewrite Rminus_0_r.
        rewrite Halg1; try (unfold period; lra).
        rewrite abs_floor_INR.
        rewrite Hobserved.
        unfold air_filter_mode_solver.
        remember (air_filter_controller_func _) as control_decision.
        destruct control_decision.
        * unfold air_filter_controller_func in Heqcontrol_decision.
          unfold cond_positivity in Heqcontrol_decision.
          destruct Rle_dec as [Htraj_target|H]; try inversion Heqcontrol_decision.
          apply Rminus_le_0 in Htraj_target.
          unfold air_filter_mode_solver_implementation.
          apply in_invariant_region_mode_off.
          - unfold period; pose proof (pos_INR i) as H. lra.
          - rewrite S_INR. rewrite Rmult_plus_distr_l. 
            unfold period. lra.  
          - rewrite S_INR; lra.
          - apply Htraj_target.
          - apply IHi.
        destruct control_decision.
        * unfold air_filter_controller_func in Heqcontrol_decision.
          unfold cond_positivity in Heqcontrol_decision.
          destruct Rle_dec as [H|Htraj_target]; try inversion Heqcontrol_decision.
          apply Rnot_le_lt in Htraj_target.
          apply Rminus_lt in Htraj_target.
          unfold air_filter_mode_solver_implementation.
          apply in_invariant_region_mode_on.
          - unfold period; pose proof (pos_INR i); lra.
          - unfold period; rewrite S_INR; lra.
          - rewrite S_INR; lra.
          - apply Htraj_target.
          - apply IHi.
        * apply air_filter_controller_func_helper_degenerate 
            in Heqcontrol_decision.
          contradiction.
Qed.

Lemma rounding_helper1:
    forall t,
        t <= period * INR (S (Z.abs_nat (floor1 (t / period)))).
Proof.
    intro t.
    apply (Rmult_le_reg_r (/ period)); try (unfold period; lra).
    rewrite (Rmult_comm (_ * _) _).
    rewrite <- Rmult_assoc.
    rewrite Rinv_l; try (unfold period; lra).
    rewrite Rmult_1_l.
    unfold Rdiv.
    apply abs_floor_Sn.
    reflexivity.
Qed.

Lemma rounding_helper2:
    forall t,
        t <= period * INR (Z.abs_nat (floor1 (t / period))) + period.
Proof.
    intros t.
    pose proof (rounding_helper1 t) as Hmain.
    rewrite S_INR in Hmain.
    rewrite Rmult_plus_distr_l in Hmain.
    rewrite Rmult_1_r in Hmain.
    apply Hmain.
Qed.

Lemma rounding_helper3:
    forall r,
        r > 0 ->
        INR (Z.abs_nat (floor1 r)) <= r.
Proof.
    intros r Hr.
    remember (Z.abs_nat (floor1 r)) as n.
    pose proof (abs_floor_monotone n r Hr Heqn) as Hmain.
    destruct Hmain as [H1 H2].
    left; apply H2.
Qed.

Lemma switches_until_helper:
    forall t,
        t > 0 ->
        switches_until t air_filter_switched_system =
        switches_until (period * INR (S (Z.abs_nat (floor1 (t / period))))) 
            air_filter_switched_system.
Proof.
    Arguments INR _ : simpl nomatch.
    intros t Ht.
    unfold switches_until.
    unfold switch_count; simpl.
    unfold periodic_controller_switch_count.
    unfold start; unfold air_filter_controller.
    unfold switched_systems.period.
    destruct Rle_lt_dec; try lra.
    pose proof (rounding_helper1 t).
    destruct Rle_lt_dec; try lra.
    repeat rewrite Rminus_0_r.
    unfold generate_switches; fold generate_switches.
    unfold compute_prev_switch.
    unfold switching_signal.
    unfold air_filter_switched_system at 1 3.
    unfold air_filter_switching_signal.
    unfold periodic_controller_to_switching_signal.
    unfold periodic_controller_compute_prev_switch.
    unfold start. unfold air_filter_controller.
    unfold control_func.
    unfold switched_systems.period.
    do 2 (destruct Rle_dec; try lra).
    repeat rewrite Rplus_0_l; repeat rewrite Rminus_0_r.
    unfold Rdiv.
    repeat rewrite (Rmult_comm (_ * _) (/ period)).
    rewrite <- Rmult_assoc.
    rewrite Rinv_l; try (unfold period; lra).
    rewrite Rmult_1_l.
    rewrite abs_floor_INR.
    reflexivity.
Qed.

Theorem air_filter_keeps_concentration: 
    forall C_init,
        let filter_traj_t := 
            trajectory air_filter_switched_system C_init 
                air_filter_mode_solver in
            Cobserved = filter_traj_t ->
            in_invariant_region C_init ->
            forall t, t > 0 -> 
                in_invariant_region (filter_traj_t t).
Proof.
    intros C_init filter_traj_t Hobserved Hinit t Ht.
    unfold filter_traj_t.
    unfold trajectory.
    unfold switches_until at 1.
    unfold switch_count.
    unfold switching_signal.
    unfold air_filter_switched_system at 1.
    unfold air_filter_switching_signal at 1.
    unfold periodic_controller_to_switching_signal.
    destruct (periodic_controller_switch_count _ t) eqn:Hswitch_count.
    * simpl; apply Hinit.
    * unfold generate_switches; fold generate_switches.
      unfold compute_prev_switch.
      unfold switching_signal.
      unfold air_filter_switched_system at 1.
      unfold air_filter_switching_signal at 1.
      unfold periodic_controller_to_switching_signal.
      unfold air_filter_controller at 1.
      unfold periodic_controller_compute_prev_switch.
      unfold start; unfold control_func; unfold switched_systems.period.
      destruct Rle_dec; try lra.
      unfold air_filter_mode_solver at 1.
      unfold air_filter_mode_solver_implementation.
      rewrite Rplus_0_l. rewrite Rminus_0_r.
      remember (air_filter_controller_func _) as control_decision.
      destruct control_decision; try destruct control_decision.
      - rewrite switches_until_helper; try lra.
        rewrite (trajectory_induction_lemma 
            (period * INR (Z.abs_nat (floor1 (t / period))))); 
            try apply air_filter_induction_support.
        unfold air_filter_controller_func in Heqcontrol_decision.
        unfold cond_positivity in Heqcontrol_decision.
        destruct Rle_dec as [Htraj|H]; try inversion Heqcontrol_decision.
        apply Rminus_le_0 in Htraj.
        rewrite Hobserved in Htraj.
        unfold filter_traj_t in Htraj.
        remember (trajectory air_filter_switched_system _ _ _) as C_prev.
        apply in_invariant_region_mode_off.
        * unfold period.
          pose proof (pos_INR (Z.abs_nat (floor1 (t/0.1)))) as H.
          lra.
        * apply (Rmult_le_reg_r (/ period)); try (unfold period; lra).
          rewrite (Rmult_comm (_ * _) _).
          rewrite <- Rmult_assoc.
          rewrite Rinv_l; try (unfold period; lra).
          rewrite Rmult_1_l.
          unfold Rdiv.
          apply rounding_helper3.
          unfold period. lra.
        * apply rounding_helper2.
        * apply Htraj.
        * rewrite HeqC_prev.
          apply air_filter_switches_invariant_specialization.
          apply Hobserved.
          apply Hinit.  
      - rewrite switches_until_helper; try lra.
        rewrite (trajectory_induction_lemma 
            (period * INR (Z.abs_nat (floor1 (t / period))))); 
          try apply air_filter_induction_support.
        pose proof (air_filter_switches_invariant_specialization 
            (Z.abs_nat (floor1 (t / period)))
            C_init Hobserved Hinit) as Hinvariant.
        remember (trajectory air_filter_switched_system _ _ _) as C_prev.
        apply in_invariant_region_mode_on.
        * unfold period; pose proof (pos_INR (Z.abs_nat (floor1 (t/0.1)))); lra.
        * apply (Rmult_le_reg_r (/ period)); try (unfold period; lra).
          rewrite (Rmult_comm (_ * _) _).
          rewrite <- Rmult_assoc.
          rewrite Rinv_l; try (unfold period; lra).
          rewrite Rmult_1_l.
          unfold Rdiv.
          apply rounding_helper3.
          unfold period. lra.
        * apply rounding_helper2.
        * rewrite Hobserved in Heqcontrol_decision.
          unfold filter_traj_t in Heqcontrol_decision.
          rewrite <- HeqC_prev in Heqcontrol_decision.
          unfold air_filter_controller_func in Heqcontrol_decision.
          unfold cond_positivity in Heqcontrol_decision.
          destruct Rle_dec; try inversion Heqcontrol_decision.
          lra.
        * apply Hinvariant.
      - apply air_filter_controller_func_helper_degenerate 
            in Heqcontrol_decision.
        contradiction.
Qed.

End VerifiedAirFilterControl.