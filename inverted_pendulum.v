From Coq Require Import List Reals Lia Lra.
Import ListNotations.
From Coquelicot Require Import Coquelicot.
From CoqSwitchedSystems Require Import matrix_extensions pendnet neural_networks switched_systems.

Open Scope R_scope.

Section InvertedPendulumProblem.

Definition pendulum_continuous (state: colvec 4) (F: R): colvec 4 :=
    let theta := coeff_colvec 0 state 0 in
    let omega := coeff_colvec 0 state 1 in 
    let x     := coeff_colvec 0 state 2 in
    let v     := coeff_colvec 0 state 3 in
    let w_new := (9.8 * sin(theta) + cos(theta)*((-F) - 0.05*omega*sin(theta)/1.1))
    /(0.5*(4/3 - (0.1 * cos(theta) * cos(theta))/(1.1))) in
    [[omega], 
     [w_new], 
     [v], 
     [(F + 0.05*(omega*omega*sin(theta) - w_new*cos(theta)))/1.1]].

Definition mode_0 (state: colvec 4): colvec 4 :=
    pendulum_continuous state (-10).

Definition mode_1 (state: colvec 4): colvec 4 :=
    pendulum_continuous state 10.

Definition pendulum_modes := [mode_0; mode_1].

Parameter pendulum_observable_trajectory : R -> colvec 4.

Definition pendulum_neural_network := onnxGemm__zero_.

Definition pendulum_neural_controller (state: colvec 4): nat :=
    let nn_out := nn_eval pendulum_neural_network state in
    match nn_out with
    | Some vec_out =>
        let mode_0_score := coeff_colvec 0 vec_out 0 in
        let mode_1_score := coeff_colvec 0 vec_out 1 in
        if Rle_dec mode_1_score mode_0_score then 0%nat else 1%nat
    | None => 0%nat
    end.

Definition pendulum_period := 0.02.

Definition pendulum_t0 := 0.

Theorem pendulum_period_greater_zero:
    0.02 > 0.
Proof.
    lra.
Qed.

Definition pendulum_controller :=
    MakePeriodicController 
    (fun t => pendulum_neural_controller (pendulum_observable_trajectory t))   
    pendulum_period pendulum_period_greater_zero pendulum_t0.

Definition pendulum_switching_signal :=
    periodic_controller_to_switching_signal pendulum_controller.

Theorem pendulum_controller_selects_modes: 
    forall t m, 
    (is_switch_descriptor pendulum_switching_signal) (t,m) -> 
    (m < length pendulum_modes)%nat.
Proof.
    apply periodic_controller_modes_helper.
    intros t.
    unfold control_func.
    unfold pendulum_controller.
    unfold pendulum_neural_controller.
    destruct nn_eval.
    destruct Rle_dec.
    all: compute; lia.
Qed.

Definition pendulum_switched_system :=
  BuildSwitchedSystem 4 
    pendulum_modes 
    pendulum_switching_signal
    pendulum_controller_selects_modes.
    
Theorem inverted_pendulum_correct: 
    forall initial_point t mode_solver,
        let pendulum_traj_t := 
            trajectory pendulum_switched_system initial_point mode_solver in
        (* Initial point configuration *)
        let theta_0 := coeff_colvec 0 initial_point 0 in
        let omega_0 := coeff_colvec 0 initial_point 1 in 
        let x_0     := coeff_colvec 0 initial_point 2 in
        let v_0     := coeff_colvec 0 initial_point 3 in
        abs theta_0 <= 0.05 ->
        abs omega_0 <= 0.05 ->
        abs x_0     <= 0.05 ->
        abs v_0     <= 0.05 ->
        (* Trajectory conditions *)
        t >= 0 ->
        let theta_t := coeff_colvec 0 (pendulum_traj_t t) 0 in
        let x_t     := coeff_colvec 0 (pendulum_traj_t t) 2 in
        abs theta_t <= 0.209 /\
        abs x_t     <= 2.4.
Proof.
Admitted.  

End InvertedPendulumProblem.