(*this file was generated automatically*)
    From Coq Require Import Strings.String.
    From Coq Require Import Strings.Ascii.

    From Coq Require Import Reals.
    From Coquelicot Require Import Coquelicot.
    From CoqSwitchedSystems Require Import piecewise_affine neuron_functions matrix_extensions.
    From CoqSwitchedSystems Require Import neural_networks.
    From CoqSwitchedSystems Require Import string_to_number.
(*  From CoqSwitchedSystems Require Import transpose_mult_matrix. *)
  
  Open Scope nat_scope.

Definition net_zero_weight := mk_matrix 4 4 (fun x y: nat =>
   match x, y with
  | 3, 3 => real_of_string "1.2689796686172485"%string
  | 3, 2 => real_of_string "-0.024546626955270767"%string
  | 3, 1 => real_of_string "-0.07672476768493652"%string
  | 3, 0 => real_of_string "-1.0973708629608154"%string
  | 2, 3 => real_of_string "1.7820576429367065"%string
  | 2, 2 => real_of_string "0.09723371267318726"%string
  | 2, 1 => real_of_string "-0.6021440625190735"%string
  | 2, 0 => real_of_string "-1.8165631294250488"%string
  | 1, 3 => real_of_string "0.18348246812820435"%string
  | 1, 2 => real_of_string "-0.11282628774642944"%string
  | 1, 1 => real_of_string "-0.2123798280954361"%string
  | 1, 0 => real_of_string "-0.3578670918941498"%string
  | 0, 3 => real_of_string "0.06511475145816803"%string
  | 0, 2 => real_of_string "0.034822672605514526"%string
  | 0, 1 => real_of_string "-0.19164104759693146"%string
  | 0, 0 => real_of_string "0.07890868186950684"%string
  | _, _ => real_of_string "0.0"%string
  end)
  .

Definition net_zero_bias := mk_colvec 4 (fun x: nat =>
   match x with
  | 3 => real_of_string "0.6186808943748474"%string
  | 2 => real_of_string "-0.12135478109121323"%string
  | 1 => real_of_string "-0.169892817735672"%string
  | 0 => real_of_string "0.6908497214317322"%string
  | _ => real_of_string "0.0"%string
  end)
  .

Definition net_two_weight := mk_matrix 4 2 (fun x y: nat =>
   match x, y with
  | 3, 3 => real_of_string "0.0"%string
  | 3, 2 => real_of_string "0.0"%string
  | 3, 1 => real_of_string "1.3887839317321777"%string
  | 3, 0 => real_of_string "-0.8598666191101074"%string
  | 2, 3 => real_of_string "0.0"%string
  | 2, 2 => real_of_string "0.0"%string
  | 2, 1 => real_of_string "0.22159084677696228"%string
  | 2, 0 => real_of_string "-0.040348511189222336"%string
  | 1, 3 => real_of_string "0.0"%string
  | 1, 2 => real_of_string "0.0"%string
  | 1, 1 => real_of_string "0.23322077095508575"%string
  | 1, 0 => real_of_string "0.39218416810035706"%string
  | 0, 3 => real_of_string "0.0"%string
  | 0, 2 => real_of_string "0.0"%string
  | 0, 1 => real_of_string "-0.40546542406082153"%string
  | 0, 0 => real_of_string "1.0268224477767944"%string
  | _, _ => real_of_string "0.0"%string
  end)
  .

Definition net_two_bias := mk_colvec 2 (fun x: nat =>
   match x with
  | 1 => real_of_string "-0.5949365496635437"%string
  | 0 => real_of_string "-0.18491101264953613"%string
  | _ => real_of_string "0.0"%string
  end)
  .



Definition onnxGemm__six_ := NNLinear (transpose net_two_weight) (scalar_mult (real_of_string "1") net_two_bias) (NNOutput (output_dim:=2)).

Definition input := NNReLU onnxGemm__six_.

Definition onnxGemm__zero_ := NNLinear (transpose net_zero_weight) (scalar_mult (real_of_string "1") net_zero_bias) input.