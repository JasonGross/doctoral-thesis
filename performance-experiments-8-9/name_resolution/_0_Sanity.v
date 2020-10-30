Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.name_resolution.
Goal True. let tac := ltac:(fun _ => uconstr:(I)) in run0 Sanity tac. Abort.
