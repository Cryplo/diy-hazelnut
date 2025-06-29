open Alcotest;

let () =
  run(
    "Hazelnut_tests",
    [
      ("erase_exp", Test_erase_exp.erase_exp_tests),
      ("syn", Test_syn.syn_tests),
      ("syn_action", Test_syn_action.syn_action_tests),
      ("type_action", Test_type_action.type_action_tests),
    ],
  );
