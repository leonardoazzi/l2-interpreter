open OUnit2
open L2

let test_small_step_binop_aritmetico _ =
  let e = L2.Binop(L2.Sum, L2.Num 2, L2.Num 3), L2.empty_mem in
  let e', _ = L2.step e in
  assert_equal (L2.Num 5) e'

let test_small_step_binop_relacional _ =
  let e = L2.Binop(L2.Lt, L2.Num 2, L2.Num 3), L2.empty_mem in
  let e', _ = L2.step e in
  assert_equal (L2.Bool true) e'

let test_small_step_if_true _ =
  let e = L2.If(L2.Bool true, L2.Num 1, L2.Num 2), L2.empty_mem in
  let e', _ = L2.step e in
  assert_equal (L2.Num 1) e'

let test_small_step_if_false _ =
  let e = L2.If(L2.Bool false, L2.Num 1, L2.Num 2), L2.empty_mem in
  let e', _ = L2.step e in
  assert_equal (L2.Num 2) e'

let test_small_step_let_binding _ =
  let e = L2.Let("x", L2.Num 10, L2.Binop(L2.Sum, L2.Id "x", L2.Num 5)), L2.empty_mem in
  let e', _ = L2.step e in
  assert_equal (L2.Binop(L2.Sum, L2.Num 10, L2.Num 5)) e'

let test_small_step_new_allocation _ =
  let e = L2.New(L2.Num 42), L2.empty_mem in
  let e', mem' = L2.step e in
  match e' with
  | L2.Memloc l -> assert_equal (Some (L2.Num 42)) (L2.lookup_memory mem' l)
  | _ -> assert_failure "Expected Memloc"

let test_small_step_assignment _ =
  let mem = L2.update_memory L2.empty_mem 0 (L2.Num 1) in
  let e = L2.Atr(L2.Memloc 0, L2.Num 99), mem in
  let e', mem' = L2.step e in
  assert_equal L2.Unit e';
  assert_equal (Some (L2.Num 99)) (L2.lookup_memory mem' 0)

let test_small_step_derref _ =
  let mem = L2.update_memory L2.empty_mem 0 (L2.Num 123) in
  let e = L2.Derref(L2.Memloc 0), mem in
  let e', _ = L2.step e in
  assert_equal (L2.Num 123) e'

let test_typeinfer_int_literal _ =
  assert_equal L2.TyInt (L2.typeinfer (L2.Num 42))

let test_typeinfer_bool_literal _ =
  assert_equal L2.TyBool (L2.typeinfer (L2.Bool false))

let test_typeinfer_binop_aritmetico _ =
  assert_equal L2.TyInt (L2.typeinfer (L2.Binop(L2.Sum, L2.Num 1, L2.Num 2)))

let test_typeinfer_binop_relacional _ =
  assert_equal L2.TyBool (L2.typeinfer (L2.Binop(L2.Lt, L2.Num 1, L2.Num 2)))

let test_typeinfer_binop_logico _ =
  assert_equal L2.TyBool (L2.typeinfer (L2.Binop(L2.And, L2.Bool true, L2.Bool false)))

let test_typeinfer_if_correto _ =
  assert_equal L2.TyInt (L2.typeinfer (L2.If(L2.Bool true, L2.Num 1, L2.Num 2)))

let test_typeinfer_if_tipos_diferentes _ =
  assert_raises (L2.TypeError "") (fun () -> L2.typeinfer (L2.If(L2.Bool true, L2.Num 1, L2.Bool false)))

let test_typeinfer_if_condicao_nao_booleana _ =
  assert_raises (L2.TypeError "") (fun () -> L2.typeinfer (L2.If(L2.Num 1, L2.Num 2, L2.Num 3)))

let test_typeinfer_binop_tipos_errados _ =
  assert_raises (L2.TypeError "") (fun () -> L2.typeinfer (L2.Binop(L2.Sum, L2.Bool true, L2.Num 2)))