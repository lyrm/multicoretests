(** Sequential tests of spsc_queue *)

open QCheck
open STM

module Spsc_queue = Lockfree.Spsc_queue

module WSDConf =
struct
  type cmd =
    | Push of int  (* use int for now *)
    | Pop
    | Size [@@deriving show { with_path = false }]
  type state = int list
  type sut = int Spsc_queue.t

  let arb_cmd _s =
    let int_gen = Gen.nat in
    QCheck.make ~print:show_cmd
      (Gen.oneof
         [Gen.map (fun i -> Push i) int_gen;
          Gen.return Size
         ])

  let stealer_cmd _s =
    QCheck.make ~print:show_cmd
      (Gen.oneof
         [Gen.return Pop;
          Gen.return Size])

  let init_state  = []
  let size_exponent = 8
  let max_size =  Int.shift_left 1 size_exponent
  let init_sut () = Spsc_queue.create ~size_exponent:size_exponent
  let cleanup _   = ()

  let next_state c s = match c with
    | Push i   -> if List.length s = max_size then s else i::s
    | Pop      ->
       (match List.rev s with
        | []    -> s
        | _::s' -> List.rev s')
    | Size     -> s

  let precond _ _ = true

  let run c q = match c with
    | Push i   -> Res (result unit exn, protect (Spsc_queue.push q) i)
    | Pop      -> Res (option int, Spsc_queue.pop q)
    | Size     -> Res (int, Spsc_queue.size q)

  let postcond c (s : state) res = match c, res with
    | Push _, Res ((Result (Unit, Exn),_),res) ->
       (if List.length s = max_size  then res = Error Spsc_queue.Full
        else res = Ok ())
    | Pop,    Res ((Option Int, _), res) ->
        (match List.rev s with
         | []   -> res = None
         | j::_ -> res = Some j)
    | Size,  Res ((Int, _),res) -> res = List.length s
    | _,_ -> false
end

module WSDT = STM.Make(WSDConf)


(*
;;
QCheck_runner.run_tests ~verbose:true [
    WSDT.agree_test     ~count:1_000 ~name:"sequential spsc_queue test";
    WSDT.agree_test_par ~count:1_000 ~name:"parallel spsc_queue test (w/repeat)";
    agree_test_par      ~count:1_000 ~name:"parallel spsc_queue test (w/non_det module)";
  ]
 *)

let agree_prop_par =
  (fun (seq_pref,owner,stealer) ->
    assume (WSDT.cmds_ok WSDConf.init_state (seq_pref@owner));
    assume (WSDT.cmds_ok WSDConf.init_state (seq_pref@stealer));
    let sut = WSDConf.init_sut () in
    let pref_obs = WSDT.interp_sut_res sut seq_pref in
    let sema = Semaphore.Binary.make false in
    let stealer_dom = Domain.spawn (fun () -> Semaphore.Binary.release sema; WSDT.interp_sut_res sut stealer) in
    while not (Semaphore.Binary.try_acquire sema) do Domain.cpu_relax() done;
    let own_obs = WSDT.interp_sut_res sut owner in
    let stealer_obs = Domain.join stealer_dom in
    let res = WSDT.check_obs pref_obs own_obs stealer_obs WSDConf.init_state in
    let () = WSDConf.cleanup sut in
    res ||
      Test.fail_reportf "  Results incompatible with linearized model:\n\n%s"
      @@ Util.print_triple_vertical ~center_prefix:false show_res
           (List.map snd pref_obs,
            List.map snd own_obs,
            List.map snd stealer_obs))

let shrink_triple =
  let (<+>) = Iter.(<+>) in
  (fun (seq,p1,p2) ->
    (Shrink.(triple list list list) (seq,p1,p2))
    <+> (match p1 with [] -> Iter.empty | c1::c1s -> Iter.return (seq@[c1],c1s,p2))
    <+> (match p2 with [] -> Iter.empty | c2::c2s -> Iter.return (seq@[c2],p1,c2s)))

let arb_triple =
  let seq_len,par_len = 20,15 in
  let seq_pref_gen = WSDT.gen_cmds_size WSDConf.init_state (Gen.int_bound seq_len) in
  let triple_gen = Gen.(seq_pref_gen >>= fun seq_pref ->
                        let spawn_state = List.fold_left (fun st c -> WSDConf.next_state c st) WSDConf.init_state seq_pref in
                        let owner_gen = WSDT.gen_cmds_size spawn_state (Gen.int_bound par_len) in
                        let stealer_gen = list_size (int_bound par_len) (WSDConf.stealer_cmd spawn_state).gen in
                        map2 (fun owner stealer -> (seq_pref,owner,stealer)) owner_gen stealer_gen) in
  make ~print:(Util.print_triple_vertical ~center_prefix:false WSDConf.show_cmd) ~shrink:shrink_triple triple_gen

(* A parallel agreement test - w/repeat and retries combined *)
let agree_test_par ~count ~name =
  let rep_count = 50 in
  Test.make ~retries:10 ~count ~name
    arb_triple (STM.repeat rep_count agree_prop_par) (* 50 times each, then 50 * 10 times when shrinking *)

(* Note: this can generate, e.g., pop commands/actions in different threads, thus violating the spec. *)
let _agree_test_par_negative ~count ~name = WSDT.agree_test_par ~count ~name
;;

Util.set_ci_printing ()
;;
QCheck_runner.run_tests_main
  (let count = 1000 in [
    WSDT.agree_test         ~count ~name:"spcp_queue test";
    agree_test_par          ~count ~name:"parallel spsc_queue test";
    (*agree_test_par_negative ~count ~name:"spsc_queue test, negative";*)
  ])
