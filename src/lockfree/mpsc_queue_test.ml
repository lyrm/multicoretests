(** Sequential tests of ws_deque *)

open QCheck
open STM

(** Mpsc_queue is a lock-free multi-producer, single-consumer,
   thread-safe queue without support for cancellation. This makes a
   good data structure for a scheduler's run queue. *)
module Mpsc_queue = Lockfree.Mpsc_queue

module WSDConf =
struct
  (* Producers can use the functions [push] and [is_empty] and [close] *)
  (* Consumer can use the functions [pop], [push_head], [is_empty] and [close]*)

  type cmd =
    | Push of int  (* use int for now *)
    | Pop
    | Is_empty
    | Push_head of int
    | Close  [@@deriving show { with_path = false }]

  type state = bool * int list
  type sut = int Mpsc_queue.t

  let is_opened s = fst s
  let is_closed_and_empty s = not (fst s) && snd s = []

  let producer_cmd _s =
    let int_gen = Gen.nat in
    QCheck.make ~print:show_cmd
      (Gen.frequency
         [6, Gen.map (fun i -> Push i) int_gen;
          3, Gen.return Is_empty;
          1, Gen.return Close;
         ])

  (* Consumer cmd *)
  let arb_cmd _s =
    let int_gen = Gen.nat in
    QCheck.make ~print:show_cmd
      (Gen.frequency
         [3, Gen.map (fun i -> Push_head i) int_gen ;
          3, Gen.return Pop;
          3, Gen.return Is_empty;
          1, Gen.return Close
         ])

  let init_state  = true, []
  let init_sut () = Mpsc_queue.create ()
  let cleanup q  = try Mpsc_queue.close q with Mpsc_queue.Closed -> ()

  let next_state c s =
    if is_closed_and_empty s then s
    else
      (match c with
       | Push i      -> if is_opened s then (fst s, (snd s) @ [i]) else s
       | Push_head i -> fst s, i :: (snd s)
       | Pop         ->
         (match snd s with
          | []    -> s
          | _::s' -> fst s, s')
       | Is_empty    -> s
       | Close       -> false, snd s)

  let precond _ _ = true

  type res =
    | RPush      of (unit, exn) result
    | RPush_head of (unit, exn) result
    | RPop       of (int option, exn) result
    | RIs_empty  of (bool, exn) result
    | RClose     of (unit, exn) result [@@deriving show { with_path = false }]

  let run c d = match c with
    | Push i      -> RPush (Util.protect (Mpsc_queue.push d) i)
    | Push_head i -> RPush_head (Util.protect (Mpsc_queue.push_head d) i)
    | Pop         -> RPop (Util.protect Mpsc_queue.pop d)
    | Is_empty    -> RIs_empty (Util.protect Mpsc_queue.is_empty d)
    | Close       -> RClose (Util.protect Mpsc_queue.close d)

  let postcond c s res = match c,res with
    | Push _, RPush res -> if not (fst s) then res = Error Mpsc_queue.Closed else res = Ok ()
    | Push_head _, RPush_head res ->
      (if is_closed_and_empty s then res = Error Mpsc_queue.Closed else res = Ok ())
    | Pop, RPop res ->
      (if is_closed_and_empty s then res = Error Mpsc_queue.Closed
       else (match snd s with | [] -> res = Ok None | x::_ -> res = Ok (Some x)))
    | Is_empty, RIs_empty res ->
      (if is_closed_and_empty s then res = Error Mpsc_queue.Closed
       else (match snd s with [] -> res = Ok true | _ -> res = Ok false))
    | Close, RClose res -> if not (fst s) then res = Error Mpsc_queue.Closed else res = Ok ()
    | _,_ -> false
end

module WSDT = STM.Make(WSDConf)

(*
;;
QCheck_runner.run_tests ~verbose:true [
    WSDT.agree_test     ~count:1_000 ~name:"sequential lf_queue test";
    WSDT.agree_test_par ~count:1_000 ~name:"parallel lf_queue test (w/repeat)";
    agree_test_par      ~count:1_000 ~name:"parallel lf_queue test (w/non_det module)";
  ]
 *)

(* Triple printer, that prints [consumer] on same line as sequential prefix [seq] *)
let print_triple show_elem (seq,consumer,producer) =
  let header1, header2 = "Seq.prefix:", "Parallel procs.:" in
  let pr_cmds = Print.list show_elem in
  let seq_str = pr_cmds seq in
  let seq_len = max (String.length header1) (String.length seq_str) in
  let buf = Buffer.create 64 in
  begin
    Printf.bprintf buf " %-*s  %s\n\n" seq_len header1 header2;
    Printf.bprintf buf " %*s  %s\n\n" seq_len seq_str (pr_cmds consumer);
    Printf.bprintf buf " %s  %s\n" (String.make seq_len ' ') (pr_cmds producer);
    Buffer.contents buf
  end

let agree_prop_par =
  (fun (seq_pref,consumer,producer) ->
    assume (WSDT.cmds_ok WSDConf.init_state (seq_pref@consumer));
    assume (WSDT.cmds_ok WSDConf.init_state (seq_pref@producer));
    let sut = WSDConf.init_sut () in
    let pref_obs = WSDT.interp_sut_res sut seq_pref in
    let sema = Semaphore.Binary.make false in
    let producer_dom = Domain.spawn (fun () -> Semaphore.Binary.release sema; WSDT.interp_sut_res sut producer) in
    while not (Semaphore.Binary.try_acquire sema) do Domain.cpu_relax() done;
    let consumer_obs = WSDT.interp_sut_res sut consumer in
    let producer_obs = Domain.join producer_dom in
    let res = WSDT.check_obs pref_obs consumer_obs producer_obs WSDConf.init_state in
    let () = WSDConf.cleanup sut in
    res ||
      Test.fail_reportf "Result observations not explainable by linearized model:\n\n %s"
      @@ print_triple WSDConf.show_res
           (List.map snd pref_obs,
            List.map snd consumer_obs,
            List.map snd producer_obs))

let shrink_triple =
  let (<+>) = Iter.(<+>) in
  (fun (seq,p1,p2) ->
    (Shrink.(triple list list list) (seq,p1,p2))
    <+> (match p1 with [] -> Iter.empty | c1::c1s -> Iter.return (seq@[c1],c1s,p2))
    <+> (match p2 with [] -> Iter.empty | c2::c2s -> Iter.return (seq@[c2],p1,c2s)))

let arb_triple =
  let seq_len,par_len = 20,15 in
  let seq_pref_gen = WSDT.gen_cmds_size WSDConf.init_state (Gen.int_bound seq_len) in
  let triple_gen =
    Gen.(seq_pref_gen >>= fun seq_pref ->
         let spawn_state = List.fold_left (fun st c -> WSDConf.next_state c st) WSDConf.init_state seq_pref in
         let consumer_gen = WSDT.gen_cmds_size spawn_state (Gen.int_bound par_len) in
         let producer_gen = list_size (int_bound par_len) (WSDConf.producer_cmd spawn_state).gen in
         map2 (fun consumer producer -> (seq_pref,consumer,producer)) consumer_gen producer_gen) in
  make ~print:(print_triple WSDConf.show_cmd) ~shrink:shrink_triple triple_gen

(* A parallel agreement test - w/repeat and retries combined *)
let agree_test_par ~count ~name =
  let rep_count = 50 in
  Test.make ~retries:10 ~count ~name
    arb_triple (STM.repeat rep_count agree_prop_par) (* 50 times each, then 50 * 10 times when shrinking *)

(* Note: this can generate, e.g., pop commands/actions in different threads,
thus violating the spec. *)
let agree_test_par_negative ~count ~name = WSDT.agree_test_par ~count ~name

;;
Util.set_ci_printing ()
;;
QCheck_runner.run_tests_main
  (let count = 1000 in [
    WSDT.agree_test         ~count ~name:"lf_queue test";
    agree_test_par          ~count ~name:"parallel lf_queue test";
    agree_test_par_negative ~count ~name:"lf_queue test, negative";
  ])
