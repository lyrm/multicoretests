open QCheck

(** ********************************************************************** *)
(**                       Tests of a simple reference                      *)
(** ********************************************************************** *)
module Sut =
  struct
    let sut = ref 0
    let get () = !sut
    let set i  = sut:=i
    let add i  = let old = !sut in sut:=i + old (* buggy: not atomic *)
    let incr () = incr sut     (* buggy: not guaranteed to be atomic *)
    let decr () = decr sut     (* buggy: not guaranteed to be atomic *)
end

module RConf = struct
  type t = int ref

  type cmd =
    | Get
    | Set of int_arg
    | Add of int_arg
    | Incr
    | Decr [@@deriving qcheck, show { with_path = false }]
  and int_arg = int [@gen Gen.nat]

  type res = RGet of int | RSet | RAdd | RIncr | RDecr [@@deriving show { with_path = false }]

  let init () = Sut.sut

  let run c _r = match c with
    | Get   -> RGet (Sut.get ())
    | Set i -> (Sut.set i; RSet)
    | Add i -> (Sut.add i; RAdd)
    | Incr  -> (Sut.incr (); RIncr)
    | Decr  -> (Sut.decr (); RDecr)

  let cleanup _ = Sut.set 0
end

module RT = Lin.Make(RConf)


(** ********************************************************************** *)
(**                  Tests of the buggy concurrent list CList              *)
(** ********************************************************************** *)
module CLConf =
struct
  type t = CList.conc_list Atomic.t

  type cmd =
    | Add_node of int_arg
    | Member of int_arg [@@deriving qcheck, show { with_path = false }]
  and int_arg = int [@gen Gen.nat]

  type res = RAdd_node of bool | RMember of bool [@@deriving show { with_path = false }]

  let init () = CList.list_init 0

  let run c r = match c with
    | Add_node i -> RAdd_node (CList.add_node r i)
    | Member i   -> RMember (CList.member r i)

  let cleanup _ = ()
end

module CLT = Lin.Make(CLConf)


(** ********************************************************************** *)
(**                   Tests of the Atomic module                           *)
(** ********************************************************************** *)
module AConf =
struct
  type t = int Atomic.t

  type cmd =
    | Get
    | Set of int_arg
    | Exchange of int_arg
    | Compare_and_set of int_arg * int_arg
    | Fetch_and_add of int_arg
    | Incr
    | Decr [@@deriving qcheck, show { with_path = false }]
  and int_arg = int [@gen Gen.nat]

  type res =
    | RGet of int
    | RSet
    | RExchange of int
    | RFetch_and_add of int
    | RCompare_and_set of bool
    | RIncr
    | RDecr [@@deriving show { with_path = false }]

  let init () = Atomic.make 0

  let run c r = match c with
    | Get                      -> RGet (Atomic.get r)
    | Set i                    -> (Atomic.set r i; RSet)
    | Exchange i               -> RExchange (Atomic.exchange r i)
    | Fetch_and_add i          -> RFetch_and_add (Atomic.fetch_and_add r i)
    | Compare_and_set (seen,v) -> RCompare_and_set (Atomic.compare_and_set r seen v)
    | Incr                     -> (Atomic.incr r; RIncr)
    | Decr                     -> (Atomic.decr r; RDecr)

  let cleanup _ = ()
end

module AT = Lin.Make(AConf)


(** ********************************************************************** *)
(**                      Tests of thread-unsafe [Hashtbl]                  *)
(** ********************************************************************** *)
module HConf =
struct
  type t = (char, int) Hashtbl.t

  type cmd =
    | Clear
    | Add of char * int_arg
    | Remove of char
    | Find of char
    | Find_opt of char
    | Find_all of char
    | Replace of char * int_arg
    | Mem of char
    | Length [@@deriving qcheck, show { with_path = false }]
  and int_arg = int [@gen Gen.nat]

  type res =
    | RClear
    | RAdd
    | RRemove
    | RFind of int option
    | RFind_opt of int option
    | RFind_all of int list
    | RReplace
    | RMem of bool
    | RLength of int [@@deriving show { with_path = false }]

  let init () = Hashtbl.create ~random:false 42

  let run c h = match c with
    | Clear         -> Hashtbl.clear h; RClear
    | Add (k,v)     -> Hashtbl.add h k v; RAdd
    | Remove k      -> Hashtbl.remove h k; RRemove
    | Find k        -> RFind
                         (try Some (Hashtbl.find h k)
                          with Not_found -> None)
    | Find_opt k    -> RFind_opt (Hashtbl.find_opt h k)
    | Find_all k    -> RFind_all (Hashtbl.find_all h k)
    | Replace (k,v) -> Hashtbl.replace h k v; RReplace
    | Mem k         -> RMem (Hashtbl.mem h k)
    | Length        -> RLength (Hashtbl.length h)

  let cleanup _ = ()
end

module HT = Lin.Make(HConf)


(** ********************************************************************** *)
(**                             Tests of [Kcas]                            *)
(** ********************************************************************** *)
module KConf =
struct
  type t = int Kcas.ref

  (* missing: equal, is_on_ref, kCAS -- mk_cas, commit (already tested as [set] *)
  type cmd =
    | Get
    | Set of int_arg
    | Cas of int_arg * int_arg
    | TryMapNone
    (*| TryMapSome*) (* Seq,exec cannot fail - hence not linearizable with [try_map] *)
    | MapNone
    | MapSome
    | Incr
    | Decr [@@deriving qcheck, show { with_path = false }]
  and int_arg = (int [@gen Gen.nat])


  type res =
    | RGet of int
    | RSet
    | RCas of bool
    | RTryMapNone of int cas_result
    (*| RTryMapSome of int cas_result*)
    | RMapNone of int cas_result
    | RMapSome of int cas_result
    | RIncr
    | RDecr [@@deriving show { with_path = false }]
  and 'a cas_result
    = 'a Kcas.cas_result =
    | Aborted
    | Failed
    | Success of 'a [@deriving show { with_path = false }]

  let init () = Kcas.ref 0

  let run c r = match c with
    | Get        -> RGet (Kcas.get r)
    | Set i      -> (Kcas.set r i; RSet)
    | Cas (i,j)  -> RCas (Kcas.cas r i j)
    | TryMapNone -> RTryMapNone (Kcas.try_map r (fun _ -> None))
    (*| TryMapSome -> RTryMapSome (Kcas.try_map r (fun i -> Some i))*)
    | MapNone    -> RMapNone (Kcas.map r (fun _ -> None))
    | MapSome    -> RMapSome (Kcas.map r (fun i -> Some i))
    | Incr       -> (Kcas.incr r; RIncr)
    | Decr       -> (Kcas.decr r; RDecr)
  let cleanup _ = ()
end

module KT = Lin.Make(KConf)


(** ********************************************************************** *)
(**                           Tests of [Kcas.W1]                           *)
(** ********************************************************************** *)
module KW1Conf =
struct
  type t = int Kcas.W1.ref

  type cmd =
    | Get
    | Set of int_arg
    | Cas of int_arg * int_arg
    | TryMapNone
    (*| TryMapSome*) (* Seq,exec cannot fail - hence not linearizable with [try_map] *)
    | MapNone
    | MapSome
    | Incr
    | Decr [@@deriving qcheck, show { with_path = false }]
  and int_arg = (int [@gen Gen.nat])


  type res =
    | RGet of int
    | RSet
    | RCas of bool
    | RTryMapNone of int cas_result
    (*| RTryMapSome of int cas_result*)
    | RMapNone of int cas_result
    | RMapSome of int cas_result
    | RIncr
    | RDecr [@@deriving show { with_path = false }]
  and 'a cas_result
    = 'a Kcas.cas_result =
    | Aborted
    | Failed
    | Success of 'a [@deriving show { with_path = false }]

  let init () = Kcas.W1.ref 0

  let run c r = match c with
    | Get        -> RGet (Kcas.W1.get r)
    | Set i      -> (Kcas.W1.set r i; RSet)
    | Cas (i,j)  -> RCas (Kcas.W1.cas r i j)
    | TryMapNone -> RTryMapNone (Kcas.W1.try_map r (fun _ -> None))
    (*| TryMapSome -> RTryMapSome (Kcas.W1.try_map r (fun i -> Some i))*)
    | MapNone    -> RMapNone (Kcas.W1.map r (fun _ -> None))
    | MapSome    -> RMapSome (Kcas.W1.map r (fun i -> Some i))
    | Incr       -> (Kcas.W1.incr r; RIncr)
    | Decr       -> (Kcas.W1.decr r; RDecr)
  let cleanup _ = ()
end

module KW1T = Lin.Make(KW1Conf)
;;
Util.set_ci_printing ()
;;
QCheck_runner.run_tests_main [
  RT.lin_test     ~count:1000 ~name:"ref test";
  CLT.lin_test    ~count:1000 ~name:"CList test";
  AT.lin_test     ~count:1000 ~name:"Atomic test";
  HT.lin_test     ~count:1000 ~name:"Hashtbl test";
  (* Kcas tests *)
  KT.lin_test     ~count:1000 ~name:"Kcas test";
  KW1T.lin_test   ~count:1000 ~name:"Kcas.W1 test";
]
