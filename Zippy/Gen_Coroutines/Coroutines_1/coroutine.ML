(*  Title:      Zippy/coroutine.ML
    Author:     Kevin Kappelmann

(Indexed) (alternating) coroutines.
*)
signature \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close> =
sig
  structure C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>

  type (@{ParaT_args} 'a, 'b, 'c) acoroutine
  type (@{ParaT_args} 'a, 'b) coroutine = (@{ParaT_args} 'a, 'b, 'b) acoroutine

  val acoroutine : (@{ParaT_args} 'a, 'b * (@{ParaT_args} 'a, 'c, 'b) acoroutine) C.cat ->
    (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val coroutine : (@{ParaT_args} 'a, 'b * (@{ParaT_args} 'a, 'b) coroutine) C.cat ->
    (@{ParaT_args} 'a, 'b) coroutine
  val resume : (@{ParaT_args} 'a, 'b, 'c) acoroutine -> (@{ParaT_args} 'a, 'b *
    (@{ParaT_args} 'a, 'c, 'b) acoroutine) C.cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(C : \<^eval>\<open>sfx_ParaT_nargs "CATEGORY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close> =
struct
structure C = C

datatype (@{ParaT_args} 'a, 'b, 'c) acoroutine =
  Coroutine of (@{ParaT_args} 'a, 'b * (@{ParaT_args} 'a, 'c, 'b) acoroutine) C.cat

type (@{ParaT_args} 'a, 'b) coroutine = (@{ParaT_args} 'a, 'b, 'b) acoroutine

fun acoroutine c = Coroutine c
fun coroutine c = acoroutine c
fun resume (Coroutine c) = c

end

signature \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close>
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION"\<close>
  sharing type AE.cat = C.cat
  val throw : @{ParaT_args encl = "(" ")"} AE.exn -> (@{ParaT_args} 'a, 'b, 'c) acoroutine
  val cons : (@{ParaT_args} 'a, 'b) C.cat -> (@{ParaT_args} 'a, 'c, 'b) acoroutine ->
    (@{ParaT_args} 'a, 'b, 'c) acoroutine

  val map : (@{ParaT_args} 'b1, 'b2) C.cat -> (@{ParaT_args}  'c1, 'c2) C.cat ->
    (@{ParaT_args} 'a, 'b1, 'c1) acoroutine -> (@{ParaT_args} 'a, 'b2, 'c2) acoroutine

  val enum : (@{ParaT_args} 'b, 'b) C.cat -> 'b -> (@{ParaT_args} 'a, 'b) coroutine
end

functor \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "ARROW_EXCEPTION"\<close>
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE"\<close>
    sharing type CO.C.cat = AE.cat
  ) : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close> =
struct

open CO
structure AE = AE

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE) open SC
in
fun throw e = AE.throw' e |> acoroutine

fun cons f c = acoroutine (f >>> AE.arr (rpair c))

fun map f g c = resume c >>> AE.*** (f, AE.arr (map2 g f)) |> acoroutine
and map2 f g c = resume c >>> AE.*** (f, AE.arr (map g f)) |> acoroutine

fun enum next x = AE.arr (K x) >>> next >>> AE.arr (fn x => (x, enum next x)) |> coroutine

end
end

signature \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
  structure AA : \<^eval>\<open>sfx_ParaT_nargs "ARROW_APPLY"\<close>
  sharing type AA.cat = C.cat

  val gen_list_of : (@{ParaT_args} 'a, 'l) AE.cat -> (@{ParaT_args} 'b * 'l, 'l) C.cat ->
    (@{ParaT_args} 'a, 'b) coroutine -> (@{ParaT_args} 'a, 'l) C.cat
  val list_of : (@{ParaT_args} 'a, 'b) coroutine -> (@{ParaT_args} 'a, 'b list) C.cat
  val seq_of : (@{ParaT_args} 'a, 'b) coroutine -> (@{ParaT_args} 'a, 'b Seq.seq) C.cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util_Apply"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "ARROW_ARROW_APPLY"\<close>
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL"\<close>
    sharing type CO.C.cat = A.A.cat
  ) : \<^eval>\<open>sfx_ParaT_nargs "COROUTINE_UTIL_APPLY"\<close> =
struct

structure AA = A.AA
open CO

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AE) open SC A.A
in
fun gen_list_of empty cons c = AE.catch'
  (resume c &&& id ()
    >>> arr (fn ((x, c), s) => (x, (gen_list_of empty cons c, s)))
    >>> second AA.app
    >>> cons)
  empty

fun list_of c = gen_list_of (K []) (arr (op ::)) c
fun seq_of c = gen_list_of (K Seq.empty) (arr (Library.uncurry Seq.cons)) c
end
end

signature \<^eval>\<open>sfx_ParaT_nargs "ICOROUTINE"\<close> =
sig
  structure C : \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close>

  type (@{ParaT_args} 'i, 'j, 'a, 'b, 'c) acoroutine
  type (@{ParaT_args} 'i, 'j, 'a, 'b) coroutine = (@{ParaT_args} 'i, 'j, 'a, 'b, 'b) acoroutine

  val acoroutine : (@{ParaT_args} 'i, 'j, 'a, 'b * (@{ParaT_args} 'j, 'i, 'a, 'c, 'b) acoroutine) C.cat ->
    (@{ParaT_args} 'i, 'j, 'a, 'b, 'c) acoroutine
  val coroutine : (@{ParaT_args} 'i, 'j, 'a, 'b * (@{ParaT_args} 'j, 'i, 'a, 'b) coroutine) C.cat ->
    (@{ParaT_args} 'i, 'j, 'a, 'b) coroutine
  val resume : (@{ParaT_args} 'i, 'j, 'a, 'b, 'c) acoroutine ->
    (@{ParaT_args} 'i, 'j, 'a, 'b * (@{ParaT_args} 'j, 'i, 'a, 'c, 'b) acoroutine) C.cat
end

functor \<^eval>\<open>sfx_ParaT_nargs "ICoroutine"\<close>(C : \<^eval>\<open>sfx_ParaT_nargs "ICATEGORY_BASE"\<close>)
  : \<^eval>\<open>sfx_ParaT_nargs "ICOROUTINE"\<close> =
struct
structure C = C

datatype (@{ParaT_args} 'i, 'j, 'a, 'b, 'c) acoroutine =
  Coroutine of (@{ParaT_args} 'i, 'j, 'a, 'b * (@{ParaT_args} 'j, 'i, 'a, 'c, 'b) acoroutine) C.cat

type (@{ParaT_args} 'i, 'j, 'a, 'b) coroutine = (@{ParaT_args} 'i, 'j, 'a, 'b, 'b) acoroutine

fun acoroutine c = Coroutine c
fun coroutine c = acoroutine c
fun resume (Coroutine c) = c
end

signature \<^eval>\<open>sfx_ParaT_nargs "ICOROUTINE_UTIL"\<close> =
sig
  include \<^eval>\<open>sfx_ParaT_nargs "ICOROUTINE"\<close>
  structure AE : \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION_BASE"\<close>
  sharing type AE.cat = C.cat
  val throw : @{ParaT_args encl = "(" ")"} AE.exn -> (@{ParaT_args} 'i, 'i, 'a, 'b, 'c) acoroutine

  val map : (@{ParaT_args} 'j, 'j, 'b1, 'b2) C.cat -> (@{ParaT_args}'i, 'i, 'c1, 'c2) C.cat ->
    (@{ParaT_args} 'i, 'j, 'a, 'b1, 'c1) acoroutine -> (@{ParaT_args} 'i, 'j, 'a, 'b2, 'c2) acoroutine
end

functor \<^eval>\<open>sfx_ParaT_nargs "ICoroutine_Util"\<close>(
    structure AE : \<^eval>\<open>sfx_ParaT_nargs "IARROW_EXCEPTION"\<close>
    structure CO : \<^eval>\<open>sfx_ParaT_nargs "ICOROUTINE"\<close>
    sharing type CO.C.cat = AE.cat
  ) : \<^eval>\<open>sfx_ParaT_nargs "ICOROUTINE_UTIL"\<close> =
struct

open CO
structure AE = AE

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "ISemi_Category"\<close>(AE) open SC
in
fun throw e = AE.throw' e |> acoroutine

fun map f g c = resume c >>> AE.*** (f, AE.arr (map2 g f)) |> acoroutine
and map2 f g c = resume c >>> AE.*** (f, AE.arr (map g f)) |> acoroutine
end

end