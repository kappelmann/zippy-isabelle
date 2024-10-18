(*  Title:      HOCLP/coroutine.ML
    Author:     Kevin Kappelmann

Indexed (alternating) coroutines.
*)
signature ICOROUTINE =
sig

structure C : ICATEGORY_BASE

type ('i, 'j, 'a, 'b, 'c) acoroutine
type ('i, 'j, 'a, 'b) coroutine = ('i, 'j, 'a, 'b, 'b) acoroutine

val acoroutine : ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'c, 'b) acoroutine) C.cat -> ('i, 'j, 'a, 'b, 'c) acoroutine
val coroutine : ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'b) coroutine) C.cat -> ('i, 'j, 'a, 'b) coroutine

val resume : ('i, 'j, 'a, 'b, 'c) acoroutine -> ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'c, 'b) acoroutine) C.cat

end

functor ICoroutine(C : ICATEGORY_BASE) : ICOROUTINE =
struct

structure C = C

datatype ('i, 'j, 'a, 'b, 'c) acoroutine =
  Coroutine of ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'c, 'b) acoroutine) C.cat

type ('i, 'j, 'a, 'b) coroutine = ('i, 'j, 'a, 'b, 'b) acoroutine

fun acoroutine f = Coroutine f
fun coroutine f = acoroutine f
fun resume (Coroutine f) = f

end

signature ICOROUTINE_UTIL =
sig
  include ICOROUTINE
  structure AE : IARROW_EXCEPTION_BASE
  sharing type AE.cat = C.cat
  val throw : AE.exn -> ('i, 'i, 'a, 'b, 'c) acoroutine
end

functor ICoroutine_Util(
    structure AE : IARROW_EXCEPTION
    structure CO : ICOROUTINE
    sharing type CO.C.cat = AE.cat
  ) : ICOROUTINE_UTIL =
struct

open CO
structure AE = AE

local structure SC = ISemi_Category(AE) open SC
in
fun throw e = AE.throw' e |> acoroutine
end

end