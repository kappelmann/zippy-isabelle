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
