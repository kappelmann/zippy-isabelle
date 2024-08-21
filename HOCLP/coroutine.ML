(*  Title:      HOCLP/coroutine.ML
    Author:     Kevin Kappelmann
*)
signature ICOROUTINE =
sig

structure C : ICATEGORY_BASE

type ('i, 'a, 'b) coroutine

val coroutine : ('i, 'i, 'a, 'b * ('i, 'a, 'b) coroutine) C.cat -> ('i, 'a, 'b) coroutine
val resume : ('i, 'a, 'b) coroutine -> ('i, 'i, 'a, 'b * ('i, 'a, 'b) coroutine) C.cat

end

functor ICoroutine(C : ICATEGORY_BASE) : ICOROUTINE =
struct

structure C = C

datatype ('i, 'a, 'b) coroutine = Coroutine of ('i, 'i, 'a, 'b * ('i, 'a, 'b) coroutine) C.cat

val coroutine = Coroutine
fun resume (Coroutine f) = f

end
