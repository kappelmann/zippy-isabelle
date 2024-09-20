(*  Title:      HOCLP/coroutine.ML
    Author:     Kevin Kappelmann
*)
signature ICOROUTINE =
sig

structure C : ICATEGORY_BASE

type ('i, 'j, 'a, 'b) coroutine

val coroutine : ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'b) coroutine) C.cat -> ('i, 'j, 'a, 'b) coroutine
val resume : ('i, 'j, 'a, 'b) coroutine -> ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'b) coroutine) C.cat

end

functor ICoroutine(C : ICATEGORY_BASE) : ICOROUTINE
=
struct

structure C = C

datatype ('i, 'j, 'a, 'b) coroutine = Coroutine of ('i, 'j, 'a, 'b * ('j, 'i, 'a, 'b) coroutine) C.cat

val coroutine = Coroutine
fun resume (Coroutine f) = f

end
