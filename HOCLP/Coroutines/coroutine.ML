(*  Title:      HOCLP/coroutine.ML
    Author:     Kevin Kappelmann

(Indexed) (alternating) coroutines.
*)
signature COROUTINE =
sig
  structure C : CATEGORY_BASE

  type ('p1, 'a, 'b, 'c) acoroutine
  type ('p1, 'a, 'b) coroutine = ('p1, 'a, 'b, 'b) acoroutine

  val acoroutine : ('p1, 'a, 'b * ('p1, 'a, 'c, 'b) acoroutine) C.cat ->
    ('p1, 'a, 'b, 'c) acoroutine
  val coroutine : ('p1, 'a, 'b * ('p1, 'a, 'b) coroutine) C.cat -> ('p1, 'a, 'b) coroutine
  val resume : ('p1, 'a, 'b, 'c) acoroutine -> ('p1, 'a, 'b * ('p1, 'a, 'c, 'b) acoroutine) C.cat
end

functor Coroutine(C : CATEGORY_BASE) : COROUTINE =
struct
structure C = C

datatype ('p1, 'a, 'b, 'c) acoroutine =
  Coroutine of ('p1, 'a, 'b * ('p1, 'a, 'c, 'b) acoroutine) C.cat

type ('p1, 'a, 'b) coroutine = ('p1, 'a, 'b, 'b) acoroutine

fun acoroutine c = Coroutine c
fun coroutine c = acoroutine c
fun resume (Coroutine c) = c

end

signature COROUTINE_UTIL =
sig
  include COROUTINE
  structure AE : ARROW_EXCEPTION
  sharing type AE.cat = C.cat
  val throw : 'p1 AE.exn -> ('p1, 'a, 'b, 'c) acoroutine
  val cons : ('p1, 'a, 'b) C.cat -> ('p1, 'a, 'c, 'b) acoroutine -> ('p1, 'a, 'b, 'c) acoroutine

  val map : ('p1, 'b1, 'b2) C.cat -> ('p1,  'c1, 'c2) C.cat ->
    ('p1, 'a, 'b1, 'c1) acoroutine -> ('p1, 'a, 'b2, 'c2) acoroutine

  val enum : ('p1, 'b, 'b) C.cat -> 'b -> ('p1, 'a, 'b) coroutine
end

functor Coroutine_Util(
    structure AE : ARROW_EXCEPTION
    structure CO : COROUTINE
    sharing type CO.C.cat = AE.cat
  ) : COROUTINE_UTIL =
struct

open CO
structure AE = AE

local structure SC = Semi_Category(AE) open SC
in
fun throw e = AE.throw' e |> acoroutine

fun cons f c = acoroutine (f >>> AE.arr (rpair c))

fun map f g c = resume c >>> AE.*** (f, AE.arr (map2 g f)) |> acoroutine
and map2 f g c = resume c >>> AE.*** (f, AE.arr (map g f)) |> acoroutine

fun enum next x = AE.arr (K x) >>> next >>> AE.arr (fn x => (x, enum next x)) |> coroutine

end
end

signature COROUTINE_UTIL_APPLY =
sig
  include COROUTINE_UTIL
  structure AA : ARROW_APPLY
  sharing type AA.cat = C.cat

  val gen_list_of : ('p1, 'a, 'l) AE.cat -> ('p1, 'b * 'l, 'l) C.cat ->
    ('p1, 'a, 'b) coroutine -> ('p1, 'a, 'l) C.cat
  val list_of : ('p1, 'a, 'b) coroutine -> ('p1, 'a, 'b list) C.cat
  val seq_of : ('p1, 'a, 'b) coroutine -> ('p1, 'a, 'b Seq.seq) C.cat
end

functor Coroutine_Util_Apply(
    structure A : ARROW_ARROW_APPLY
    structure CO : COROUTINE_UTIL
    sharing type CO.C.cat = A.A.cat
  ) : COROUTINE_UTIL_APPLY =
struct

structure AA = A.AA
open CO

local structure SC = Semi_Category(AE) open SC A.A
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

signature ICOROUTINE =
sig
  structure C : ICATEGORY_BASE

  type ('p1, 'i, 'j, 'a, 'b, 'c) acoroutine
  type ('p1, 'i, 'j, 'a, 'b) coroutine = ('p1, 'i, 'j, 'a, 'b, 'b) acoroutine

  val acoroutine : ('p1, 'i, 'j, 'a, 'b * ('p1, 'j, 'i, 'a, 'c, 'b) acoroutine) C.cat ->
    ('p1, 'i, 'j, 'a, 'b, 'c) acoroutine
  val coroutine : ('p1, 'i, 'j, 'a, 'b * ('p1, 'j, 'i, 'a, 'b) coroutine) C.cat ->
    ('p1, 'i, 'j, 'a, 'b) coroutine
  val resume : ('p1, 'i, 'j, 'a, 'b, 'c) acoroutine ->
    ('p1, 'i, 'j, 'a, 'b * ('p1, 'j, 'i, 'a, 'c, 'b) acoroutine) C.cat
end

functor ICoroutine(C : ICATEGORY_BASE) : ICOROUTINE =
struct
structure C = C

datatype ('p1, 'i, 'j, 'a, 'b, 'c) acoroutine =
  Coroutine of ('p1, 'i, 'j, 'a, 'b * ('p1, 'j, 'i, 'a, 'c, 'b) acoroutine) C.cat

type ('p1, 'i, 'j, 'a, 'b) coroutine = ('p1, 'i, 'j, 'a, 'b, 'b) acoroutine

fun acoroutine c = Coroutine c
fun coroutine c = acoroutine c
fun resume (Coroutine c) = c
end

signature ICOROUTINE_UTIL =
sig
  include ICOROUTINE
  structure AE : IARROW_EXCEPTION_BASE
  sharing type AE.cat = C.cat
  val throw : 'p1 AE.exn -> ('p1, 'i, 'i, 'a, 'b, 'c) acoroutine

  val map : ('p1, 'j, 'j, 'b1, 'b2) C.cat -> ('p1,'i, 'i, 'c1, 'c2) C.cat ->
    ('p1, 'i, 'j, 'a, 'b1, 'c1) acoroutine -> ('p1, 'i, 'j, 'a, 'b2, 'c2) acoroutine
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

fun map f g c = resume c >>> AE.*** (f, AE.arr (map2 g f)) |> acoroutine
and map2 f g c = resume c >>> AE.*** (f, AE.arr (map g f)) |> acoroutine
end

end