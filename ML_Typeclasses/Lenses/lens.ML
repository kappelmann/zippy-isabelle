(*  Title:  lens.ML
    Author: Kevin Kappelmann

Lenses adopted from Haskell's fclables https://hackage.haskell.org/package/fclabels
Unlike fclabels, which uses GADTs and categories, we register lenses as indexed categories.
*)
signature LENS_BASE =
sig

structure C : CATEGORY_BASE

(*abstract point datatype. The getter and modifier operations work in some
category. The type of the value pointed to might change, thereby changing
the type of the outer structure.*)
type ('t, 'o, 's, 'i) lens
type ('s, 'i) getter = ('s, 'i) C.cat
type ('t, 'o, 's, 'i) modifier = (('i, 'o) C.cat * 's, 't) C.cat

val lens : ('s, 'i) getter -> ('t, 'o, 's, 'i) modifier -> ('t, 'o, 's, 'i) lens

val get : ('t, 'o, 's, 'i) lens -> ('s, 'i) getter
val modify : ('t, 'o, 's, 'i) lens -> ('t, 'o, 's, 'i) modifier

include ICATEGORY_BASE
sharing type cat = lens

end

functor Lens_Base(AA : ARROW_APPLY_BASE) : LENS_BASE =
struct

structure AA = Arrow_Apply(AA)
structure A = Arrow(AA)
structure C = AA

type ('s, 'i) getter = ('s, 'i) C.cat
type ('t, 'o, 's, 'i) modifier = (('i, 'o) C.cat * 's, 't) C.cat

datatype ('t, 'o, 's, 'i) lens = Lens of {
  get : ('s, 'i) getter,
  modify : ('t, 'o, 's, 'i) modifier
}

fun lens get modify = Lens {get = get, modify = modify}

fun get (Lens {get, ...}) = get
fun modify (Lens {modify, ...}) = modify

type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) lens

fun id _ = lens (A.id ()) AA.app

fun comp l1 l2 =
  let
    val g1 = get l1
    val m1 = modify l1
    val g2 = get l2
    val m2 = modify l2
  in lens (A.comp g1 g2) (AA.uncurry (A.curry m2 o A.curry m1)) end

end

signature LENS =
sig

include LENS_BASE

type ('t, 's, 'o) setter = (('o * 's), 't) C.cat

val set : ('t, 'o, 's, 'i) lens -> ('t, 's, 'o) setter

end

functor Lens(AA : ARROW_APPLY_BASE) : LENS =
struct

structure L = Lens_Base(AA)
open L
structure A = Arrow(AA)

type ('t, 's, 'o) setter = (('o * 's), 't) C.cat

fun set p = C.comp (modify p) (A.first (A.arr A.K))

end
