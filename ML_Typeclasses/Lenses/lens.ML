(*  Title:  lens.ML
    Author: Kevin Kappelmann

Lenses adopted from Haskell's fclables https://hackage.haskell.org/package/fclabels
Unlike fclabels, which uses GADTs and categories, we register lenses as indexed categories.
*)
signature LENS_BASE =
sig

structure C : CATEGORY_BASE

(*abstract lens datatype. The getter and modifier operations work in some
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

functor Lens_Base(AA : ARROW_APPLY) : LENS_BASE =
struct

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

val lift_get : ('s, 'i) C.cat -> ('o, 'o, 's, 'i) lens
val lift_modify : ('o, 't) C.cat -> ('t, 'o, 'i, 'i) lens

val comp_get_modify : ('i, 'j) C.cat -> ('u, 'o) C.cat -> ('t, 'o, 's, 'i) cat ->
  ('t, 'u, 's, 'j) cat

end

functor Lens(structure L : LENS_BASE; structure A : ARROW sharing type L.C.cat = A.cat) : LENS =
struct

open L

type ('t, 's, 'o) setter = (('o * 's), 't) C.cat

fun set l = C.comp (modify l) (A.first (A.arr A.K))

fun lift_get f =
  L.lens (L.id () |> L.get |> L.C.comp f) (A.second f |> L.C.comp (L.modify (L.id ())))

fun lift_modify f =
  let val id = L.id ()
  in L.lens (L.get id) (L.C.comp f (L.modify id)) end

fun comp_get_modify get modify f = f |> comp (lift_get get) |> comp (lift_modify modify)

end
