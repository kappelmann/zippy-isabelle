(*  Title:      HOCLP/zipper_data.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPER_DATA =
sig
  type ('c, 'zctxt) zipper

  val zipper : 'c -> 'zctxt -> ('c, 'zctxt) zipper
  val dest_zipper : ('c, 'zctxt) zipper -> {content : 'c, zcontext : 'zctxt}

  val content : unit -> ('p1, ('c2, 'zctxt) zipper, 'c2, ('c1, 'zctxt) zipper, 'c1) SLens.lens
  val zcontext : unit ->
    ('p1, ('c, 'zctxt2) zipper, 'zctxt2, ('c, 'zctxt1) zipper, 'zctxt1) SLens.lens
  val get_content : ('c, 'zctxt) zipper -> 'c
  val get_zcontext : ('c, 'zctxt) zipper -> 'zctxt
  val map_content : ('c1 -> 'c2) -> ('c1, 'zctxt) zipper -> ('c2, 'zctxt) zipper
  val map_zcontext : ('zctxt1 -> 'zctxt2) -> ('c, 'zctxt1) zipper -> ('c, 'zctxt2) zipper
end

structure Zipper_Data : ZIPPER_DATA =
struct

datatype ('c, 'zctxt) zipper = Zipper of {
  content : 'c,
  zcontext : 'zctxt
}

fun zipper content zcontext = Zipper {content = content, zcontext = zcontext}
fun dest_zipper (Zipper zipper) = zipper

fun get_content (Zipper {content, ...}) = content
fun get_zcontext (Zipper {zcontext, ...}) = zcontext

fun map_content f (Zipper {content, zcontext}) = Zipper {content = f content, zcontext = zcontext}
fun map_zcontext f (Zipper {content, zcontext}) = Zipper {content = content, zcontext = f zcontext}

fun content _ = SLens.lens get_content (uncurry map_content)
fun zcontext _ = SLens.lens get_zcontext (uncurry map_zcontext)

end
