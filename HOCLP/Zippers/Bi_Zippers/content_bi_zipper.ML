(*  Title:      HOCLP/content_bi_zipper..ML
    Author:     Kevin Kappelmann
*)
functor Content_Bi_Zipper_Base(
    type ('i, 'a, 'b) content
    type ('i, 'a, 'b) container
    val unzip : ('i, 'a, 'b) content -> ('i, 'a, 'b) container
  ) :
    BI_ZIPPER_BASE
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) content
    where type ('i, 'a, 'b) zcontext = unit
    where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) content
    where type ('i, 'a, 'b) container = ('i, 'a, 'b) container
  =
struct
  type ('i, 'a, 'b) content = ('i, 'a, 'b) content
  type ('i, 'a, 'b) zcontext = unit
  type ('i, 'a, 'b) zipper = ('i, 'a, 'b) content
  fun zipper x = K x

  val get_content = I
  fun get_zcontext _ = ()

  val map_content = I
  fun map_zcontext _ = I

  type ('i, 'a, 'b) container = ('i, 'a, 'b) container
  val unzip = unzip
end

functor Content_Bi_Zipper(
    structure M : HOM_BI_ZIPPER_MOVES
    val unzip : ('i, 'a, 'b) M.data -> ('i, 'a, 'b) M.init_from
  ) :
    BI_ZIPPER
    where type ('i, 'a, 'b) content = ('i, 'a, 'b) M.data
    where type ('i, 'a, 'b) zcontext = unit
    where type ('i, 'a, 'b) zipper = ('i, 'a, 'b) M.data
    where type ('i, 'a, 'b) container = ('i, 'a, 'b) M.init_from
    where type ('i, 'j, 'a, 'b) C.cat = ('i, 'j, 'a, 'b) M.C.cat
  =
Bi_Zipper_Bi_Zipper_Moves(
  structure M = M
  structure Z = Content_Bi_Zipper_Base(
    type ('i, 'a, 'b) content = ('i, 'a, 'b) M.data
    type ('i, 'a, 'b) container = ('i, 'a, 'b) M.init_from
    val unzip = unzip
  )
)