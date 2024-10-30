(*  Title:      HOCLP/content_qzipper..ML
    Author:     Kevin Kappelmann
*)
functor Content_QZipper_Base(
    type ('i, 'a, 'b, 'c, 'd) content
    type ('i, 'a, 'b, 'c, 'd) container
    val unzip : ('i, 'a, 'b, 'c, 'd) content -> ('i, 'a, 'b, 'c, 'd) container
  ) :
    QZIPPER_BASE
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content
    where type ('i, 'a, 'b, 'c, 'd) zcontext = unit
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) content
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) container
  =
struct
  type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) content
  type ('i, 'a, 'b, 'c, 'd) zcontext = unit
  type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) content
  fun zipper x = K x

  val get_content = I
  fun get_zcontext _ = ()

  val map_content = I
  fun map_zcontext _ = I

  type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) container
  val unzip = unzip
end

functor Content_QZipper(
    structure M : HOM_QZIPPER_MOVES
    val unzip : ('i, 'a, 'b, 'c, 'd) M.data -> ('i, 'a, 'b, 'c, 'd) M.init_from
  ) :
    QZIPPER
    where type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) M.data
    where type ('i, 'a, 'b, 'c, 'd) zcontext = unit
    where type ('i, 'a, 'b, 'c, 'd) zipper = ('i, 'a, 'b, 'c, 'd) M.data
    where type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) M.init_from
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  =
QZipper_QZipper_Moves(
  structure M = M
  structure Z = Content_QZipper_Base(
    type ('i, 'a, 'b, 'c, 'd) content = ('i, 'a, 'b, 'c, 'd) M.data
    type ('i, 'a, 'b, 'c, 'd) container = ('i, 'a, 'b, 'c, 'd) M.init_from
    val unzip = unzip
  )
)