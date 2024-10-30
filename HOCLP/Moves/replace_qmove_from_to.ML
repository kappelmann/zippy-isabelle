(*  Title:      HOCLP/replace_qmove_from_to.ML
    Author:     Kevin Kappelmann
*)
functor Replace_QMove_From(
    structure C : LAZY_ISEMI_CATEGORY_BASE
    structure M : QMOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) C.T.lcat
    type ('i, 'a, 'b, 'c, 'd) nfrom
    val dest_nfrom : ('i, ('i, 'a, 'b, 'c, 'd) nfrom, ('i, 'a, 'b, 'c, 'd) M.from) M.move
  )
  : QMOVE
    where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) nfrom
    where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) M.to
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  =
struct
  open M
  type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) nfrom
  fun move _ = M.comp M.move dest_nfrom ()
end

functor Replace_QMove_To(
    structure C : LAZY_ISEMI_CATEGORY_BASE
    structure M : QMOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) C.T.lcat
    type ('i, 'a, 'b, 'c, 'd) nto
    val nto : ('i, ('i, 'a, 'b, 'c, 'd) M.to, ('i, 'a, 'b, 'c, 'd) nto) M.move
  )
  : QMOVE
    where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) M.from
    where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) nto
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  =
struct
  open M
  type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) nto
  fun move _ = M.comp nto M.move ()
end

functor Replace_QMove_From_To(
    structure C : LAZY_ISEMI_CATEGORY_BASE
    structure M : QMOVE
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) C.T.lcat
    type ('i, 'a, 'b, 'c, 'd) nfrom
    val dest_nfrom : ('i, ('i, 'a, 'b, 'c, 'd) nfrom, ('i, 'a, 'b, 'c, 'd) M.from) M.move
    type ('i, 'a, 'b, 'c, 'd) nto
    val nto : ('i, ('i, 'a, 'b, 'c, 'd) M.to, ('i, 'a, 'b, 'c, 'd) nto) M.move
  )
  : QMOVE
    where type ('i, 'a, 'b, 'c, 'd) from = ('i, 'a, 'b, 'c, 'd) nfrom
    where type ('i, 'a, 'b, 'c, 'd) to = ('i, 'a, 'b, 'c, 'd) nto
    where type ('i, 'j, 'a, 'b) cat = ('i, 'j, 'a, 'b) M.cat
  =
Replace_QMove_To(
  structure C = C
  type ('i, 'a, 'b, 'c, 'd) nto = ('i, 'a, 'b, 'c, 'd) nto
  val nto = nto
  structure M = Replace_QMove_From(
    structure C = C
    type ('i, 'a, 'b, 'c, 'd) nfrom = ('i, 'a, 'b, 'c, 'd) nfrom
    val dest_nfrom = dest_nfrom
    structure M = M
))
