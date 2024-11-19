(*  Title:      HOCLP/replace_move4_from_to.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Move4_From(
    structure C : LAZY_SEMI_CATEGORY_BASE
    structure M : MOVE4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) C.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    val dest_nfrom : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nfrom, ('p1, 'a1, 'a2, 'a3, 'a4) M.from) M.move
  )
  : MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) M.to
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M.cat
  =
struct
  open M
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
  fun move _ = M.comp M.move dest_nfrom
    |> Lazy_Cat_Util.unlift

end

functor Replace_Move4_To(
    structure C : LAZY_SEMI_CATEGORY_BASE
    structure M : MOVE4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) C.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nto
    val nto : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) M.to, ('p1, 'a1, 'a2, 'a3, 'a4) nto) M.move
  )
  : MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) M.from
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) nto
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M.cat
  =
struct
  open M
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) nto
  fun move _ = M.comp nto M.move
    |> Lazy_Cat_Util.unlift
end

functor Replace_Move4_From_To(
    structure C : LAZY_SEMI_CATEGORY_BASE
    structure M : MOVE4
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) C.cat
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    val dest_nfrom : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nfrom, ('p1, 'a1, 'a2, 'a3, 'a4) M.from) M.move
    type ('p1, 'a1, 'a2, 'a3, 'a4) nto
    val nto : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) M.to, ('p1, 'a1, 'a2, 'a3, 'a4) nto) M.move
  )
  : MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) nto
    where type ('p1, 'a, 'b) cat = ('p1, 'a, 'b) M.cat
  =
Replace_Move4_To(
  structure C = C
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nto
  val nto = nto
  structure M = Replace_Move4_From(
    structure C = C
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    val dest_nfrom = dest_nfrom
    structure M = M
))
