(*  Title:      HOCLP/replace_move4_from_to.ML
    Author:     Kevin Kappelmann
*)
functor Replace_Move4_From(
    structure M : MOVE4
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    val dest_nfrom : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nfrom, ('p1, 'a1, 'a2, 'a3, 'a4) M.from) M.move
  )
  : MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) M.to
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
struct
  structure Min = M
  open M
  type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
  fun move x = x |> Min.comp Min.move dest_nfrom
end

functor Replace_Move4_To(
    structure M : MOVE4
    type ('p1, 'a1, 'a2, 'a3, 'a4) nto
    val nto : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) M.to, ('p1, 'a1, 'a2, 'a3, 'a4) nto) M.move
  )
  : MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) M.from
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) nto
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
struct
  structure Min = M
  open M
  type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) nto
  fun move x = x |> Min.comp nto Min.move
end

functor Replace_Move4_From_To(
    structure M : MOVE4
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    val dest_nfrom : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) nfrom, ('p1, 'a1, 'a2, 'a3, 'a4) M.from) M.move
    type ('p1, 'a1, 'a2, 'a3, 'a4) nto
    val nto : ('p1, ('p1, 'a1, 'a2, 'a3, 'a4) M.to, ('p1, 'a1, 'a2, 'a3, 'a4) nto) M.move
  )
  : MOVE4
    where type ('p1, 'a1, 'a2, 'a3, 'a4) from = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    where type ('p1, 'a1, 'a2, 'a3, 'a4) to = ('p1, 'a1, 'a2, 'a3, 'a4) nto
    where type ('p1, 'a) M.t = ('p1, 'a) M.M.t
  =
Replace_Move4_To(
  type ('p1, 'a1, 'a2, 'a3, 'a4) nto = ('p1, 'a1, 'a2, 'a3, 'a4) nto
  val nto = nto
  structure M = Replace_Move4_From(
    type ('p1, 'a1, 'a2, 'a3, 'a4) nfrom = ('p1, 'a1, 'a2, 'a3, 'a4) nfrom
    val dest_nfrom = dest_nfrom
    structure M = M
))
