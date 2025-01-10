(*  Title:      HOCLP/list_zipper4.ML
    Author:     Kevin Kappelmann
*)
signature LIST_ZIPPER4 =
sig
  structure LI : GLIST
  include ZIPPER4
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.content = 'a1
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext = 'a1 LI.t * 'a1 LI.t
  where type ('p1, 'a) M.t = ('p1, 'a) LI.M.t
  where type ('p1, 'a1, 'a2, 'a3, 'a4) ZM.container = 'a1 LI.t
  val cons_zcontext : 'a1 -> ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext ->
    ('p1, 'a1, 'a2, 'a3, 'a4) ZO.zcontext
end

functor List_Zipper4(
    structure A : KLEISLI_ARROW
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    sharing type LI.M.t = A.K.M.t
    val mk_exn_horizontal : ('p1, unit, 'p1 LI.M.exn) A.cat
  ) : LIST_ZIPPER4 =
struct

structure LI = LI
structure ZO = Zipper4_Optics_Zipper_Data(
struct
  structure ZD = Zipper_Data
  structure A = A
  structure L = L
  type ('p1, 'a1, 'a2, 'a3, 'a4) content = 'a1
  type ('p1, 'a1, 'a2, 'a3, 'a4) zcontext = 'a1 LI.t * 'a1 LI.t
end
)
structure ZM = Zipper4_Moves(
  structure M = Move_Base(A.K.M)
  structure SC = Semi_Category(A) open SC ZO A
  type ('p1, 'a1, 'a2, 'a3, 'a4) container = 'a1 LI.t
  fun zip x = x |> (LI.dest >>> second (arr (pair LI.empty)) >>> zipper)
  fun unzip x = x |> (get_content &&& get_zcontext
    >>> arr (fn (c, (rev_pref, suff)) => rev rev_pref @ [c] @ suff))
  fun dest_zipper x = x |> (get_content &&& get_zcontext
    >>> arr (fn (c, (hs, ts)) => (hs, (c, ts))))
  fun up x = x |> (dest_zipper
    >>> first LI.dest
    >>> arr (fn ((h, hs), (c, ts)) => (h, (hs, LI.cons c ts)))
    >>> zipper)
  fun down x = x |> (dest_zipper
    >>> second (second LI.dest)
    >>> arr (fn (hs, (c, (t, ts))) => (t, (LI.cons c hs, ts)))
    >>> zipper)
  fun left x = x |> (K () >>> mk_exn_horizontal >>> LI.M.throw)
  fun right x = x |> (K () >>> mk_exn_horizontal >>> LI.M.throw)
)

structure Z = Zipper4(structure ZO = ZO; structure ZM = ZM)
open Z

fun cons_zcontext content = apfst (fn ts => ts @ [content])

end

