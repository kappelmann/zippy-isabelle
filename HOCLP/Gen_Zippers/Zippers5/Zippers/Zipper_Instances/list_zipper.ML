(*  Title:      HOCLP/list_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close> =
sig
  structure LI : GLIST
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZO.content = @{PolyT_arg 0}
  where type @{T_args} ZO.zcontext = @{PolyT_arg 0} LI.t * @{PolyT_arg 0} LI.t
  where type @{T_args} ZM.container = @{PolyT_arg 0} LI.t
  where type ('p1, 'a) M.t = ('p1, 'a) LI.M.t
  val cons_zcontext : @{PolyT_arg 0} -> @{T_args} ZO.zcontext -> @{T_args} ZO.zcontext
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "List_Zipper"\<close>(
    structure A : KLEISLI_ARROW
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    sharing type LI.M.t = A.K.M.t
    val mk_exn_horizontal : ('p1, unit, 'p1 LI.M.exn) A.cat
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close> =
struct

structure LI = LI
structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data"\<close>(
struct
  structure ZD = Zipper_Data
  structure A = A
  structure L = L
  type @{T_args} content = @{PolyT_arg 0}
  type @{T_args} zcontext = @{PolyT_arg 0} LI.t * @{PolyT_arg 0} LI.t
end
)
structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  structure M = Move_Base(A.K.M)
  structure SC = Semi_Category(A) open SC ZO A
  type @{T_args} container = @{PolyT_arg 0} LI.t
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

structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper"\<close>(
  structure ZO = ZO; structure ZM = ZM)
open Z

fun cons_zcontext c = apfst (fn hs => hs @ [c])

end

