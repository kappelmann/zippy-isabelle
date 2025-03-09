(*  Title:      HOCLP/list_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close> =
sig
  structure LI : GLIST
  type @{T_args} content
  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  where type @{T_args} ZO.content = @{T_args} content
  where type @{T_args} ZO.zcontext = @{T_args} content LI.t * @{T_args} content LI.t
  where type @{T_args} ZM.container = @{T_args} content LI.t
  where type ('p1, 'a) M.t = ('p1, 'a) LI.M.t
  val cons_zcontext : @{T_args} content -> @{T_args} ZO.zcontext -> @{T_args} ZO.zcontext
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "List_Zipper"\<close>(
    structure A : KLEISLI_ARROW
    structure L : LENS
    where type ('p1, 'a, 'b) C.cat = ('p1, 'a, 'b) A.cat
    structure LI : GLIST
    where type 'a t = 'a list
    sharing type LI.M.t = A.K.M.t
    val mk_exn_horizontal : ('p1, unit, 'p1 LI.M.exn) A.cat
    type @{T_args} content
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type @{T_args} content = @{T_args} content
   =
struct

type @{T_args} content = @{T_args} content

structure LI = LI
structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data"\<close>(
struct
  structure ZD = Zipper_Data
  structure A = A
  structure L = L
  type @{T_args} content = @{T_args} content
  type @{T_args} zcontext = @{T_args} content LI.t * @{T_args} content LI.t
end
)
structure ZM = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Moves"\<close>(
  structure M = Move_Base(A.K.M)
  structure SC = Semi_Category(A) open SC ZO A
  type @{T_args} container = @{T_args} content LI.t
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

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_List_Zipper"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "LIST_ZIPPER"\<close>
    where type 'a LI.t = 'a Z.LI.t
    where type @{T_args} content = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.content
    where type @{T_args} zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{T_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
  = Z
