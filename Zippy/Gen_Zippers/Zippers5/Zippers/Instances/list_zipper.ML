(*  Title:      Zippy/list_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close> =
sig
  structure LI : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  type @{AllT_args} content
  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZD.content = @{AllT_args} content
  where type @{AllT_args} ZD.zcontext = @{AllT_args} content LI.t * @{AllT_args} content LI.t
  where type @{AllT_args} ZM.container = @{AllT_args} content LI.t
  sharing type M.t = LI.M.t
  val cons_zcontext : @{AllT_args} content -> @{AllT_args} ZD.zcontext -> @{AllT_args} ZD.zcontext
end

functor \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS_KLEISLI"\<close>
    structure LI : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
    where type 'a t = 'a list
    sharing type LI.M.t = L.K.M.t
    val mk_exn_horizontal : (@{ParaT_args} unit, @{ParaT_args encl = "(" ")"} LI.M.exn) L.C.cat
    type @{AllT_args} content
  ) :
    \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
    where type @{AllT_args} content = @{AllT_args} content
   =
struct

type @{AllT_args} content = @{AllT_args} content

structure LI = LI
structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
struct
  structure L = L
  type @{AllT_args} content = @{AllT_args} content
  type @{AllT_args} zcontext = @{AllT_args} content LI.t * @{AllT_args} content LI.t
end)
structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(L.K.M)
  type @{AllT_args} container = @{AllT_args} content LI.t
  open ZD
  local
    structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(M)
    structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M.M)
    open SC A
  in
  fun zip x = x |> (LI.dest >>> second (arr (pair LI.empty)) >>> zipper)
  fun unzip x = x |> (CO.getter &&& ZCTXT.getter
    >>> arr (fn (c, (rev_pref, suff)) => rev rev_pref @ [c] @ suff))
  fun dest_zipper x = x |> (CO.getter &&& ZCTXT.getter
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
  end
)

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(structure ZD = ZD; structure ZM = ZM)
open Z

fun cons_zcontext c = apfst (fn hs => hs @ [c])

end

\<^imap>\<open>\<open>{i}\<close> => \<open>
functor \<^eval>\<open>sfx_inst_T_nargs "Instantiate_List_Zipper" {i}\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.content
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {i}\<close>) Z.zipper
  = Z\<close>\<close>
