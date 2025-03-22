(*  Title:      HOCLP/list_zipper.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close> =
sig
  structure LI : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
  type @{AllT_args} content
  include \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  where type @{AllT_args} ZO.content = @{AllT_args} content
  where type @{AllT_args} ZO.zcontext = @{AllT_args} content LI.t * @{AllT_args} content LI.t
  where type @{AllT_args} ZM.container = @{AllT_args} content LI.t
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) LI.M.t
  val cons_zcontext : @{AllT_args} content -> @{AllT_args} ZO.zcontext -> @{AllT_args} ZO.zcontext
end

functor \<^eval>\<open>sfx_T_nargs "List_Zipper"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW"\<close>
    structure L : \<^eval>\<open>sfx_ParaT_nargs "LENS"\<close>
    where type (@{ParaT_args} 'a, 'b) C.cat = (@{ParaT_args} 'a, 'b) A.cat
    structure LI : \<^eval>\<open>sfx_ParaT_nargs "GLIST"\<close>
    where type 'a t = 'a list
    sharing type LI.M.t = A.K.M.t
    val mk_exn_horizontal : (@{ParaT_args} unit, @{ParaT_args encl = "(" ")"} LI.M.exn) A.cat
    type @{AllT_args} content
  ) :
    \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
    where type @{AllT_args} content = @{AllT_args} content
   =
struct

type @{AllT_args} content = @{AllT_args} content

structure LI = LI
structure ZO = \<^eval>\<open>sfx_T_nargs "Zipper_Optics_Zipper_Data"\<close>(
struct
  structure ZD = \<^eval>\<open>sfx_ParaT_nargs "Zipper_Data"\<close>
  structure A = A
  structure L = L
  type @{AllT_args} content = @{AllT_args} content
  type @{AllT_args} zcontext = @{AllT_args} content LI.t * @{AllT_args} content LI.t
end
)
structure ZM = \<^eval>\<open>sfx_T_nargs "Zipper_Moves"\<close>(
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(A.K.M)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A)
  open SC ZO A
  type @{AllT_args} container = @{AllT_args} content LI.t
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

structure Z = \<^eval>\<open>sfx_T_nargs "Zipper"\<close>(
  structure ZO = ZO; structure ZM = ZM)
open Z

fun cons_zcontext c = apfst (fn hs => hs @ [c])

end

functor \<^eval>\<open>sfx_T_nargs "Instantiate_List_Zipper"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "LIST_ZIPPER"\<close>
    where type 'a LI.t = 'a Z.LI.t
    where type @{AllT_args} content = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.content
    where type @{AllT_args} zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) Z.zipper
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
  = Z
