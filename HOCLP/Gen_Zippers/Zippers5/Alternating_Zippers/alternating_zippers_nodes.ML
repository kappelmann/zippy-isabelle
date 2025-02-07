(*  Title:      HOCLP/alternating_zippers_nodes.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close> =
sig
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER"\<close>
  sharing type Z{i}.M.t = Z1.M.t
  sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
  where type @{T_args} next = (@{ParaT_args},
    @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>M.t
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) Z{i}.cat
  sharing type N{i}.node = Z{i}.ZO.content
  sharing type N{i}.L.lens = Z{i}.ZO.L.lens\<close>\<close>
end

signature \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close> =
sig
  structure A : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "NODE"\<close>
  where type @{T_args} content = @{T_args} A.N{i}.content
  where type @{T_args} next = @{T_args} A.N{i}.next
  where type @{T_args} node = @{T_args} A.N{i}.node
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.N{i}.L.C.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.N{i}.L.lens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{T_args} zcontext{i}
  type @{T_args} pzipper{i}
  type @{T_args} parent{i} = (@{ParaT_args}, @{T_args} pzipper{i})
    A.Z\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>M.t\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val mk_zcontext{i} : (@{ParaT_args}, @{T_args} A.Z{i}.ZO.zcontext *
    @{T_args} parent{i}, @{T_args} zcontext{i}) A.Z{i}.cat
  val parent{i} : unit -> (@{ParaT_args}, @{T_args} zcontext{i},
    @{T_args} parent{i}) A.Z{i}.ZO.L.slens
  val pzipper{i} : unit -> (@{ParaT_args}, @{T_args} zcontext{i},
    @{T_args} pzipper{i}) A.Z{i}.ZO.L.slens
  val lzcontext{i} : unit -> (@{ParaT_args}, @{T_args} zcontext{i},
    @{T_args} A.Z{i}.ZO.zcontext) A.Z{i}.ZO.L.slens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure PZO{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "ZIPPER" ^ "_OPTICS"\<close>
  where type @{T_args} content = @{T_args} N\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>content
  where type @{T_args} zcontext = @{T_args} zcontext\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i}\<close>
  where type @{T_args} zipper = @{T_args} pzipper{i}
  where type ('p1, 'a, 'b) L.C.cat = ('p1, 'a, 'b) A.Z{i}.cat
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z{i}.ZO.L.lens\<close>\<close>

  include \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{T_args} Z{i}.ZO.content = @{T_args} A.Z{i}.ZO.content
  where type @{T_args} Z{i}.ZO.zcontext = @{T_args} zcontext{i}
  where type @{T_args} Z{i}.ZM.container = @{T_args} A.Z{i}.ZM.container * @{T_args} parent{i}\<close>\<close>
  where type ('p1, 'a) M.t = ('p1, 'a) A.Z1.M.t
  where type ('p1, 't, 'o, 's, 'i) L.lens = ('p1, 't, 'o, 's, 'i) A.Z1.ZO.L.lens
end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Alternating_Zippers" ^ "_Nodes"\<close>(
    structure A : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close>
    structure ZD : ZIPPER_DATA
  ) : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close> =
struct

structure A = A
open A
structure M : MOVE_BASE = Z1
open M
structure AA = Kleisli_Arrow_Arrow_Apply(M)
structure L = Lens_App(open AA; structure L = Z1.ZO.L)

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{T_args} lzcontext{i} = @{T_args} Z{i}.ZO.zcontext\<close>\<close>

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{T_args} zcontext{i} = ZContext{i} of (
    @{T_args} lzcontext{i},
    (@{ParaT_args}, @{T_args} pzipper{i}) M.t
  ) lzcontext_parent\<close>
where sep = \<open>and\<close>\<close>
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{T_args} pzipper{i} = (@{T_args} N\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>content,
  @{T_args} zcontext\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i}\<close>) ZD.zipper\<close>
where sep = \<open>and\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{T_args} parent{i} = (@{ParaT_args}, @{T_args} pzipper{i})
  A.Z\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>M.t\<close>\<close>

structure Base =
struct
  structure A = struct open AA AA.A end
  structure L = L
  structure ZD = ZD
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure PZO{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data"\<close>(
  open Base
  type @{T_args} content = @{T_args} N\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>content
  type @{T_args} zcontext = @{T_args} zcontext\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i}\<close>
)\<close>\<close>

local structure SC = Semi_Category(AA.A); open SC AA.A
in

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun mk_zcontext{i} x = x |> arr (uncurry lzcontext_parent #> ZContext{i})\<close>\<close>

structure LK = Lens_Kleisli(structure A = struct open AA.A AA end; structure L = L)
fun monad_lens l = LK.lens_monad l

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun zcontext{i} _ = L.lens_get_mk
  (arr (fn (ZContext{i} {lzcontext, parent}) => (lzcontext, parent))) mk_zcontext{i}
fun lzcontext{i} _ = L.lens_fst (zcontext{i} ())
fun parent{i} _ = L.lens_snd (zcontext{i} ())
fun pzipper{i} _ = monad_lens (parent{i} ())\<close>\<close>

end

structure Base = struct structure A = struct open AA AA.A end end
structure BaseZO =
struct
  structure A = struct open AA AA.A end
  structure ZD = ZD
  structure L = Z1.ZO.L
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>T_Args.suffix_Poly_nargs "Extend_Zipper" ^ "_Context"\<close>(
  open Base
  structure Z = Z{i}
  structure ZO = \<^eval>\<open>T_Args.suffix_Poly_nargs "Zipper" ^ "_Optics_Zipper_Data"\<close>(
    open BaseZO
    type @{T_args} content = @{T_args} Z{i}.ZO.content
    type @{T_args} zcontext = @{T_args} zcontext{i}
  )
  type @{T_args} new_zcontext = @{T_args} parent{i}
  type @{T_args} zcontext = @{T_args} zcontext{i}
  val mk_zcontext = mk_zcontext{i}
  fun get_base_zcontext x = x |> L.get (lzcontext{i} ())
  fun get_new_zcontext x = x |> L.get (parent{i} ())
)\<close>\<close>

structure Base =
struct
  structure MB = Move_Base(AA.K.M); open MB
  structure SC = Semi_Category(MB); open SC
  structure M = Monad(M); open M
  open AA AA.A
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close> =
struct
  open Base
  type @{T_args} from = @{T_args} Z{i}.zipper
  type @{T_args} to = @{T_args} Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>zipper
  fun move x = x |>
    ((Z{i}.ZO.get_content >>> (N{i}.get_content &&& N{i}.get_next)) &&& Z{i}.ZO.get_zcontext
    >>> (fn ((content, next), zcontext) => next
    >>= (fn next => Z\<^eval>\<open>T_Args.succ_mod_Poly_nargs' {i} ^ "."\<close>ZM.Zip.move
      (next, ZD.zipper content zcontext |> M.pure))))
end\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} : \<^eval>\<open>T_Args.suffix_Poly_nargs "MOVE"\<close> =
struct
  open Base
  type @{T_args} from = @{T_args} Z{i}.zipper
  type @{T_args} to = @{T_args} Z\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>zipper
  fun move x = x |>
    (Z{i}.ZM.Unzip.move
    >>> (fn (next, parent) => parent
    >>= (arr ZD.dest_zipper
    >>> arr (fn {content, zcontext} => (pair content (M.pure next), zcontext))
    >>> first N\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>node
    >>> Z\<^eval>\<open>T_Args.pred_mod_Poly_nargs' {i} ^ "."\<close>ZO.zipper)))
end\<close>\<close>

end

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers" ^ "_Nodes_Base_Args"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure A : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.ZM.container
    where type @{T_args} Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.ZO.content
    where type @{T_args} Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.ZO.zcontext
    where type @{T_args} Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.zipper\<close>\<close>
    where type ('p1, 'a) Z1.M.t = ('p1, 'a) A.Z1.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} N{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) A.N{i}.content\<close>\<close>
 = A

functor \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers" ^ "_Nodes"\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close>
  ) :
    \<^eval>\<open>T_Args.suffix_Poly_nargs "ALTERNATING_ZIPPERS" ^ "_NODES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.Z{i}.ZM.container = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZM.container
    where type @{T_args} A.Z{i}.ZO.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.content
    where type @{T_args} A.Z{i}.ZO.zcontext = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.zcontext
    where type @{T_args} A.Z{i}.zipper = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.zipper\<close>\<close>
    where type ('p1, 'a) M.t = ('p1, 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} A.N{i}.content = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.A.N{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{T_args} zcontext{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.zcontext{i}
    where type @{T_args} pzipper{i} = (@{ParaT_args},
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{T_args} inst{j}\<close> where sep = ","\<close>) Z.pzipper{i}\<close>\<close>
    =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{T_args} inst{i} = @{T_args} inst{i}\<close>\<close> end
structure Z = \<^eval>\<open>T_Args.suffix_Poly_nargs "Instantiate_Alternating_Zippers"\<close>(
  open Base; structure Z = Z)
open Z
end