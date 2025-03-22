(*  Title:      HOCLP/alternating_zipper_nodes.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close> =
sig
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{i}.M.t = Z1.M.t
  sharing type Z{i}.ZO.L.lens = Z1.ZO.L.lens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} next = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container)
    Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>M.t
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) Z{i}.cat
  sharing type N{i}.node = Z{i}.ZO.content
  sharing type N{i}.L.lens = Z{i}.ZO.L.lens\<close>\<close>
end

signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close> =
sig
  structure A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} content = @{AllT_args} A.N{i}.content
  where type @{AllT_args} next = @{AllT_args} A.N{i}.next
  where type @{AllT_args} node = @{AllT_args} A.N{i}.node
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.N{i}.L.C.cat
  where type (@{ParaT_args} 't, 'o, 's, 'i) L.lens = (@{ParaT_args} 't, 'o, 's, 'i) A.N{i}.L.lens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zcontext{i}
  type @{AllT_args} pzipper{i}
  type @{AllT_args} parent{i} = (@{ParaT_args} @{AllT_args} pzipper{i})
    A.Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>M.t\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  val mk_zcontext{i} : (@{ParaT_args} @{AllT_args} A.Z{i}.ZO.zcontext *
    @{AllT_args} parent{i}, @{AllT_args} zcontext{i}) A.Z{i}.cat
  val parent{i} : unit -> (@{ParaT_args} @{AllT_args} zcontext{i},
    @{AllT_args} parent{i}) A.Z{i}.ZO.L.slens
  val pzipper{i} : unit -> (@{ParaT_args} @{AllT_args} zcontext{i},
    @{AllT_args} pzipper{i}) A.Z{i}.ZO.L.slens
  val lzcontext{i} : unit -> (@{ParaT_args} @{AllT_args} zcontext{i},
    @{AllT_args} A.Z{i}.ZO.zcontext) A.Z{i}.ZO.L.slens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure PZO{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER_OPTICS"\<close>
  where type @{AllT_args} content = @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content
  where type @{AllT_args} zcontext = @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
  where type @{AllT_args} zipper = @{AllT_args} pzipper{i}
  where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.Z{i}.cat
  where type (@{ParaT_args} 't, 'o, 's, 'i) L.lens = (@{ParaT_args} 't, 'o, 's, 'i) A.Z{i}.ZO.L.lens\<close>\<close>

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZO.content = @{AllT_args} A.Z{i}.ZO.content
  where type @{AllT_args} Z{i}.ZO.zcontext = @{AllT_args} zcontext{i}
  where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} A.Z{i}.ZM.container * @{AllT_args} parent{i}\<close>\<close>
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) A.Z1.M.t
  where type (@{ParaT_args} 't, 'o, 's, 'i) L.lens = (@{ParaT_args} 't, 'o, 's, 'i) A.Z1.ZO.L.lens
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
    structure A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    structure ZD : \<^eval>\<open>sfx_ParaT_nargs "ZIPPER_DATA"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close> =
struct

structure A = A
open A
structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = Z1
open M
structure AA = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow_Arrow_Apply"\<close>(M)
structure L = \<^eval>\<open>sfx_ParaT_nargs "Lens_App"\<close>(open AA; structure L = Z1.ZO.L)

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} lzcontext{i} = @{AllT_args} Z{i}.ZO.zcontext\<close>\<close>

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} zcontext{i} = ZContext{i} of (
    @{AllT_args} lzcontext{i},
    (@{ParaT_args} @{AllT_args} pzipper{i}) M.t
  ) lzcontext_parent\<close>
where sep = \<open>and\<close>\<close>
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} pzipper{i} = (@{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
  @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>) ZD.zipper\<close>
where sep = \<open>and\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} parent{i} = (@{ParaT_args} @{AllT_args} pzipper{i})
  A.Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>M.t\<close>\<close>

structure Base =
struct
  structure A = struct open AA AA.A end
  structure L = L
  structure ZD = ZD
end
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure PZO{i} = \<^eval>\<open>sfx_T_nargs "Zipper_Optics_Zipper_Data"\<close>(
  open Base
  type @{AllT_args} content = @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content
  type @{AllT_args} zcontext = @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
)\<close>\<close>

local structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(AA.A); open SC AA.A
in

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun mk_zcontext{i} x = x |> arr (uncurry lzcontext_parent #> ZContext{i})\<close>\<close>

structure LK = \<^eval>\<open>sfx_ParaT_nargs "Lens_Kleisli"\<close>(
  structure A = struct open AA.A AA end
  structure L = L)
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
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Extend_Zipper_Context"\<close>(
  open Base
  structure Z = Z{i}
  structure ZO = \<^eval>\<open>sfx_T_nargs "Zipper_Optics_Zipper_Data"\<close>(
    open BaseZO
    type @{AllT_args} content = @{AllT_args} Z{i}.ZO.content
    type @{AllT_args} zcontext = @{AllT_args} zcontext{i}
  )
  type @{AllT_args} new_zcontext = @{AllT_args} parent{i}
  type @{AllT_args} zcontext = @{AllT_args} zcontext{i}
  val mk_zcontext = mk_zcontext{i}
  fun get_base_zcontext x = x |> L.get (lzcontext{i} ())
  fun get_new_zcontext x = x |> L.get (parent{i} ())
)\<close>\<close>

structure Base =
struct
  structure MB = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(AA.K.M); open MB
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(MB); open SC
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M); open M
  open AA AA.A
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close> =
struct
  open Base
  type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  fun move x = x |>
    ((Z{i}.ZO.get_content >>> (N{i}.get_content &&& N{i}.get_next)) &&& Z{i}.ZO.get_zcontext
    >>> (fn ((content, next), zcontext) => next
    >>= (fn next => Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Zip.move
      (next, ZD.zipper content zcontext |> M.pure))))
end\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Up{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close> =
struct
  open Base
  type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>zipper
  fun move x = x |>
    (Z{i}.ZM.Unzip.move
    >>> (fn (next, parent) => parent
    >>= (arr ZD.dest_zipper
    >>> arr (fn {content, zcontext} => (pair content (M.pure next), zcontext))
    >>> first N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>node
    >>> Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>ZO.zipper)))
end\<close>\<close>

end

functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_nargs "Alternating_Zipper_Nodes_Base_Args"]\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.ZO.content
    where type @{AllT_args} Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.ZO.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) A.Z{i}.zipper\<close>\<close>
    where type (@{ParaT_args} 'a) Z1.M.t = (@{ParaT_args} 'a) A.Z1.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} N{i}.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) A.N{i}.content\<close>\<close>
 = A

functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_nargs "Alternating_Zipper_Nodes"]\<close>(
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} A.Z{i}.ZM.container = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZM.container
    where type @{AllT_args} A.Z{i}.ZO.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.content
    where type @{AllT_args} A.Z{i}.ZO.zcontext = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.ZO.zcontext
    where type @{AllT_args} A.Z{i}.zipper = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.A.Z{i}.zipper\<close>\<close>
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) Z.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} A.N{i}.content = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.A.N{i}.content\<close>\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} zcontext{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.zcontext{i}
    where type @{AllT_args} pzipper{i} = (@{ParaT_args}
      \<^imap>\<open>\<open>{j}\<close> => \<open>@{AllT_args} inst{j}\<close> where sep = ","\<close>) Z.pzipper{i}\<close>\<close>
    =
struct
open Z
structure Base = struct \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i} = @{AllT_args} inst{i}\<close>\<close> end
structure Z = \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_nargs "Alternating_Zipper"]\<close>(
  open Base; structure Z = Z)
open Z
end