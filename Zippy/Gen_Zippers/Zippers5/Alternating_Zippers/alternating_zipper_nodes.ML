(*  Title:      Zippy/alternating_zipper_nodes.ML
    Author:     Kevin Kappelmann
*)
signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close> =
sig
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure Z{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER"\<close>
  sharing type Z{i}.M.t = Z1.M.t
  sharing type Z{i}.ZD.L.lens = Z1.ZD.L.lens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} next = (@{ParaT_args}
    @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.container) Z{i}.M.t
  sharing type N{i}.node = Z{i}.ZD.content
  sharing type N{i}.L.K.M.t = Z{i}.M.t
  sharing type N{i}.L.lens = Z{i}.ZD.L.lens\<close>\<close>
end

 \<^imap>\<open>\<open>{j}\<close> => \<open>
functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper_Nodes_Base_Args" {j}]\<close>(
    type @{AllT_args} inst
    structure A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} Z{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) A.Z{i}.ZM.container
    where type @{AllT_args} Z{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) A.Z{i}.ZD.content
    where type @{AllT_args} Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) A.Z{i}.ZD.zcontext
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) A.Z{i}.zipper
    where type @{AllT_args} N{i}.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) A.N{i}.content\<close>\<close>
 = A\<close>\<close>


signature \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close> =
sig
  structure A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure N{i} : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
  where type @{AllT_args} next = @{AllT_args} A.N{i}.next
  sharing type N{i}.content = A.N{i}.content
  sharing type N{i}.node = A.N{i}.node
  sharing type N{i}.L.K.M.t = A.N{i}.L.K.M.t
  sharing type N{i}.L.lens = A.N{i}.L.lens\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  type @{AllT_args} zcontext{i}
  type @{AllT_args} pzipper{i}
  type @{AllT_args} parent{i} = (@{ParaT_args} @{AllT_args} pzipper{i}) A.Z{i}.M.t

  val zcontext{i} : (@{ParaT_args} @{AllT_args} A.Z{i}.ZD.zcontext *
    @{AllT_args} parent{i}, @{AllT_args} zcontext{i}) A.Z{i}.cat

  structure LZCTXT{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type LZCTXT{i}.container = zcontext{i}
  sharing type LZCTXT{i}.data = A.Z{i}.ZD.zcontext
  sharing type LZCTXT{i}.lens = A.Z{i}.ZD.L.lens
  sharing type LZCTXT{i}.K.M.t = A.Z{i}.M.t

  structure PARENT{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  where type @{AllT_args} data = @{AllT_args} parent{i}
  sharing type PARENT{i}.container = zcontext{i}
  sharing type PARENT{i}.lens = A.Z{i}.ZD.L.lens
  sharing type PARENT{i}.K.M.t = A.Z{i}.M.t

  structure PZ{i} : \<^eval>\<open>sfx_T_nargs "STRUCTURED_LENS"\<close>
  sharing type PZ{i}.container = zcontext{i}
  sharing type PZ{i}.data = pzipper{i}
  sharing type PZ{i}.lens = A.Z{i}.ZD.L.lens
  sharing type PZ{i}.K.M.t = A.Z{i}.M.t\<close>\<close>

  \<^imap>\<open>\<open>{i}\<close> => \<open>
  structure PZD{i} : \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  sharing type PZD{i}.content = N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content
  sharing type PZD{i}.zcontext = zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
  sharing type PZD{i}.zipper = pzipper{i}
  sharing type PZD{i}.L.K.M.t = A.Z{i}.M.t
  sharing type PZD{i}.L.lens = A.Z{i}.ZD.L.lens\<close>\<close>

  include \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER"\<close>
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  where type @{AllT_args} Z{i}.ZD.content = @{AllT_args} A.Z{i}.ZD.content
  where type @{AllT_args} Z{i}.ZD.zcontext = @{AllT_args} zcontext{i}
  where type @{AllT_args} Z{i}.ZM.container = @{AllT_args} A.Z{i}.ZM.container * @{AllT_args} parent{i}\<close>\<close>
  sharing type M.t = A.Z1.M.t
  sharing type L.lens = A.Z1.ZD.L.lens
end

functor \<^eval>\<open>pfx_sfx_nargs "Alternating_Zipper_Nodes"\<close>(
    A : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES_BASE_ARGS"\<close>
  ) : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close> =
struct

structure A = A
open A
structure M : \<^eval>\<open>sfx_ParaT_nargs "MOVE_BASE"\<close> = Z1
open M
structure L = Z1.ZD.L

(*stores local zipper context and parent*)
type ('lctxt, 'parent) lzcontext_parent = {
  lzcontext : 'lctxt,
  parent : 'parent
}

fun lzcontext_parent lzcontext parent = {lzcontext = lzcontext, parent = parent}

structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
  structure L = L
  type @{AllT_args} content = @{ZipperT_arg 0}
  type @{AllT_args} zcontext = @{ZipperT_arg 1})

datatype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} zcontext{i} = ZContext{i} of (
    @{AllT_args} Z{i}.ZD.zcontext,
    (@{ParaT_args} @{AllT_args} pzipper{i}) M.t) lzcontext_parent\<close>
where sep = \<open>and\<close>\<close>
withtype
\<^imap>\<open>\<open>{i}\<close> => \<open>
@{AllT_args} pzipper{i} = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg = "," "" and sep = "" and start = 2}) ZD.zipper\<close>
where sep = \<open>and\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
type @{AllT_args} parent{i} = (@{ParaT_args} @{AllT_args} pzipper{i}) A.Z{i}.M.t\<close>\<close>

(*create parent zipper data by simultaneous instantiation*)
\<^imap>\<open>\<open>{i}\<close> => \<open>
structure PZD{i} :
  \<^eval>\<open>sfx_T_nargs "ZIPPER_DATA"\<close>
  where type @{AllT_args} content = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg = "," "" and sep = "" and start = 2}) ZD.content
  where type @{AllT_args} zcontext = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg = "," "" and sep = "" and start = 2}) ZD.zcontext
  where type @{AllT_args} zipper = (@{ParaT_args}
    @{AllT_args} N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>content,
    @{AllT_args} zcontext\<^eval>\<open>pred_mod_nzippers {i}\<close>
    @{ZipperT_args encl_arg = "," "" and sep = "" and start = 2}) ZD.zipper
  = ZD\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
fun zcontext{i} x = x |> arr (uncurry lzcontext_parent #> ZContext{i})\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Base = struct open L; type @{AllT_args} container = @{AllT_args} zcontext{i} end
structure LZCTXT{i} =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} Z{i}.ZD.zcontext
  fun getter (ZContext{i} {lzcontext,...}) = M.pure lzcontext
  fun modifier (f, ZContext{i} {lzcontext, parent}) = M.bind (f lzcontext)
    (fn lzcontext => zcontext{i} (lzcontext, parent))
  fun lens _ = L.mk_lens getter modifier
end
structure PARENT{i} =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} parent{i}
  fun getter (ZContext{i} {parent,...}) = M.pure parent
  fun modifier (f, ZContext{i} {lzcontext, parent}) = M.bind (f parent)
    (fn parent => zcontext{i} (lzcontext, parent))
  fun lens _ = L.mk_lens getter modifier
end
structure PZ{i} =
struct
  open Base
  type @{AllT_args} data = @{AllT_args} pzipper{i}
  fun getter x = L.get_monad PARENT{i}.getter x
  fun modifier x = L.modify_monad PARENT{i}.modifier x
  fun lens _ = L.mk_lens getter modifier
end
\<close>\<close>

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Z{i} = \<^eval>\<open>sfx_T_nargs "Extend_Zipper_Context"\<close>(
  structure Z = Z{i}
  structure ZD = \<^eval>\<open>sfx_T_nargs "Zipper_Data"\<close>(
    structure L = L
    type @{AllT_args} content = @{AllT_args} Z{i}.ZD.content
    type @{AllT_args} zcontext = @{AllT_args} zcontext{i}
  )
  type @{AllT_args} new_zcontext = @{AllT_args} parent{i}
  val mk_zcontext = zcontext{i}
  val get_base_zcontext = LZCTXT{i}.getter
  val get_new_zcontext = PARENT{i}.getter
)\<close>\<close>

structure Base =
struct
  structure MB = \<^eval>\<open>sfx_ParaT_nargs "Move_Base"\<close>(K.M)
  structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(MB)
  structure A = \<^eval>\<open>sfx_ParaT_nargs "Kleisli_Arrow"\<close>(M)
  structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad"\<close>(M)
  open MB SC A M
end

\<^imap>\<open>\<open>{i}\<close> => \<open>
structure Down{i} : \<^eval>\<open>sfx_T_nargs "MOVE"\<close> =
struct
  open Base
  type @{AllT_args} from = @{AllT_args} Z{i}.zipper
  type @{AllT_args} to = @{AllT_args} Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>zipper
  fun move x = x |>
    ((Z{i}.ZD.CO.getter >>> (N{i}.CO.getter &&& N{i}.NEXT.getter)) &&& Z{i}.ZD.ZCTXT.getter
    >>> (fn ((content, next), zctxt) => next
    >>= (fn next => Z\<^eval>\<open>succ_mod_nzippers {i} ^ "."\<close>ZM.Zip.move
      (next, ZD.zipper (content, zctxt)))))
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
    >>= (PZD{i}.CO.getter &&& PZD{i}.ZCTXT.getter)
    >>= first (rpair (pure next) #> N\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>node)
    >>= Z\<^eval>\<open>pred_mod_nzippers {i} ^ "."\<close>ZD.zipper))
end\<close>\<close>

end

\<^imap>\<open>\<open>{j}\<close> => \<open>
functor \<^eval>\<open>mk_name ["Instantiate", pfx_sfx_inst_nargs "Alternating_Zipper_Nodes" {j}]\<close>(
    type @{AllT_args} inst
    structure Z : \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
  ) :
    \<^eval>\<open>pfx_sfx_nargs "ALTERNATING_ZIPPER_NODES"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    where type @{AllT_args} A.Z{i}.ZM.container = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.A.Z{i}.ZM.container
    where type @{AllT_args} A.Z{i}.ZD.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.A.Z{i}.ZD.content
    where type @{AllT_args} A.Z{i}.ZD.zcontext = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.A.Z{i}.ZD.zcontext
    where type @{AllT_args} A.Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.A.Z{i}.zipper
    where type @{AllT_args} A.N{i}.content = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.A.N{i}.content
    where type @{AllT_args} Z{i}.zipper = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.Z{i}.zipper
    where type @{AllT_args} zcontext{i} = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.zcontext{i}
    where type @{AllT_args} pzipper{i} = (@{ParaT_args}
      \<^eval>\<open>ML_Gen.inst_zipperT "@{AllT_args} inst" {j}\<close>) Z.pzipper{i}\<close>\<close>
  = Z\<close>\<close>