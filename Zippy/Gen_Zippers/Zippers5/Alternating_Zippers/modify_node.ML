(*  Title:      Zippy/modify_node.ML
    Author:     Kevin Kappelmann
*)
functor \<^eval>\<open>sfx_T_nargs "Instantiate_Node"\<close>(
    structure N : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    \<^imap>\<open>\<open>{i}\<close> => \<open>type @{AllT_args} inst{i}\<close>\<close>
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.content
    where type @{AllT_args} next = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.next
    where type @{AllT_args} node = (@{ParaT_args}
      \<^imap>\<open>\<open>{i}\<close> => \<open>@{AllT_args} inst{i}\<close> where sep = ","\<close>) N.node
  = N

functor \<^eval>\<open>sfx_T_nargs "Replace_Node_Content_Next"\<close>(
    structure A : \<^eval>\<open>sfx_ParaT_nargs "KLEISLI_ARROW_BASE"\<close>
    structure N : \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) A.cat
    type @{AllT_args} ncontent
    val ncontent : (@{ParaT_args} @{AllT_args} N.content, @{AllT_args} ncontent) A.cat
    val dest_ncontent : (@{ParaT_args} @{AllT_args} ncontent, @{AllT_args} N.content) A.cat
    type @{AllT_args} nnext val nnext : (@{ParaT_args} @{AllT_args} N.next, @{AllT_args} nnext) A.cat
    val dest_nnext : (@{ParaT_args} @{AllT_args} nnext, @{AllT_args} N.next) A.cat
  ) :
    \<^eval>\<open>sfx_T_nargs "NODE"\<close>
    where type @{AllT_args} content = @{AllT_args} ncontent
    where type @{AllT_args} next = @{AllT_args} nnext
    where type @{AllT_args} node = @{AllT_args} N.node
    where type (@{ParaT_args} 'a, 'b) L.C.cat = (@{ParaT_args} 'a, 'b) N.L.C.cat
    where type (@{ParaT_args} 't, 'o, 's, 'i) L.lens = (@{ParaT_args} 't, 'o, 's, 'i) N.L.lens
  =
struct

structure L = N.L
type @{AllT_args} content = @{AllT_args} ncontent
type @{AllT_args} next = @{AllT_args} nnext
type @{AllT_args} node = @{AllT_args} N.node

structure SC = \<^eval>\<open>sfx_ParaT_nargs "Semi_Category"\<close>(A) open SC A

fun node x = x |> ((dest_ncontent *** dest_nnext) >>> N.node)

fun content _ = L.comp (L.lens_get_mk ncontent dest_ncontent) (N.content ())
fun next _ = L.comp (L.lens_get_mk nnext dest_nnext) (N.next ())

fun get_content x = x |> L.get (content ())
fun get_next x = x |> L.get (next ())
fun map_content x = x |> L.modify (content ())
fun map_next x = x |> L.modify (next ())

end
