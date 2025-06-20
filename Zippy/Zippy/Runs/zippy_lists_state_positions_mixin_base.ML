(*  Title:      Zippy/zippy_lists_state_positions_mixin_base.ML
    Author:     Kevin Kappelmann
*)
signature ZIPPY_LISTS_STATE_POSITIONS_MIXIN_BASE =
sig
  structure ZS : ZIPPY_STATE_MIXIN_BASE

  include ZIPPY_LISTS_POSITIONS_MIXIN_BASE
  where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) ZS.M.t
  \<^imap>\<open>\<open>{i}\<close> => \<open>
  sharing type ZS.Z{i}.ZM.container = Z{i}.ZM.container
  sharing type ZS.Z{i}.ZD.content = Z{i}.ZD.content
  sharing type ZS.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
  sharing type ZS.Z{i}.zipper = Z{i}.zipper\<close>\<close>
end

functor Zippy_Lists_State_Positions_Mixin_Base(A :
  sig
    structure ZS : ZIPPY_STATE_MIXIN_BASE
    include ZIPPY_LISTS_POSITIONS_MIXIN_BASE
    where type (@{ParaT_args} 'a) M.t = (@{ParaT_args} 'a) ZS.M.t
    \<^imap>\<open>\<open>{i}\<close> => \<open>
    sharing type ZS.Z{i}.ZM.container = Z{i}.ZM.container
    sharing type ZS.Z{i}.ZD.content = Z{i}.ZD.content
    sharing type ZS.Z{i}.ZD.zcontext = Z{i}.ZD.zcontext
    sharing type ZS.Z{i}.zipper = Z{i}.zipper\<close>\<close>
  end
  ) : ZIPPY_LISTS_STATE_POSITIONS_MIXIN_BASE
  = A
