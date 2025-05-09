\<^marker>\<open>creator "Kevin Kappelmann"\<close>
theory Test_Less_Sequential_Mixins
  imports
    Zippy_Actions
    Zippy_Lists_Actions
    Zippy_Goals
    Zippy_Lists_Goals
    Zippy_Lists_Position
begin

ML\<open>
  local fun update_content old_content data_more m c = old_content (data_more m c)
  in
  structure Zippy =
  struct
    (* monads and arrows *)
    structure M = \<^eval>\<open>sfx_ParaT_nargs "Monad_Exception_Monad_Or"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Option_Monad_Or_Trans"\<close>(
      \<^eval>\<open>sfx_ParaT_nargs "Identity_Monad"\<close>))
    structure MU = Zippy_Monad_Util(M)
    structure MEU = Zippy_Monad_Exception_Util(M)

    (* misc *)
    structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util_Apply"\<close>(
      structure A = MU
      structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine_Util"\<close>(
        structure AE = MEU.AE
        structure Co = \<^eval>\<open>sfx_ParaT_nargs "Coroutine"\<close>(MEU.A)))

    (* create alternating zipper skeleton *)
    structure ZLP = Zippy_Lists_Position_Mixin_Base(Zippy_Lists_Base(M))
    structure ZL = Zippy_Lists(structure Z = ZLP; structure Co = Co)
    structure ZN = Zippy_Node(structure Z = ZL; structure AE = MEU.AE)
    structure Z = ZLP

    (* add data *)
    \<^imap>\<open>\<open>{i}\<close> => \<open>val content{i} = I\<close>\<close>

    (** goal clusters **)
    structure GClusters = Zippy_Goal_Clusters_Mixin_Base(ZN.Node_Co1)
    local
      structure DataM = GClusters.DataM
      val old_content = content1
    in fun content1 m = update_content old_content DataM.data_more m end

    (** goal cluster **)
    structure GCluster =
    struct
      local
        structure Base = Zippy_Goal_Cluster_Mixin_Base(ZN.Node_Co2)
        structure More = Zippy_Goal_Cluster_Mixin(Base)
      in open Base More end
    end
    local
      structure DataM = GCluster.DataM
      val old_content = content2
    in fun content2 m = update_content old_content DataM.data_more m end

    structure Goals = Zippy_Lists_Goals_Mixin(
      structure Z = ZL
      structure Goals = struct structure GClusters = GClusters; structure GCluster = GCluster end)

    (** action clusters **)
    (* structure Copy =
    struct
      local
        structure Base = Zippy_Copy_Mixin_Base(
          structure M = ZL
          structure L = ZN.Node_Co3
          type @{AllT_args} zipper_to = @{AllT_args} ZL.Z1.zipper
          type copy_update_data = unit)
        structure More = Zippy_Copy_Mixin(structure Copy = Base; structure AE = MEU.AE)
      in open Base More end
    end
    local
      structure DataM = Copy.DataM
      structure Base = struct type @{AllT_args} inst = @{AllT_args} DataM.data_more end
      val old_content = content3
    in
      structure ZN = Instantiate_Zippy_Node_3(open Base; structure Z = ZN)
      structure ZL = Instantiate_Zippy_Lists_3(open Base; structure Z = ZL)
      fun content3 m = update_content old_content DataM.data_more m
    end

    structure Copy =
    struct
      local structure More = Zippy_Lists_Copy_Mixin(structure Z = ZL; structure Copy = Copy)
      in open Copy More end
    end

    (** actions **)
    structure PAction = Zippy_PAction_Mixin_Base(
      structure M = Z
      structure L = ZN.Node_Co4
      type prio = int)
    local
      structure DataM = PAction.DataM
      structure Base = struct type @{AllT_args} inst = @{AllT_args} DataM.data_more end
      val old_content = content4
    in
      structure ZN = Instantiate_Zippy_Node_4(open Base; structure Z = ZN)
      structure ZL = Instantiate_Zippy_Lists_4(open Base; structure Z = ZL)
      fun content4 m = update_content old_content DataM.data_more m
    end

    structure PResults =
    struct
      local
        structure Base = Zippy_PResults_Mixin_Base(
          structure L = PAction.DataM_More
          structure Co = Co
          type prio = PAction.prio
          type result = unit)
        structure More = Zippy_PResults_Mixin(structure PResults = Base; structure K = MEU.AE.K)
      in open Base More end
    end
    local
      structure DataM = PResults.DataM
      structure Base = struct type @{AllT_args} inst = @{AllT_args} DataM.data_more end
      val old_content = content4
    in
      structure ZN = Instantiate_Zippy_Node_4(open Base; structure Z = ZN)
      structure ZL = Instantiate_Zippy_Lists_4(open Base; structure Z = ZL)
      structure PAction =
      struct
        local
          structure Base = Instantiate_Zippy_PAction_Mixin_Base_4(
            open Base; structure PAction = PAction)
          structure More = Zippy_PAction_Mixin(structure PAction = Base; structure AE = MEU.AE)
        in open PAction Base More end
      end
      fun content4 m = update_content old_content DataM.data_more m
    end

    structure PAction_PResults = Zippy_PAction_PResults_Mixin(
      struct structure PResults = PResults; structure PAction = PAction end)

    structure ActionAN =
    struct
      local
        structure Base = Zippy_Action_App_Num_Mixin_Base(PResults.DataM_More)
        structure More = Zippy_Action_App_Num_Mixin(Base)
      in open Base More end
    end
    local
      structure DataM = ActionAN.DataM
      structure Base = struct type @{AllT_args} inst = @{AllT_args} DataM.data_more end
      val old_content = content4
    in
      structure ZN = Instantiate_Zippy_Node_4(open Base; structure Z = ZN)
      structure ZL = Instantiate_Zippy_Lists_4(open Base; structure Z = ZL)
      fun content4 m = update_content old_content DataM.data_more m
    end

    (** action applications **)
    structure AActionAN =
    struct
      local
        structure Base = Zippy_Action_App_Num_Mixin_Base(
          struct
            open ZN.Node_Co5
            type @{AllT_args} container = (@{ParaT_args}
              @{ZipperT_args start = 4},
              @{ZipperT_args stop = 3}) container
          end)
        structure More = Zippy_Action_App_Num_Mixin(Base)
      in open Base More end
    end
    local
      structure DataM :
        \<^eval>\<open>sfx_T_nargs "DATA_MORE"\<close>
        where type @{AllT_args} data = (@{ParaT_args}
          @{ZipperT_args start = 1},
          @{ZipperT_args stop = 0}) AActionAN.DataM.data
        where type @{AllT_args} more = (@{ParaT_args}
          @{ZipperT_args start = 1},
          @{ZipperT_args stop = 0}) AActionAN.DataM.more
        = AActionAN.DataM
      structure Base = struct type @{AllT_args} inst = @{AllT_args} DataM.data_more end
      val old_content = content5
    in
      structure ZN = Instantiate_Zippy_Node_5(open Base; structure Z = ZN)
      structure ZL = Instantiate_Zippy_Lists_5(open Base; structure Z = ZL)
      fun content5 m = update_content old_content DataM.data_more m
    end

    structure Prio = Zippy_Prio_Mixin_Base(
      structure L :
        \<^eval>\<open>sfx_T_nargs "SSTRUCTURED_LENS"\<close>
        where type @{AllT_args} container = @{AllT_args} ZN.Z5.zipper
        where type @{AllT_args} data = @{ZipperT_arg 4}
        = AActionAN.DataM_More
      type prio = PResults.prio)
    local
      structure DataM = Prio.DataM
      structure Base = struct type @{AllT_args} inst = @{AllT_args} DataM.data_more end
      val old_content = content5
    in
      structure ZN = Instantiate_Zippy_Node_5(open Base; structure Z = ZN)
      structure ZL = Instantiate_Zippy_Lists_5(open Base; structure Z = ZL)
      fun content5 m = update_content old_content DataM.data_more m
    end *)

    (*close content constructors*)
    \<^imap>\<open>\<open>{i}\<close> => \<open>val closed_content{i} = content{i} ()\<close>\<close>
    (*open basic functions*)
    open Z
  end
  end
\<close>

ML_val\<open>
  local open Zippy Zippy.MEU.SC
  in
  val aan1 = ZN.node_no_next5 () (closed_content5 0 AActionAN.AAN.init)
  val pact = PAction.no_paction ()
  val paco = PResults.Co.cons (MEU.A.K 10) (PResults.empty_aco ())
  val presults = PResults.presults paco
  val an1 = ZCore.N4.node (closed_content4 ActionAN.AAN.init presults pact, M.pure [aan1])
  val an2 = ZN.node_no_next4 () (closed_content4 ActionAN.AAN.init presults pact)
  val copy = Copy.copy (fn cud => fn z3 => fn z1 => MEU.AE.throw ())
  val cn1 = ZCore.N3.node (closed_content3 copy, M.pure [an1, an2])
  val test =
    (
    Z3.ZM.Zip.move
    >>> Down3.move
    (* >>> Z4.ZM.Down.move *)
    >>> Down4.move
    >>> arr AActionAN.L.getter
    (* >>> PResults.get_run_presults *)
    (* >>> PAction.get_run_paction *)
    )
    (init_container3 (ZN.container_no_parent () [cn1]))
  end
\<close>

end
