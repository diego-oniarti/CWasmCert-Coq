(** Wasm operational semantics **)
(** The interpreter in the [interpreter_func] module is an executable version of this operational semantics. **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Coq Require Import ZArith.BinInt BinNat.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From CWasm Require Export operations colored_memory color_ptr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section Opsem.
   Context `{PointerBytes}.

   Inductive reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=

(** unop **)
  | rs_unop : forall v op t,
    reduce_simple [::AI_const v; AI_basic (BI_unop t op)] [::AI_const (@app_unop op v)]

(** binop **)
  | rs_binop_success : forall v1 v2 v op t,
    app_binop op v1 v2 = Some v ->
    reduce_simple [::AI_const v1; AI_const v2; AI_basic (BI_binop t op)] [::AI_const v]
  | rs_binop_failure : forall v1 v2 op t,
    app_binop op v1 v2 = None ->
    reduce_simple [::AI_const v1; AI_const v2; AI_basic (BI_binop t op)] [::AI_trap]

  (** testops **)
  | rs_testop_i32 :
    forall c testop,
    reduce_simple [::AI_const (VAL_int32 c); AI_basic (BI_testop T_i32 testop)] [::AI_const (VAL_int32 (wasm_bool (@app_testop_i i32t testop c)))]
  | rs_testop_i64 :
    forall c testop,
    reduce_simple [::AI_const (VAL_int64 c); AI_basic (BI_testop T_i64 testop)] [::AI_const (VAL_int32 (wasm_bool (@app_testop_i i64t testop c)))]

  (** relops **)
  | rs_relop: forall v1 v2 t op,
    reduce_simple [::AI_const v1; AI_const v2; AI_basic (BI_relop t op)] [::AI_const (VAL_int32 (wasm_bool (app_relop op v1 v2)))]

  (** convert and reinterpret **)
  | rs_convert_success :
    forall t1 t2 v v' sx,
    types_agree t1 v ->
    cvt t2 sx v = Some v' ->
    reduce_simple [::AI_const v; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_const v']
  | rs_convert_failure :
    forall t1 t2 v sx,
    types_agree t1 v ->
    cvt t2 sx v = None ->
    reduce_simple [::AI_const v; AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_trap]
  | rs_reinterpret :
    forall t1 t2 v,
      t1 <> T_pointer -> t2 <> T_pointer ->
    types_agree t1 v ->
    reduce_simple [::AI_const v; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_const (wasm_deserialise (bits v) t2)]

  (** control-flow operations **)
  | rs_unreachable :
    reduce_simple [::AI_basic BI_unreachable] [::AI_trap]
  | rs_nop :
    reduce_simple [::AI_basic BI_nop] [::]
  | rs_drop :
    forall v,
    reduce_simple [::AI_const v; AI_basic BI_drop] [::]
  | rs_select_false :
    forall n v1 v2,
    n = Wasm_int.int_zero i32m ->
    reduce_simple [::AI_const v1; AI_const v2; AI_const (VAL_int32 n); AI_basic BI_select] [::AI_const v2]
  | rs_select_true :
    forall n v1 v2,
    n <> Wasm_int.int_zero i32m ->
    reduce_simple [::AI_const v1; AI_const v2; AI_const (VAL_int32 n); AI_basic BI_select] [::AI_const v1]
  | rs_block :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) [::AI_label m [::] (vs ++ to_e_list es)]
  | rs_loop :
      forall vs es n m t1s t2s,
        const_list vs ->
        length vs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_simple (vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)]) [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)]
  | rs_if_false :
      forall n tf e1s e2s,
        n = Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_const (VAL_int32 n); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e2s)]
  | rs_if_true :
      forall n tf e1s e2s,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple ([::AI_const (VAL_int32 n); AI_basic (BI_if tf e1s e2s)]) [::AI_basic (BI_block tf e1s)]
  | rs_label_const :
      forall n es vs,
        const_list vs ->
        reduce_simple [::AI_label n es vs] vs
  | rs_label_trap :
      forall n es,
        reduce_simple [::AI_label n es [::AI_trap]] [::AI_trap]
  | rs_br :
      forall n vs es i LI lh,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
        reduce_simple [::AI_label n es LI] (vs ++ es)
  | rs_br_if_false :
      forall n i,
        n = Wasm_int.int_zero i32m ->
        reduce_simple [::AI_const (VAL_int32 n); AI_basic (BI_br_if i)] [::]
  | rs_br_if_true :
      forall n i,
        n <> Wasm_int.int_zero i32m ->
        reduce_simple [::AI_const (VAL_int32 n); AI_basic (BI_br_if i)] [::AI_basic (BI_br i)]
  | rs_br_table :
      forall iss c i j,
        length iss > Wasm_int.nat_of_uint i32m c ->
        List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
        reduce_simple [::AI_const (VAL_int32 c); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br j)]
  | rs_br_table_length :
      forall iss c i,
        length iss <= (Wasm_int.nat_of_uint i32m c) ->
        reduce_simple [::AI_const (VAL_int32 c); AI_basic (BI_br_table iss i)] [::AI_basic (BI_br i)]
  | rs_local_const :
      forall es n f,
        const_list es ->
        length es = n ->
        reduce_simple [::AI_local n f es] es
  | rs_local_trap :
      forall n f,
        reduce_simple [::AI_local n f [::AI_trap]] [::AI_trap]
  | rs_return :
      forall n i vs es lh f,
        const_list vs ->
        length vs = n ->
        lfilled i lh (vs ++ [::AI_basic BI_return]) es ->
        reduce_simple [::AI_local n f es] vs
  | rs_tee_local :
      forall i v,
        is_const v ->
        reduce_simple [::v; AI_basic (BI_tee_local i)] [::v; v; AI_basic (BI_set_local i)]

  | rs_pointeradd_success :
      forall p c n p',
        n = Wasm_int.Z_of_sint i32m c ->
        pointer_arith p n = Some p' ->
        reduce_simple [:: AI_const (VAL_int32 c); AI_const (VAL_pointer p); AI_basic BI_pointeradd]
          [:: AI_const (VAL_pointer p')]

  | rs_pointeradd_failure :
      forall p c n,
        n = Wasm_int.Z_of_sint i32m c ->
        pointer_arith p n = None ->
        reduce_simple [:: AI_const (VAL_int32 c); AI_const (VAL_pointer p); AI_basic BI_pointeradd]
          [:: AI_trap]

  | rs_pointersub_success :
      forall p c n p',
        n = Wasm_int.Z_of_sint i32m c ->
        pointer_arith p (- n)%Z = Some p' ->
        reduce_simple [:: AI_const (VAL_int32 c); AI_const (VAL_pointer p); AI_basic BI_pointersub]
          [:: AI_const (VAL_pointer p')]

  | rs_pointersub_failure :
      forall p c n,
        n = Wasm_int.Z_of_sint i32m c ->
        pointer_arith p (- n)%Z = None ->
        reduce_simple [:: AI_const (VAL_int32 c); AI_const (VAL_pointer p); AI_basic BI_pointersub]
          [:: AI_trap]

  | rs_pointerdiff_success :
      forall p1 p2 d,
        same_origin p1 p2 ->
        d = (Z.of_N p1.(ptr_addr) - Z.of_N p2.(ptr_addr))%Z ->
        reduce_simple [:: AI_const (VAL_pointer p1); AI_const (VAL_pointer p2); AI_basic BI_pointerdiff]
          [:: AI_const (VAL_int32 (Wasm_int.int_of_Z i32m d))]

  | rs_pointerdiff_failure :
      forall p1 p2,
        ~ same_origin p1 p2 ->
        reduce_simple [:: AI_const (VAL_pointer p1); AI_const (VAL_pointer p2); AI_basic BI_pointerdiff]
          [:: AI_trap]

  | rs_isnull_true :
     forall p, is_null p ->
    reduce_simple [:: AI_const (VAL_pointer p) ; AI_basic BI_isnull ] [:: AI_const (VAL_int32 (Wasm_int.Int32.repr 1))]

  | rs_isnull_false:
     forall p, ~~is_null p ->
     reduce_simple [:: AI_const (VAL_pointer p) ; AI_basic BI_isnull ] [:: AI_const (VAL_int32 (Wasm_int.Int32.repr 0))]

  | rs_demote:
    forall p p',
      ptr_addr p = ptr_addr p' ->
      ptr_col p = ptr_col p' ->
      ptr_freeable p' = false ->
      reduce_simple [:: AI_const (VAL_pointer p); AI_basic BI_demote]
        [:: AI_const (VAL_pointer p')]

  | rs_trap :
      forall es lh,
        es <> [::AI_trap] ->
        lfilled 0 lh [::AI_trap] es ->
        reduce_simple es [::AI_trap]
  .

Inductive reduce_silent : store_record -> frame -> list administrative_instruction ->
                   store_record -> frame -> list administrative_instruction -> Prop :=
  | r_simple :
      forall e e' s f,
        reduce_simple e e' ->
        reduce_silent s f e s f e'

  (** calling operations **)
  | r_call :
      forall s f i a,
        List.nth_error f.(f_inst).(inst_funcs) i = Some a ->
        reduce_silent s f [::AI_basic (BI_call i)] s f [::AI_invoke a]
  | r_call_indirect_success :
      forall s f i a cl c ,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes s f.(f_inst) i = Some (cl_type cl) ->
        reduce_silent s f [::AI_const (VAL_int32 c); AI_basic (BI_call_indirect i)] s f [::AI_invoke a]
  | r_call_indirect_failure1 :
      forall s f i a cl c,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
        List.nth_error s.(s_funcs) a = Some cl ->
        stypes s f.(f_inst) i <> Some (cl_type cl) ->
        reduce_silent s f [::AI_const (VAL_int32 c); AI_basic (BI_call_indirect i)] s f [::AI_trap]
  | r_call_indirect_failure2 :
      forall s f i c,
        stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
        reduce_silent s f [::AI_const (VAL_int32 c); AI_basic (BI_call_indirect i)] s f [::AI_trap]
  | r_invoke_native :
      forall a cl t1s t2s ts es ves vcs n m k zs s f f' i,
        List.nth_error s.(s_funcs) a = Some cl ->
        cl = FC_func_native i (Tf t1s t2s) ts es ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length ts = k ->
        length t1s = n ->
        length t2s = m ->
        n_zeros ts = zs ->
        f'.(f_inst) = i ->
        f'.(f_locs) = vcs ++ zs ->
        reduce_silent s f (ves ++ [::AI_invoke a]) s f [::AI_local m f' [::AI_basic (BI_block (Tf [::] t2s) es)]]
  | r_invoke_host :
      forall a cl h t1s t2s ves vcs m n s f,
        List.nth_error s.(s_funcs) a = Some cl ->
        cl = FC_func_host (Tf t1s t2s) h ->
        ves = v_to_e_list vcs ->
        length vcs = n ->
        length t1s = n ->
        length t2s = m ->
        reduce_silent s f (ves ++ [::AI_invoke a]) s f [:: AI_call_host (Tf t1s t2s) h vcs]


  (** get, set, load, and store operations **)
  | r_get_local :
      forall f v j s,
        List.nth_error f.(f_locs) j = Some v ->
        reduce_silent s f [::AI_basic (BI_get_local j)] s f [::AI_const v]
  | r_set_local :
      forall f f' i v s vd,
        f'.(f_inst) = f.(f_inst) ->
        i < length f.(f_locs) ->
        f'.(f_locs) = set_nth vd f.(f_locs) i v ->
        reduce_silent s f [::AI_const v; AI_basic (BI_set_local i)] s f' [::]
  | r_get_global :
      forall s f i v,
        sglob_val s f.(f_inst) i = Some v ->
        reduce_silent s f [::AI_basic (BI_get_global i)] s f [::AI_const v]
  | r_set_global :
      forall s f i v s',
        supdate_glob s f.(f_inst) i v = Some s' ->
        reduce_silent s f [::AI_const v; AI_basic (BI_set_global i)] s' f [::]
 | r_load_success :
   forall s i f t bs k a off m,
     t <> T_pointer ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load m (Wasm_int.N_of_uint i32m k) off (t_length t) = Some bs ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_basic (BI_load t None a off)] s f [::AI_const (wasm_deserialise bs t)]
  | r_load_failure :
    forall s i f t k a off m,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      t = T_pointer \/ load m (Wasm_int.N_of_uint i32m k) off (t_length t) = None ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_basic (BI_load t None a off)] s f [::AI_trap]
  | r_load_packed_success :
    forall s i f t tp k a off m bs sx,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = Some bs ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) a off)] s f [::AI_const (wasm_deserialise bs t)]
  | r_load_packed_failure :
    forall s i f t tp k a off m sx,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      load_packed sx m (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t) = None ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_basic (BI_load t (Some (tp, sx)) a off)] s f [::AI_trap]
  | r_store_success :
    forall t v s i f mem' k a off m,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = Some mem' ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_const v; AI_basic (BI_store t None a off)] (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_failure :
    forall t v s i f m k off a,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store m (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t) = None ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_const v; AI_basic (BI_store t None a off)] s f [::AI_trap]
  | r_store_packed_success :
    forall t v s i f m k off a mem' tp,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = Some mem' ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_const v; AI_basic (BI_store t (Some tp) a off)] (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::]
  | r_store_packed_failure :
    forall t v s i f m k off a tp,
      types_agree t v ->
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp) = None ->
      reduce_silent s f [::AI_const (VAL_int32 k); AI_const v; AI_basic (BI_store t (Some tp) a off)] s f [::AI_trap]

  (** memory **)
  | r_current_memory :
      forall i f m n s,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce_silent s f [::AI_basic (BI_current_memory)] s f [::AI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)))]
  | r_grow_memory_success :
    forall s i f m n mem' c,
      smem_ind s f.(f_inst) = Some i ->
      List.nth_error s.(s_mems) i = Some m ->
      mem_size m = n ->
      mem_grow m (Wasm_int.N_of_uint i32m c) = Some mem' ->
      reduce_silent s f [::AI_const (VAL_int32 c); AI_basic BI_grow_memory] (upd_s_mem s (update_list_at s.(s_mems) i mem')) f [::AI_const (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat n)))]
  | r_grow_memory_failure :
      forall i f m n s c,
        smem_ind s f.(f_inst) = Some i ->
        List.nth_error s.(s_mems) i = Some m ->
        mem_size m = n ->
        reduce_silent s f [::AI_const (VAL_int32 c); AI_basic BI_grow_memory] s f [::AI_const (VAL_int32 int32_minus_one)]
  .

  Inductive reduce : store_record -> frame -> list administrative_instruction ->
                     memory_event ->
                     store_record -> frame -> list administrative_instruction -> Prop :=
  | rm_silent :
    forall s f es s' f' es',
      reduce_silent s f es s' f' es' ->
      reduce s f es Eempty s' f' es'

  | rm_colload_success :
    forall s f t bs c cm tbs p v A,
      t <> T_pointer ->
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      p.(ptr_col) = Some c ->
      isAlloc c A ->
      (* The boundary check is implicitly implemented by read_colbytes,
      which returns None if it goes out of range *)
      read_colbytes cm p.(ptr_addr) (t_length t) = Some tbs ->
      all (fun tb => (tb_color tb == Some c) && (tb_tag tb == Numeric)) tbs ->
      bs = map tb_value tbs ->
      v = wasm_deserialise bs t ->
      reduce s f [::AI_const (VAL_pointer p); AI_basic (BI_colload t)]
        (Eread t p) s f [::AI_const v]

  | rm_colload_ptr_success :
    forall s f bs c cm tbs p v A,
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      p.(ptr_col) = Some c ->
      isAlloc c A ->
      isAlign p ->
      read_colbytes cm p.(ptr_addr) (t_length T_pointer) = Some tbs ->
      all (fun tb => (tb_color tb == Some c) && (tb_tag tb == Pointer)) tbs ->
      bs = map tb_value tbs ->
      v = wasm_deserialise bs T_pointer ->
      reduce s f [::AI_const (VAL_pointer p); AI_basic (BI_colload T_pointer)]
        (Eread T_pointer p) s f [::AI_const v]

  | rm_colload_failure :
    forall s f t cm p A,
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      (
      is_null p \/                                 (* fail-null *)
      (t=T_pointer /\ ~ isAlign p) \/              (* fail-align *)
      read_colbytes cm p.(ptr_addr) (t_length t) = None \/ (* fail-oob *)
      ( forall c, ptr_col p = Some c -> ~ isAlloc c A \/               (* fail-freed *)
      ( forall tbs,
          read_colbytes cm p.(ptr_addr) (t_length t) = Some tbs ->
          ~ all (fun tb => (tb_color tb == Some c) && (tb_tag tb == match t with T_pointer => Pointer | _ => Numeric end)) tbs
      ))                                                    (* fail *)
      ) ->
      reduce s f [::AI_const (VAL_pointer p); AI_basic (BI_colload t)]
       Etrap s f [::AI_trap]

  | rm_colstore_success :
    forall s f t v c cm tbs p A cm',
      t <> T_pointer ->
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      types_agree t v ->
      p.(ptr_col) = Some c ->
      isAlloc c A ->
      read_colbytes cm p.(ptr_addr) (t_length t) = Some tbs ->
      all (fun tb => tb_color tb == Some c) tbs ->
      write_cmembytes cm p.(ptr_addr) (bits v) (Some c) Numeric = Some cm' ->
      reduce s f [::AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)]
        (Ewrite t p v) (upd_s_cmem s cm') f [::]

  | rm_colstore_ptr_success :
    forall s f v c cm tbs p cm' A,
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      types_agree T_pointer v ->
      p.(ptr_col) = Some c ->
      isAlloc c A ->
      isAlign p ->
      read_colbytes cm p.(ptr_addr) (t_length T_pointer) = Some tbs ->
      all (fun tb => tb_color tb == Some c) tbs ->
      write_cmembytes cm p.(ptr_addr) (bits v) (Some c) Pointer = Some cm' ->
      reduce s f [::AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore T_pointer)]
        (Ewrite T_pointer p v) (upd_s_cmem s cm') f [::]

  | rm_colstore_failure :
    forall s f t v cm p A,
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      is_null p \/
      (t=T_pointer /\ ~ isAlign p) \/
      (* types_agree t v <> true \/ *)
      read_colbytes cm p.(ptr_addr) (t_length t) = None \/
      (forall c, ptr_col p = Some c -> ~ isAlloc c A \/
      ( forall tbs,
        p.(ptr_col) = Some c ->
        read_colbytes cm p.(ptr_addr) (t_length t) = Some tbs ->
        ~ all (fun tb => tb_color tb == Some c) tbs (* mem_disagree *)
        \/
        write_cmembytes cm p.(ptr_addr) (bits v) p.(ptr_col) (match t with T_pointer => Pointer | _ => Numeric end) = None)
      ) ->
      reduce s f [::AI_const (VAL_pointer p); AI_const v; AI_basic (BI_colstore t)]
        Etrap s f [::AI_trap]

  | rm_colalloc_success :
    forall s f cm A a n n_val c cm' A' p,
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      n_val = Wasm_int.N_of_uint i32m n ->
      calloc cm A a n_val c cm' A' ->
      p = new_pointer a (Some c) true ->
      reduce s f [::AI_basic (BI_const (NVAL_int32 n)); AI_basic BI_colalloc]
        (Ecalloc p n_val) (upd_s_all (upd_s_cmem s cm') A') f
        [::AI_const (VAL_pointer p)]

  | rm_colalloc_failure :
    forall s f m A n,
        (* TODO should there be an explicit precondition stating `calloc`
        rule doesn't succeed? *)
      m = s.(s_cmems) ->
      A = s.(s_alls) ->
      reduce s f [::AI_basic (BI_const (NVAL_int32 n)); AI_basic BI_colalloc]
        Eempty s f [::AI_const (VAL_pointer dummy_pointer)]

  | rm_colfree_success :
    forall s f p c cm A A' s',
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      p.(ptr_col) = Some c ->
      p.(ptr_freeable) ->
      isAlloc c A ->
      cfree cm A c A' ->
      s' = upd_s_all s A' ->
      reduce s f [::AI_const (VAL_pointer p); AI_basic BI_colfree]
        (Ecfree c) s' f [::]

  | rm_colfree_failure :
    forall s f p cm A,
      cm = s.(s_cmems) ->
      A = s.(s_alls) ->
      (
      is_null p \/
      p.(ptr_freeable) = false \/
      forall c, ptr_col p = Some c -> ~isAlloc c A
      ) ->
      reduce s f [::AI_const (VAL_pointer p); AI_basic BI_colfree]
        Etrap s f [::AI_trap]

  (** label and local **)
  | rm_label :
      forall s f es les me s' f' es' les' k lh,
        reduce s f es me s' f' es' ->
        lfilled k lh es les ->
        lfilled k lh es' les' ->
        reduce s f les me s' f' les'
  | rm_local :
      forall s f es me s' f' es' n f0,
        reduce s f es me s' f' es' ->
        reduce s f0 [::AI_local n f es] me s' f0 [::AI_local n f' es']
  .

Definition reduce_tuple s_f_es me s'_f'_es' : Prop :=
  let '(s, f, es) := s_f_es in
  let '(s', f', es') := s'_f'_es' in
  reduce s f es me s' f' es'.

  Inductive reduce_trans : store_record * frame * seq administrative_instruction -> seq memory_event -> store_record * frame * seq administrative_instruction -> Prop :=
  | reduce_trivial : forall status, reduce_trans status [::] status
  | reduce_step : forall status mes status' me status'',
      reduce_tuple status me status' ->
      reduce_trans status' mes status'' ->
      reduce_trans status (me :: mes) status''
  .

End Opsem.
