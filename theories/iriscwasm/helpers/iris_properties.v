From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
From CWasm.iriscwasm.language.iris Require Import iris iris_locations.
From CWasm Require Import stdpp_aux.
From CWasm Require Import datatypes operations properties opsem.
From CWasm.iriscwasm.helpers Require Export iris_lfilled_properties
        iris_wasm_lang_properties
        iris_reduce_properties
        iris_reduction_core
        iris_split_reduce
        iris_wasm_determ
        iris_reduce_det_prelude
        first_instr
        lfill_prelude
        lfilled_reduce
        iris_prim_step_split.
