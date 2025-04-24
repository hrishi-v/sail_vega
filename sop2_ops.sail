$include <string.sail>

// Chapter 5

type op8 = bits(8)
type op5 = bits(5)
let SCC : bits(8) = 0xFD
let SCC_0 : bits(64) = 0x0000_0000_0000_0000
let SCC_1 : bits(64) = 0x0000_0000_0000_0001
let MSB_32 : bits(32) = 0x8000_0000
let MSB_64 : bits(64) = 0x8000_0000_0000_0000
let ZERO_32 : bits(32) = 0x0000_0000

enum SOP2_IA = {S_ADD_I32, S_ADD_U32, S_ADDC_U32, S_SUB_I32, S_SUB_U32, S_SUBB_U32, S_ABSDIFF_I32, S_MIN_I32, S_MIN_U32, S_MAX_I32, S_MAX_U32, S_MUL_I32} // IA = Integer Arithmetic

// enum SOP2_COND = {S_CSELECT_B32}

scattered union ast

val decode : bits(32) -> option(ast)
val execute : ast -> unit

union clause ast = SOP2 : (sgpr_dst_bits, sgpr_src_bits, sgpr_src_bits, SOP2_IA) // defining the SOP2 constructor for ast

// -------- S_ADD_U32 --------

function clause decode 0b10 @ 0b0000000 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_ADD_U32))

function clause execute (SOP2(sdst, ssrc1, ssrc0, S_ADD_U32)) = {
    let ssrc1_val = SGPR_32(ssrc1, bitzero); // bitzero to read lower 32 bits
    let ssrc0_val = SGPR_32(ssrc0, bitzero);
    let result = ssrc1_val + ssrc0_val;
    wSCC() = if unsigned(result) > unsigned(0xFFFFFFFF) then SCC_1 else SCC_0;
    SGPR(sdst) = EXTS(result)
}

// -------- S_SUB_U32 --------

function clause decode 0b10 @ 0b0000001 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_SUB_U32))

function clause execute (SOP2(sdst, ssrc1, ssrc0, S_SUB_U32)) = {
    let ssrc1_val = SGPR_32(ssrc1, bitzero); // bitzero to read lower 32 bits
    let ssrc0_val = SGPR_32(ssrc0, bitzero);
    let result = sub_bits(ssrc1_val, ssrc0_val);
    wSCC() = if unsigned(result) > unsigned(0xFFFFFFFF) then SCC_1 else SCC_0;
    SGPR(sdst) = EXTS(result)
}

// -------- S_ADD_I32 --------

function clause decode 0b10 @ 0b0000010 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_ADD_I32))

function clause execute (SOP2(sdst, ssrc1, ssrc0, S_ADD_I32)) = {
    let ssrc1_val = SGPR_32(ssrc1, bitzero);
    let ssrc0_val = SGPR_32(ssrc0, bitzero);
    let result = ssrc1_val + ssrc0_val;

    let result_msb = result & MSB_32;
    let ssrc1_msb = ssrc1_val & MSB_32;
    let ssrc0_msb = ssrc0_val & MSB_32;
    
    let case1 = (ssrc1_msb == ZERO_32) & (ssrc0_msb == ZERO_32) & (result_msb == MSB_32);
    let case2 = (ssrc1_msb == MSB_32) & (ssrc0_msb == MSB_32) & (result_msb == ZERO_32);

    SCC(if case1 | case2 then SCC_1 else SCC_0);
    SGPR(sdst) = EXTS(result)
}

// -------- S_SUB_I32 --------

function clause decode 0b10 @ 0b0000011 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_SUB_I32))

function clause execute (SOP2(sdst, ssrc1, ssrc0, S_SUB_I32)) = {
    let ssrc1_val = SGPR_32(ssrc1, bitzero);
    let ssrc0_val = SGPR_32(ssrc0, bitzero);
    let result = sub_bits(ssrc1_val, ssrc0_val);

    let result_msb = result & MSB_32;
    let ssrc1_msb = ssrc1_val & MSB_32;
    let ssrc0_msb = ssrc0_val & MSB_32;
    
    let case1 = (ssrc1_msb == ZERO_32) & (ssrc0_msb == ZERO_32) & (result_msb == MSB_32);
    let case2 = (ssrc1_msb == MSB_32) & (ssrc0_msb == MSB_32) & (result_msb == ZERO_32);

    SCC(if case1 | case2 then SCC_1 else SCC_0);
    SGPR(sdst) = EXTS(result)
}

// -------- S_ADDC_U32 --------

function clause decode 0b10 @ 0b0000100 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_ADDC_U32))

function clause execute (SOP2(sdst, ssrc1, ssrc0, S_ADDC_I32)) = {
    let ssrc1_val = SGPR_32(ssrc1, bitzero);
    let ssrc0_val = SGPR_32(ssrc0, bitzero);
    let result = ssrc0_val + ssrc1_val + rSCC_32();

    let result_msb = result & MSB_32;
    let ssrc1_msb = ssrc1_val & MSB_32;
    let ssrc0_msb = ssrc0_val & MSB_32;
    
    let case1 = (ssrc1_msb == ZERO_32) & (ssrc0_msb == ZERO_32) & (result_msb == MSB_32);
    let case2 = (ssrc1_msb == MSB_32) & (ssrc0_msb == MSB_32) & (result_msb == ZERO_32);

    SCC(if case1 | case2 then SCC_1 else SCC_0);
    SGPR(sdst) = EXTS(result)
}

// -------- S_SUBB_U32 --------

function clause decode 0b10 @ 0b0000101 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_SUBB_U32))

function clause execute (SOP2(sdst, ssrc1, ssrc0, S_SUBB_U32)) = {
    let ssrc1_val = SGPR_32(ssrc1, bitzero);
    let ssrc0_val = SGPR_32(ssrc0, bitzero);
    let result = sub_bits(sub_bits(ssrc1_val, ssrc0_val), rSCC_32());

    let result_msb = result & MSB_32;
    let ssrc1_msb = ssrc1_val & MSB_32;
    let ssrc0_msb = ssrc0_val & MSB_32;
    
    let case1 = (ssrc1_msb == ZERO_32) & (ssrc0_msb == ZERO_32) & (result_msb == MSB_32);
    let case2 = (ssrc1_msb == MSB_32) & (ssrc0_msb == MSB_32) & (result_msb == ZERO_32);

    SCC(if case1 | case2 then SCC_1 else SCC_0);
    SGPR(sdst) = EXTS(result)
}

// -------- S_MIN_I32 --------

function clause decode 0b10 @ 0b0000110 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_MIN_I32))

// -------- S_MAX_I32 --------

function clause decode 0b10 @ 0b0000111 @ sdst : sgpr_dst_bits @ ssrc1 : sgpr_src_bits @ ssrc0 : sgpr_src_bits = Some(SOP2(sdst, ssrc1, ssrc0, S_MAX_I32))

// -------- S_CSELECT_B32 --------

// -------- S_CSELECT_B64 --------



function clause decode _ = None()


