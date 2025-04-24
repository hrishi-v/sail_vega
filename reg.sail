default Order dec
$include <prelude.sail>
/* Global register widths bits/bytes */

val EXTS : forall 'n 'm, 'm >= 'n. (implicit('m), bits('n)) -> bits('m)
function EXTS(m, v) = sail_sign_extend(v, m)

type xlen : Int = 64
type xlen_half : Int = 32
type xlen_bytes : Int = 8
type xlenbits        = bits(xlen)
type xlenbits_32        = bits(xlen_half)

type sgpr_dst_bits = bits(7) // SGPR dst indexing
type sgpr_src_bits = bits(8) // SGPR src indexing

let zero_64: bits(64) = 0x0000_0000_0000_0000
let zero_32: bits(32) = 0x0000_0000
let lower_word: bits(64) = 0x0000_0000_FFFF_FFFF
let upper_word: bits(64) = 0xFFFF_FFFF_0000_0000

/* Reg read/write functions */

register PC : xlenbits // PC register of 64 bits
register nextPC : xlenbits

register SGPR : vector(256, dec, xlenbits)

val rSGPR_64 : sgpr_src_bits -> xlenbits // SGPR getter
function rSGPR_64(r) =
    match r {
        0b01000000 => zero_64,
        _ => SGPR[unsigned(r)]
    }

val wSGPR : (sgpr_dst_bits, xlenbits) -> unit
function wSGPR(r, v) =
    if r != 0b1000000 then {
        SGPR[unsigned(r)] = v // r is just register idx!
    }

val rSGPR_32 : (sgpr_src_bits, bit) -> xlenbits_32 // SGPR (32 bit) getter
function rSGPR_32(r, s) =
    match r {
        0b01000000 => zero_32,
        _ => if s == bitzero then truncate(SGPR[unsigned(r)], 32) else truncateLSB(SGPR[unsigned(r)], 32) // 0 - bottom half, 1 - top half
    }

val rSCC_32: unit -> xlenbits_32
function rSCC_32() = {
    truncate(SGPR[253], 32)
}

val rSCC: unit -> xlenbits
function rSCC() = {
    SGPR[253]
}

val wSCC : (xlenbits) -> unit
function wSCC(v) = {
    SGPR[253] = v
}

overload SGPR = {rSGPR_64, wSGPR} // overloads, selecting based on parameters
overload SGPR_32 = {rSGPR_32}
overload SCC = {rSCC, wSCC} // same here
