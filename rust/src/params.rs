//! Sizes for the FAEST-EM-128f (v3) VOLEitH parameters with a given witness length.

/// Number of GGM trees (small VOLEs).
pub const TAU: usize = 17;
/// Number of bits of Delta; the remaining 8 are zero (grinding).
pub const DELTA_BITS: usize = 120;
/// Number of masks: QS_DEGREE - 1 for QuickSilver plus 4 for the VOLE check.
pub const N_MASK: usize = 12;
/// QuickSilver degree.
pub const QS_DEGREE: usize = 9;
/// Number of VOLE rows per mask, in each small VOLE.
pub const MAX_USED_K: usize = 8;
/// Number of CRT multiplication gates.
pub const N_MULT: usize = crate::crt_tables::N_MULT;
pub const N_MULT_BYTES: usize = N_MULT.div_ceil(8);
pub const CMULT_BYTES: usize = N_MASK * N_MULT_BYTES;
pub const VOLE_CHECK_PROOF_BYTES: usize = 64;
pub const VOLE_CHECK_CHALLENGE_BYTES: usize = 8 * 16 + 8;
pub const QS_PROOF_BYTES: usize = (QS_DEGREE - 1) * 16;
pub const QS_CHALLENGE_BYTES: usize = 3 * 16 + 8;
pub const COMMIT_CHECK_BYTES: usize = 32;

/// Depth of tree `i`.
#[inline(always)]
pub const fn tree_k(i: usize) -> usize {
    if i == 0 { 8 } else { 7 }
}

/// First column (Delta bit) of tree `i`.
#[inline(always)]
pub const fn tree_col(i: usize) -> usize {
    if i == 0 { 0 } else { 8 + 7 * (i - 1) }
}

#[derive(Clone, Copy, Debug)]
pub struct Params {
    pub witness_bytes: usize,
    /// Rows corrected to the witness (= witness bits).
    pub corr_rows: usize,
    pub corr_bytes: usize,
    /// Witness rows plus the mask rows.
    pub vole_rows: usize,
    pub rows_padded: usize,
    /// Length of a VOLE column in blocks.
    pub col_blocks: usize,
    pub extra_bytes: usize,

    pub off_corrections: usize,
    pub off_cmult: usize,
    pub off_vole_check: usize,
    pub off_correction: usize,
    pub off_qs_proof: usize,
    pub off_open: usize,
    pub off_delta: usize,
    pub off_iv_pre: usize,
    pub off_ctr: usize,
    pub proof_bytes: usize,
}

impl Params {
    pub const fn new(witness_bytes: usize) -> Params {
        let corr_rows = witness_bytes * 8;
        let vole_rows = corr_rows + N_MASK * MAX_USED_K;
        let rows_padded = vole_rows.div_ceil(256) * 256;
        let col_blocks = rows_padded / 128;
        let corr_bytes = witness_bytes;
        let extra_bytes = vole_rows.div_ceil(8) - corr_bytes;

        let off_corrections = 0;
        let off_cmult = off_corrections + corr_bytes * (TAU - 1);
        let off_vole_check = off_cmult + CMULT_BYTES;
        let off_correction = off_vole_check + VOLE_CHECK_PROOF_BYTES;
        let off_qs_proof = off_correction + witness_bytes;
        let off_open = off_qs_proof + QS_PROOF_BYTES;
        let off_delta = off_open + crate::bavc::OPEN_SIZE;
        let off_iv_pre = off_delta + 16;
        let off_ctr = off_iv_pre + 16;
        let proof_bytes = off_ctr + 4;
        Params {
            witness_bytes,
            corr_rows,
            corr_bytes,
            vole_rows,
            rows_padded,
            col_blocks,
            extra_bytes,
            off_corrections,
            off_cmult,
            off_vole_check,
            off_correction,
            off_qs_proof,
            off_open,
            off_delta,
            off_iv_pre,
            off_ctr,
            proof_bytes,
        }
    }
}
