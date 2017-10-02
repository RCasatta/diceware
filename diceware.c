/*
 * This work is dedicated to the public domain. The statements in the
 * Creative Commons Zero 1.0 Universal Public Domain Dedication apply.
 * https://creativecommons.org/publicdomain/zero/1.0/
 */

#define ENABLE_ERROR_RETURN
#define USE_TI89
#define MIN_AMS 200

#include <tigcclib.h>

typedef signed char int8_t;
typedef unsigned char uint8_t;
typedef signed short int16_t;
typedef unsigned short uint16_t;
typedef signed long int32_t;
typedef unsigned long uint32_t;
typedef signed long long int64_t;
typedef unsigned long long uint64_t;

static inline uint32_t rotl(uint32_t v, int16_t s) {
    return (v << s) | (v >> 32 - s);
}

static inline uint32_t rotr(uint32_t v, int16_t s) {
    return (v >> s) | (v << 32 - s);
}

static inline uint32_t bswap32(uint32_t v) {
    asm("rol.w #8,%[dst]\n\t"
        "swap %[dst]\n\t"
        "rol.w #8,%[dst]"
        : [dst] "+d" (v)
        :
        : "cc");
    return v;
}

static void disp(const char *str) {
    ESI save_estack = top_estack;
    push_END_TAG();
    if (str) {
        push_zstr(str);
    }
    cmd_disp(top_estack);
    top_estack = save_estack;
}

static void disp_wrap(char *str) {
    size_t len = strlen(str);
    while (len > 26) {
        char save = str[26];
        str[26] = '\0';
        disp(str);
        str[26] = save;
        str += 26, len -= 26;
    }
    disp(str);
}

static size_t input(char *buf, size_t n_buf, const char *str) {
    ESI save_estack = top_estack;
    SYM_STR temp_fld_sym = FolderAddTemp();
    top_estack += 8;
    memcpy(top_estack - 7, temp_fld_sym - 5, 5);
    memcpy(top_estack - 2, "\\x", 3);
    ESI temp_var_sym = top_estack;
    if (str) {
        push_zstr(str);
    }
    cmd_inputstr(top_estack);
    MULTI_EXPR *me = HeapDeref(SymFindPtr(temp_var_sym, 0)->handle);
    size_t n = me->Size - 3;
    if (n >= n_buf) {
        n = n_buf - 1;
    }
    memcpy(buf, me->Expr + 1, n);
    buf[n] = '\0';
    FolderDelTemp();
    top_estack = save_estack;
    return n;
}

static uint32_t * copy256(uint32_t dst[8], const uint32_t src[8]) {
    for (size_t i = 0; i < 8; ++i) {
        dst[i] = src[i];
    }
    return dst;
}

static uint32_t * zero256(uint32_t dst[8]) {
    for (size_t i = 0; i < 8; ++i) {
        dst[i] = 0;
    }
    return dst;
}

static int zero_p(const uint32_t dst[], size_t n) {
    while (n > 0) {
        if (dst[--n] != 0) {
            return FALSE;
        }
    }
    return TRUE;
}

static int zero256_p(const uint32_t dst[8]) {
    return zero_p(dst, 8);
}

static int one256_p(const uint32_t dst[8]) {
    for (size_t i = 0; i < 7; ++i) {
        if (dst[i] != 0) {
            return FALSE;
        }
    }
    return dst[7] == 1;
}

static int even256_p(const uint32_t dst[8]) {
    return (dst[7] & 1) == 0;
}

static int cmp256(const uint32_t dst[8], const uint32_t src[8]) {
    for (size_t i = 0; i < 8; ++i) {
        if (dst[i] < src[i]) {
            return -1;
        }
        if (dst[i] > src[i]) {
            return 1;
        }
    }
    return 0;
}

static int add256(uint32_t dst[8], const uint32_t src[8]) {
    int ret;
    uint32_t *dp = dst + 8;
    const uint32_t *sp = src + 8;
    asm("andi #0xEF,%%ccr\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "addx.l -(%[src]),-(%[dst])\n\t"
        "scs %[ret]\n\t"
        "ext.w %[ret]\n\t"
        "neg.w %[ret]"
        : [dst] "+a" (dp), [src] "+a" (sp), [ret] "=d" (ret), "+m" (*(uint32_t (*)[8]) dst)
        : "m" (*(const uint32_t (*)[8]) src)
        : "cc");
    return ret;
}

static int sub256(uint32_t dst[8], const uint32_t src[8]) {
    int ret;
    uint32_t *dp = dst + 8;
    const uint32_t *sp = src + 8;
    asm("andi #0xEF, %%ccr\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "subx.l -(%[src]),-(%[dst])\n\t"
        "scs %[ret]\n\t"
        "ext.w %[ret]"
        : [dst] "+a" (dp), [src] "+a" (sp), [ret] "=d" (ret), "+m" (*(uint32_t (*)[8]) dst)
        : "m" (*(const uint32_t (*)[8]) src)
        : "cc");
    return ret;
}

static uint16_t muln_1(uint32_t dst[], size_t n_dst, uint16_t src, uint16_t carry_in) {
    uint16_t *dst_w = (uint16_t *) dst;
    uint32_t tmp1, tmp2 = carry_in;
    for (size_t i = n_dst * 2; i > 0;) {
        asm("mulu.w %[src],%[tmp]"
            : [tmp] "=d" (tmp1)
            : "0" (dst_w[--i]), [src] "idm" (src)
            : "cc");
        dst_w[i] = (uint16_t) (tmp1 += tmp2);
        tmp1 >>= 16;
        asm("mulu.w %[src],%[tmp]"
            : [tmp] "=d" (tmp2)
            : "0" (dst_w[--i]), [src] "idm" (src)
            : "cc");
        dst_w[i] = (uint16_t) (tmp2 += tmp1);
        tmp2 >>= 16;
    }
    return (uint16_t) tmp2;
}

static uint16_t divn_1(uint32_t dst[], size_t n_dst, uint16_t src) {
    uint16_t *dst_w = (uint16_t *) dst;
    uint32_t tmp1, tmp2 = 0;
    n_dst *= 2;
    for (size_t i = 0; i < n_dst;) {
        asm("divu.w %[src],%[tmp]"
            : [tmp] "=d" (tmp1)
            : "0" (dst_w[i] + tmp2), [src] "idm" (src)
            : "cc");
        dst_w[i++] = (uint16_t) tmp1;
        tmp1 &= 0xFFFF0000UL;
        asm("divu.w %[src],%[tmp]"
            : [tmp] "=d" (tmp2)
            : "0" (dst_w[i] + tmp1), [src] "idm" (src)
            : "cc");
        dst_w[i++] = (uint16_t) tmp2;
        tmp2 &= 0xFFFF0000UL;
    }
    return (uint16_t) (tmp2 >> 16);
}

static int shr256_1(uint32_t dst[8]) {
    int ret;
    asm("lsr.w (%[dst])\n\t"
        "roxr.w 2(%[dst])\n\t"
        "roxr.w 4(%[dst])\n\t"
        "roxr.w 6(%[dst])\n\t"
        "roxr.w 8(%[dst])\n\t"
        "roxr.w 10(%[dst])\n\t"
        "roxr.w 12(%[dst])\n\t"
        "roxr.w 14(%[dst])\n\t"
        "roxr.w 16(%[dst])\n\t"
        "roxr.w 18(%[dst])\n\t"
        "roxr.w 20(%[dst])\n\t"
        "roxr.w 22(%[dst])\n\t"
        "roxr.w 24(%[dst])\n\t"
        "roxr.w 26(%[dst])\n\t"
        "roxr.w 28(%[dst])\n\t"
        "roxr.w 30(%[dst])\n\t"
        "scs %[ret]\n\t"
        "ext.w %[ret]\n\t"
        "neg.w %[ret]"
        : [ret] "=d" (ret), "+m" (*(uint32_t (*)[8]) dst)
        : [dst] "a" (dst)
        : "cc");
    return ret;
}

static void mpn_set_str(uint32_t result[], size_t n_result, const uint8_t digits[], size_t n_digits, uint16_t base) {
    for (size_t i = 0; i < n_result; ++i) {
        result[i] = 0;
    }
    for (size_t i = 0; i < n_digits; ++i) {
        muln_1(result, n_result, base, digits[i]);
    }
}

static uint32_t * fp_add256(uint32_t dst[8], const uint32_t src[8], const uint32_t p[8]) {
    if (add256(dst, src) || cmp256(dst, p) >= 0) {
        sub256(dst, p);
    }
    return dst;
}

static uint32_t * fp_sub256(uint32_t dst[8], const uint32_t src[8], const uint32_t p[8]) {
    if (sub256(dst, src)) {
        add256(dst, p);
    }
    return dst;
}

static inline uint32_t * fp_dbl256(uint32_t dst[8], const uint32_t p[8]) {
    return fp_add256(dst, dst, p);
}

static uint32_t * fp_mul256(uint32_t * restrict r, const uint32_t n1[8], const uint32_t n2[8], const uint32_t p[8]) {
    zero256(r);
    int active = FALSE;
    for (size_t i = 0; i < 8; ++i) {
        uint32_t w = n2[i];
        for (size_t j = sizeof(uint32_t) * 8; j > 0; --j) {
            if (active) {
                fp_dbl256(r, p);
            }
            if ((int32_t) w < 0) {
                fp_add256(r, n1, p);
                active = TRUE;
            }
            w <<= 1;
        }
    }
    return r;
}

static inline uint32_t * fp_sqr256(uint32_t * restrict r, const uint32_t n[8], const uint32_t p[8]) {
    return fp_mul256(r, n, n, p);
}

static uint32_t * fp_inv256(uint32_t * restrict r, const uint32_t n[8], const uint32_t p[8]) {
    uint32_t u[8], v[8], s[8];
    copy256(u, n), copy256(v, p);
    zero256(r), zero256(s);
    r[7] = 1;
    for (;;) {
        if (one256_p(u)) {
            return r;
        }
        if (one256_p(v)) {
            copy256(r, s);
            return r;
        }
        while (even256_p(u)) {
            shr256_1(u);
            if (even256_p(r)) {
                shr256_1(r);
            }
            else {
                uint32_t c = (uint32_t) add256(r, p) << sizeof(uint32_t) * 8 - 1;
                shr256_1(r);
                r[0] |= c;
            }
        }
        while (even256_p(v)) {
            shr256_1(v);
            if (even256_p(s)) {
                shr256_1(s);
            }
            else {
                uint32_t c = (uint32_t) add256(s, p) << sizeof(uint32_t) * 8 - 1;
                shr256_1(s);
                s[0] |= c;
            }
        }
        if (cmp256(u, v) >= 0) {
            sub256(u, v);
            fp_sub256(r, s, p);
        }
        else {
            sub256(v, u);
            fp_sub256(s, r, p);
        }
    }
}

static uint32_t (* ecp_copy256(uint32_t dst[][8], const uint32_t src[][8]))[8] {
    copy256(dst[0], src[0]), copy256(dst[1], src[1]), copy256(dst[2], src[2]);
    return dst;
}

static uint32_t (* ecp_dbl256(uint32_t (* restrict R)[8], const uint32_t N[3][8], const uint32_t p[8]))[8] {
    const uint32_t *x = N[0], *y = N[1], *z = N[2];
    uint32_t *xr = R[0], *yr = R[1], *zr = R[2];
    if (zero256_p(z)) {
        zero256(xr), zero256(yr), zero256(zr);
        return R;
    }
    uint32_t t0[8], t1[8], t2[8], t3[8];
    // t0 := 3*x^2
    fp_add256(t0, fp_dbl256(copy256(t1, fp_sqr256(t0, x, p)), p), p);
    // t1 := 2*y^2
    fp_dbl256(fp_sqr256(t1, y, p), p);
    // t2 := 4*x*y^2
    fp_dbl256(fp_mul256(t2, x, t1, p), p);
    // t3 := 8*y^4
    fp_dbl256(fp_sqr256(t3, t1, p), p);
    // xr := 9*x^4 - 8*x*y^2
    fp_sub256(fp_sqr256(xr, t0, p), fp_dbl256(copy256(t1, t2), p), p);
    // yr := 3*x^2*(4*x*y^2-xr) - 8*y^4
    fp_sub256(fp_mul256(yr, t0, fp_sub256(t2, xr, p), p), t3, p);
    // zr := 2*y*z
    fp_dbl256(fp_mul256(zr, y, z, p), p);
    return R;
}

static uint32_t (* ecp_add256_aff(uint32_t (* restrict R)[8], const uint32_t N1[3][8], const uint32_t N2[3][8], const uint32_t p[8]))[8] {
    const uint32_t *x1 = N1[0], *y1 = N1[1], *z1 = N1[2], *x2 = N2[0], *y2 = N2[1];
    uint32_t *xr = R[0], *yr = R[1], *zr = R[2];
    uint32_t t0[8], t1[8], t2[8], t3[8], t4[8];
    fp_sqr256(t0, z1, p);
    fp_mul256(t1, x2, t0, p);
    fp_mul256(t2, z1, t0, p);
    fp_mul256(t0, y2, t2, p);
    if (cmp256(t1, x1) == 0) {
        if (cmp256(t0, y1) == 0) {
            return ecp_dbl256(R, N1, p);
        }
        zero256(xr), zero256(yr), zero256(zr);
        xr[7] = yr[7] = 1;
        return R;
    }
    fp_sub256(copy256(t2, t1), x1, p);
    fp_sub256(copy256(t1, t0), y1, p);
    fp_sqr256(t0, t2, p);
    fp_mul256(t3, t0, t2, p);
    fp_mul256(t4, x1, t0, p);
    fp_sub256(fp_sub256(fp_sqr256(xr, t1, p), t3, p), fp_dbl256(copy256(t0, t4), p), p);
    fp_sub256(fp_mul256(yr, t1, fp_sub256(t4, xr, p), p), fp_mul256(t0, y1, t3, p), p);
    fp_mul256(zr, z1, t2, p);
    return R;
}

static uint32_t (* ecp_add256(uint32_t (* restrict R)[8], const uint32_t N1[3][8], const uint32_t N2[3][8], const uint32_t p[8]))[8] {
    const uint32_t *x1 = N1[0], *y1 = N1[1], *z1 = N1[2], *x2 = N2[0], *y2 = N2[1], *z2 = N2[2];
    uint32_t *xr = R[0], *yr = R[1], *zr = R[2];
    if (zero256_p(z1)) {
        if (zero256_p(z2)) {
            zero256(xr), zero256(yr), zero256(zr);
            return R;
        }
        return ecp_copy256(R, N2);
    }
    if (zero256_p(z2)) {
        return ecp_copy256(R, N1);
    }
    if (one256_p(z2)) {
        return ecp_add256_aff(R, N1, N2, p);
    }
    uint32_t t0[8], t1[8], t2[8], t3[8], t4[8], t5[8], t6[8];
    fp_sqr256(t0, z1, p);
    fp_mul256(t1, x2, t0, p);
    fp_mul256(t2, z1, t0, p);
    fp_mul256(t0, y2, t2, p);
    fp_sqr256(t2, z2, p);
    fp_mul256(t3, x1, t2, p);
    fp_mul256(t4, z2, t2, p);
    fp_mul256(t2, y1, t4, p);
    if (cmp256(t3, t1) == 0) {
        if (cmp256(t2, t0) == 0) {
            return ecp_dbl256(R, N1, p);
        }
        zero256(xr), zero256(yr), zero256(zr);
        xr[7] = yr[7] = 1;
        return R;
    }
    fp_sub256(copy256(t4, t1), t3, p);
    fp_sub256(copy256(t1, t0), t2, p);
    fp_sqr256(t0, t4, p);
    fp_mul256(t5, t4, t0, p);
    fp_mul256(t6, t3, t0, p);
    fp_sub256(fp_sub256(fp_sqr256(xr, t1, p), t5, p), fp_dbl256(copy256(t0, t6), p), p);
    fp_sub256(fp_mul256(yr, t1, fp_sub256(t6, xr, p), p), fp_mul256(t0, t2, t5, p), p);
    fp_mul256(zr, t4, fp_mul256(t0, z1, z2, p), p);
    return R;
}

static uint32_t (* ecp_mul256_(uint32_t (* restrict R)[8], const uint32_t n1[8], const uint32_t N2[3][8], const uint32_t p[8], uint32_t (* (*add)(uint32_t (* restrict)[8], const uint32_t [3][8], const uint32_t [3][8], const uint32_t [8]))[8]))[8] {
    int active = FALSE;
    size_t swaps = 0;
    uint32_t Ss[3][8], (*S)[8] = Ss, (*T)[8];
    ST_PROGRESS_BAR pb;
    ST_progressBar(&pb, 0, 8);
    for (size_t i = 0; i < 8; ++i) {
        uint32_t w = n1[i];
        for (size_t j = sizeof(uint32_t) * 8; j > 0; --j) {
            if (OSCheckBreak()) {
                ER_throw(ER_BREAK);
            }
            if (active) {
                ecp_dbl256(S, (const uint32_t (*)[8]) R, p);
                T = S, S = R, R = T, ++swaps;
            }
            if ((int32_t) w < 0) {
                if (active) {
                    (*add)(S, (const uint32_t (*)[8]) R, N2, p);
                    T = S, S = R, R = T, ++swaps;
                }
                else {
                    ecp_copy256(R, N2);
                    active = TRUE;
                }
            }
            w <<= 1;
        }
        ST_progressIncrement(&pb, 1);
    }
    ST_progressDismiss(&pb);
    if (swaps & 1) {
        return ecp_copy256(S, (const uint32_t (*)[8]) R);
    }
    return R;
}

static uint32_t (* ecp_mul256(uint32_t (* restrict R)[8], const uint32_t n1[8], const uint32_t N2[3][8], const uint32_t p[8]))[8] {
    return ecp_mul256_(R, n1, N2, p, one256_p(N2[2]) ? &ecp_add256_aff : &ecp_add256);
}

static uint32_t (* ecp_proj256(uint32_t (* restrict R)[8], const uint32_t N[3][8], const uint32_t p[8]))[8] {
    const uint32_t *x = N[0], *y = N[1], *z = N[2];
    uint32_t *xr = R[0], *yr = R[1], *zr = R[2];
    uint32_t t0[8], t1[8], t2[8];
    fp_mul256(t2, t0, fp_sqr256(t1, fp_inv256(t0, z, p), p), p);
    fp_mul256(xr, x, t1, p);
    fp_mul256(yr, y, t2, p);
    zero256(zr), zr[7] = 1;
    return R;
}

static void ecp_pubkey256(uint32_t (* restrict Q)[8], const uint32_t p[8], const uint32_t G[3][8], const uint32_t d[8]) {
    uint32_t R[3][8];
    ecp_proj256(Q, (const uint32_t (*)[8]) ecp_mul256(R, d, G, p), p);
}

static const uint32_t secp256k1_p[8] = {
    0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFEUL, 0xFFFFFC2FUL
};
static const uint32_t secp256k1_G[3][8] = {
    {
        0x79BE667EUL, 0xF9DCBBACUL, 0x55A06295UL, 0xCE870B07UL, 0x029BFCDBUL, 0x2DCE28D9UL, 0x59F2815BUL, 0x16F81798UL
    },
    {
        0x483ADA77UL, 0x26A3C465UL, 0x5DA4FBFCUL, 0x0E1108A8UL, 0xFD17B448UL, 0xA6855419UL, 0x9C47D08FUL, 0xFB10D4B8UL
    },
    {
        0x00000000UL, 0x00000000UL, 0x00000000UL, 0x00000000UL, 0x00000000UL, 0x00000000UL, 0x00000000UL, 0x00000001UL
    }
};
static const uint32_t secp256k1_n[8] = {
    0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFFUL, 0xFFFFFFFEUL, 0xBAAEDCE6UL, 0xAF48A03BUL, 0xBFD25E8CUL, 0xD0364141UL
};

static void _sha256_update(uint32_t state[8], const uint8_t block[64]) {
    static const uint32_t rc[64] = {
        0x428a2f98UL, 0x71374491UL, 0xb5c0fbcfUL, 0xe9b5dba5UL, 0x3956c25bUL, 0x59f111f1UL, 0x923f82a4UL, 0xab1c5ed5UL,
        0xd807aa98UL, 0x12835b01UL, 0x243185beUL, 0x550c7dc3UL, 0x72be5d74UL, 0x80deb1feUL, 0x9bdc06a7UL, 0xc19bf174UL,
        0xe49b69c1UL, 0xefbe4786UL, 0x0fc19dc6UL, 0x240ca1ccUL, 0x2de92c6fUL, 0x4a7484aaUL, 0x5cb0a9dcUL, 0x76f988daUL,
        0x983e5152UL, 0xa831c66dUL, 0xb00327c8UL, 0xbf597fc7UL, 0xc6e00bf3UL, 0xd5a79147UL, 0x06ca6351UL, 0x14292967UL,
        0x27b70a85UL, 0x2e1b2138UL, 0x4d2c6dfcUL, 0x53380d13UL, 0x650a7354UL, 0x766a0abbUL, 0x81c2c92eUL, 0x92722c85UL,
        0xa2bfe8a1UL, 0xa81a664bUL, 0xc24b8b70UL, 0xc76c51a3UL, 0xd192e819UL, 0xd6990624UL, 0xf40e3585UL, 0x106aa070UL,
        0x19a4c116UL, 0x1e376c08UL, 0x2748774cUL, 0x34b0bcb5UL, 0x391c0cb3UL, 0x4ed8aa4aUL, 0x5b9cca4fUL, 0x682e6ff3UL,
        0x748f82eeUL, 0x78a5636fUL, 0x84c87814UL, 0x8cc70208UL, 0x90befffaUL, 0xa4506cebUL, 0xbef9a3f7UL, 0xc67178f2UL
    };
    uint32_t words[64];
    memcpy(words, block, 64);
    for (size_t i = 16; i < 64; ++i) {
        words[i] = words[i - 16] + (rotr(words[i - 15], 7) ^ rotr(words[i - 15], 18) ^ words[i - 15] >> 3) + words[i - 7] + (rotr(words[i - 2], 17) ^ rotr(words[i - 2], 19) ^ words[i - 2] >> 10);
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3], e = state[4], f = state[5], g = state[6], h = state[7];
    for (size_t i = 0; i < 64; ++i) {
        uint32_t t1 = h + ((g ^ f) & e ^ g) + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + rc[i] + words[i];
        h = g, g = f, f = e, e = d + t1;
        uint32_t t2 = (c & (b ^ a) ^ b & a) + (rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22));
        d = c, c = b, b = a, a = t1 + t2;
    }
    state[0] += a, state[1] += b, state[2] += c, state[3] += d, state[4] += e, state[5] += f, state[6] += g, state[7] += h;
}

static void sha256(uint8_t digest[32], const void *data, size_t data_size) {
    uint32_t state[8] = {
        0x6a09e667UL, 0xbb67ae85UL, 0x3c6ef372UL, 0xa54ff53aUL, 0x510e527fUL, 0x9b05688cUL, 0x1f83d9abUL, 0x5be0cd19UL
    };
    size_t data_rem = data_size;
    while (data_rem >= 64) {
        _sha256_update(state, data);
        data = (uint8_t *) data + 64, data_rem -= 64;
    }
    union {
        uint8_t b[64];
        uint32_t l[16];
    } block;
    memcpy(block.b, data, data_rem);
    block.b[data_rem++] = 0x80;
    if (data_rem > sizeof block - sizeof(uint64_t)) {
        memset(block.b + data_rem, 0, sizeof block - data_rem);
        _sha256_update(state, block.b);
        data_rem = 0;
    }
    memset(block.b + data_rem, 0, sizeof block - sizeof(size_t) - data_rem);
    block.l[15] = data_size << 3;
    _sha256_update(state, block.b);
    memcpy(digest, state, sizeof state);
}

static void _ripemd160_update(uint32_t state[5], const uint8_t block[64]) {
    uint32_t words[16];
    memcpy(words, block, sizeof words);
    for (size_t i = 0; i < 16; ++i) {
        words[i] = bswap32(words[i]);
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3], e = state[4];
#define _(A, B, C, D, E, r, s) A = rotl(A + (B ^ C ^ D) + words[r] + 0x00000000, s) + E, C = rotl(C, 10)
    _(a, b, c, d, e,  0, 11); _(e, a, b, c, d,  1, 14); _(d, e, a, b, c,  2, 15); _(c, d, e, a, b,  3, 12);
    _(b, c, d, e, a,  4,  5); _(a, b, c, d, e,  5,  8); _(e, a, b, c, d,  6,  7); _(d, e, a, b, c,  7,  9);
    _(c, d, e, a, b,  8, 11); _(b, c, d, e, a,  9, 13); _(a, b, c, d, e, 10, 14); _(e, a, b, c, d, 11, 15);
    _(d, e, a, b, c, 12,  6); _(c, d, e, a, b, 13,  7); _(b, c, d, e, a, 14,  9); _(a, b, c, d, e, 15,  8);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + (B & C | ~B & D) + words[r] + 0x5a827999, s) + E, C = rotl(C, 10)
    _(e, a, b, c, d,  7,  7); _(d, e, a, b, c,  4,  6); _(c, d, e, a, b, 13,  8); _(b, c, d, e, a,  1, 13);
    _(a, b, c, d, e, 10, 11); _(e, a, b, c, d,  6,  9); _(d, e, a, b, c, 15,  7); _(c, d, e, a, b,  3, 15);
    _(b, c, d, e, a, 12,  7); _(a, b, c, d, e,  0, 12); _(e, a, b, c, d,  9, 15); _(d, e, a, b, c,  5,  9);
    _(c, d, e, a, b,  2, 11); _(b, c, d, e, a, 14,  7); _(a, b, c, d, e, 11, 13); _(e, a, b, c, d,  8, 12);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + ((B | ~C) ^ D) + words[r] + 0x6ed9eba1, s) + E, C = rotl(C, 10)
    _(d, e, a, b, c,  3, 11); _(c, d, e, a, b, 10, 13); _(b, c, d, e, a, 14,  6); _(a, b, c, d, e,  4,  7);
    _(e, a, b, c, d,  9, 14); _(d, e, a, b, c, 15,  9); _(c, d, e, a, b,  8, 13); _(b, c, d, e, a,  1, 15);
    _(a, b, c, d, e,  2, 14); _(e, a, b, c, d,  7,  8); _(d, e, a, b, c,  0, 13); _(c, d, e, a, b,  6,  6);
    _(b, c, d, e, a, 13,  5); _(a, b, c, d, e, 11, 12); _(e, a, b, c, d,  5,  7); _(d, e, a, b, c, 12,  5);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + (B & D | C & ~D) + words[r] + 0x8f1bbcdc, s) + E, C = rotl(C, 10)
    _(c, d, e, a, b,  1, 11); _(b, c, d, e, a,  9, 12); _(a, b, c, d, e, 11, 14); _(e, a, b, c, d, 10, 15);
    _(d, e, a, b, c,  0, 14); _(c, d, e, a, b,  8, 15); _(b, c, d, e, a, 12,  9); _(a, b, c, d, e,  4,  8);
    _(e, a, b, c, d, 13,  9); _(d, e, a, b, c,  3, 14); _(c, d, e, a, b,  7,  5); _(b, c, d, e, a, 15,  6);
    _(a, b, c, d, e, 14,  8); _(e, a, b, c, d,  5,  6); _(d, e, a, b, c,  6,  5); _(c, d, e, a, b,  2, 12);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + (B ^ (C | ~D)) + words[r] + 0xa953fd4e, s) + E, C = rotl(C, 10)
    _(b, c, d, e, a,  4,  9); _(a, b, c, d, e,  0, 15); _(e, a, b, c, d,  5,  5); _(d, e, a, b, c,  9, 11);
    _(c, d, e, a, b,  7,  6); _(b, c, d, e, a, 12,  8); _(a, b, c, d, e,  2, 13); _(e, a, b, c, d, 10, 12);
    _(d, e, a, b, c, 14,  5); _(c, d, e, a, b,  1, 12); _(b, c, d, e, a,  3, 13); _(a, b, c, d, e,  8, 14);
    _(e, a, b, c, d, 11, 11); _(d, e, a, b, c,  6,  8); _(c, d, e, a, b, 15,  5); _(b, c, d, e, a, 13,  6);
#undef _
    uint32_t t = a;
    state[0] = (a = state[0]) + b, state[1] = (b = state[1]) + c, state[2] = (c = state[2]) + d, state[3] = (d = state[3]) + e, state[4] = (e = state[4]) + t;
#define _(A, B, C, D, E, r, s) A = rotl(A + (B ^ (C | ~D)) + words[r] + 0x50a28be6, s) + E, C = rotl(C, 10)
    _(a, b, c, d, e,  5,  8); _(e, a, b, c, d, 14,  9); _(d, e, a, b, c,  7,  9); _(c, d, e, a, b,  0, 11);
    _(b, c, d, e, a,  9, 13); _(a, b, c, d, e,  2, 15); _(e, a, b, c, d, 11, 15); _(d, e, a, b, c,  4,  5);
    _(c, d, e, a, b, 13,  7); _(b, c, d, e, a,  6,  7); _(a, b, c, d, e, 15,  8); _(e, a, b, c, d,  8, 11);
    _(d, e, a, b, c,  1, 14); _(c, d, e, a, b, 10, 14); _(b, c, d, e, a,  3, 12); _(a, b, c, d, e, 12,  6);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + (B & D | C & ~D) + words[r] + 0x5c4dd124, s) + E, C = rotl(C, 10)
    _(e, a, b, c, d,  6,  9); _(d, e, a, b, c, 11, 13); _(c, d, e, a, b,  3, 15); _(b, c, d, e, a,  7,  7);
    _(a, b, c, d, e,  0, 12); _(e, a, b, c, d, 13,  8); _(d, e, a, b, c,  5,  9); _(c, d, e, a, b, 10, 11);
    _(b, c, d, e, a, 14,  7); _(a, b, c, d, e, 15,  7); _(e, a, b, c, d,  8, 12); _(d, e, a, b, c, 12,  7);
    _(c, d, e, a, b,  4,  6); _(b, c, d, e, a,  9, 15); _(a, b, c, d, e,  1, 13); _(e, a, b, c, d,  2, 11);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + ((B | ~C) ^ D) + words[r] + 0x6d703ef3, s) + E, C = rotl(C, 10)
    _(d, e, a, b, c, 15,  9); _(c, d, e, a, b,  5,  7); _(b, c, d, e, a,  1, 15); _(a, b, c, d, e,  3, 11);
    _(e, a, b, c, d,  7,  8); _(d, e, a, b, c, 14,  6); _(c, d, e, a, b,  6,  6); _(b, c, d, e, a,  9, 14);
    _(a, b, c, d, e, 11, 12); _(e, a, b, c, d,  8, 13); _(d, e, a, b, c, 12,  5); _(c, d, e, a, b,  2, 14);
    _(b, c, d, e, a, 10, 13); _(a, b, c, d, e,  0, 13); _(e, a, b, c, d,  4,  7); _(d, e, a, b, c, 13,  5);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + (B & C | ~B & D) + words[r] + 0x7a6d76e9, s) + E, C = rotl(C, 10)
    _(c, d, e, a, b,  8, 15); _(b, c, d, e, a,  6,  5); _(a, b, c, d, e,  4,  8); _(e, a, b, c, d,  1, 11);
    _(d, e, a, b, c,  3, 14); _(c, d, e, a, b, 11, 14); _(b, c, d, e, a, 15,  6); _(a, b, c, d, e,  0, 14);
    _(e, a, b, c, d,  5,  6); _(d, e, a, b, c, 12,  9); _(c, d, e, a, b,  2, 12); _(b, c, d, e, a, 13,  9);
    _(a, b, c, d, e,  9, 12); _(e, a, b, c, d,  7,  5); _(d, e, a, b, c, 10, 15); _(c, d, e, a, b, 14,  8);
#undef _
#define _(A, B, C, D, E, r, s) A = rotl(A + (B ^ C ^ D) + words[r] + 0x00000000, s) + E, C = rotl(C, 10)
    _(b, c, d, e, a, 12,  8); _(a, b, c, d, e, 15,  5); _(e, a, b, c, d, 10, 12); _(d, e, a, b, c,  4,  9);
    _(c, d, e, a, b,  1, 12); _(b, c, d, e, a,  5,  5); _(a, b, c, d, e,  8, 14); _(e, a, b, c, d,  7,  6);
    _(d, e, a, b, c,  6,  8); _(c, d, e, a, b,  2, 13); _(b, c, d, e, a, 13,  6); _(a, b, c, d, e, 14,  5);
    _(e, a, b, c, d,  0, 15); _(d, e, a, b, c,  3, 13); _(c, d, e, a, b,  9, 11); _(b, c, d, e, a, 11, 11);
#undef _
    t = state[0], state[0] = state[1] + d, state[1] = state[2] + e, state[2] = state[3] + a, state[3] = state[4] + b, state[4] = t + c;
}

static void ripemd160(uint8_t digest[], const void *data, size_t data_size) {
    uint32_t state[5] = {
        0x67452301UL, 0xefcdab89UL, 0x98badcfeUL, 0x10325476UL, 0xc3d2e1f0UL
    };
    size_t data_rem = data_size;
    while (data_rem >= 64) {
        _ripemd160_update(state, data);
        data = (uint8_t *) data + 64, data_rem -= 64;
    }
    union {
        uint8_t b[64];
        uint32_t l[16];
    } block;
    memcpy(block.b, data, data_rem);
    block.b[data_rem++] = 0x80;
    if (data_rem > sizeof block - sizeof(uint64_t)) {
        memset(block.b + data_rem, 0, sizeof block - data_rem);
        _ripemd160_update(state, block.b);
        data_rem = 0;
    }
    memset(block.b + data_rem, 0, sizeof block - sizeof(uint64_t) - data_rem);
    block.l[14] = bswap32(data_size << 3);
    block.l[15] = 0;
    _ripemd160_update(state, block.b);
    for (size_t i = 0; i < 5; ++i) {
        state[i] = bswap32(state[i]);
    }
    memcpy(digest, state, sizeof state);
}

static size_t base58check_encode(char * restrict out, size_t n_out, const void * restrict in, size_t n_in) {
    static const char encode[58] = {
        '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F', 'G',
        'H', 'J', 'K', 'L', 'M', 'N', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y',
        'Z', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'm', 'n', 'o', 'p',
        'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z'
    };
    if (n_out < n_in + 4) {
        ER_throw(ER_DIMENSION);
    }
    uint8_t digest[32];
    sha256(digest, in, n_in);
    sha256(digest, digest, sizeof digest);
    memcpy(out, in, n_in);
    memcpy(out + n_in, digest, 4);
    size_t z = 0, n = n_in + 4;
    while (n > 0 && out[z] == 0) {
        out[z++] = '1', --n;
    }
    out += z, n_out -= z;
    uint32_t mpn[(n + sizeof(uint32_t) - 1) / sizeof(uint32_t)];
    mpn[0] = 0;
    memcpy(((uint8_t *) mpn) + sizeof mpn - n, out, n);
    char *p = out + n_out;
    while (!zero_p(mpn, sizeof mpn / sizeof *mpn)) {
        if (--p < out) {
            ER_throw(ER_DIMENSION);
        }
        *p = encode[divn_1(mpn, sizeof mpn / sizeof *mpn, 58)];
    }
    n = out + n_out - p;
    if (p != out) {
        memmove(out, p, n);
    }
    return z + n;
}

void _main() {
    int n_sides;
    do {
        cmd_clrio();
        char buf[4];
        input(buf, sizeof buf, "How many sides (2-256)?");
        n_sides = atoi(buf);
    } while (n_sides < 2 || n_sides > 256);
    size_t n_rolls = (size_t) ceil(flt(256) * log(2) / log(n_sides));
    uint8_t rolls[n_rolls];
    struct {
        uint32_t overflow;
        uint32_t d[8];
        uint8_t flags;
    } privkey;
restart:
    for (;;) {
        memset(rolls, 0, n_rolls);
        for (size_t i = 0; i < n_rolls; ++i) {
            int roll;
            do {
                char buf[17];
                sprintf(buf, "Roll (%lu more):", n_rolls - i);
                input(buf, sizeof buf, buf);
                roll = atoi(buf);
            } while (roll < 1 || roll > n_sides);
            rolls[i] = roll - 1;
            mpn_set_str(&privkey.overflow, 9, rolls, n_rolls, n_sides);
            if (privkey.overflow != 0 || cmp256(privkey.d, secp256k1_n) >= 0) {
                disp("Start over!");
                goto restart;
            }
        }
        break;
    }
    cmd_clrio();
    {
        disp("Private key:");
        privkey.overflow = 0x80;
        privkey.flags = 0x01;
        char base58[53];
        base58[base58check_encode(base58, sizeof base58 - 1, (uint8_t *) privkey.d - 1, 34)] = '\0';
        disp_wrap(base58);
    }
    disp("Address:");
    struct {
        uint32_t type;
        uint32_t Q[3][8];
    } pubkey;
    ecp_pubkey256(pubkey.Q, secp256k1_p, secp256k1_G, privkey.d);
    pubkey.type = even256_p(pubkey.Q[1]) ? 0x02 : 0x03;
    uint8_t digest[32];
    sha256(digest, (uint8_t *) pubkey.Q[0] - 1, 33);
    ripemd160(digest + 1, digest, sizeof digest);
    digest[0] = 0;
    char base58[35];
    base58[base58check_encode(base58, sizeof base58 - 1, digest, 21)] = '\0';
    disp_wrap(base58);
}
