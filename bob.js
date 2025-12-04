a0 = 0, a1 = 1, a16 = 16, a32 = 32, a48 = 48, a64 = 64, a128 = 128

function big (a) {
  return BigInt(a)
}

function num (a) {
  return Number(a)
}

function int8 (a) {
  return new Int8Array(a)
}

function int16 (a) {
  return new Int16Array(a)
}

function int32 (a) {
  return new Int32Array(a)
}

function uint8 (a) {
  return new Uint8Array(a)
}

function uint16 (a) {
  return new Uint16Array(a)
}

function uint32 (a) {
  return new Uint32Array(a)
}

function uint64 (a) {
  return new BigUint64Array(a)
}

function int16_t (a) {
  return int16([a])[0]
}

function int32_t (a) {
  return int32([a])[0]
}

function uint8_t (a) {
  return uint8([a])[0]
}

function uint16_t (a) {
  return uint16([a])[0]
}

function uint32_t (a) {
  return uint32([a])[0]
}

function uint64_t (a) {
  return uint64([a])[0]
}

function randombytes (a) {
  return crypto.getRandomValues(uint8(a))
}

gfbits = 13
sys_n = 1 << gfbits
sys_n_8 = sys_n / 8
sys_t = 128
sys_t_1 = sys_t + 1
cond_bytes = (1 << (gfbits - 4)) * (gfbits * 2 - 1)
r_bytes = sys_t * 2
pk_nrows = sys_t * gfbits
row_bytes = uint32_t((sys_n - pk_nrows + 7) / 8)
synd_bytes = uint32_t((pk_nrows + 7) / 8)
gfmask = sys_n - 1
bgfmask = big(gfmask)
public_bytes = 1357824
secret_bytes = 14120
cipher_bytes = 208
shared_bytes = 32

function load_gf (a, ai=0) {
  let b = a[ai + 1]
  b <<= 8
  b |= a[ai]
  return b & gfmask
}

function store_gf (a, b, ai=0) {
  a[ai] = b & 255
  a[ai + 1] = b >> 8
}

function load4 (a, ai=0) {
  let b = a[ai + 3], i = 2
  for (; i >= 0; i--) {
    b <<= 8
    b |= a[ai + i]
  }
  return b
}

function load8 (a, ai=0) {
  let b = big(a[ai + 7]), i = 6
  for (; i >= 0; i--) {
    b <<= 8n
    b |= big(a[ai + i])
  }
  return b
}

function store8 (a, b, ai=0) {
  a[ai] = num((b >> 0n) & 255n)
  a[ai + 1] = num((b >> 8n) & 255n)
  a[ai + 2] = num((b >> 16n) & 255n)
  a[ai + 3] = num((b >> 24n) & 255n)
  a[ai + 4] = num((b >> 32n) & 255n)
  a[ai + 5] = num((b >> 40n) & 255n)
  a[ai + 6] = num((b >> 48n) & 255n)
  a[ai + 7] = num((b >> 56n) & 255n)
}

function bitrev (a) {
  a = ((a & 0x00FF) << 8) | ((a & 0xFF00) >> 8)
  a = ((a & 0x0F0F) << 4) | ((a & 0xF0F0) >> 4)
  a = ((a & 0x3333) << 2) | ((a & 0xCCCC) >> 2)
  a = ((a & 0x5555) << 1) | ((a & 0xAAAA) >> 1)
  return a >> 3
}

function transpose (a, b) {
  let d, e, f, i, j, k, l, m, n, s, t, u
  for (i = 0; i < 64; i++) {
    a[i] = b[i]
  }
  const m0 = [
    0x5555555555555555n,
    0x3333333333333333n,
    0x0F0F0F0F0F0F0F0Fn,
    0x00FF00FF00FF00FFn,
    0x0000FFFF0000FFFFn,
    0x00000000FFFFFFFFn
  ]
  const m1 = [
    0xAAAAAAAAAAAAAAAAn,
    0xCCCCCCCCCCCCCCCCn,
    0xF0F0F0F0F0F0F0F0n,
    0xFF00FF00FF00FF00n,
    0xFFFF0000FFFF0000n,
    0xFFFFFFFF00000000n
  ]
  for (d = 5; d >= 0; d--) {
    m = m0[d]
    n = m1[d]
    s = 1 << d
    t = s * 2
    u = big(s)
    for (i = 0; i < 64; i += t) {
      for (j = i, l = i + s; j < l; j++) {
        k = j + s
        e = a[j]
        f = a[k]
        a[j] = (e & m) | ((f & m) << u)
        a[k] = ((e & n) >> u) | (f & n)
      }
    }
  }
}

function layer_in (a0, a1, b, l) {
  let c = 0, d, i, j, k, s = 1 << l, t = s * 2
  for (i = 0; i < 64; i += t) {
    for (j = i, l = i + s; j < l; j++) {
      k = j + s
      d = a0[j] ^ a0[k]
      d &= b[c++] | 0n
      a0[j] ^= d
      a0[k] ^= d
      d = a1[j] ^ a1[k]
      d &= b[c++] | 0n
      a1[j] ^= d
      a1[k] ^= d
    }
  }
}

function layer_ex (a, b, l) {
  let c = 0, d, i, j, k, s = 1 << l, t = s * 2
  for (i = 0; i < 128; i += t) {
    for (j = i, l = i + s; j < l; j++) {
      k = j + s
      d = a[j] ^ a[k]
      d &= b[c++] | 0n
      a[j] ^= d
      a[k] ^= d
    }
  }
}

function apply_benes (a, b, bi) {
  const av0 = uint64(64)
  const av1 = uint64(64)
  const ah0 = uint64(64)
  const ah1 = uint64(64)
  const ahb = uint64(128)
  const bv = uint64(64)
  const bh = uint64(64)
  let h, i, j
  for (i = 0; i < 64; i++) {
    h = i * 16
    av0[i] = load8(a, h)
    av1[i] = load8(a, h + 8)
  }
  transpose(ah0, av0)
  transpose(ah1, av1)
  for (j = 0; j <= 6; j++) {
    for (i = 0; i < 64; i++) {
      bv[i] = load8(b, bi)
      bi += 8
    }
    transpose(bh, bv)
    for (i = 0; i < 64; i++) {
      ahb[i] = ah0[i]
      ahb[i + 64] = ah1[i]
    }
    layer_ex(ahb, bh, j)
    for (i = 0; i < 64; i++) {
      ah0[i] = ahb[i]
      ah1[i] = ahb[i + 64]
    }
  }
  transpose(av0, ah0)
  transpose(av1, ah1)
  for (j = 0; j <= 5; j++) {
    for (i = 0; i < 64; i++) {
      bv[i] = load8(b, bi)
      bi += 8
    }
    layer_in(av0, av1, bv, j)
  }
  for (j = 4; j >= 0; j--) {
    for (i = 0; i < 64; i++) {
      bv[i] = load8(b, bi)
      bi += 8
    }
    layer_in(av0, av1, bv, j)
  }
  transpose(ah0, av0)
  transpose(ah1, av1)
  for (j = 6; j >= 0; j--) {
    for (i = 0; i < 64; i++) {
      bv[i] = load8(b, bi)
      bi += 8
    }
    transpose(bh, bv)
    for (i = 0; i < 64; i++) {
      ahb[i] = ah0[i]
      ahb[i + 64] = ah1[i]
    }
    layer_ex(ahb, bh, j)
    for (i = 0; i < 64; i++) {
      ah0[i] = ahb[i]
      ah1[i] = ahb[i + 64]
    }
  }
  transpose(av0, ah0)
  transpose(av1, ah1)
  for (i = 0; i < 64; i++) {
    h = i * 16
    store8(a, av0[i], h)
    store8(a, av1[i], h + 8)
  }
  return a
}

function support_gen (a, b, bi) {
  let f, g, h, i, j
  const l = []
  for (i = 0; i < gfbits; i++) {
    l.push(uint8(sys_n_8))
  }
  for (i = 0; i < sys_n; i++) {
    f = bitrev(uint16_t(i))
    g = i % 8
    h = uint32_t(i / 8)
    for (j = 0; j < gfbits; j++) {
      l[j][h] |= ((f >> j) & 1) << g
    }
  }
  for (j = 0; j < gfbits; j++) {
    l[j] = apply_benes(l[j], b, bi)
  }
  for (f = gfbits - 1, i = 0; i < sys_n; i++) {
    a[i] = 0
    g = i % 8
    h = uint32_t(i / 8)
    for (j = f; j >= 0; j--) {
      a[i] <<= 1
      a[i] |= (l[j][h] >> g) & 1
    }
  }
}

function gf_iszero (a) {
  return (a - 1) >>> 19
}

function gf_mul (a, b) {
  a = big(a)
  b = big(b)
  let i, j, l, t
  j = a * (b & 1n)
  for (i = 1n, l = big(gfbits); i < l; i++) {
    j ^= a * (b & (1n << i))
  }
  t = j & 0x1FF0000n
  j ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  t = j & 0x000E000n
  j ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  return uint16_t(num(j) & gfmask)
}

function gf_sq2 (a) {
  a = big(a)
  const b = [
    0x1111111111111111n,
    0x0303030303030303n,
    0x000F000F000F000Fn,
    0x000000FF000000FFn
  ]
  const m = [
    0x0001FF0000000000n,
    0x000000FF80000000n,
    0x000000007FC00000n,
    0x00000000003FE000n
  ]
  a = (a | (a << 24n)) & b[3]
  a = (a | (a << 12n)) & b[2]
  a = (a | (a << 6n)) & b[1]
  a = (a | (a << 3n)) & b[0]
  let i = 0, t
  for (; i < 4; i++) {
    t = a & m[i]
    a ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  }
  return uint16_t(num(a & bgfmask))
}

function gf_sqmul (a, b) {
  a = BigInt(a)
  b = BigInt(b)
  let i, t, x
  x = (b << 6n) * (a & 64n)
  a ^= a << 7n
  x ^= b * (a & 0x04001n)
  x ^= (b * (a & 0x08002n)) << 1n
  x ^= (b * (a & 0x10004n)) << 2n
  x ^= (b * (a & 0x20008n)) << 3n
  x ^= (b * (a & 0x40010n)) << 4n
  x ^= (b * (a & 0x80020n)) << 5n
  const m = [
    0x0000001FF0000000n,
    0x000000000FF80000n,
    0x000000000007E000n
  ]
  for (i = 0; i < 3; i++) {
    t = x & m[i]
    x ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  }
  return uint16_t(num(x & bgfmask))
}

function gf_sq2mul (a, b) {
  a = BigInt(a)
  b = BigInt(b)
  let i, t, x
  x = (b << 18n) * (a & BigInt(1 << 6))
  a ^= a << 21n
  x ^= b * (a & 0x010000001n)
  x ^= (b * (a & 0x020000002n)) << 3n
  x ^= (b * (a & 0x040000004n)) << 6n
  x ^= (b * (a & 0x080000008n)) << 9n
  x ^= (b * (a & 0x100000010n)) << 12n
  x ^= (b * (a & 0x200000020n)) << 15n
  const m = [
    0x1FF0000000000000n,
    0x000FF80000000000n,
    0x000007FC00000000n,
    0x00000003FE000000n,
    0x0000000001FE0000n,
    0x000000000001E000n
  ]
  for (i = 0; i < 6; i++) {
    t = x & m[i]
    x ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  }
  return uint16_t(num(x & bgfmask))
}

function gf_frac (a, b) {
  a = gf_sqmul(a, a)
  a = gf_sq2mul(a, a)
  let c = gf_sq2(a)
  c = gf_sq2mul(c, a)
  c = gf_sq2(c)
  c = gf_sq2mul(c, a)
  return gf_sqmul(c, b)
}

function gf_inv (a) {
  return gf_frac(a, 1)
}

function mul_gf (a, b, c) {
  const d = uint16(r_bytes - 1)
  let i, j
  for (i = 0; i < sys_t; i++) {
    for (j = 0; j < sys_t; j++) {
      d[i + j] ^= gf_mul(b[i], c[j])
    }
  }
  for (i = (sys_t - 1) * 2; i >= sys_t; i--) {
    j = i - sys_t
    d[j + 7] ^= d[i]
    d[j + 2] ^= d[i]
    d[j + 1] ^= d[i]
    d[j] ^= d[i]
  }
  for (i = 0; i < sys_t; i++) {
    a[i] = d[i]
  }
}

function min (a, b) {
  return a < b ? a : b
}

function bm (a, b) {
  const c = uint16(sys_t_1)
  const s = uint16(sys_t_1)
  const t = uint16(sys_t_1)
  const m = uint16(2)
  c[0] = s[1] = 1
  let d, f, g, h, i, m0, m1, n
  let e = 1, l = 0
  for (n = 0, g = sys_t * 2; n < g; n++) {
    d = 0
    for (i = 0, h = min(n, sys_t); i <= h; i++) {
      d ^= gf_mul(c[i], b[n - i])
    }
    m[0] = d - 1
    m[0] >>= 15
    m0 = m[0] -= 1
    m[1] = n - l * 2
    m[1] >>= 15
    m[1] -= 1
    m1 = m[1] &= m0
    for (i = 0; i <= sys_t; i++) {
      t[i] = c[i]
    }
    f = gf_frac(e, d)
    for (i = 0; i <= sys_t; i++) {
      c[i] ^= gf_mul(f, s[i]) & m0
    }
    l = (l & ~m1) | ((n + 1 - l) & m1)
    for (i = 0; i <= sys_t; i++) {
      s[i] = (s[i] & ~m1) | (t[i] & m1)
    }
    e = (e & ~m1) | (d & m1)
    for (i = sys_t; i >= 1; i--) {
      s[i] = s[i - 1]
    }
    s[0] = 0
  }
  for (i = 0; i <= sys_t; i++) {
    a[i] = c[sys_t - i]
  }
}

function int16_negative_mask (a) {
  return a >> 15
}

function int16_nonzero_mask (a) {
  return int16_negative_mask(a) | int16_negative_mask(-a)
}

function uint16_signed_negative_mask (a) {
  return a >> 15
}

function uint16_nonzero_mask (a) {
  return uint16_signed_negative_mask(a) | uint16_signed_negative_mask(-a)
}

function uint16_zero_mask (a) {
  return ~uint16_nonzero_mask(a)
}

function uint32_signed_negative_mask (a) {
  return a >> 31
}

function uint32_nonzero_mask (a) {
  return uint32_signed_negative_mask(a) | uint32_signed_negative_mask(-a)
}

function uint32_equal_mask (a, b) {
  return ~uint32_nonzero_mask(a ^ b)
}

function uint64_signed_negative_mask (a) {
  return big(a) >> 63n
}

function uint64_nonzero_mask (a) {
  return uint64_signed_negative_mask(a) | uint64_signed_negative_mask(-a)
}

function uint64_equal_mask (a, b) {
  return ~uint64_nonzero_mask(a ^ b)
}

function uint64_zero_mask (a) {
  return ~uint64_nonzero_mask(big(a))
}

function memcpy (a, b, c, ai=0, bi=0) {
  const l = a.length
  if (ai < l && bi < b.length) {
    if (bi + c < l - ai) {
      for (let i = 0; i < c; i++) {
        a[ai + i] = b[bi + i]
      }
    } else {
      for (let i = 0, c = l - ai; i < c; i++) {
        a[ai + i] = b[bi + i]
      }
    }
  }
}

function int32_minmax (a, b) {
  const c = b ^ a
  let d = b - a
  d ^= c & (d ^ b)
  return (d >> 31) & c
}

function int32_sort (a, b, ai=0) {
  if (b < 2) {
    return
  }
  let c, d, h, i, j, k, l, p, q, r, t = 1
  while (t < b - t) {
    t += t
  }
  for (p = t; p > 0; p >>= 1) {
    for (i = 0, l = b - p; i < l; ++i) {
      if (!(i & p)) {
        h = ai + i
        j = h + p
        c = int32_minmax(a[h], a[j])
        a[h] ^= c
        a[j] ^= c
      }
    }
    i = 0
    for (q = t; q > p; q >>= 1) {
      for (l = b - q; i < l; ++i) {
        if (!(i & p)) {
          h = ai + i
          j = h + p
          d = a[j]
          for (r = q; r > p; r >>= 1) {
            k = h + r
            c = int32_minmax(d, a[k])
            d ^= c
            a[k] ^= c
          }
          a[j] = d
        }
      }
    }
  }
}

function cbrecursion (a, p, pi, s, r, w, n, b) {
  let e, f, i, j, k, l
  const g = n / 2
  if (w == 1) {
    a[p + (pi >> 3)] ^= r[0] << (pi & 7)
    return
  }
  for (i = 0; i < n; ++i) {
    b[i] = ((r[i] ^ 1) << 16) | r[i ^ 1]
  }
  int32_sort(b, n)
  for (i = 0; i < n; ++i) {
    e = b[i] & 0xffff
    f = e ^ int32_minmax(e, i)
    b[i + n] = (e << 16) | f
  }
  for (i = 0; i < n; ++i) {
    b[i] = ((b[i] << 16) | i)
  }
  int32_sort(b, n)
  for (i = 0; i < n; ++i) {
    b[i] = (b[i] << 16) + (b[i + n] >> 16)
  }
  int32_sort(b, n)
  if (w <= 10) {
    for (i = 0; i < n; ++i) {
      b[i + n] = ((b[i] & 0xffff) << 10) | (b[i + n] & 0x3ff)
    }
    for (i = 1, l = w - 1; i < l; ++i) {
      for (j = 0; j < n; ++j) {
        b[j] = ((b[j + n] & ~0x3ff) << 6) | j
      }
      int32_sort(b, n)
      for (j = 0; j < n; ++j) {
        b[j] = (b[j] << 20) | b[j + n]
      }
      int32_sort(b, n)
      for (j = 0; j < n; ++j) {
        e = b[j] & 0xfffff
        f = (b[j] & 0xffc00) | (b[j + n] & 0x3ff)
        b[j + n] = f ^ int32_minmax(f, e)
      }
    }
    for (i = 0; i < n; ++i) {
      b[i + n] &= 0x3ff
    }
  } else {
    for (i = 0; i < n; ++i) {
      b[i + n] = (b[i] << 16) | (b[i + n] & 0xffff)
    }
    for (i = 1, l = w - 1; i < l; ++i) {
      for (j = 0; j < n; ++j) {
        b[j] = (b[j + n] & ~0xffff) | j
      }
      int32_sort(b, n)
      for (j = 0; j < n; ++j) {
        b[j] = (b[j] << 16) | (b[j + n] & 0xffff)
      }
      if (i < w - 2) {
        for (j = 0; j < n; ++j) {
          b[j + n] = (b[j] & ~0xffff) | (b[j + n] >> 16)
        }
        int32_sort(b, n, n)
        for (j = 0; j < n; ++j) {
          b[j + n] = (b[j + n] << 16) | (b[j] & 0xffff)
        }
      }
      int32_sort(b, n)
      for (j = 0; j < n; ++j) {
        e = (b[j + n] & ~0xffff) | (b[j] & 0xffff)
        b[j + n] ^= int32_minmax(b[j + n], e)
      }
    }
    for (j = 0; j < n; ++j) {
      b[j + n] &= 0xffff
    }
  }
  for (i = 0; i < n; ++i) {
    b[i] = (r[i] << 16) + i
  }
  int32_sort(b, n)
  let fi, fj
  for (i = 0; i < g; ++i) {
    j = i * 2
    fi = b[j + n] & 1
    fj = j + fi
    a[p + (pi >> 3)] ^= fi << (pi & 7)
    pi += s
    b[j + n] = (b[j] << 16) | fj
    b[j] = b[j + 1]
    b[j + n + 1] = (b[j] << 16) | (fj ^ 1)
  }
  int32_sort(b, n, n)
  t = (w * 2 - 3) * s * g
  pi += t
  let x, y
  for (i = 0; i < g; ++i) {
    j = i * 2
    k = j + n
    x = b[k] & 1
    y = j + x
    a[p + (pi >> 3)] ^= x << (pi & 7)
    pi += s
    b[j] = (y << 16) | (b[k] & 0xffff)
    b[j + 1] = ((y ^ 1) << 16) | (b[k + 1] & 0xffff)
  }
  int32_sort(b, n)
  r = int16((b.length - (n + n / 4)) * 2)
  for (i = 0; i < g; ++i) {
    j = i * 2
    r[i] = (b[j] & 0xffff) >> 1
    r[i + g] = (b[j + 1] & 0xffff) >> 1
  }
  pi -= t + s * g
  cbrecursion(a, p, pi, s * 2, r, w - 1, g, b)
  cbrecursion(a, p, pi + s, s * 2, r.slice(g), w - 1, g, b)
}

function layer (a, b, p, s, n) {
  let d, g, h, i, j, m, t = 1 << (s & 31), u = t * 2, x = 0
  for (i = 0; i < n; i += u) {
    for (j = 0; j < t; j++) {
      g = i + j
      h = g + t
      d = a[g] ^ a[h]
      m = (b[p + (x >> 3)] >> (x & 7)) & 1
      d &= int16_t(d & -m)
      a[g] ^= d
      a[h] ^= d
      x++
    }
  }
}

function memset (a, p, v, b) {
  for (let i = p, l = b + p; i < l; i++) {
    a[i] = v
  }
}

function control (a, b, w, n) {
  const p = int16(n)
  const t = int32(n * 2)
  const j = n >> 4, v = (((w * 2 - 1) * n / 2) + 7) / 8
  let d, i, r = 0
  while (1) {
    memset(a, r, 0, v)
    cbrecursion(a, r, 0, 1, b, w, n, t)
    for (i = 0; i < n; i++) {
      p[i] = i
    }
    for (i = 0; i < w; i++) {
      layer(p, a, r, i, n)
      r += j
    }
    for (i = w - 2; i >= 0; i--) {
      layer(p, a, r, i, n)
      r += j
    }
    d = 0
    for (i = 0; i < n; i++) {
      d |= b[i] ^ p[i]
    }
    d = int16_nonzero_mask(d)
    if (d == 0) {
      break
    }
  }
  return a
}

function evals (a, b) {
  let c = a[sys_t]
  for (let i = sys_t - 1; i >= 0; i--) {
    c = gf_mul(c, b)
    c ^= a[i]
  }
  return c
}

function root (a, f, l) {
  for (let i = 0; i < sys_n; i++) {
    a[i] = evals(f, l[i])
  }
}

function genpoly_gen (a, f) {
  let c, i, j, k, t
  const m = []
  for (i = 0; i < sys_t_1; i++) {
    m.push(uint16(sys_t))
  }
  m[0][0] = 1
  for (i = 1; i < sys_t; i++) {
    m[1][i] = f[i]
  }
  m[1][0] = f[0]
  for (j = 2; j <= sys_t; j++) {
    mul_gf(m[j], m[j - 1], f)
  }
  for (j = 0; j < sys_t; j++) {
    for (k = j + 1; k < sys_t; k++) {
      t = gf_iszero(m[j][j])
      for (c = j; c < sys_t_1; c++) {
        m[c][j] ^= m[c][k] & t
      }
    }
    t = m[j][j]
    if (uint16_zero_mask(t)) {
      return -1
    }
    t = gf_inv(t)
    for (c = j; c < sys_t_1; c++) {
      m[c][j] = gf_mul(m[c][j], t)
    }
    for (k = 0; k < sys_t; k++) {
      if (k != j) {
        t = m[j][k]
        for (c = j; c < sys_t_1; c++) {
          m[c][k] ^= gf_mul(m[c][j], t)
        }
      }
    }
  }
  t = m[sys_t]
  for (i = 0; i < sys_t; i++) {
    a[i] = t[i]
  }
  return 0
}

function synd (a, f, l, r) {
  let c, d, e, i, j
  const t = sys_t * 2
  a.fill(0, 0, t)
  for (i = 0; i < sys_n; i++) {
    c = (r[uint32_t(i / 8)] >> (i % 8)) & 1
    e = evals(f, l[i])
    d = gf_inv(gf_mul(e, e))
    for (j = 0; j < t; j++) {
      a[j] ^= gf_mul(d, c)
      d = gf_mul(d, l[i])
    }
  }
}

function uint64_minmax (a, b) {
  let c = uint64_t(b - a)
  c = uint64_t(-(c >> 63n))
  return c & (a ^ b)
}

function uint64_sort (a, b) {
  if (b < 2) {
    return
  }
  let c, d, i, j, k, l, p, q, r, t = 1
  while (t < b - t) {
    t += t
  }
  for (p = t; p > 0; p >>= 1) {
    for (i = 0, l = b - p; i < l; ++i) {
      if (!(i & p)) {
        j = i + p
        c = uint64_minmax(a[i], a[j])
        a[i] ^= c
        a[i + p] ^= c
      }
    }
    i = 0
    for (q = t; q > p; q >>= 1) {
      for (l = b - q; i < l; ++i) {
        if (!(i & p)) {
          j = i + p
          d = a[j]
          for (r = q; r > p; r >>= 1) {
            k = i + r
            c = uint64_minmax(d, a[k])
            a[k] ^= c
            d ^= c
          }
          a[j] = d
        }
      }
    }
  }
}

function ctz (a) {
  let b, i, m = 0, r = 0
  for (i = 0; i < 64; i++) {
    b = num((a >> big(i)) & 1n)
    m |= b
    r += (m ^ 1) & (b ^ 1)
  }
  return r
}

function same_mask_big (a, b) {
  const m = uint64([big(a ^ b)])
  m[0] -= 1n
  m[0] >>= 63n
  m[0] = -m[0]
  return m[0]
}

function mov_columns (a, b, p=0n) {
  let d, i, j, k, m, s, t
  const c = uint64(32)
  const f = uint64(64)
  const r = pk_nrows - 32
  const q = r / 8
  const u = uint8(8)
  for (i = 0; i < 32; i++) {
    for (j = 0; j < 8; j++) {
      u[j] = a[i + r][j + q]
    }
    f[i] = load8(u)
  }
  for (i = 0; i < 32; i++) {
    t = f[i]
    for (j = i + 1; j < 32; j++) {
      t |= f[j]
    }
    if (uint64_zero_mask(t)) {
      return -1n
    }
    c[i] = s = big(ctz(t))
    p |= 1n << s
    for (j = i + 1; j < 32; j++) {
      m = (f[i] >> s) & 1n
      f[i] ^= f[j] & (m - 1n)
    }
    for (j = i + 1; j < 32; j++) {
      m = (f[j] >> s) & 1n
      f[j] ^= f[i] & -m
    }
  }
  for (j = 0; j < 32; j++) {
    for (k = j + 1; k < 64; k++) {
      d = big(b[r + j] ^ b[r + k])
      d &= same_mask_big(k, num(c[j]))
      d = int16_t(num(d))
      b[r + j] ^= d
      b[r + k] ^= d
    }
  }
  for (i = 0; i < pk_nrows; i++) {
    for (k = 0; k < 8; k++) {
      u[k] = a[i][k + q]
    }
    t = load8(u)
    for (j = 0; j < 32; j++) {
      d = t >> big(j)
      d ^= t >> c[j]
      d &= 1n
      t ^= d << c[j]
      t ^= d << big(j)
    }
    store8(u, t)
    for (k = 0; k < 8; k++) {
      a[i][k + q] = u[k]
    }
  }
  return p
}

function pk_gen (p, s, si, h, o, v) {
  let b, c, d, i, j, k, r, t
  const f = uint64(sys_n)
  const m = []
  for (i = 0; i < pk_nrows; i++) {
    m.push(uint8(sys_n_8))
  }
  const g = uint16(sys_t_1)
  const l = uint16(sys_n)
  const n = uint16(sys_n)
  g[sys_t] = 1
  for (i = 0; i < sys_t; i++) {
    g[i] = load_gf(s, si)
    si += 2
  }
  for (i = 0; i < sys_n; i++) {
    f[i] = big(h[i])
    f[i] <<= 31n
    f[i] |= big(i)
  }
  uint64_sort(f, sys_n)
  for (i = 1; i < sys_n; i++) {
    if (uint64_equal_mask(f[i - 1] >> 31n, f[i] >> 31n)) {
      return -1n
    }
  }
  for (i = 0; i < sys_n; i++) {
    o[i] = num(f[i] & bgfmask)
  }
  for (i = 0; i < sys_n; i++) {
    l[i] = bitrev(o[i])
  }
  root(n, g, l)
  for (i = 0; i < sys_n; i++) {
    n[i] = gf_inv(n[i])
  }
  for (i = 0; i < sys_t; i++) {
    d = i * gfbits
    for (j = 0; j < sys_n; j += 8) {
      for (k = 0; k < gfbits; k++) {
        b = 0
        for (h = 7; h > 0; h--) {
          b = (b | ((n[j + h] >> k) & 1)) << 1
        }
        b |= (n[j] >> k) & 1
        m[d + k][j / 8] = b
      }
    }
    for (j = 0; j < sys_n; j++) {
      n[j] = gf_mul(n[j], l[j])
    }
  }
  for (i = 0, b = (pk_nrows + 7) / 8; i < b; i++) {
    h = i * 8
    for (j = 0; j < 8; j++) {
      r = h + j
      if (r >= pk_nrows) {
        break
      }
      if (v >= 0n && r == pk_nrows - 32) {
        v = mov_columns(m, o, v)
        if (v < 0n) {
          return -1n
        }
      }
      for (k = r + 1; k < pk_nrows; k++) {
        t = m[r][i] ^ m[k][i]
        t >>= j
        t &= 1
        t = uint8_t(-t)
        for (c = 0; c < sys_n_8; c++) {
          m[r][c] ^= m[k][c] & t
        }
      }
      if (uint64_zero_mask((m[r][i] >> j) & 1)) {
        return -1n
      }
      for (k = 0; k < pk_nrows; k++) {
        if (k != r) {
          t = m[k][i] >> j
          t &= 1
          t = uint8_t(-t)
          for (c = 0; c < sys_n_8; c++) {
            m[k][c] ^= m[r][c] & t
          }
        }
      }
    }
  }
  for (i = 0; i < pk_nrows; i++) {
    memcpy(p, m[i], row_bytes, i * row_bytes, synd_bytes)
  }
  return v
}

function same_mask (a, b) {
  const c = uint32([uint16_t(a) ^ uint16_t(b)])
  c[0] -= 1
  c[0] >>>= 31
  c[0] = -c[0]
  return uint8_t(c[0] & 255)
}

function gen_e (a) {
  let b, e, i, j
  const c = uint8(sys_t)
  const d = uint16(sys_t)
  while (1) {
    b = randombytes(r_bytes)
    for (i = 0; i < sys_t; i++) {
      d[i] = load_gf(b, i * 2)
    }
    e = 0
    for (i = 1; i < sys_t; i++) {
      for (j = 0; j < i; j++) {
        if (uint32_equal_mask(d[i], d[j])) {
          e = 1
        }
      }
    }
    if (e == 0) {
      break
    }
  }
  for (j = 0; j < sys_t; j++) {
    c[j] = 1 << (d[j] & 7)
  }
  for (i = 0; i < sys_n_8; i++) {
    a[i] = 0
    for (j = 0; j < sys_t; j++) {
      a[i] |= c[j] & same_mask(i, d[j] >> 3)
    }
  }
}

function syndrome (s, p, e) {
  let b, i, j, o = 0
  const r = uint8(sys_n_8)
  for (i = 0; i < synd_bytes; i++) {
    s[i] = 0
  }
  for (i = 0; i < pk_nrows; i++) {
    for (j = 0; j < sys_n_8; j++) {
      r[j] = 0
    }
    for (j = 0; j < row_bytes; j++) {
      r[j - row_bytes + sys_n_8] = p[j + o]
    }
    o += row_bytes
    r[uint32_t(i / 8)] |= 1 << (i % 8)
    b = 0
    for (j = 0; j < sys_n_8; j++) {
      b ^= r[j] & e[j]
    }
    b ^= b >> 4
    b ^= b >> 2
    b ^= b >> 1
    b &= 1
    s[uint32_t(i / 8)] |= b << (i % 8)
  }
}

function decrypts (e, s, si, c) {
  let b, i, t, w = 0
  const r = uint8(sys_n_8)
  const g = uint16(sys_t_1)
  const l = uint16(sys_n)
  const p = uint16(r_bytes)
  const f = p.slice()
  const m = l.slice()
  const o = g.slice()
  for (i = 0; i < synd_bytes; i++) {
    r[i] = c[i]
  }
  for (i = 0; i < sys_t; i++) {
    g[i] = load_gf(s, si)
    si += 2
  }
  g[sys_t] = 1
  support_gen(l, s, si)
  synd(p, g, l, r)
  bm(o, p)
  root(m, o, l)
  for (i = 0; i < sys_n_8; i++) {
    e[i] = 0
  }
  for (i = 0; i < sys_n; i++) {
    t = gf_iszero(m[i]) & 1
    e[uint32_t(i / 8)] |= t << (i % 8)
    w += t
  }
  synd(f, g, l, e)
  b = w ^ sys_t
  for (i = 0; i < r_bytes; i++) {
    b |= p[i] ^ f[i]
  }
  b -= 1
  b >>= 15
  return b ^ 1
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24)
  }
  return d
}

function unpack (a) {
  let b = 0, c = a.length, d = [], e, f = 255
  while (b < c) {
    e = a[b++]
    d.push(e & f, e >> 8 & f, e >> 16 & f, e >> 24 & f)
  }
  return d
}

function shift (a, b) {
  return a << b | a >>> a32 - b
}

function expand (a, g=a0, h=a1) {
  g = big(g)
  h = big(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a32] | a0),
      j = uint32(a16).map((c, b) => a[b + a16] | a0 + a[b + a48] | a0)
  a = uint8(num(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + a1
    a[c] = h + a1
    a[d] = i + a1
    a[e] = j + a1
  }

  function l () {
    let a = i.slice(), b = j.slice(), c, d = a16, e = 25

    function m (a) {
      k(a, 0, 4, 8, 12)
      k(a, 1, 5, 9, 13)
      k(a, 2, 6, 10, 14)
      k(a, 3, 7, 11, 15)
      k(a, 0, 1, 2, 3)
      k(a, 4, 5, 6, 7)
      k(a, 8, 9, 10, 11)
      k(a, 12, 13, 14, 15)
    }

    while (e--) {
      m(a)
      m(b)
      if (e % 5 == a0) {
        c = d
        while (c--) {
          b[c] = a[c] += b[c]
        }
        b.reverse()
      }
    }
    return a
  }

  let m = 2n ** 32n

  function n (a) {
    let b = a0, c = a16, d = 0n
    while (b < c) {
      d = d * m + big(a[b++])
    }
    return d
  }

  function o (a, b) {
    let c = a0, d = a16
    while (c < d) {
      b[--d] = num(a % m)
      a /= m
    }
    return b
  }

  const p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(num(m), num(h - g + m)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, num(h - b)), num(b - g))
  }
  return a
}

function reduces (a, h=a1) {
  while (a.length > a128) {
    a = [...expand(a.slice(a0, a128), a0, a64), ...a.slice(a128)]
  }
  return expand(a, a0, h)
}

function crypto_kem_keypair (p, s) {
  const o = int16(sys_n)
  const l = sys_n_8 + sys_n * 4 + r_bytes + 32
  const r = uint8(l)
  const f = uint16(sys_t)
  const g = uint16(sys_t)
  const h = uint32(sys_n)
  const j = 0n
  let i, ri, si
  while (1) {
    r.set(randombytes(l))
    ri = l - f.length * 2 - 32
    for (i = 0; i < sys_t; i++) {
      f[i] = load_gf(r, i * 2 + ri)
    }
    if (genpoly_gen(g, f)) {
      continue
    }
    si = 40
    for (i = 0; i < sys_t; i++) {
      store_gf(s, g[i], i * 2 + si)
    }
    si += r_bytes
    ri -= h.length * 4
    for (i = 0; i < sys_n; i++) {
      h[i] = load4(r, i * 4 + ri)
    }
    if (pk_gen(p, s, si - r_bytes, h, o, j) < 0n) {
      continue
    }
    s.set(control(s.slice(), o, gfbits, sys_n).slice(0, secret_bytes - 296), 296)
    si += cond_bytes
    ri -= sys_n_8
    memcpy(s, r, sys_n_8, si, ri)
    break
  }
}

function crypto_kem_enc (c, k, p) {
  const a = uint8(synd_bytes + sys_n_8 + 1)
  const e = uint8(sys_n_8)
  a[0] = 1
  gen_e(e)
  syndrome(c, p, e)
  memcpy(a, e, sys_n_8, 1)
  memcpy(a, c, synd_bytes, sys_n_8 + 1)
  k.set(reduces(a, 32))
}

function crypto_kem_dec (k, c, s) {
  const e = uint8(sys_n_8)
  const a = uint8(synd_bytes + sys_n_8 + 1)
  const d = decrypts(e, s, 40, c)
  s = s.slice(cond_bytes + r_bytes + 40)
  if (d > 0) {
    return []
  }
  const m = (d - 1) >> 8
  a[0] = m & 1
  for (let i = 0, j = 1; i < sys_n_8; i++) {
    a[j++] = (~m & s[i]) | (m & e[i])
  }
  memcpy(a, c, synd_bytes, sys_n_8 + 1)
  k.set(reduces(a, 32))
}

priv = uint8(secret_bytes)
pub = uint8(public_bytes)
crypto_kem_keypair(pub, priv)
ciph = uint8(cipher_bytes)
key0 = uint8(shared_bytes)
crypto_kem_enc(ciph, key0, pub)
key1 = uint8(shared_bytes)
crypto_kem_dec(key1, ciph, priv)
key0.toString() == key1.toString()