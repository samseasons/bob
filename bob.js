a0 = 0, a1 = 1, a2 = 2, a5 = 5, a8 = 8, a16 = 16, a32 = 32, a64 = 64, a128 = 128, b0 = 0n

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

public_bytes = 1357824
secret_bytes = 14120
cipher_bytes = 208
shared_bytes = a32
gfbits = 13
sys_t = 128
sys_n = 1 << gfbits
sys_n_8 = sys_n / a8
sys_t_1 = sys_t + 1
cond_bytes = (1 << (gfbits - 4)) * (2 * gfbits - 1)
irr_bytes = sys_t * 2
pk_nrows = sys_t * gfbits
row_bytes = uint32_t((sys_n - pk_nrows + 7) / a8)
synd_bytes = uint32_t((pk_nrows + 7) / a8)
gfmask = sys_n - 1
bgfmask = BigInt(gfmask)

function load_gf (a, p=0) {
  let b = a[p + 1]
  b <<= a8
  b |= a[p]
  return b & gfmask
}

function store_gf (a, b, p=0) {
  a[p] = b & 255
  a[p + 1] = b >> a8
}

function load4 (a, p=0) {
  let b = a[p + 3], i = 2
  for (; i >= 0; i--) {
    b <<= a8
    b |= a[p + i]
  }
  return b
}

function store8 (a, b, p=0) {
  a[p] = Number((b >> b0) & 255n)
  a[p + 1] = Number((b >> 8n) & 255n)
  a[p + 2] = Number((b >> 16n) & 255n)
  a[p + 3] = Number((b >> 24n) & 255n)
  a[p + 4] = Number((b >> 32n) & 255n)
  a[p + 5] = Number((b >> 40n) & 255n)
  a[p + 6] = Number((b >> 48n) & 255n)
  a[p + 7] = Number((b >> 56n) & 255n)
}

function load8 (a, p=0) {
  let b = BigInt(a[p + 7]), i = 6
  for (; i >= 0; i--) {
    b <<= 8n
    b |= BigInt(a[p + i])
  }
  return b
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
  const m0 = [0x5555555555555555n, 0x3333333333333333n, 0x0F0F0F0F0F0F0F0Fn, 0x00FF00FF00FF00FFn, 0x0000FFFF0000FFFFn,
    0x00000000FFFFFFFFn]
  const m1 = [0xAAAAAAAAAAAAAAAAn, 0xCCCCCCCCCCCCCCCCn, 0xF0F0F0F0F0F0F0F0n, 0xFF00FF00FF00FF00n, 0xFFFF0000FFFF0000n,
    0xFFFFFFFF00000000n]
  a.set(b.slice(0, a64))
  for (d = a5; d >= 0; d--) {
    s = 1 << d
    t = s * 2
    u = BigInt(s)
    m = m0[d]
    n = m1[d]
    for (i = 0; i < a64; i += t) {
      for (j = i, l = j + s; j < l; j++) {
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
  for (i = 0; i < a64; i += t) {
    for (j = i; j < i + s; j++) {
      k = j + s
      d = a0[j] ^ a0[k]
      d &= b[c++] | b0
      a0[j] ^= d
      a0[k] ^= d
      d = a1[j] ^ a1[k]
      d &= b[c++] | b0
      a1[j] ^= d
      a1[k] ^= d
    }
  }
}

function layer_ex (a, b, l) {
  let c = 0, d, i, j, k, s = 1 << l, t = s * 2
  for (i = 0; i < a128; i += t) {
    for (j = i, l = i + s; j < l; j++) {
      k = j + s
      d = a[j] ^ a[k]
      d &= b[c++] | b0
      a[j] ^= d
      a[k] ^= d
    }
  }
}

function apply_benes (a, b, p) {
  const av0 = uint64(a64)
  const av1 = uint64(a64)
  const ah0 = uint64(a64)
  const ah1 = uint64(a64)
  const ahb = uint64(a128)
  const bv = uint64(a64)
  const bh = uint64(a64)
  let i, i16, j
  for (i = 0; i < a64; i++) {
    i16 = i * a16
    av0[i] = load8(a, i16)
    av1[i] = load8(a, i16 + a8)
  }
  transpose(ah0, av0)
  transpose(ah1, av1)
  for (j = 0; j <= 6; j++) {
    for (i = 0; i < a64; i++) {
      bv[i] = load8(b, p)
      p += a8
    }
    transpose(bh, bv)
    ahb.set(ah0)
    ahb.set(ah1, a64)
    layer_ex(ahb, bh, j)
    ah0.set(ahb.slice(0, a64))
    ah1.set(ahb.slice(a64))
  }
  transpose(av0, ah0)
  transpose(av1, ah1)
  for (j = 0; j <= a5; j++) {
    for (i = 0; i < a64; i++) {
      bv[i] = load8(b, p)
      p += a8
    }
    layer_in(av0, av1, bv, j)
  }
  for (j = 4; j >= 0; j--) {
    for (i = 0; i < a64; i++) {
      bv[i] = load8(b, p)
      p += a8
    }
    layer_in(av0, av1, bv, j)
  }
  transpose(ah0, av0)
  transpose(ah1, av1)
  for (j = 6; j >= 0; j--) {
    for (i = 0; i < a64; i++) {
      bv[i] = load8(b, p)
      p += a8
    }
    transpose(bh, bv)
    ahb.set(ah0)
    ahb.set(ah1, a64)
    layer_ex(ahb, bh, j)
    ah0.set(ahb.slice(0, a64))
    ah1.set(ahb.slice(a64))
  }
  transpose(av0, ah0)
  transpose(av1, ah1)
  for (i = 0; i < a64; i++) {
    i16 = i * a16
    store8(a, av0[i], i16)
    store8(a, av1[i], i16 + a8)
  }
  return a
}

function support_gen (a, b, p) {
  let f, g, h, i, j
  const l = uint8(gfbits * sys_n_8)
  for (i = 0; i < sys_n; i++) {
    h = uint32_t(i / a8)
    g = i % a8
    f = bitrev(uint16_t(i))
    for (j = 0; j < gfbits; j++) {
      l[j * sys_n_8 + h] |= ((f >> j) & 1) << g
    }
  }
  for (i = 0; i < gfbits; i++) {
    j = i * sys_n_8
    l.set(apply_benes(l.slice(j, j + sys_n_8), b, p), j)
  }
  a.set(int8(sys_n))
  for (i = 0; i < sys_n; i++) {
    h = uint32_t(i / a8)
    g = i % a8
    for (j = gfbits - 1; j >= 0; j--) {
      a[i] = (a[i] << 1) | ((l[j * sys_n_8 + h] >> g) & 1)
    }
  }
}

function min (a, b) {
  return a < b ? a : b
}

function bm (a, b) {
  let d, f, i, m0, m1, n
  let e = 1, l = 0
  const c = uint16(sys_t_1)
  const s = uint16(sys_t_1)
  const t = uint16(sys_t_1)
  const m = uint16(2)
  s[1] = c[0] = 1
  for (n = 0; n < 2 * sys_t; n++) {
    d = 0
    for (i = 0; i <= min(n, sys_t); i++) {
      d ^= gf_mul(c[i], b[n - i])
    }
    m[0] = d - 1
    m[0] = m[0] >> 15
    m[0] = m0 = m[0] - 1
    m[1] = n - 2 * l
    m[1] = m[1] >> 15
    m[1] = m[1] - 1
    m[1] = m1 = m[1] & m[0]
    t.set(c.slice(0, sys_t))
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
  a.set(c.slice(0, sys_t + 1).reverse())
}

function int16_negative_mask (int16_x) {
  return int16_x >> 15
}

function int16_nonzero_mask (int16_x) {
  return int16_negative_mask(int16_x) | int16_negative_mask(-int16_x)
}

function uint16_signed_negative_mask (uint16_signed_x) {
  return uint16_signed_x >> 15
}

function uint16_nonzero_mask (uint16_x) {
  return uint16_signed_negative_mask(uint16_x) | uint16_signed_negative_mask(-uint16_x)
}

function uint16_zero_mask (uint16_x) {
  return ~uint16_nonzero_mask(uint16_x)
}

function uint32_signed_negative_mask (uint32_signed_x) {
  return uint32_signed_x >> 31
}

function uint32_nonzero_mask (uint32_x) {
  return uint32_signed_negative_mask(uint32_x) | uint32_signed_negative_mask(-uint32_x)
}

function uint32_unequal_mask (uint32_x, uint32_y) {
  return uint32_nonzero_mask(uint32_x ^ uint32_y)
}

function uint32_equal_mask (uint32_x, uint32_y) {
  return ~uint32_unequal_mask(uint32_x, uint32_y)
}

function uint64_signed_negative_mask (uint64_signed_x) {
  return uint64_signed_x >> 63n
}

function uint64_nonzero_mask (uint64_x) {
  return uint64_signed_negative_mask(uint64_x) | uint64_signed_negative_mask(-uint64_x)
}

function uint64_unequal_mask (uint64_x, uint64_y) {
  return uint64_nonzero_mask(uint64_x ^ uint64_y)
}

function uint64_equal_mask (uint64_x, uint64_y) {
  return ~uint64_unequal_mask(uint64_x, uint64_y)
}

function uint64_zero_mask (uint64_x) {
  return ~uint64_nonzero_mask(BigInt(uint64_x))
}

function gf_iszero (a) {
  a = uint32([a])
  a[0] -= 1
  a[0] >>= 19
  return uint16_t(a[0])
}

function gf_mul (a, b) {
  let i, j, t
  j = BigInt(a * (b & 1))
  for (i = 1; i < gfbits; i++) {
    j ^= BigInt(a * (b & (1 << i)))
  }
  t = j & 0x1FF0000n
  j ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  t = j & 0x000E000n
  j ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  return uint16_t(Number(j & bgfmask))
}

function gf_sq2 (a) {
  let i, t, x = BigInt(a)
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
  x = (x | (x << 24n)) & b[3]
  x = (x | (x << 12n)) & b[2]
  x = (x | (x << 6n)) & b[1]
  x = (x | (x << 3n)) & b[0]
  for (i = 0; i < 4; i++) {
    t = x & m[i]
    x ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  }
  return uint16_t(Number(x & bgfmask))
}

function gf_sqmul (a, b) {
  let i, t, x
  const m = [
    0x0000001FF0000000n,
    0x000000000FF80000n,
    0x000000000007E000n
  ]
  a = BigInt(a)
  b = BigInt(b)
  x = (b << 6n) * (a & 64n)
  a ^= a << 7n
  x ^= (b * (a & 0x04001n))
  x ^= (b * (a & 0x08002n)) << 1n
  x ^= (b * (a & 0x10004n)) << 2n
  x ^= (b * (a & 0x20008n)) << 3n
  x ^= (b * (a & 0x40010n)) << 4n
  x ^= (b * (a & 0x80020n)) << 5n
  for (i = 0; i < 3; i++) {
    t = x & m[i]
    x ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  }
  return uint16_t(Number(x & bgfmask))
}

function gf_sq2mul (a, b) {
  let i, t, x
  const m = [
    0x1FF0000000000000n,
    0x000FF80000000000n,
    0x000007FC00000000n,
    0x00000003FE000000n,
    0x0000000001FE0000n,
    0x000000000001E000n
  ]
  a = BigInt(a)
  b = BigInt(b)
  x = (b << 18n) * (a & BigInt(1 << 6))
  a ^= a << 21n
  x ^= (b * (a & 0x010000001n))
  x ^= (b * (a & 0x020000002n)) << 3n
  x ^= (b * (a & 0x040000004n)) << 6n
  x ^= (b * (a & 0x080000008n)) << 9n
  x ^= (b * (a & 0x100000010n)) << 12n
  x ^= (b * (a & 0x200000020n)) << 15n
  for (i = 0; i < 6; i++) {
    t = x & m[i]
    x ^= (t >> 9n) ^ (t >> 10n) ^ (t >> 12n) ^ (t >> 13n)
  }
  return uint16_t(Number(x & bgfmask))
}

function gf_frac (a, b) {
  let c, d
  d = gf_sqmul(a, a)
  d = gf_sq2mul(d, d)
  c = gf_sq2(d)
  c = gf_sq2mul(c, d)
  c = gf_sq2(c)
  c = gf_sq2mul(c, d)
  return gf_sqmul(c, b)
}

function gf_inv (a) {
  return gf_frac(a, 1)
}

function mul_gf (a, b, c) {
  let i, j
  const d = uint16(sys_t * 2 - 1)
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

function memcpy (a, b, c, p=0, q=0) {
  const l = a.length
  c = c + q
  if (p < l && q < b.length) {
    if (c < l - p) {
      a.set(b.slice(q, c), p)
    } else {
      a.set(b.slice(q, q + l - p), p)
    }
  }
}

function int32_minmax (a, b) {
  const ab = int32_t(b ^ a)
  let c = int32_t(b - a)
  c ^= ab & (c ^ b)
  return (c >> 31) & ab
}

function int32_sort (a, b, o=0) {
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
        h = i + o
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
          h = i + o
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

function int32_min (a, b) {
  a = int32_t(a)
  b = int32_t(b)
  const c = int32_t(a ^ b)
  let d = int32_t(b - a)
  d = int32_t(d ^ int32_t(c & int32_t(d ^ b)))
  d = int32_t(d >> 31)
  d = int32_t(d & c)
  return int32_t(a ^ d)
}

function cbrecursion (a, p, q, s, r, w, n, b) {
  let i, j, k, l, v, x, y
  const n2 = n / 2, n4 = n / 4, qi = n + n4
  const xs = {}
  if (w == 1) {
    a[p + (q >> 3)] ^= r[0] << (q & 7)
    return
  }
  for (x = 0; x < n; ++x) {
    b[x] = ((r[x] ^ 1) << a16) | r[x ^ 1]
  }
  int32_sort(b, n)
  let ax, px, cx
  for (x = 0; x < n; ++x) {
    xs[x] = x + n
    px = b[x] & 65535
    cx = int32_min(px, x)
    b[xs[x]] = (px << a16) | cx
  }
  for (x = 0; x < n; ++x) {
    b[x] = (b[x] << a16) | x
  }
  int32_sort(b, n)
  for (x = 0; x < n; ++x) {
    b[x] = (b[x] << a16) + (b[xs[x]] >> a16)
  }
  int32_sort(b, n)
  if (w <= 10) {
    for (x = 0; x < n; ++x) {
      v = xs[x]
      b[v] = ((b[x] & 65535) << 10) | (b[v] & 1023)
    }
    let ppcpx, ppcx
    for (i = 1, l = w - 1; i < l; ++i) {
      for (x = 0; x < n; ++x) {
        b[x] = ((b[xs[x]] & ~1023) << 6) | x
      }
      int32_sort(b, n)
      for (x = 0; x < n; ++x) {
        b[x] = (b[x] << 20) | b[xs[x]]
      }
      int32_sort(b, n)
      for (x = 0; x < n; ++x) {
        v = xs[x]
        ax = b[x]
        ppcpx = ax & 1048575
        ppcx = (ax & 1047552) | (b[v] & 1023)
        b[v] = int32_min(ppcx, ppcpx)
      }
    }
    for (x = 0; x < n; ++x) {
      b[xs[x]] &= 1023
    }
  } else {
    for (x = 0; x < n; ++x) {
      v = xs[x]
      b[v] = (b[x] << a16) | (b[v] & 65535)
    }
    for (i = 1, l = w - 1; i < l; ++i) {
      for (x = 0; x < n; ++x) {
        b[x] = (b[xs[x]] & ~65535) | x
      }
      int32_sort(b, n)
      for (x = 0; x < n; ++x) {
        b[x] = (b[x] << a16) | (b[xs[x]] & 65535)
      }
      if (i < w - 2) {
        for (x = 0; x < n; ++x) {
          v = xs[x]
          b[v] = (b[x] & ~65535) | (b[v] >> a16)
        }
        int32_sort(b, n, n)
        for (x = 0; x < n; ++x) {
          v = xs[x]
          b[v] = (b[v] << a16) | (b[x] & 65535)
        }
      }
      int32_sort(b, n)
      for (x = 0; x < n; ++x) {
        v = xs[x]
        ax = b[v]
        b[v] = int32_min(ax, (ax & ~65535) | (b[x] & 65535))
      }
    }
    for (x = 0; x < n; ++x) {
      b[xs[x]] &= 65535
    }
  }
  for (x = 0; x < n; ++x) {
    b[x] = (r[x] << a16) + x
  }
  int32_sort(b, n)
  let fj, fx
  for (j = 0; j < n2; ++j) {
    x = 2 * j
    v = xs[x]
    fj = b[v] & 1
    fx = x + fj
    a[p + (q >> 3)] ^= fj << (q & 7)
    q += s
    b[v] = (b[x] << a16) | fx
    b[v + 1] = (b[x + 1] << a16) | (fx ^ 1)
  }
  int32_sort(b, n, n)
  q += (2 * w - 3) * s * n2
  let by, lk, ly, ly1
  for (k = 0; k < n2; ++k) {
    y = 2 * k
    by = y + n
    lk = b[by] & 1
    ly = y + lk
    ly1 = ly ^ 1
    a[p + (q >> 3)] ^= lk << (q & 7)
    q += s
    b[y] = (ly << a16) | (b[by] & 65535)
    b[y + 1] = (ly1 << a16) | (b[by + 1] & 65535)
  }
  int32_sort(b, n)
  q -= (2 * w - 2) * s * n2
  r = int16(b.slice(qi).length * 2)
  for (j = 0; j < n2; ++j) {
    k = j * 2
    r[j] = (b[k] & 65535) >> 1
    r[j + n2] = (b[k + 1] & 65535) >> 1
  }
  cbrecursion(a, p, q, s * 2, r, w - 1, n2, b)
  cbrecursion(a, p, q + s, s * 2, r.slice(n2), w - 1, n2, b)
}

function layer (a, b, p, s, n) {
  let d, g, h, i, j, m, t = 1 << (s & 31), t2 = t * 2, x = 0
  for (i = 0; i < n; i += t2) {
    for (j = 0; j < t; j++) {
      h = i + j
      g = h + t
      d = a[h] ^ a[g]
      m = (b[p + (x >> 3)] >> (x & 7)) & 1
      d = int16_t(d & -m)
      a[h] ^= d
      a[g] ^= d
      x++
    }
  }
}

function memset (a, p, v, b) {
  for (let i = p, l = b + p; i < l; i++) {
    a[i] = v
  }
}

function controlbits (a, b, w, n) {
  const temp = int32(2 * n)
  const pi_test = int16(n)
  let diff, i, n4 = n >> 4, p = 0, v = (((2 * w - 1) * n / 2) + 7) / a8
  while (1) {
    memset(a, p, 0, v)
    cbrecursion(a, p, 0, 1, b, w, n, temp)
    for (i = 0; i < n; i++) {
      pi_test[i] = i
    }
    for (i = 0; i < w; i++) {
      layer(pi_test, a, p, i, n)
      p += n4
    }
    for (i = w - 2; i >= 0; i--) {
      layer(pi_test, a, p, i, n)
      p += n4
    }
    diff = 0
    for (i = 0; i < n; i++) {
      diff = int16_t(diff | (b[i] ^ pi_test[i]))
    }
    diff = int16_nonzero_mask(diff)
    if (diff == 0) {
      break
    }
  }
  return a
}

function evals (f, l) {
  let r = f[sys_t]
  for (let i = sys_t - 1; i >= 0; i--) {
    r = gf_mul(r, l)
    r = int16_t(r ^ f[i])
  }
  return r
}

function root (a, f, l) {
  for (let i = 0; i < sys_n; i++) {
    a[i] = evals(f, l[i])
  }
}

function genpoly_gen (a, f) {
  let c, i, j, k, l, m, t
  const mat = []
  for (i = 0; i < sys_t_1; i++) {
    mat.push(uint16(sys_t))
  }
  mat[0][0] = 1
  m = mat[1]
  for (i = 0; i < sys_t; i++) {
    m[i] = f[i]
  }
  mat[1] = m
  for (j = 2; j <= sys_t; j++) {
    mul_gf(mat[j], mat[j - 1], f)
  }
  for (j = 0; j < sys_t; j++) {
    m = gf_iszero(mat[j][j])
    for (c = j; c < sys_t_1; c++) {
      l = mat[c]
      for (k = j + 1; k < sys_t; k++) {
        l[j] ^= l[k] & m
      }
      mat[c] = l
    }
    m = mat[j][j]
    if (uint16_zero_mask(m)) {
      return -1
    }
    m = gf_inv(m)
    for (c = j; c < sys_t_1; c++) {
      mat[c][j] = gf_mul(mat[c][j], m)
    }
    for (c = j; c < sys_t_1; c++) {
      l = mat[c]
      m = mat[j]
      for (k = 0; k < sys_t; k++) {
        if (k != j) {
          l[k] ^= gf_mul(l[j], m[k])
        }
      }
      mat[c] = l
    }
  }
  a.set(mat[sys_t])
}

function synd (a, f, l, r) {
  let c, d, e, i, j, m
  const t = sys_t * 2
  a.set(int8(t))
  for (i = 0; i < sys_n; i++) {
    m = l[i]
    c = uint16_t((r[uint32_t(i / a8)] >> (i % a8)) & 1)
    e = evals(f, m)
    d = gf_inv(gf_mul(e, e))
    for (j = 0; j < t; j++) {
      a[j] ^= gf_mul(d, c)
      d = gf_mul(d, m)
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
  let t = 1
  while (t < b - t) {
    t += t
  }
  let c, d, i, j, k, p, q, r
  for (p = t; p > 0; p >>= 1) {
    for (i = 0; i < b - p; ++i) {
      if (!(i & p)) {
        j = i + p
        c = uint64_minmax(a[i], a[j])
        a[i] ^= c
        a[i + p] ^= c
      }
    }
    i = 0
    for (q = t; q > p; q >>= 1) {
      for (; i < b - q; ++i) {
        if (!(i & p)) {
          j = i + p
          d = a[j]
          for (r = q; r > p; r >>= 1) {
            k = i + r
            c = uint64_minmax(d, a[k])
            d ^= c
            a[k] ^= c
          }
          a[j] = d
        }
      }
    }
  }
}

function ctz (a) {
  let b, i, m = 0, r = 0
  for (i = 0; i < a64; i++) {
    b = Number((a >> BigInt(i)) & 1n)
    m |= b
    r += (m ^ 1) & (b ^ 1)
  }
  return r
}

function same_mask_big (a, b) {
  const c = uint64([BigInt(uint16_t(Number(a)) ^ uint16_t(Number(b)))])
  c[0] -= 1n
  c[0] >>= 63n
  c[0] = -c[0]
  return c[0]
}

function mov_columns (a, b, p=b0) {
  let c, d, i, j, k, m, s, t
  const buf = uint64(a64)
  const cts = uint64(a32)
  const one = 1n
  const r = pk_nrows - a32
  const q = r / a8
  for (i = 0; i < a32; i++) {
    j = (r + i) * sys_n_8 + q
    buf[i] = load8(a.slice(j, j + a8))
  }
  for (i = 0; i < a32; i++) {
    t = buf[i]
    for (j = i + 1; j < a32; j++) {
      t |= buf[j]
    }
    if (uint64_zero_mask(t)) {
      return -1n
    }
    cts[i] = s = BigInt(ctz(t))
    p |= one << s
    for (j = i + 1; j < a32; j++) {
      m = (buf[i] >> s) & 1n
      buf[i] ^= buf[j] & (m - 1n)
    }
    for (j = i + 1; j < a32; j++) {
      m = (buf[j] >> s) & 1n
      buf[j] ^= buf[i] & -m
    }
  }
  for (j = 0; j < a32; j++) {
    for (k = j + 1; k < a64; k++) {
      d = b[r + j] ^ b[r + k]
      d = Number(BigInt(d) & same_mask_big(k, cts[j]))
      b[r + j] ^= d
      b[r + k] ^= d
    }
  }
  for (i = 0; i < pk_nrows; i++) {
    j = i * sys_n_8 + q
    t = load8(a.slice(j, j + a8))
    for (k = 0; k < a32; k++) {
      c = BigInt(k)
      d = t >> c
      d ^= t >> cts[k]
      d &= 1n
      t ^= d << cts[k]
      t ^= d << c
    }
  }
  return p
}

function pk_gen (pk, sk, q, pe, pi, p) {
  let b, c, d, e, f, h, i, j, k, m, r
  const buf = uint64(sys_n)
  const mat = uint8(pk_nrows * sys_n_8)
  const g = uint16(sys_t_1)
  const l = uint16(sys_n)
  const n = uint16(sys_n)
  g[sys_t] = 1
  for (i = 0; i < sys_t; i++) {
    g[i] = load_gf(sk, q)
    q += 2
  }
  h = sys_n
  for (i = 0; i < h; i++) {
    buf[i] = (BigInt(pe[i]) << 31n) | BigInt(i)
  }
  uint64_sort(buf, sys_n)
  for (i = 1; i < h; i++) {
    if (uint64_equal_mask(buf[i - 1] >> 31n, buf[i] >> 31n)) {
      return -1n
    }
  }
  for (i = 0; i < h; i++) {
    pi[i] = Number(buf[i] & bgfmask)
  }
  for (i = 0; i < sys_n; i++) {
    l[i] = bitrev(pi[i])
  }
  root(n, g, l)
  for (i = 0; i < sys_n; i++) {
    n[i] = gf_inv(n[i])
  }
  for (i = 0; i < sys_t; i++) {
    d = i * gfbits
    for (j = 0; j < sys_n; j += a8) {
      f = uint32_t(j / a8)
      for (k = 0; k < gfbits; k++) {
        b = 0
        for (h = 7; h > 0; h--) {
          b = (b | ((n[j + h] >> k) & 1)) << 1
        }
        b |= (n[j] >> k) & 1
        mat[(d + k) * sys_n_8 + f] = b
      }
    }
    for (j = 0; j < sys_n; j++) {
      n[j] = gf_mul(n[j], l[j])
    }
  }
  for (i = 0, h = uint32_t((pk_nrows + 7) / a8); i < h; i++) {
    e = i * a8
    for (j = 0; j < a8; j++) {
      r = e + j
      if (r >= pk_nrows) {
        break
      }
      if (p >= b0 && r == pk_nrows - a32) {
        p = mov_columns(mat, pi, p)
        if (p < b0) {
          return -1n
        }
      }
      for (k = r + 1; k < pk_nrows; k++) {
        m = uint8_t(mat[r * sys_n_8 + i] ^ mat[k * sys_n_8 + i])
        m >>= j
        m &= 1
        m = uint8_t(-m)
        for (c = 0; c < sys_n_8; c++) {
          mat[r * sys_n_8 + c] ^= mat[k * sys_n_8 + c] & m
        }
      }
      if (uint64_zero_mask((mat[r * sys_n_8 + i] >> j) & 1)) {
        return -1n
      }
      for (k = 0; k < pk_nrows; k++) {
        if (k != r) {
          m = uint8_t(mat[k * sys_n_8 + i])
          m >>= j
          m &= 1
          m = uint8_t(-m)
          for (c = 0; c < sys_n_8; c++) {
            mat[k * sys_n_8 + c] ^= mat[r * sys_n_8 + c] & m
          }
        }
      }
    }
  }
  h = pk_nrows / a8
  for (i = 0; i < pk_nrows; i++) {
    j = i * sys_n_8
    memcpy(pk, mat.slice(j, j + sys_n_8), row_bytes, i * row_bytes, h)
  }
  return p
}

function same_mask (a, b) {
  const c = uint32([uint16_t(a) ^ uint16_t(b)])
  c[0] -= 1
  c[0] >>>= 31
  c[0] = -c[0]
  return uint8_t(c[0] & 255)
}

function gen_e (a) {
  let e, i, j, m
  const ind = uint16(sys_t)
  const val = uint8(sys_t)
  const bytes = uint8(sys_t * 2)
  while (1) {
    bytes.set(randombytes(bytes.length))
    for (i = 0; i < sys_t; i++) {
      ind[i] = load_gf(bytes, i * 2)
    }
    e = 0
    for (i = 1; i < sys_t; i++) {
      for (j = 0; j < i; j++) {
        if (uint32_equal_mask(ind[i], ind[j])) {
          e = 1
        }
      }
    }
    if (e == 0) {
      break
    }
  }
  for (j = 0; j < sys_t; j++) {
    val[j] = 1 << (ind[j] & 7)
  }
  a.set(uint8(sys_n_8))
  for (i = 0; i < sys_n_8; i++) {
    for (j = 0; j < sys_t; j++) {
      m = same_mask(i, ind[j] >> 3)
      a[i] |= val[j] & m
    }
  }
}

function syndrome (s, pk, e) {
  let b, i, j, p = 0
  let r = uint8(sys_n_8)
  s.set(uint8(synd_bytes))
  for (i = 0; i < pk_nrows; i++) {
    r = uint8(sys_n_8)
    for (j = 0; j < row_bytes; j++) {
      r[sys_n_8 - row_bytes + j] = pk[j + p]
    }
    r[uint32_t(i / a8)] |= 1 << (i % a8)
    b = 0
    for (j = 0; j < sys_n_8; j++) {
      b ^= r[j] & e[j]
    }
    b ^= b >> 4
    b ^= b >> 2
    b ^= b >> 1
    b &= 1
    s[uint32_t(i / a8)] |= (b << (i % a8))
    p += row_bytes
  }
}

function decrypts (e, sk, q, c) {
  let d, i, t, w = 0
  const r = uint8(sys_n_8)
  const g = uint16(sys_t_1)
  const l = uint16(sys_n)
  const s = uint16(sys_t * 2)
  const s_cmp = s.slice()
  const locator = g.slice()
  const images = l.slice()
  r.set(c.slice(0, synd_bytes))
  for (i = 0; i < sys_t; i++) {
    g[i] = load_gf(sk, q)
    q += 2
  }
  g[sys_t] = 1
  support_gen(l, sk, q)
  synd(s, g, l, r)
  bm(locator, s)
  root(images, locator, l)
  for (i = 0; i < sys_n; i++) {
    t = gf_iszero(images[i]) & 1
    e[uint32_t(i / a8)] |= t << (i % a8)
    w += t
  }
  synd(s_cmp, g, l, e)
  d = w ^ sys_t
  for (i = 0; i < sys_t * 2; i++) {
    d |= s[i] ^ s_cmp[i]
  }
  d -= 1
  d >>= 15
  return d ^ 1
}

function pack (a) {
  let b = 0, c = a.length, d = []
  while (b < c) {
    d.push(a[b++] ^ a[b++] << 8 ^ a[b++] << 16 ^ a[b++] << 24 >> 0)
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
  g = BigInt(g)
  h = BigInt(h)
  if (g >= h) {
    return uint8(a0)
  }
  a = pack(a)
  let i = uint32(a16).map((c, b) => a[b] | a0 + a[b + a16] | a0),
      j = uint32(a16).map((c, b) => a[b + a32])
  a = uint8(Number(h - g))

  function k (a, b, c, d, e, g=a[b], h=a[c], i=a[d], j=a[e]) {
    g = shift(g ^ h, i)
    h += i
    i = shift(i ^ j, g)
    j += g
    h = shift(h ^ i, j)
    i += j
    j = shift(j ^ g, h)
    g += h
    a[b] = g + 1
    a[c] = h + 1
    a[d] = i + 1
    a[e] = j + 1
  }

  function l () {
    let a = i.slice(), b = i.slice(), c, d = 16, e = 25

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
      if (e % a5 == a0) {
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
    let b = b0, c = a0, d = a16
    while (c < d) {
      b = b * m + BigInt(a[c++])
    }
    return b
  }

  function o (a, b) {
    let c = 15, d = a0
    while (c > d) {
      b[c--] = Number(a % m)
      a /= m
    }
    return b
  }

  let p = 64n, q = g / p
  i = o(n(i) + q, uint32(a16))
  j = o(n(j) + q, uint32(a16))
  m = g % p
  a.set(unpack(l()).slice(Number(m), Number(m + h - g)))
  for (let b = g - m + p, c; b < h; b += p) {
    i[c = 15]++
    while (i[c] == a0) {
      i[--c]++
    }
    j[c = 15]++
    while (j[c] == a0) {
      j[--c]++
    }
    a.set(unpack(l()).slice(a0, Number(h - b)), Number(b - g))
  }
  return a
}

function reduce (a, h=a1) {
  let b, c = a.length, d
  while (c > a32) {
    b = []
    while (c > a0) {
      d = c / a2
      b.push(...expand([...a.slice(a0, a32), ...a.slice(d, d + a32)], a0, a32))
      a = [...a.slice(a32, d), ...a.slice(d + a32)]
      c = a.length
    }
    a = b.slice()
    c = a.length
  }
  return expand(a, a0, h)
}

function crypto_kem_keypair () {
  const pk = uint8(public_bytes)
  const sk = uint8(secret_bytes)
  const l = sys_n_8 + sys_n * 4 + sys_t * 2 + a32
  const r = uint8(l)
  const f = uint16(sys_t)
  const ir = uint16(sys_t)
  const pe = uint32(sys_n)
  const pi = int16(sys_n)
  let i, o, p, q, t = 1
  while (1) {
    o = b0
    q = 40
    r.set(randombytes(l))
    p = l - a32 - f.length * 2
    for (i = 0; i < sys_t; i++) {
      f[i] = load_gf(r, p + i * 2)
    }
    if (genpoly_gen(ir, f)) {
      continue
    }
    for (i = 0; i < sys_t; i++) {
      store_gf(sk, ir[i], q + i * 2)
    }
    q += irr_bytes
    p -= pe.length * 4
    for (i = 0; i < sys_n; i++) {
      pe[i] = load4(r, p + i * 4)
    }
    o = pk_gen(pk, sk, q - irr_bytes, pe, pi, o)
    if (o < b0) {
      console.log('retry', t++)
      continue
    }
    console.log('tried', t)
    sk.set(controlbits(sk.slice(), pi, gfbits, sys_n).slice(0, secret_bytes - 296), 296)
    q += cond_bytes
    p -= sys_n_8
    memcpy(sk, r, sys_n_8, q, p)
    store8(sk, o, a32)
    break
  }
  const k = uint8(public_bytes + secret_bytes)
  k.set(pk)
  k.set(sk, public_bytes)
  return k
}

function crypto_kem_enc (pk) {
  const a = uint8(1 + sys_n_8 + synd_bytes)
  const c = randombytes(cipher_bytes)
  const e = uint8(sys_n_8)
  a[0] = 1
  gen_e(e)
  syndrome(c, pk, e)
  memcpy(a, e, sys_n_8, 1)
  memcpy(a, c, synd_bytes, 1 + sys_n_8)
  const k = uint8(shared_bytes + cipher_bytes)
  k.set(reduce(a, shared_bytes))
  k.set(c, shared_bytes)
  return k
}

function crypto_kem_dec (sk, c) {
  const e = uint8(sys_n_8)
  const s = sk.slice(40 + irr_bytes + cond_bytes)
  const x = uint8(1 + sys_n_8 + synd_bytes)
  const ret = decrypts(e, sk, 40, c)
  if (ret > 0) {
    return []
  }
  const m = (ret - 1) >> 8
  let j = 0
  x[j++] = m & 1
  for (let i = 0; i < sys_n_8; i++) {
    x[j++] = (~m & s[i]) | (m & e[i])
  }
  memcpy(x, c, synd_bytes, 1 + sys_n_8)
  return reduce(x, shared_bytes)
}

// priv = crypto_kem_keypair()
// pub = priv.slice(0, public_bytes)
// priv = priv.slice(public_bytes)
// key0 = crypto_kem_enc(pub)
// ciph = key0.slice(shared_bytes)
// key0 = key0.slice(0, shared_bytes)
// key1 = crypto_kem_dec(priv, ciph)
// key0.toString() == key1.toString()