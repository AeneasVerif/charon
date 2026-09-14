U128_MASK = (1 << 128) - 1

def checked_add_u128(left, right):
    result = left + right
    return result & U128_MASK, result > U128_MASK

def checked_mul_u128(left, right):
    result = left * right
    return result & U128_MASK, result > U128_MASK

def init_MAX():
    _0 = (~0) & ((1 << 64) - 1)
    return _0

MAX = init_MAX()

def init_MASK():
    _1 = int(MAX)
    _0 = _1
    return _0

MASK = init_MASK()

def to_low_high(x):
    _3 = x
    _2 = _3 & MASK
    _5 = x
    _6 = int(64)
    _7 = _6 < 128
    assert _7 == True
    _4 = _5 >> 64
    _0 = [_2, _4]
    return _0

def scalar_mul(low_high, k):
    _7 = k
    _9 = 0
    _10 = _9 < 2
    assert _10 == True
    _8 = low_high[_9]
    _11 = checked_mul_u128(_7, _8)
    assert _11[1] == False
    _6 = _11[0]
    _5 = to_low_high(_6)
    x = _5[0]
    c = _5[1]
    _17 = k
    _19 = 1
    _20 = _19 < 2
    assert _20 == True
    _18 = low_high[_19]
    _21 = checked_mul_u128(_17, _18)
    assert _21[1] == False
    _16 = _21[0]
    _22 = c
    _23 = checked_add_u128(_16, _22)
    assert _23[1] == False
    _15 = _23[0]
    _14 = to_low_high(_15)
    y = _14[0]
    z = _14[1]
    _24 = x
    _25 = y
    _26 = z
    _0 = [_24, _25, _26]
    return _0

def from_low_high(x):
    _3 = 0
    _4 = _3 < 2
    assert _4 == True
    _2 = x[_3]
    _7 = 1
    _8 = _7 < 2
    assert _8 == True
    _6 = x[_7]
    _9 = int(64)
    _10 = _9 < 128
    assert _10 == True
    _5 = _6 << 64
    _0 = _2 | _5
    return _0

def wide_mul_u128(a, b):
    _4 = a
    a = to_low_high(_4)
    _6 = b
    b = to_low_high(_6)
    _8 = a
    _10 = 0
    _11 = _10 < 2
    assert _11 == True
    _9 = b[_10]
    low = scalar_mul(_8, _9)
    _13 = a
    _15 = 1
    _16 = _15 < 2
    assert _16 == True
    _14 = b[_15]
    high = scalar_mul(_13, _14)
    _18 = 0
    _19 = _18 < 3
    assert _19 == True
    r0 = low[_18]
    _25 = 1
    _26 = _25 < 3
    assert _26 == True
    _24 = low[_25]
    _28 = 0
    _29 = _28 < 3
    assert _29 == True
    _27 = high[_28]
    _30 = checked_add_u128(_24, _27)
    assert _30[1] == False
    _23 = _30[0]
    _22 = to_low_high(_23)
    r1 = _22[0]
    c = _22[1]
    _37 = 2
    _38 = _37 < 3
    assert _38 == True
    _36 = low[_37]
    _40 = 1
    _41 = _40 < 3
    assert _41 == True
    _39 = high[_40]
    _42 = checked_add_u128(_36, _39)
    assert _42[1] == False
    _35 = _42[0]
    _43 = c
    _44 = checked_add_u128(_35, _43)
    assert _44[1] == False
    _34 = _44[0]
    _33 = to_low_high(_34)
    r2 = _33[0]
    c = _33[1]
    _47 = 2
    _48 = _47 < 3
    assert _48 == True
    _46 = high[_47]
    _49 = c
    _50 = checked_add_u128(_46, _49)
    assert _50[1] == False
    r3 = _50[0]
    _53 = r0
    _54 = r1
    _52 = [_53, _54]
    _51 = from_low_high(_52)
    _57 = r2
    _58 = r3
    _56 = [_57, _58]
    _55 = from_low_high(_56)
    _0 = (_51, _55)
    return _0

def overflowing_add(self, rhs):
    _6 = self
    _7 = rhs
    _5 = checked_add_u128(_6, _7)
    a = _5[0]
    b = _5[1]
    _8 = a
    _9 = b
    _0 = (_8, _9)
    return _0

def carrying_mul_add(self, b, c, d):
    _8 = self
    _9 = b
    _7 = wide_mul_u128(_8, _9)
    low = _7[0]
    high = _7[1]
    _13 = low
    _14 = c
    _12 = overflowing_add(_13, _14)
    low = _12[0]
    carry = _12[1]
    _16 = carry
    _15 = int(_16)
    _17 = checked_add_u128(high, _15)
    assert _17[1] == False
    high = _17[0]
    _21 = low
    _22 = d
    _20 = overflowing_add(_21, _22)
    low = _20[0]
    carry = _20[1]
    _24 = carry
    _23 = int(_24)
    _25 = checked_add_u128(high, _23)
    assert _25[1] == False
    high = _25[0]
    _26 = low
    _27 = high
    _0 = (_26, _27)
    return _0

def mult_u128(a, b):
    _4 = a
    _5 = b
    _3 = carrying_mul_add(_4, _5, 0, 0)
    _0 = _3[0]
    return _0

