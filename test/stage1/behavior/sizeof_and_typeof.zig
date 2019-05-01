const builtin = @import("builtin");
const expect = @import("std").testing.expect;

test "@sizeOf and @typeOf" {
    const y: @typeOf(x) = 120;
    expect(@sizeOf(@typeOf(y)) == 2);
}
const x: u16 = 13;
const z: @typeOf(x) = 19;

const A = struct {
    a: u8,
    b: u32,
    c: u8,
    d: u3,
    e: u5,
    f: u16,
    g: u16,
};

const P = packed struct {
    a: u8,
    b: u32,
    c: u8,
    d: u3,
    e: u5,
    f: u16,
    g: u16,
};

test "@byteOffsetOf" {
    // Packed structs have fixed memory layout
    expect(@byteOffsetOf(P, "a") == 0);
    expect(@byteOffsetOf(P, "b") == 1);
    expect(@byteOffsetOf(P, "c") == 5);
    expect(@byteOffsetOf(P, "d") == 6);
    expect(@byteOffsetOf(P, "e") == 6);
    expect(@byteOffsetOf(P, "f") == 7);
    expect(@byteOffsetOf(P, "g") == 9);

    // Normal struct fields can be moved/padded
    var a: A = undefined;
    expect(@ptrToInt(&a.a) - @ptrToInt(&a) == @byteOffsetOf(A, "a"));
    expect(@ptrToInt(&a.b) - @ptrToInt(&a) == @byteOffsetOf(A, "b"));
    expect(@ptrToInt(&a.c) - @ptrToInt(&a) == @byteOffsetOf(A, "c"));
    expect(@ptrToInt(&a.d) - @ptrToInt(&a) == @byteOffsetOf(A, "d"));
    expect(@ptrToInt(&a.e) - @ptrToInt(&a) == @byteOffsetOf(A, "e"));
    expect(@ptrToInt(&a.f) - @ptrToInt(&a) == @byteOffsetOf(A, "f"));
    expect(@ptrToInt(&a.g) - @ptrToInt(&a) == @byteOffsetOf(A, "g"));
}

test "@bitOffsetOf" {
    // Packed structs have fixed memory layout
    expect(@bitOffsetOf(P, "a") == 0);
    expect(@bitOffsetOf(P, "b") == 8);
    expect(@bitOffsetOf(P, "c") == 40);
    expect(@bitOffsetOf(P, "d") == 48);
    expect(@bitOffsetOf(P, "e") == 51);
    expect(@bitOffsetOf(P, "f") == 56);
    expect(@bitOffsetOf(P, "g") == 72);

    expect(@byteOffsetOf(A, "a") * 8 == @bitOffsetOf(A, "a"));
    expect(@byteOffsetOf(A, "b") * 8 == @bitOffsetOf(A, "b"));
    expect(@byteOffsetOf(A, "c") * 8 == @bitOffsetOf(A, "c"));
    expect(@byteOffsetOf(A, "d") * 8 == @bitOffsetOf(A, "d"));
    expect(@byteOffsetOf(A, "e") * 8 == @bitOffsetOf(A, "e"));
    expect(@byteOffsetOf(A, "f") * 8 == @bitOffsetOf(A, "f"));
    expect(@byteOffsetOf(A, "g") * 8 == @bitOffsetOf(A, "g"));
}

test "@sizeOf on compile-time types" {
    expect(@sizeOf(comptime_int) == 0);
    expect(@sizeOf(comptime_float) == 0);
    expect(@sizeOf(@typeOf(.hi)) == 0);
    expect(@sizeOf(@typeOf(type)) == 0);
}
