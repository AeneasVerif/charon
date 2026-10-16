//@ no-default-options
//@ charon-args=--treat-box-as-builtin --mir=elaborated --index-to-function-calls --reconstruct-fallible-operations
pub fn shared(arr: (&mut (&mut (u64,),),)) {
    arr.0.0.0 = 0;
}

pub fn mutable(arr: (&(&(u64,),),)) {
    arr.0.0.0;
}

pub fn boxed(mut arr: (Box<(Box<(u64,)>,)>,)) {
    arr.0.0.0 = 0;
}

pub fn f(ctx: &mut [u64]) {
    let acc: (&mut [u64], &mut [u64]) = ctx.split_at_mut(0);
    acc.1[0] = 0;
}
