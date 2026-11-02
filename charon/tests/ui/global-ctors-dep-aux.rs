//@ ignore
extern "C" fn dep_ctor() {}

#[used]
#[unsafe(link_section = ".init_array")]
static DEP_CTOR: extern "C" fn() = dep_ctor;
