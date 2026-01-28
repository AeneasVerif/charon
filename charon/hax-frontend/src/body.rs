pub use module::*;

mod module {
    pub use crate::prelude::*;
    pub use rustc_hir::{
        def_id::{DefId as RDefId, LocalDefId as RLocalDefId},
        hir_id::OwnerId as ROwnerId,
    };
    use rustc_middle::ty;

    pub trait IsBody: Sized + std::fmt::Debug + Clone + 'static {
        fn body<'tcx, S: UnderOwnerState<'tcx>>(
            s: &S,
            did: RDefId,
            instantiate: Option<ty::GenericArgsRef<'tcx>>,
        ) -> Option<Self>;

        /// Reuse a MIR body we already got. Panic if that's impossible.
        fn from_mir<'tcx, S: UnderOwnerState<'tcx>>(
            _s: &S,
            _body: rustc_middle::mir::Body<'tcx>,
        ) -> Option<Self> {
            None
        }
    }

    mod implementations {
        use super::*;
        impl IsBody for () {
            fn body<'tcx, S: UnderOwnerState<'tcx>>(
                _s: &S,
                _did: RDefId,
                _instantiate: Option<ty::GenericArgsRef<'tcx>>,
            ) -> Option<Self> {
                Some(())
            }
            fn from_mir<'tcx, S: UnderOwnerState<'tcx>>(
                _s: &S,
                _body: rustc_middle::mir::Body<'tcx>,
            ) -> Option<Self> {
                Some(())
            }
        }

        impl<A: IsBody, B: IsBody> IsBody for (A, B) {
            fn body<'tcx, S: UnderOwnerState<'tcx>>(
                s: &S,
                did: RDefId,
                instantiate: Option<ty::GenericArgsRef<'tcx>>,
            ) -> Option<Self> {
                Some((A::body(s, did, instantiate)?, B::body(s, did, instantiate)?))
            }
        }

        impl<MirKind: IsMirKind + Clone + 'static> IsBody for MirBody<MirKind> {
            fn body<'tcx, S: UnderOwnerState<'tcx>>(
                s: &S,
                did: RDefId,
                instantiate: Option<ty::GenericArgsRef<'tcx>>,
            ) -> Option<Self> {
                let tcx = s.base().tcx;
                let typing_env = s.typing_env();
                MirKind::get_mir(tcx, did, |body| {
                    let body = substitute(tcx, typing_env, instantiate, body.clone());
                    let body = Rc::new(body);
                    body.sinto(&s.with_mir(body.clone()))
                })
            }
            fn from_mir<'tcx, S: UnderOwnerState<'tcx>>(
                s: &S,
                body: rustc_middle::mir::Body<'tcx>,
            ) -> Option<Self> {
                let body = Rc::new(body.clone());
                let s = &s.with_mir(body.clone());
                Some(body.sinto(s))
            }
        }
    }
}
