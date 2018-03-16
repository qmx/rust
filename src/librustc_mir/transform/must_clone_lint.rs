use rustc::ty::{TyCtxt, TyClosure};
use rustc::hir::def_id::DefId;
use rustc::mir::*;
use rustc::mir::visit::Visitor;
use rustc::ty::maps::Providers;

pub fn provide(providers: &mut Providers) {
    *providers = Providers {
        must_clone_lint,
        ..*providers
    };
}

pub struct MustCloneChecker<'a,'tcx: 'a> {
    mir: &'a Mir<'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'gcx, 'tcx> MustCloneChecker<'a, 'tcx> {
    fn new(mir: &'a Mir<'tcx>,
           tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        Self {
            mir, tcx
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for MustCloneChecker<'a, 'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>,
                     _location: Location) {
        if let Operand::Copy(ref place) = *operand {
            let ty = place.ty(self.mir, self.tcx).to_ty(self.tcx);
            if let TyClosure(_, _) = ty.sty {
                debug!("closure copy");
            }
        }
    }
}

fn must_clone_lint<'a, 'tcx>(tcx: TyCtxt<'a,'tcx,'tcx>,
                             def_id: DefId)
-> MustCloneCheckResult {
    debug!("must clone lint invoked");
    let mir = &tcx.mir_built(def_id).borrow();
    let mut checker = MustCloneChecker::new(mir, tcx);
    checker.visit_mir(mir);

    MustCloneCheckResult{}
}
