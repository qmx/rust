// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::trans::abi::Abi;
use rustc::trans::glue;
use rustc::traits;
use hir::def_id::DefId;
use ty::{self, Ty, TypeFoldable, Substs, TyCtxt};
use util::ppaux;

use std::fmt;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Instance<'tcx> {
    pub def: InstanceDef<'tcx>,
    pub substs: &'tcx Substs<'tcx>,
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum InstanceDef<'tcx> {
    Item(DefId),
    Intrinsic(DefId),

    /// <fn() as FnTrait>::call_*
    /// def-id is FnTrait::call_*
    FnPtrShim(DefId, Ty<'tcx>),

    /// <Trait as Trait>::fn
    Virtual(DefId, usize),

    /// <[mut closure] as FnOnce>::call_once
    ClosureOnceShim { call_once: DefId },

    /// drop_in_place::<T>; None for empty drop glue.
    DropGlue(DefId, Option<Ty<'tcx>>),

    /// Builtin method implementation, e.g. `Clone::clone`.
    CloneShim(DefId, Ty<'tcx>),
}

impl<'tcx> InstanceDef<'tcx> {
    #[inline]
    pub fn def_id(&self) -> DefId {
        match *self {
            InstanceDef::Item(def_id) |
            InstanceDef::FnPtrShim(def_id, _) |
            InstanceDef::Virtual(def_id, _) |
            InstanceDef::Intrinsic(def_id, ) |
            InstanceDef::ClosureOnceShim { call_once: def_id } |
            InstanceDef::DropGlue(def_id, _) |
            InstanceDef::CloneShim(def_id, _) => def_id
        }
    }

    #[inline]
    pub fn def_ty<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Ty<'tcx> {
        tcx.type_of(self.def_id())
    }

    #[inline]
    pub fn attrs<'a>(&self, tcx: TyCtxt<'a, 'tcx, 'tcx>) -> ty::Attributes<'tcx> {
        tcx.get_attrs(self.def_id())
    }
}

impl<'tcx> fmt::Display for Instance<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        ppaux::parameterized(f, self.substs, self.def_id(), &[])?;
        match self.def {
            InstanceDef::Item(_) => Ok(()),
            InstanceDef::Intrinsic(_) => {
                write!(f, " - intrinsic")
            }
            InstanceDef::Virtual(_, num) => {
                write!(f, " - shim(#{})", num)
            }
            InstanceDef::FnPtrShim(_, ty) => {
                write!(f, " - shim({:?})", ty)
            }
            InstanceDef::ClosureOnceShim { .. } => {
                write!(f, " - shim")
            }
            InstanceDef::DropGlue(_, ty) => {
                write!(f, " - shim({:?})", ty)
            }
            InstanceDef::CloneShim(_, ty) => {
                write!(f, " - shim({:?})", ty)
            }
        }
    }
}

impl<'a, 'b, 'tcx> Instance<'tcx> {
    pub fn new(def_id: DefId, substs: &'tcx Substs<'tcx>)
               -> Instance<'tcx> {
        assert!(substs.is_normalized_for_trans() && !substs.has_escaping_regions(),
                "substs of instance {:?} not normalized for trans: {:?}",
                def_id, substs);
        Instance { def: InstanceDef::Item(def_id), substs: substs }
    }

    pub fn mono(tcx: TyCtxt<'a, 'tcx, 'b>, def_id: DefId) -> Instance<'tcx> {
        Instance::new(def_id, tcx.global_tcx().empty_substs_for_def_id(def_id))
    }

    #[inline]
    pub fn def_id(&self) -> DefId {
        self.def.def_id()
    }

    /// The point where linking happens. Resolve a (def_id, substs)
    /// pair to an instance.
    pub fn resolve(&self, tcx: &TyCtxt<'a, 'tcx, 'b>) -> Instance<'tcx> {
        debug!("resolve(def_id={:?}, substs={:?})",
        self.def_id(), self.substs);
        let result = if let Some(trait_def_id) = tcx.trait_of_item(self.def_id()) {
            debug!(" => associated item, attempting to find impl");
            let item = tcx.associated_item(self.def_id());
            resolve_associated_item(tcx, &item, trait_def_id, self.substs)
        } else {
            let item_type = def_ty(tcx, self.def_id(), self.substs);
            let def = match item_type.sty {
                ty::TyFnDef(..) if {
                    let f = item_type.fn_sig(tcx);
                    f.abi() == Abi::RustIntrinsic ||
                        f.abi() == Abi::PlatformIntrinsic
                } =>
                {
                    debug!(" => intrinsic");
                    ty::InstanceDef::Intrinsic(self.def_id())
                }
                _ => {
                    if Some(def_id) == tcx.lang_items().drop_in_place_fn() {
                        let ty = self.substs.type_at(0);
                        if glue::needs_drop_glue(tcx, ty) {
                            debug!(" => nontrivial drop glue");
                            ty::InstanceDef::DropGlue(self.def_id(), Some(ty))
                        } else {
                            debug!(" => trivial drop glue");
                            ty::InstanceDef::DropGlue(self.def_id(), None)
                        }
                    } else {
                        debug!(" => free item");
                        ty::InstanceDef::Item(self.def_id())
                    }
                }
            };
            Instance::new(def, self.substs)
        };
        debug!("resolve(def_id={:?}, substs={:?}) = {}",
        self.def_id(), self.substs, result);
        result
    }


}


pub fn resolve_closure<'a, 'tcx, 'b> (
    tcx: &TyCtxt<'a, 'tcx, 'b>,
    def_id: DefId,
    substs: ty::ClosureSubsts<'tcx>,
    requested_kind: ty::ClosureKind)
    -> Instance<'tcx>
{
    let actual_kind = tcx.closure_kind(def_id);

    match needs_fn_once_adapter_shim(actual_kind, requested_kind) {
        Ok(true) => fn_once_adapter_instance(tcx, def_id, substs),
        _ => Instance::new(def_id, substs.substs)
    }
}

fn resolve_associated_item<'a, 'tcx, 'b>(
    tcx: &TyCtxt<'a, 'tcx, 'b>,
    trait_item: &ty::AssociatedItem,
    trait_id: DefId,
    rcvr_substs: &'tcx Substs<'tcx>
    ) -> Instance<'tcx> {
    let def_id = trait_item.def_id;
    debug!("resolve_associated_item(trait_item={:?}, \
                                    trait_id={:?}, \
           rcvr_substs={:?})",
           def_id, trait_id, rcvr_substs);

    let trait_ref = ty::TraitRef::from_method(tcx, trait_id, rcvr_substs);
    let vtbl = tcx.trans_fulfill_obligation(DUMMY_SP, ty::Binder(trait_ref));

    // Now that we know which impl is being used, we can dispatch to
    // the actual function:
    match vtbl {
        traits::VtableImpl(impl_data) => {
            let (def_id, substs) = traits::find_associated_item(
                tcx, trait_item, rcvr_substs, &impl_data);
            let substs = tcx.erase_regions(&substs);
            ty::Instance::new(def_id, substs)
        }
        traits::VtableGenerator(closure_data) => {
            Instance {
                def: ty::InstanceDef::Item(closure_data.closure_def_id),
                substs: closure_data.substs.substs
            }
        }
        traits::VtableClosure(closure_data) => {
            let trait_closure_kind = tcx.lang_items().fn_trait_kind(trait_id).unwrap();
            resolve_closure(tcx, closure_data.closure_def_id, closure_data.substs,
                            trait_closure_kind)
        }
        traits::VtableFnPointer(ref data) => {
            Instance {
                def: ty::InstanceDef::FnPtrShim(trait_item.def_id, data.fn_ty),
                substs: rcvr_substs
            }
        }
        traits::VtableObject(ref data) => {
            let index = tcx.get_vtable_index_of_object_method(data, def_id);
            Instance {
                def: ty::InstanceDef::Virtual(def_id, index),
                substs: rcvr_substs
            }
        }
        traits::VtableBuiltin(..) if Some(trait_id) == tcx.lang_items().clone_trait() => {
            Instance {
                def: ty::InstanceDef::CloneShim(def_id, trait_ref.self_ty()),
                substs: rcvr_substs
            }
        }
        _ => {
            bug!("static call to invalid vtable: {:?}", vtbl)
        }
    }
}

/// Given a DefId and some Substs, produces the monomorphic item type.
pub fn def_ty<'a, 'tcx>(shared: &SharedCrateContext<'a, 'tcx>,
                        def_id: DefId,
                        substs: &'tcx Substs<'tcx>)
                        -> Ty<'tcx>
{
    let ty = shared.tcx().type_of(def_id);
    shared.tcx().trans_apply_param_substs(substs, &ty)
}

