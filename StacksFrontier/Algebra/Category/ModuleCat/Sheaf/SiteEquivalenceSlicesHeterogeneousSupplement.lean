module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalenceAnyUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceSlicesHeterogeneous

/-!
# Slices of an equivalence of ringed sites whose sites live in different universes

Let `X` and `Y` be ringed sites whose underlying categories may lie in *different* universes,
whose structure sheaves have sections in one universe `w`, and let `e : Y.C ≌ X.C` be an
equivalence of the underlying sites, continuous in both directions, with structure maps `φ` and
`ψ` exhibiting the two pushforwards of modules as mutually inverse equivalences.  For an object
`W` of `Y.C` the slices `Y.C/W` and `X.C/e(W)` are equivalent, and so are the categories of
modules on them.

All names are in the namespace `Stacks.SheafOfModules.InternalHom`.

## Main definitions

* `siteEquivPsiOverHet`: the structure map `ψ` localized at `W`.
* `siteEquivModulesOverHet`: the equivalence between the categories of sheaves of modules on the
  slices `X.C/e(W)` and `Y.C/W`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v u' v' w m

namespace Stacks.SheafOfModules.InternalHom

/-- The structure map `ψ` of the equivalence, localized at `W`: the whiskering of `ψ` along the
slice projection, for `X` a `RingedSite.{u, v, w}` and `Y` a `RingedSite.{u', v', w}`. -/
def siteEquivPsiOverHet {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}}
    (eqv : Y.C ≌ X.C) [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
    (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
      (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (W : Y.C) :
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ⟶
      (((Over.postEquiv (X := W) eqv).inverse).sheafPushforwardContinuous RingCat.{w}
        (X.J.over (eqv.functor.obj W)) (Y.J.over W)).obj
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  ⟨Functor.whiskerLeft (Over.forget (eqv.functor.obj W)).op ψ.hom⟩

variable {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))

variable
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

/-- **Sheaves of modules on the slice `X.C/e(W)` and on the slice `Y.C/W` agree**, along the
equivalence of slices `Y.C/W ≌ X.C/e(W)` induced by `e`, for ringed sites in independent
universes. -/
def siteEquivModulesOverHet (W : Y.C) :
    _root_.SheafOfModules.{m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) ≌
      _root_.SheafOfModules.{m} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W) :=
  _root_.SheafOfModules.pushforwardPushforwardEquivalence (Over.postEquiv (X := W) eqv)
    (Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivPhiOver eqv φ W)
    (siteEquivPsiOverHet eqv ψ W)
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left)) H₁)
    (by
      ext T : 2
      exact congrArg (fun t => NatTrans.app t (op T.unop.left)) H₂)

end Stacks.SheafOfModules.InternalHom

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.InternalHom

variable {X : RingedSite.{u, v, w}} {Y : RingedSite.{u', v', w}} (eqv : Y.C ≌ X.C)
  [eqv.functor.IsContinuous Y.J X.J] [eqv.inverse.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (ψ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (eqv.inverse.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit)
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj =
    ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
  (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
    Functor.whiskerRight (NatTrans.op eqv.unit) (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj =
      𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)

end AlgebraicGeometry.RingedSite

end
