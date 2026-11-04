module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InternalHomSiteEquivalenceAnyUniverse
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal

/-!
# Slices of an equivalence of ringed sites whose sites live in different universes

Let `X` and `Y` be ringed sites whose underlying categories may lie in *different* universes,
whose structure sheaves have sections in one universe `w`, and let `e : Y.C ≌ X.C` be an
equivalence of the underlying sites, continuous in both directions, with structure maps `φ` and
`ψ` exhibiting the two pushforwards of modules as mutually inverse equivalences.  For an object
`W` of `Y.C` the slices `Y.C/W` and `X.C/e(W)` are equivalent, and so are the categories of
modules on them (`Stacks.SheafOfModules.InternalHom.AnyUniverse.siteEquivModulesOver`).
Restricting a module along the slice and then transporting it is pushing it forward and then
restricting, on the nose (`AlgebraicGeometry.RingedSite.pushforwardOverSquareHet`), and when `ψ`
is invertible the transported unit is the unit
(`AlgebraicGeometry.RingedSite.pushforwardUnitIsoHet`).

The two ringed sites live in independent universes: for instance `X` may be the small étale
ringed site of an algebraic space, an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`, and `Y` its
equi-universe model, an `AlgebraicGeometry.RingedSite.{u, u, u}`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe u v u' v' w m

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.InternalHom.AnyUniverse

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

/-- The localized structure map is invertible when the structure map is. -/
instance isIso_siteEquivPsiOverHet_hom [IsIso ψ] (W : Y.C) :
    IsIso (siteEquivPsiOver eqv ψ W) := by
  rw [← ObjectProperty.isIso_hom_iff]
  have : IsIso ψ.hom := by rwa [ObjectProperty.isIso_hom_iff]
  exact inferInstanceAs (IsIso (Functor.whiskerLeft (Over.forget (eqv.functor.obj W)).op ψ.hom))

/-- **The localization square of the pushforward along an equivalence of ringed sites**, for
ringed sites in independent universes: restricting `ψ_* A` to `e(W)` is transporting `A|_W`
along the equivalence of slices.  Both sides are equal on the nose. -/
def pushforwardOverSquareHet (W : Y.C) :
    _root_.SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) W ⋙
        (siteEquivModulesOver.{u, v, w, w, u', v'} eqv φ ψ H₁ H₂ W).inverse ≅
      _root_.SheafOfModules.pushforward.{w} ψ ⋙
        _root_.SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (eqv.functor.obj W) :=
  Iso.refl _

/-- The transported unit of a slice is the unit, when the structure map `ψ` is invertible. -/
def pushforwardUnitIsoHet [IsIso ψ] (W : Y.C) :
    (siteEquivModulesOver.{u, v, w, w, u', v'} eqv φ ψ H₁ H₂ W).inverse.obj
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over W)) ≅
      _root_.SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (eqv.functor.obj W)) :=
  haveI := Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit (siteEquivPsiOver eqv ψ W)
  (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit
    (F := (Over.postEquiv W eqv).inverse) (siteEquivPsiOver eqv ψ W))).symm

end AlgebraicGeometry.RingedSite

end
