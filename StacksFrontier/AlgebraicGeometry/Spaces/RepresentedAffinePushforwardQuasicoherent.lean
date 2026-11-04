module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedPushforwardQuasicoherent

/-!
# The direct image along an affine morphism of represented algebraic spaces is quasi-coherent

Let `g : T' ⟶ T` be a morphism of the big fppf category over `S` whose underlying morphism of
schemes is affine.  The direct image of modules along the morphism of representable algebraic
spaces `g` represents preserves quasi-coherence.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePushforward_representedSpaceMap`: the
  direct image of modules along a morphism of representable algebraic spaces with affine
  underlying morphism of schemes preserves quasi-coherence.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T' T : BigFppfOver B S hS} (g : T' ⟶ T)

/-- The morphism of schemes that `AlgebraicGeometry.SmallEtale.schemeHom` attaches to `g` in the
associated big étale site is the morphism of schemes underlying `g`. -/
theorem schemeHom_associatedBigEtaleSite :
    _root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) g.left =
      (BigFppfOver.toScheme B S hS).map g :=
  rfl

/-- The direct image of modules along a morphism of representable algebraic spaces whose
underlying morphism of schemes is affine preserves quasi-coherence. -/
theorem isQuasicoherentOnSite_modulePushforward_representedSpaceMap
    [_root_.AlgebraicGeometry.IsAffineHom (_root_.AlgebraicGeometry.SmallEtale.schemeHom
      (associatedBigEtaleSite B) g.left)]
    (F : Modules.{u, u} B S hS (yoneda.obj T')
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T'))
    (hF : F.IsQuasicoherentOnSite) :
    ((modulePushforward B S hS (representedSpaceMap B S hS g)).obj F).IsQuasicoherentOnSite := by
  rw [isQuasicoherentOnSite_modulePushforward_representedSpaceMap_iff B S hS g F]
  exact _root_.AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_pushforward
    (associatedBigEtaleSite B) g.left _
    ((isQuasicoherentOnSite_representedSmallEtaleModule_iff B S hS T' _).1
      (SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((representedSmallEtaleModuleEquivalence B S hS T').counitIso.app F).symm hF))

end AlgebraicGeometry.Space

end
