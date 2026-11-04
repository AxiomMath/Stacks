module

public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.AffineDerivedPushforwardQcoh

/-!
# A termwise quasi-coherent complex computes its derived pushforward along an affine morphism

Let `f : X ⟶ Y` be an affine morphism of schemes and let `K` be a cochain complex of
quasi-coherent `𝒪_X`-modules, in general unbounded. The comparison from the degreewise
pushforward `f_* K` to the derived direct image `Rf_* K` is then an isomorphism.

This is the case of [Stacks, Tag 0G9N] in which the termwise acyclicity hypothesis is
automatic: along an affine morphism the higher direct images of a quasi-coherent module vanish
([Stacks, Tag 01XC]), so every term of `K` is acyclic for `f_*`.

## Main results

* `AlgebraicGeometry.affineRightDerivedPushforward_unit_isIso`: for an affine morphism, the
  comparison from degreewise to derived pushforward is an isomorphism at a complex of
  quasi-coherent modules.

## Implementation notes

The derived functor is an arbitrary model `(RF, α)`, so the statement does not depend on the
construction of `Rf_*`.

The standard model of the derived category is installed at a raised priority because the
locally small model of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` is also in the
import closure, and at equal priority instance search no longer resolves
`HasDerivedCategory.{u + 1} X.Modules`.

## References

* [Stacks Project, Tag 08D7](https://stacks.math.columbia.edu/tag/08D7)
* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

/-- **The comparison from degreewise to derived pushforward along an affine morphism is an
isomorphism on complexes of quasi-coherent modules.** The higher direct images of a
quasi-coherent module along an affine morphism vanish, so every term of the complex is acyclic
for pushforward and [Stacks, Tag 0G9N] applies. -/
public theorem affineRightDerivedPushforward_unit_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (RF : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules)
    (α : (Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
    (K : CochainComplex X.Modules ℤ)
    (hK : ∀ n, (K.X n).IsQuasicoherent) :
    IsIso (α.app ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K)) :=
  isIso_to_rightDerived_of_termwise_acyclic f K hK
    (fun n => rightAcyclic_pushforward_of_isQuasicoherent f (K.X n) (hK n)) RF α

end AlgebraicGeometry

end
