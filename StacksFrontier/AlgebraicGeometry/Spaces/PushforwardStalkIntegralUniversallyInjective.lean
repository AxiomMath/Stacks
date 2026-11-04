module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStalkComparison

/-!
# The stalk comparison along an integral universally injective morphism

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. This file shows that the canonical comparison
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` between the stalk of a direct
image and the stalk of the sheaf is an isomorphism for such an `f`, exactly as it is for a
closed immersion.

The reason is the same in both cases: the comparison is the stalk of the counit
`f^{-1}f_* ⟶ 𝟭` of the inverse-image/direct-image adjunction, read through Stacks 04K2
part (4), and that counit is invertible because the direct image is fully faithful. For a
closed immersion this is Stacks 04E5 part (2); for an integral universally injective morphism
it is the trailing clause of Stacks 0AEH, which is
`AlgebraicGeometry.Space.smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective`.

## References

* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 04K2](https://stacks.math.columbia.edu/tag/04K2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- **The comparison on stalks is an isomorphism along an integral universally injective
morphism.** For such a morphism `f : Y ⟶ X` of algebraic spaces over `S` and a geometric point
`ȳ` of `Y`, the canonical map `(f_*F)_{f(ȳ)} ⟶ F_ȳ` is an isomorphism.

The direct image of abelian sheaves along `f` is fully faithful, so the counit of the
adjunction is invertible, which is the trailing clause of Stacks 0AEH. -/
theorem isIso_smallEtaleAbelianPushforwardStalkMap_of_isIntegralHom_of_universallyInjective
    (f : Y ⟶ X) (hf : IsIntegralHom B S hS f.hom) (hui : UniversallyInjective B S hS f.hom)
    (y : GeometricPoint B S hS Y.1) :
    IsIso (smallEtaleAbelianPushforwardStalkMap B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf) y) := by
  have hiso := smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective.{u + 1}
    B S hS f hf hui
  have : IsIso (smallEtaleAbelianInverseImageAdjunction B S hS f
      (relativelyRepresentable_of_isIntegralHom B S hS f hf)).counit :=
    NatIso.isIso_of_isIso_app _
  unfold smallEtaleAbelianPushforwardStalkMap
  infer_instance

end AlgebraicGeometry.Space

end
