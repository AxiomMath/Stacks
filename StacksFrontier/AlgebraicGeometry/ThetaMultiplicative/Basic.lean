module

public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.Multiplication
public import StacksFrontier.AlgebraicGeometry.ThetaMultiplicative.Pointwise
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twist comparison preserves the canonical product and unit

For a homomorphism `ψ : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings,
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap` is the adjoint form of the
comparison `θ` of Tag 01MY: a morphism `𝒪_{Proj 𝒜}(n) ⟶ mapHom_* (𝒪_{Proj ℬ}(n)|_{U(ψ)})`, given
pointwise by the fibre comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistFibreMap`, a ring
homomorphism between localizations. We show that it carries the canonical product
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct` and the unit section
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistUnit` of the twists on `Proj 𝒜` to those
on `Proj ℬ`, as equalities of sections.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_absoluteTwistProduct`: the
  comparison carries the canonical product of two local sections of the twists on `Proj 𝒜` to the
  canonical product of their images, over every open and in all integer degrees; restated for
  `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection` as
  `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistSection_absoluteTwistProduct`.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistPushforwardMap_absoluteTwistUnit`: the same
  for the unit section in degree zero, with
  `Stacks.AlgebraicGeometry.ThetaMultiplicative.twistSection_absoluteTwistUnit` alongside.
* `Stacks.AlgebraicGeometry.ThetaMultiplicative.absoluteTwistUnit_apply`: the value of the unit
  section at every point is `1`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.RelativeProjTwists
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ThetaMultiplicative

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The unit section, pointwise -/

omit [SetLike σ A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The fraction `1 / 1` in `LocalizedModule P A` is the unit of the localization. -/
@[ega "0 1.2.2" "i_A^S preserves 1"]
public theorem localizedModule_mk_one_one (P : Submonoid A) :
    (LocalizedModule.mk (1 : A) (1 : P) : LocalizedModule P A) = 1 := by
  show Localization.mk (1 : A) (1 : P) = 1
  exact Localization.mk_one

/-- The value of the unit section of the degree-zero twist at every point is `1`. -/
public theorem absoluteTwistUnit_apply (V : Opens (ProjectiveSpectrum.top 𝒜)) (y : V) :
    (absoluteTwistUnit 𝒜 V).1 y = 1 :=
  (degreeSection_apply 𝒜 0 ⟨1, SetLike.one_mem_graded 𝒜⟩ ⟨y.1, trivial⟩).trans
    (localizedModule_mk_one_one _)

/-! ### The comparison against the product and the unit -/

/-- The action of the adjoint comparison on sections is
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection`. -/
public theorem twistPushforwardMap_app_eq_twistSection (ψ : 𝒜 →+*ᵍ ℬ) (n : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 n).val.obj (op U)) :
    ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U)).hom' a = twistSection 𝒜 ℬ ψ n U a := rfl

/-- The comparison of Tag 01MY carries the canonical product of two local sections of the twists to
the canonical product of their images, over an arbitrary open of `Proj 𝒜` and in arbitrary integer
degrees. -/
public theorem twistPushforwardMap_absoluteTwistProduct (ψ : 𝒜 →+*ᵍ ℬ) (i j : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 i).val.obj (op U))
    (b : (twistingSheaf 𝒜 j).val.obj (op U)) :
    ((twistPushforwardMap 𝒜 ℬ ψ (i + j)).val.app (op U)).hom'
        (absoluteTwistProduct 𝒜 i j U a b) =
      absoluteTwistProduct ℬ i j ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (((twistPushforwardMap 𝒜 ℬ ψ i).val.app (op U)).hom' a)
        (((twistPushforwardMap 𝒜 ℬ ψ j).val.app (op U)).hom' b) := by
  refine Subtype.ext (funext fun z => ?_)
  refine Eq.trans (twistPushforwardMap_mul_val 𝒜 ℬ ψ i j U a b z) ?_
  exact (TwistRigidity.absoluteTwistProduct_apply ℬ i j
    ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) _ _ z).symm

/-- The comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection` on sections carries the
canonical product of two local sections of the twists to the canonical product of their images. -/
public theorem twistSection_absoluteTwistProduct (ψ : 𝒜 →+*ᵍ ℬ) (i j : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) (a : (twistingSheaf 𝒜 i).val.obj (op U))
    (b : (twistingSheaf 𝒜 j).val.obj (op U)) :
    twistSection 𝒜 ℬ ψ (i + j) U (absoluteTwistProduct 𝒜 i j U a b) =
      absoluteTwistProduct ℬ i j ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))
        (twistSection 𝒜 ℬ ψ i U a) (twistSection 𝒜 ℬ ψ j U b) :=
  twistPushforwardMap_absoluteTwistProduct 𝒜 ℬ ψ i j U a b

/-- The comparison of Tag 01MY carries the unit section of the degree-zero twist to the unit
section. -/
public theorem twistPushforwardMap_absoluteTwistUnit (ψ : 𝒜 →+*ᵍ ℬ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    ((twistPushforwardMap 𝒜 ℬ ψ 0).val.app (op U)).hom' (absoluteTwistUnit 𝒜 U) =
      absoluteTwistUnit ℬ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) := by
  refine Subtype.ext (funext fun z => ?_)
  refine Eq.trans (twistPushforwardMap_app_val 𝒜 ℬ ψ 0 (op U) _ z) ?_
  refine Eq.trans (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
    (absoluteTwistUnit_apply 𝒜 U ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) ?_
  exact (map_one (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))).trans
    (absoluteTwistUnit_apply ℬ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) z).symm

/-- The comparison `Stacks.AlgebraicGeometry.ProjTwistCompare.twistSection` on sections carries the
unit section of the degree-zero twist to the unit section. -/
public theorem twistSection_absoluteTwistUnit (ψ : 𝒜 →+*ᵍ ℬ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens) :
    twistSection 𝒜 ℬ ψ 0 U (absoluteTwistUnit 𝒜 U) =
      absoluteTwistUnit ℬ ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) :=
  twistPushforwardMap_absoluteTwistUnit 𝒜 ℬ ψ U

end Stacks.AlgebraicGeometry.ThetaMultiplicative

end
