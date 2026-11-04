module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveFlatness

/-!
# Surjectivity of the class map at the rank-one module

In the proof of the second display of [Stacks Project, Tag 0E41], the class map
`Def_X(k[ε])/≅ ⟶ Ext¹(NL_{X/k}, 𝒪_X ⊗_k k)` is surjective. A class `ξ` is the class of an
extension `P` of `f⁻¹𝒪_{Spec k}`-algebras of `𝒪_X` by `𝒪_X ⊗_k k` (Stacks 0GQ5,
`AlgebraicGeometry.Space.exists_modelExtClass_eq`); `P` is realized by a first order thickening
`X ⊂ X'` (Stacks 05ZT), `ε = 1 ⊗ 1` gives `X' ⟶ Spec k[ε]`, which is flat with closed fibre `X`
(`Deformation.Examples.isFlat_and_isPullback_spaceSurjToDual`), and the class of the resulting
deformation is the class of `P` (`Deformation.Examples.spaceTangentFiberClass_spaceSurjPoint`).

## Main results

* `Deformation.Examples.surjective_spaceTangentExtClassAt`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u

namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

/-- **The class map `Def_X(k[ε])/≅ ⟶ Ext¹(NL_{X/k}, 𝒪_X ⊗_k k)` is surjective.** -/
theorem surjective_spaceTangentExtClassAt :
    Function.Surjective (spaceTangentExtClassAt B hΛ hSpec X hX toK (FGModuleCat.of k k)) := by
  intro ξ
  obtain ⟨P, hP⟩ := exists_modelExtClass_eq B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
    (f := spaceStructureMap B hΛ hSpec X hX toK)
    (M := spaceRankOneCoefficient B hΛ hSpec X hX toK) ξ
  obtain ⟨hflat, hcart⟩ := isFlat_and_isPullback_spaceSurjToDual B hΛ hSpec X hX toK P
  refine ⟨classOf (spaceDeformationBased B hΛ hSpec X hX toK)
    (spaceDeformation_cofibered B hΛ hSpec X hX toK)
    (spaceSurjPoint B hΛ hSpec X hX toK P hflat hcart), ?_⟩
  refine (spaceTangentExtClassAt_classOf B hΛ hSpec X hX toK (FGModuleCat.of k k) _).trans ?_
  exact (spaceTangentFiberClass_spaceSurjPoint B hΛ hSpec X hX toK P hflat hcart).trans hP

end Deformation.Examples

end
