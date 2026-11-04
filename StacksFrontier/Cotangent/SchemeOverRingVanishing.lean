module

public import StacksFrontier.Cotangent.SchemeOverRingComparison
public import StacksFrontier.Cotangent.SheavesOfRings.FundamentalTriangleGeneral

/-!
# The first vertex of the triangle of a scheme over a ring vanishes

Let `Λ` be a ring and let `X` be a scheme over `Λ` with structure morphism `p : X ⟶ Spec Λ`. The
fundamental triangle of Tag 08SZ for the tower `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` is

`L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗ 𝒪_X ⟶ L_{𝒪_X/Λ̲} ⟶ L_{X/Spec Λ} ⟶ (L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗ 𝒪_X)[1]`,

and the proof of Tag 08V6 in the source consists in showing that its first vertex, the pullback
of the complex the source calls `L_q`, vanishes. This file records that vanishing: the second
arrow is the comparison of Tag 08V6, an isomorphism by
`AlgebraicGeometry.SchemeOverRing.isIso_constantComparison`, so the first vertex of the
distinguished triangle `CategoryTheory.Sheaf.exists_distTriang_towerCotangent` is zero.

## Main results

* `AlgebraicGeometry.SchemeOverRing.isZero_pullbackCotangentComplex`: the first vertex
  `L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗_{p⁻¹𝒪_{Spec Λ}} 𝒪_X` vanishes in `D(𝒪_X)`.

## References

* [Stacks Project, Tag 08V6](https://stacks.math.columbia.edu/tag/08V6)
* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

universe u t

namespace AlgebraicGeometry.SchemeOverRing

variable (Λ : Type u) [CommRing Λ] {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of Λ))

/-- **The first vertex of the fundamental triangle of `Λ̲ ⟶ p⁻¹𝒪_{Spec Λ} ⟶ 𝒪_X` vanishes.**
The complex `L_{p⁻¹𝒪_{Spec Λ}/Λ̲} ⊗_{p⁻¹𝒪_{Spec Λ}} 𝒪_X`, the pullback of the complex the source
calls `L_q` in its proof of Tag 08V6, is zero in `D(𝒪_X)`: it is the first vertex of the
distinguished triangle of Tag 08SZ, whose second arrow is the isomorphism of Tag 08V6. -/
theorem isZero_pullbackCotangentComplex
    [HasDerivedCategory.{t} (CategoryTheory.Sheaf.targetModules.{u, u, u}
      (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))] :
    IsZero ((DerivedCategory.Q (C := CategoryTheory.Sheaf.targetModules.{u, u, u}
      (Opens.grothendieckTopology ↥X) (structureSheafOfSite X))).obj
        (pullbackCotangentComplex Λ p)) := by
  obtain ⟨δ, hδ⟩ := CategoryTheory.Sheaf.exists_distTriang_towerCotangent.{u, u, u, t}
    (Opens.grothendieckTopology ↥X) (constantToPullback Λ p) (pullbackStructureMap Λ p)
  have := isIso_constantComparison.{u, t} Λ p
  exact (Triangle.isZero₁_iff_isIso₂ _ hδ).2 this

end AlgebraicGeometry.SchemeOverRing
