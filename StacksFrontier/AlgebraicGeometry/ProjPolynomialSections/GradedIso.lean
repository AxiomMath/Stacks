module

public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Chart

/-!
# `Proj` of a graded ring isomorphism

`AlgebraicGeometry.Proj.map` turns a graded ring homomorphism `ψ : 𝒜 →+*ᵍ ℬ` satisfying Mathlib's
inclusion `ℬ₊ ≤ 𝒜₊.map ψ` into a morphism `Proj ℬ ⟶ Proj 𝒜`, and
`Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` is the same morphism built by glueing. This
file records the two facts about an *invertible* `ψ` that neither of those files states: that the
inclusion of irrelevant ideals is automatic, and that the induced morphism is an isomorphism.

The two gradings are allowed to be valued in **different** `SetLike` carriers, which is the point
of the file. `Stacks.AlgebraicGeometry.RelativeProj.GradedAlgebra` grades its section rings by
`AddSubgroup`, while `Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading` grades a polynomial ring
by `Submodule`; the two `Proj`s are therefore distinct terms of distinct instance paths, and the
only comparison between them is through a graded ring homomorphism.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.projIsoOfGradedSections`: the isomorphism
  `Proj ℬ ≅ Proj 𝒜` attached to a pair of mutually inverse graded ring homomorphisms.

## Main results

* `Stacks.AlgebraicGeometry.ProjPolynomialSections.irrelevant_le_map_of_graded_section`:
  **Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` is free for a graded ring homomorphism
  with a graded section.** A homogeneous element of the target of positive degree is the image of
  its preimage, which is homogeneous of the same degree because the section is graded.
* `Stacks.AlgebraicGeometry.ProjPolynomialSections.mapHomOfTop_congr`: two equal graded ring
  homomorphisms induce the same morphism, without having to transport the proof that the domain
  of definition is everything.

## Implementation notes

The isomorphism's two components are `Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop` rather
than `AlgebraicGeometry.Proj.map`, so that
`Stacks.AlgebraicGeometry.ProjBundleSurjection.mapHomOfTop_comp` applies to a composite in which
one factor comes from this file and another from elsewhere. The two round-trip identities are
proved by passing to `AlgebraicGeometry.Proj.map`, where the composition law is
`AlgebraicGeometry.Proj.map_comp`.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits HomogeneousIdeal
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjShared

namespace Stacks.AlgebraicGeometry.ProjPolynomialSections

universe u

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **Mathlib's hypothesis for `AlgebraicGeometry.Proj.map` is free for a graded ring
homomorphism with a graded section.** A homogeneous element `b` of `ℬ` of positive degree equals
`ψ (χ b)`, and `χ b` is homogeneous of the same positive degree. -/
public theorem irrelevant_le_map_of_graded_section (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (h : ∀ b, ψ (χ b) = b) :
    irrelevant ℬ ≤ (irrelevant 𝒜).map ψ := by
  refine irrelevant_le_map_of_mem_span 𝒜 ℬ ψ fun d hd b hb => ?_
  have hmem : ψ (χ b) ∈ Ideal.span (ψ '' ⋃ m > 0, (𝒜 m : Set A)) :=
    Ideal.subset_span ⟨χ b, Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd, χ.map_mem hb⟩⟩, rfl⟩
  rwa [h b] at hmem

/-- Equal graded ring homomorphisms induce the same morphism of projective spectra. The two
proofs that the domain of definition is everything need no transporting, being proofs of the same
proposition. -/
public theorem mapHomOfTop_congr {φ₁ φ₂ : 𝒜 →+*ᵍ ℬ} (h : φ₁ = φ₂)
    (h₁ : mapDomain 𝒜 ℬ φ₁ = ⊤) (h₂ : mapDomain 𝒜 ℬ φ₂ = ⊤) :
    mapHomOfTop 𝒜 ℬ φ₁ h₁ = mapHomOfTop 𝒜 ℬ φ₂ h₂ := by
  subst h; rfl

/-- The morphism of projective spectra induced by a graded ring homomorphism with a graded
section, which is defined on all of `Proj ℬ`. -/
public def mapHomOfSection (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜) (h : ∀ b, ψ (χ b) = b) :
    AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj 𝒜 :=
  mapHomOfTop 𝒜 ℬ ψ (mapDomain_eq_top_of_irrelevant_le_map 𝒜 ℬ ψ
    (irrelevant_le_map_of_graded_section 𝒜 ℬ ψ χ h))

/-- **`Proj` of a graded ring isomorphism.** A pair of mutually inverse graded ring homomorphisms
induces an isomorphism of the projective spectra; the two gradings may be valued in different
`SetLike` carriers. -/
public def projIsoOfGradedSections (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a) :
    AlgebraicGeometry.Proj ℬ ≅ AlgebraicGeometry.Proj 𝒜 where
  hom := mapHomOfSection 𝒜 ℬ ψ χ hψχ
  inv := mapHomOfSection ℬ 𝒜 χ ψ hχψ
  hom_inv_id := by
    have hid : ψ.comp χ = GradedRingHom.id ℬ := GradedRingHom.ext fun b => hψχ b
    rw [mapHomOfSection, mapHomOfSection,
      mapHomOfTop_eq_map 𝒜 ℬ ψ (irrelevant_le_map_of_graded_section 𝒜 ℬ ψ χ hψχ),
      mapHomOfTop_eq_map ℬ 𝒜 χ (irrelevant_le_map_of_graded_section ℬ 𝒜 χ ψ hχψ),
      ← Proj.map_comp]
    simp only [hid, Proj.map_id]
  inv_hom_id := by
    have hid : χ.comp ψ = GradedRingHom.id 𝒜 := GradedRingHom.ext fun a => hχψ a
    rw [mapHomOfSection, mapHomOfSection,
      mapHomOfTop_eq_map 𝒜 ℬ ψ (irrelevant_le_map_of_graded_section 𝒜 ℬ ψ χ hψχ),
      mapHomOfTop_eq_map ℬ 𝒜 χ (irrelevant_le_map_of_graded_section ℬ 𝒜 χ ψ hχψ),
      ← Proj.map_comp]
    simp only [hid, Proj.map_id]

/-- The forward component of `projIsoOfGradedSections` is the morphism `mapHomOfSection` induced
by `ψ`. -/
@[simp] public theorem projIsoOfGradedSections_hom (ψ : 𝒜 →+*ᵍ ℬ) (χ : ℬ →+*ᵍ 𝒜)
    (hψχ : ∀ b, ψ (χ b) = b) (hχψ : ∀ a, χ (ψ a) = a) :
    (projIsoOfGradedSections 𝒜 ℬ ψ χ hψχ hχψ).hom = mapHomOfSection 𝒜 ℬ ψ χ hψχ :=
  rfl

end Stacks.AlgebraicGeometry.ProjPolynomialSections

end
