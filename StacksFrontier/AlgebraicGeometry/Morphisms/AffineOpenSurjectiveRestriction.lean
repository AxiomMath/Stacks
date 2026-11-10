module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic

/-!
# An affine open of the base inside a prescribed neighbourhood, surjected onto by an open

Let `f : X ⟶ S` be an open map of schemes, `V` an open of `X`, `x` a point of `V` and `A` an
open neighbourhood of `f x`. The image `f '' V` is open and contains `f x`, so `f '' V ⊓ A` is
an open neighbourhood of `f x`; since the affine opens of a scheme form a basis of its topology,
some affine open `W` of `S` satisfies `f x ∈ W ≤ f '' V ⊓ A`. Being below `f '' V` says exactly
that every point of `W` is the image of a point of `V`, which is the surjectivity below.

## Main results

* `Stacks.Morphisms.exists_affineOpen_le_surjective_on_restriction`: an affine open `W ≤ A` of
  the base containing `f x` over which `V` surjects, in the form of surjectivity of
  `(f ⁻¹ᵁ W).ι ⁻¹ᵁ V).ι ≫ (f ∣_ W)`.

## Implementation notes

The conclusion is stated for `f ∣_ W` rather than for `f` itself, so that it can be used as the
surjectivity hypothesis of a statement about the restricted morphism. The reduction to `f` is
`AlgebraicGeometry.morphismRestrict_ι`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Morphisms

/-- **An affine open of the base, inside a prescribed neighbourhood, surjected onto by an open
of the source.** For `f` an open map, a point `x` of an open `V` of the source and an open
neighbourhood `A` of `f x`, there is an affine open `W ≤ A` of the base containing `f x` such
that `V ∩ f ⁻¹ᵁ W` surjects onto `W`. -/
theorem exists_affineOpen_le_surjective_on_restriction
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : IsOpenMap f)
    (V : X.Opens) (x : X) (hx : x ∈ V) (A : S.Opens) (hA : f x ∈ A) :
    ∃ W : S.Opens, f x ∈ W ∧ W ≤ A ∧ IsAffineOpen W ∧
      Function.Surjective ((((f ⁻¹ᵁ W).ι ⁻¹ᵁ V).ι) ≫ (f ∣_ W)).base := by
  obtain ⟨_, ⟨W : S.Opens, hW, rfl⟩, hxW, hWA⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (show f x ∈ f '' (V : Set X) ∩ (A : Set S) from ⟨⟨x, hx, rfl⟩, hA⟩)
      ((hf _ V.isOpen).inter A.isOpen)
  refine ⟨W, hxW, fun s hs ↦ (hWA hs).2, hW, fun s ↦ ?_⟩
  obtain ⟨y, hy, hys⟩ := (hWA s.property).1
  have hyW : y ∈ f ⁻¹ᵁ W := by
    change f y ∈ W
    rw [hys]
    exact s.property
  refine ⟨⟨⟨y, hyW⟩, hy⟩, Subtype.ext ?_⟩
  change (f ∣_ W ≫ W.ι) ⟨y, hyW⟩ = s.val
  rwa [morphismRestrict_ι]

end Stacks.Morphisms

end
