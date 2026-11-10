module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic

/-!
# The blowup morphism is bijective away from its centre

Let `I` be a quasi-coherent ideal sheaf on a scheme `X`. The blowup morphism `blowUpToBase I`
restricts to an isomorphism over the open complement of the closed subscheme cut out by `I`
(`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`, [Stacks, Tag 02OS]). This file records
the two consequences on points that the applications use: over the complement of the centre the
blowup morphism hits every point, and it identifies no two points.

Both are read off the restricted morphism. It is an isomorphism, hence a homeomorphism on points,
and its action on points is that of `blowUpToBase I` by
`AlgebraicGeometry.morphismRestrict_base_coe`.

## Main results

* `AlgebraicGeometry.exists_blowUpToBase_eq_of_notMem_support`: every point of `X` outside the
  support of `I` is the image of a point of the blowup.
* `AlgebraicGeometry.blowUpToBase_injective_of_notMem_support`: two points of the blowup with the
  same image outside the support of `I` are equal.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The restriction of the blowup morphism over the complement of the support of `I` is bijective,
being an isomorphism. -/
private theorem bijective_blowUpToBase_restrict_compl_support (I : X.IdealSheafData) :
    Function.Bijective
      (blowUpToBase I ∣_ (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)) := by
  have hiso := isIso_blowUp_restrict_compl_support I
  simpa only [Scheme.coe_homeoOfIso, asIso_hom] using
    (Scheme.homeoOfIso (asIso (blowUpToBase I ∣_
      (⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens)))).bijective

/-- **The blowup morphism is surjective over the complement of its centre.** A point of `X`
outside the support of `I` lies in an open over which the blowup morphism is an isomorphism,
hence a homeomorphism on points, so it is the image of a point of the blowup. -/
theorem exists_blowUpToBase_eq_of_notMem_support (I : X.IdealSheafData) {x : X}
    (hx : x ∉ (I.support : Set X)) : ∃ y : blowUp I, blowUpToBase I y = x := by
  set V : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  obtain ⟨y, hy⟩ := (bijective_blowUpToBase_restrict_compl_support I).2 ⟨x, hx⟩
  exact ⟨y.1, (morphismRestrict_base_coe (blowUpToBase I) V y).symm.trans
    (congrArg Subtype.val hy)⟩

/-- **The blowup morphism is injective over the complement of its centre.** If two points of the
blowup have the same image and that image avoids the support of `I`, then both lie over an open
on which the blowup morphism restricts to an isomorphism, hence are equal. -/
theorem blowUpToBase_injective_of_notMem_support (I : X.IdealSheafData) {y₁ y₂ : blowUp I}
    (hy : blowUpToBase I y₁ ∉ (I.support : Set X))
    (h : blowUpToBase I y₁ = blowUpToBase I y₂) : y₁ = y₂ := by
  set V : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  have hy₂ : blowUpToBase I y₂ ∈ V := by
    change blowUpToBase I y₂ ∉ (I.support : Set X)
    rwa [← h]
  have heq : (blowUpToBase I ∣_ V) ⟨y₁, hy⟩ = (blowUpToBase I ∣_ V) ⟨y₂, hy₂⟩ :=
    Subtype.ext ((morphismRestrict_base_coe (blowUpToBase I) V ⟨y₁, hy⟩).trans
      (h.trans (morphismRestrict_base_coe (blowUpToBase I) V ⟨y₂, hy₂⟩).symm))
  exact congrArg Subtype.val ((bijective_blowUpToBase_restrict_compl_support I).1 heq)

end AlgebraicGeometry

end
