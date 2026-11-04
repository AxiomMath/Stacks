module

public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackUnionPointsWithin
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenImageSubstack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackFiniteSubcover
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackUnion
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsWithinOpenSubstack

/-!
# Open substacks as loci of their points, and the finite subcover of Stacks 05UR

**Stacks 06FJ** says that `𝒰 ↦ |𝒰|` is an inclusion-preserving bijection from the open substacks
of an algebraic stack `𝒳` to the open subsets of `|𝒳|`; it is
`AlgebraicGeometry.Stack.OpenSubstack.bijective_opens_and_opens_le_iff`, with the reflection of
inclusions `AlgebraicGeometry.Stack.OpenSubstack.property_le_of_pointSet_subset`. This file reads
that reflection as the statement that an open substack is the locus
`AlgebraicGeometry.Stack.pointsWithin` of its own point set, and states **Stacks 05UR** in the form
quantified over the open substacks containing the finite subfamily.

## Main results

* `AlgebraicGeometry.Stack.OpenSubstack.pointsWithin_pointSet_le` and
  `AlgebraicGeometry.Stack.OpenSubstack.pointsWithin_pointSet_ge`: an open substack is exactly
  the locus of its own point set.
* `AlgebraicGeometry.Stack.exists_finset_le_of_isQuasiCompactStack_unconditional`:
  **Stacks 05UR**, with the union of the finite subfamily read through the open substacks
  containing each of its members.

## References

* [Stacks Project, Tag 05UR](https://stacks.math.columbia.edu/tag/05UR)
* [Stacks Project, Tag 06FJ](https://stacks.math.columbia.edu/tag/06FJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An open substack is the locus of its own point set.** An object of `𝒳` all of whose
field-valued points lie in an open substack `V` is an object of `V`. -/
theorem OpenSubstack.pointsWithin_pointSet_le {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : OpenSubstack 𝒳) :
    pointsWithin 𝒳 (V.pointSet B S hS) ≤ V.property := by
  intro x hx
  have h : (OpenSubstack.ofIsOpen B S hS (V.pointSet B S hS)
      (OpenSubstack.isOpen_pointSet B S hS V)).property x := fun q ⟨φ⟩ => hx q φ
  rwa [OpenSubstack.ofIsOpen_pointSet] at h

/-- **An open substack is contained in the locus of its own point set.** Every field-valued point
of `𝒳` admitting a morphism to an object of an open substack `V` represents a point of `|V|`. -/
theorem OpenSubstack.pointsWithin_pointSet_ge {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (V : OpenSubstack 𝒳) :
    V.property ≤ pointsWithin 𝒳 (V.pointSet B S hS) := by
  have := V.strictlyFull
  intro x hx q φ
  exact V.pointClass_mem_pointSet B S hS q
    (prop_of_isHomLift B S hS V.isAlgebraic (𝒳.val.val.p.map φ) φ (IsHomLift.map _ _) hx)

/-- Let `𝒳'` be a quasi-compact open substack of an algebraic stack `𝒳` and let `𝒳ᵢ`, `i ∈ I`, be
open substacks of `𝒳` covering `𝒳'`. Then there is a finite `I' ⊆ I` such that `𝒳'` is contained
in every open substack containing `𝒳ᵢ` for all `i ∈ I'`, that is, `𝒳' ⊆ ⋃_{i ∈ I'} 𝒳ᵢ`. -/
@[stacks 05UR]
theorem exists_finset_le_of_isQuasiCompactStack_unconditional {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (𝒳' : OpenSubstack 𝒳)
    (hqc : IsQuasiCompactStack.{u, w} B S hS
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).val
      (fullSubcategoryAlgebraicStack 𝒳 𝒳'.property 𝒳'.isAlgebraic).property)
    {I : Type*} (𝒰 : I → OpenSubstack 𝒳)
    (hcover : IsOpenSubstackCoverOn B S hS 𝒳 𝒳' 𝒰) :
    ∃ J : Finset I, ∀ W : OpenSubstack 𝒳,
      (∀ i ∈ J, (𝒰 i).property ≤ W.property) → 𝒳'.property ≤ W.property := by
  obtain ⟨J, hJ⟩ :=
    exists_finset_pointSet_subset_of_isQuasiCompactStack B S hS 𝒳' hqc 𝒰 hcover
  exact ⟨J, fun W hW => OpenSubstack.property_le_of_pointSet_subset B S hS
    (hJ.trans (Set.iUnion₂_subset fun i hi => OpenSubstack.pointSet_mono B S hS (hW i hi)))⟩

end AlgebraicGeometry.Stack

end
