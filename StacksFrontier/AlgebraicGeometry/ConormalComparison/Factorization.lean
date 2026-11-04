module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The coborder neighbourhood is the largest one on which an immersion is closed

An immersion of schemes `i : Z ⟶ X` factors canonically as a closed immersion
`i.liftCoborder : Z ⟶ i.coborderRange` followed by the open immersion `i.coborderRange.ι`. For
every open `U` of `X` through which `i` factors as a closed immersion, `U ≤ i.coborderRange`,
and the factorizing morphism composed with the open immersion `X.homOfLE` is `i.liftCoborder`.
Thus `i.coborderRange` is the greatest open through which `i` factors as a closed immersion.

## Main results

* `Stacks.Conormal.subset_coborder_of_closure_inter_subset`: if `closure s ∩ u ⊆ s`, then
  `u ⊆ coborder s`.
* `Stacks.Conormal.le_coborderRange_of_comp_eq`: an open `U` through which `i` factors as a
  closed immersion satisfies `U ≤ i.coborderRange`.
* `Stacks.Conormal.comp_homOfLE_eq_liftCoborder`: the factorizing morphism followed by
  `X.homOfLE` is `i.liftCoborder`.
* `Stacks.Conormal.isGreatest_coborderRange`: `i.coborderRange` is the greatest open through
  which `i` factors as a closed immersion.

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

/-- If the closure of `s` meets `u` only inside `s`, then `u` is contained in the coborder of
`s`. -/
theorem subset_coborder_of_closure_inter_subset {X : Type*} [TopologicalSpace X]
    {s u : Set X} (h : closure s ∩ u ⊆ s) : u ⊆ coborder s := by
  rw [coborder_eq_union_closure_compl]
  exact fun x hx ↦ (em (x ∈ closure s)).imp (fun hc ↦ h ⟨hc, hx⟩) id

/-- If an immersion `i : Z ⟶ X` factors as a closed immersion `i' : Z ⟶ U.toScheme` followed
by the inclusion of an open `U`, then `U` is contained in `i.coborderRange`. -/
theorem le_coborderRange_of_comp_eq {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) :
    U ≤ i.coborderRange := by
  have hrange : Set.range i = U.ι.base '' Set.range i'.base := by
    rw [← hfac]; simp [Scheme.Hom.comp_base, Set.range_comp]
  refine subset_coborder_of_closure_inter_subset ?_
  rw [hrange]
  rintro x ⟨hxc, hxu⟩
  obtain ⟨a, rfl⟩ : x ∈ Set.range U.ι.base := by
    rwa [show Set.range U.ι.base = (U : Set X) from U.range_ι]
  have ha : a ∈ U.ι.base ⁻¹' closure (U.ι.base '' Set.range i'.base) := hxc
  rw [← U.ι.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
    i'.isClosedEmbedding.isClosed_range.closure_eq] at ha
  exact ⟨a, ha, rfl⟩

/-- The morphism factorizing an immersion through an open subscheme, followed by the induced
open immersion into the coborder neighbourhood, is the canonical lift `i.liftCoborder`. -/
theorem comp_homOfLE_eq_liftCoborder {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (i' : Z ⟶ U.toScheme) [IsClosedImmersion i'] (hfac : i' ≫ U.ι = i) :
    i' ≫ X.homOfLE (le_coborderRange_of_comp_eq i U i' hfac) = i.liftCoborder :=
  (cancel_mono i.coborderRange.ι).mp <| by
    rw [Category.assoc, Scheme.homOfLE_ι, hfac, i.liftCoborder_ι]

/-- `i.coborderRange` is the greatest open of `X` through which the immersion `i` factors as a
closed immersion. -/
theorem isGreatest_coborderRange {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] :
    IsGreatest {U : X.Opens | ∃ i' : Z ⟶ U.toScheme, IsClosedImmersion i' ∧ i' ≫ U.ι = i}
      i.coborderRange :=
  ⟨⟨i.liftCoborder, inferInstance, i.liftCoborder_ι⟩,
    fun V ⟨i', _, hfac⟩ ↦ le_coborderRange_of_comp_eq i V i' hfac⟩

end Stacks.Conormal

end
