module

public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ImpliedProperties.LocalDomain

/-!
# Regularity from a cover by open immersions

The fourth item of `AlgebraicGeometry.isRegular_tfae_cover` (Tag 02IU) says that a scheme is
regular as soon as it has an open covering by regular open subschemes. This file restates that in
the two shapes a construction usually has its covering in: a family of open immersions with
covering ranges, and a supremum of opens each of which is regular.

## Main results

* `AlgebraicGeometry.isRegular_of_isOpenImmersion_cover` — a scheme covered by the ranges of open
  immersions from regular schemes is regular.
* `AlgebraicGeometry.isRegular_iSup_opens` — a supremum of regular opens is regular.
* `AlgebraicGeometry.isRegular_opensRange` — the range of an open immersion from a regular scheme
  is a regular open.
* `AlgebraicGeometry.isRegular_of_sup_eq_top` — a scheme covered by two regular opens is
  regular.

## References

* [Stacks Project, Tag 02IU](https://stacks.math.columbia.edu/tag/02IU)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A scheme covered by the ranges of open immersions from regular schemes is regular.** -/
public theorem isRegular_of_isOpenImmersion_cover {X : Scheme.{u}} {K : Type u}
    {Z : K → Scheme.{u}} (g : ∀ k, Z k ⟶ X) [hg : ∀ k, IsOpenImmersion (g k)]
    (hcov : ⨆ k, (g k).opensRange = ⊤) (hreg : ∀ k, IsRegular (Z k)) : IsRegular X := by
  refine ((isRegular_tfae_cover X).out 4 1 rfl rfl).mp
    ⟨K, fun k ↦ (g k).opensRange, hcov, fun k ↦ ?_⟩
  exact IsRegular.of_iso (Scheme.Hom.isoOpensRange (g k)).symm (hreg k)

/-- **A supremum of regular opens is regular.** -/
public theorem isRegular_iSup_opens {X : Scheme.{u}} {K : Type u} (U : K → X.Opens)
    (hU : ∀ k, IsRegular (U k).toScheme) : IsRegular (⨆ k, U k).toScheme := by
  refine isRegular_of_isOpenImmersion_cover
    (fun k ↦ X.homOfLE (le_iSup U k)) ?_ fun k ↦ hU k
  rw [show (fun k ↦ (X.homOfLE (le_iSup U k)).opensRange) =
    fun k ↦ (⨆ j, U j).ι ⁻¹ᵁ U k from funext fun k ↦ Scheme.opensRange_homOfLE _,
    ← Scheme.Hom.preimage_iSup]
  exact (⨆ j, U j).ι_preimage_self

/-- A union of two regular opens is regular. -/
public theorem isRegular_sup_opens {X : Scheme.{u}} (U V : X.Opens)
    (hU : IsRegular U.toScheme) (hV : IsRegular V.toScheme) : IsRegular (U ⊔ V).toScheme := by
  have h : (⨆ b : ULift.{u} Bool, if b.down then U else V) = U ⊔ V := by
    refine le_antisymm (iSup_le fun b ↦ ?_) (sup_le ?_ ?_)
    · cases b.down <;> simp
    · exact le_iSup_of_le (ULift.up true) (by simp)
    · exact le_iSup_of_le (ULift.up false) (by simp)
  rw [← h]
  refine isRegular_iSup_opens _ fun b ↦ ?_
  cases b.down
  · simpa using hV
  · simpa using hU

/-- The range of an open immersion from a regular scheme is a regular open. -/
public theorem isRegular_opensRange {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (hX : IsRegular X) : IsRegular j.opensRange.toScheme :=
  IsRegular.of_iso (Scheme.Hom.isoOpensRange j).symm hX

/-- **A scheme covered by two regular opens is regular.** -/
public theorem isRegular_of_sup_eq_top {X : Scheme.{u}} (U V : X.Opens)
    (hU : IsRegular U.toScheme) (hV : IsRegular V.toScheme) (h : U ⊔ V = ⊤) : IsRegular X := by
  have htop : IsRegular (⊤ : X.Opens).toScheme := h ▸ isRegular_sup_opens U V hU hV
  exact IsRegular.of_iso (X.topIso).symm htop

end AlgebraicGeometry

end
