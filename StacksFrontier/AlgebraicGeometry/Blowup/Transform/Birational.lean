module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Integral
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic

/-!
# Birationality of a blowup

The blowup of an integral scheme in a nonzero quasi-coherent ideal is birational: it is an
isomorphism over the complement of the centre, and that complement contains the generic point
because the centre is a proper closed subscheme.

## Main results

* `AlgebraicGeometry.isBirational_blowUpToBase`: the blowup morphism of an integral scheme in a
  nonzero ideal is birational.
* `AlgebraicGeometry.isBirational_of_comp_blowUpToBase`: a morphism into such a blowup is
  birational as soon as its composite with the blowup morphism is.
* `AlgebraicGeometry.isEffectiveCartierDivisor_of_isIso_blowUpToBase`: an ideal whose blowup
  morphism is an isomorphism is already an effective Cartier divisor.

## Implementation notes

The bijection on generic points is [Stacks, Tag 0BFM],
`AlgebraicGeometry.bijOn_genericPoints_blowUpToBase`; on an integral scheme with a nonzero
centre its target `genericPoints X \ I.supportSet` is all of `genericPoints X`, because the
generic point avoids the support of a nonzero ideal
(`AlgebraicGeometry.genericPoint_notMem_supportSet`). The isomorphism of local rings at the
generic point is transported from the restriction of the blowup to the complement of the centre
along `AlgebraicGeometry.morphismRestrictStalkMap`.

The last result reads the universal property [Stacks, Tag 0806] backwards: the inverse image of
the centre along the blowup morphism is always an effective Cartier divisor, and when that
morphism is an isomorphism the inverse image along its inverse returns the centre itself.

## References

* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BFM](https://stacks.math.columbia.edu/tag/0BFM)
* [Stacks Project, Tag 0806](https://stacks.math.columbia.edu/tag/0806)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The open complement of the centre of a blowup. -/
private abbrev centreCompl : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩

/-- A birational morphism of integral schemes maps the generic point to the generic point. -/
private theorem apply_genericPoint_of_isBirational {A B : Scheme.{u}} [IsIntegral A]
    [IsIntegral B] {f : A ⟶ B} (hf : IsBirational f) : f (genericPoint A) = genericPoint B := by
  have := hf.bijOn.mapsTo (by rw [genericPoints_eq_singleton]; rfl :
    genericPoint A ∈ genericPoints A)
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at this

/-- A point of the blowup over the generic point lies over the complement of the centre. -/
private theorem mem_preimage_centreCompl [IsIntegral X] (hI : I ≠ ⊥) {y : blowUp I}
    (h : blowUpToBase I y = genericPoint X) : y ∈ blowUpToBase I ⁻¹ᵁ centreCompl I := by
  change blowUpToBase I y ∈ centreCompl I
  rw [h]
  exact genericPoint_notMem_supportSet I hI

/-- **The blowup of an integral scheme in a nonzero ideal is birational.** -/
theorem isBirational_blowUpToBase [IsIntegral X] (hI : I ≠ ⊥) :
    IsBirational (blowUpToBase I) := by
  have hint : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  have hiso : IsIso (blowUpToBase I ∣_ centreCompl I) := isIso_blowUp_restrict_compl_support I
  have hdiff : genericPoints X \ I.supportSet = genericPoints X := by
    refine Set.Subset.antisymm Set.sdiff_subset fun z hz => ⟨hz, ?_⟩
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hz
    exact hz ▸ genericPoint_notMem_supportSet I hI
  have hbij : Set.BijOn (blowUpToBase I) (genericPoints (blowUp I)) (genericPoints X) :=
    hdiff ▸ bijOn_genericPoints_blowUpToBase I
  refine isBirational_of_bijOn_of_isIso_stalkMap _ hbij ?_
  intro y hy
  have hyU : y ∈ blowUpToBase I ⁻¹ᵁ centreCompl I := by
    refine mem_preimage_centreCompl I hI ?_
    simpa [genericPoints_eq_singleton] using hbij.mapsTo hy
  have hstalk : IsIso ((blowUpToBase I ∣_ centreCompl I).stalkMap ⟨y, hyU⟩) :=
    ((isIso_iff_isIso_stalkMap (blowUpToBase I ∣_ centreCompl I)).mp hiso).2 ⟨y, hyU⟩
  exact ((MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap (blowUpToBase I) (centreCompl I) ⟨y, hyU⟩)).mp hstalk

/-- **A morphism into a blowup is birational as soon as its composite with the blowup morphism
is.** -/
theorem isBirational_of_comp_blowUpToBase {A : Scheme.{u}} [IsIntegral A] [IsIntegral X]
    (hI : I ≠ ⊥) (g : A ⟶ blowUp I)
    (hg : IsBirational (g ≫ blowUpToBase I)) : IsBirational g := by
  have hint : IsIntegral (blowUp I) := isIntegral_blowUp I hI
  have hb := isBirational_blowUpToBase I hI
  have hiso : IsIso (blowUpToBase I ∣_ centreCompl I) := isIso_blowUp_restrict_compl_support I
  -- Both the generic point of the blowup and the image of the generic point of `A` lie over the
  -- generic point of `X`, inside the open where the blowup morphism is an isomorphism.
  have hbη := apply_genericPoint_of_isBirational hb
  have hgηb : blowUpToBase I (g (genericPoint A)) = genericPoint X :=
    apply_genericPoint_of_isBirational hg
  have hx := mem_preimage_centreCompl I hI hgηb
  have hy := mem_preimage_centreCompl I hI hbη
  have hres : ∀ z : (blowUpToBase I ⁻¹ᵁ centreCompl I),
      ((blowUpToBase I ∣_ centreCompl I) z).1 = blowUpToBase I z.1 := fun z =>
    morphismRestrict_base_coe (blowUpToBase I) (centreCompl I) z
  have hgen : g (genericPoint A) = genericPoint (blowUp I) := by
    have hcoe : (blowUpToBase I ∣_ centreCompl I) ⟨g (genericPoint A), hx⟩ =
        (blowUpToBase I ∣_ centreCompl I) ⟨genericPoint (blowUp I), hy⟩ :=
      Subtype.ext ((hres ⟨_, hx⟩).trans ((hgηb.trans hbη.symm).trans (hres ⟨_, hy⟩).symm))
    exact congrArg Subtype.val ((asIso (blowUpToBase I ∣_ centreCompl I)).hom.injective hcoe)
  refine isBirational_of_bijOn_of_isIso_stalkMap _ ?_ ?_
  · rw [genericPoints_eq_singleton, genericPoints_eq_singleton, Set.bijOn_singleton]
    exact hgen
  · intro x hx'
    rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hx'
    subst hx'
    have hbstalk : IsIso ((blowUpToBase I).stalkMap (g (genericPoint A))) := by
      rw [hgen]
      exact hb.isIso_stalkMap _ (by rw [genericPoints_eq_singleton]; rfl)
    have hcomp : IsIso ((g ≫ blowUpToBase I).stalkMap (genericPoint A)) :=
      hg.isIso_stalkMap _ (by rw [genericPoints_eq_singleton]; rfl)
    rw [Scheme.Hom.stalkMap_comp] at hcomp
    exact (isIso_comp_left_iff ((blowUpToBase I).stalkMap (g (genericPoint A)))
      (g.stalkMap (genericPoint A))).mp hcomp

/-- **An ideal whose blowup morphism is an isomorphism is an effective Cartier divisor.** -/
theorem isEffectiveCartierDivisor_of_isIso_blowUpToBase [IsIso (blowUpToBase I)] :
    Stacks.Divisors.IsEffectiveCartierDivisor I := by
  obtain ⟨hD, -⟩ := Stacks.Blowup.isTerminal_blowUp I
  have h := Stacks.Divisors.isPullbackDefined_of_flat (inv (blowUpToBase I))
    (I.comap (blowUpToBase I)) hD
  change Stacks.Divisors.IsEffectiveCartierDivisor
    ((I.comap (blowUpToBase I)).comap (inv (blowUpToBase I))) at h
  rwa [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id,
    Scheme.IdealSheafData.comap_id] at h

end AlgebraicGeometry

end
