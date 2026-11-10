module

public import Mathlib.AlgebraicGeometry.FunctionField
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Reduced
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Integrality of a blowup

The blowup of an integral scheme in a nonzero quasi-coherent ideal is integral. Reducedness is
Stacks tag 0808; irreducibility is read off the standard affine charts
`Spec Γ(X, U)[I(U)/a]` attached to *nonzero* sections `a` of `I(U)`: those charts have an
integral coordinate ring, they cover the blowup because the chart at a zero section is empty,
and they pairwise meet because each of them contains a point lying over the generic point of
`X`.

## Main results

* `AlgebraicGeometry.isIntegral_blowUp`: **Stacks Tag 02ND.**

## Implementation notes

Over the complement of the centre the blowup morphism is an isomorphism
(`AlgebraicGeometry.isIso_blowUp_restrict_compl_support`), so the inverse image of that
complement is irreducible in the blowup; the generic point of each nonzero chart maps to the
generic point of `X`, so every nonzero chart meets that irreducible open, and therefore any two
of them meet.

## References

* [Stacks Project, Tag 02ND](https://stacks.math.columbia.edu/tag/02ND)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- An affine open carrying a nonzero section of `I` is nonempty. -/
theorem nonempty_of_ne_zero_ideal_section (U : X.affineOpens) (a : I.ideal U)
    (ha : (a : X.presheaf.obj (.op U.1)) ≠ 0) : Nonempty U.1 := by
  by_contra hU
  have hbot : U.1 = ⊥ := (Opens.not_nonempty_iff_eq_bot U.1).mp (by simpa using hU)
  have : Subsingleton (X.presheaf.obj (.op U.1)) := by rw [hbot]; infer_instance
  exact ha (congrArg Subtype.val (Subsingleton.elim a 0))

/-- Every point of the blowup lies on a standard affine chart attached to a nonzero section of
the centre: the chart at a zero section is empty. -/
theorem exists_ne_zero_mem_range_blowUpAffineChart (x : blowUp I) :
    ∃ (U : X.affineOpens) (a : I.ideal U), (a : X.presheaf.obj (.op U.1)) ≠ 0 ∧
      x ∈ Set.range (blowUpAffineChart I U a) := by
  obtain ⟨U, a, hmem⟩ := exists_mem_range_blowUpAffineChart I x
  obtain ⟨z, hz⟩ := hmem
  refine ⟨U, a, fun hzero ↦ ?_, z, hz⟩
  exact (isEmpty_spec_blowUpAffineChartRing_of_eq_zero I U a hzero).elim z

variable [IsIntegral X]

/-- On an affine open carrying a nonzero section of `I`, the affine blowup algebra is a domain:
the section is a nonzerodivisor, so the localization at it is a domain, and the blowup algebra
is a subring of that localization. -/
theorem isDomain_blowUpAffineChartRing (U : X.affineOpens) (a : I.ideal U)
    (ha : (a : X.presheaf.obj (.op U.1)) ≠ 0) :
    IsDomain (blowUpAffineChartRing I U a) := by
  have : Nonempty U.1 := nonempty_of_ne_zero_ideal_section I U a ha
  have : IsDomain (X.presheaf.obj (.op U.1)) := IsIntegral.component_integral U.1
  have : IsDomain (Localization.Away (a : X.presheaf.obj (.op U.1))) :=
    Localization.Away.isDomain ha
  infer_instance

/-- A standard affine chart at a nonzero section of the centre is integral. -/
theorem isIntegral_spec_blowUpAffineChartRing (U : X.affineOpens) (a : I.ideal U)
    (ha : (a : X.presheaf.obj (.op U.1)) ≠ 0) :
    IsIntegral (Spec (.of (blowUpAffineChartRing I U a))) :=
  have := nonempty_of_ne_zero_ideal_section I U a ha
  have := isDomain_blowUpAffineChartRing I U a ha
  (affine_isIntegral_iff (.of (blowUpAffineChartRing I U a))).2 inferInstance

/-- The generic point of a standard affine chart at a nonzero section of the centre maps to the
generic point of `X`: the canonical map `Γ(X, U) → Γ(X, U)[I(U)/a]` is injective, so it pulls
the zero ideal back to the zero ideal. -/
theorem blowUpToBase_genericPoint_blowUpAffineChart (U : X.affineOpens) (a : I.ideal U)
    (ha : (a : X.presheaf.obj (.op U.1)) ≠ 0) :
    haveI := isIntegral_spec_blowUpAffineChartRing I U a ha
    blowUpToBase I (blowUpAffineChart I U a
      (genericPoint (Spec (.of (blowUpAffineChartRing I U a))))) = genericPoint X := by
  have := isIntegral_spec_blowUpAffineChartRing I U a ha
  have : Nonempty U.1 := nonempty_of_ne_zero_ideal_section I U a ha
  have hR : IsDomain (X.presheaf.obj (.op U.1)) := IsIntegral.component_integral U.1
  have hB : IsDomain (blowUpAffineChartRing I U a) := isDomain_blowUpAffineChartRing I U a ha
  have hmap : Function.Injective
      (algebraMap (X.presheaf.obj (.op U.1)) (blowUpAffineChartRing I U a)) := fun p q hpq ↦
    IsLocalization.injective (Localization.Away (a : X.presheaf.obj (.op U.1)))
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero ha)) (congrArg Subtype.val hpq)
  have hspec : Spec.map (CommRingCat.ofHom
      (algebraMap (X.presheaf.obj (.op U.1)) (blowUpAffineChartRing I U a)))
      (genericPoint (Spec (.of (blowUpAffineChartRing I U a)))) =
      genericPoint (Spec (.of (X.presheaf.obj (.op U.1)))) := by
    change PrimeSpectrum.comap _ _ = _
    rw [genericPoint_eq_bot_of_affine (CommRingCat.of (blowUpAffineChartRing I U a)),
      genericPoint_eq_bot_of_affine (CommRingCat.of (X.presheaf.obj (.op U.1)))]
    refine PrimeSpectrum.ext (Ideal.ext fun p ↦ ?_)
    change (algebraMap (X.presheaf.obj (.op U.1)) (blowUpAffineChartRing I U a) p = 0) ↔ p = 0
    exact ⟨fun hp ↦ hmap (hp.trans (map_zero _).symm), fun hp ↦ hp ▸ map_zero _⟩
  have hcomp := congrArg (fun f ↦ f (genericPoint
    (Spec (.of (blowUpAffineChartRing I U a))))) (blowUpAffineChart_comp_blowUpToBase I U a)
  simp only [Scheme.Hom.comp_apply] at hcomp
  rw [hcomp, hspec]
  exact genericPoint_eq_of_isOpenImmersion (U.2.isoSpec.inv ≫ U.1.ι)

/-- The generic point of `X` lies outside the centre, as soon as the centre is nonzero. -/
theorem genericPoint_notMem_supportSet (hI : I ≠ ⊥) : genericPoint X ∉ I.supportSet := by
  intro hη
  refine hI (Scheme.IdealSheafData.support_eq_top_iff.mp (TopologicalSpace.Closeds.ext ?_))
  refine Set.eq_univ_of_univ_subset ?_
  rw [← genericPoint_closure X]
  exact closure_minimal (Set.singleton_subset_iff.mpr hη) I.support.isClosed

/-- The range of a morphism from a preirreducible scheme is preirreducible. -/
private theorem isPreirreducible_range_of_preirreducibleSpace {Y Z : Scheme.{u}}
    [PreirreducibleSpace Y] (f : Y ⟶ Z) : IsPreirreducible (Set.range f) := by
  simpa only [Set.image_univ] using (PreirreducibleSpace.isPreirreducible_univ (X := Y)).image f
    (continuousOn_univ.mpr f.continuous)

/-- **Stacks Project, Tag 02ND.** The blowup of an integral scheme in a nonzero quasi-coherent
ideal is integral. -/
@[stacks 02ND, ega "II 8.1.4" "(i) integrality, blowup"]
theorem isIntegral_blowUp (hI : I ≠ ⊥) : IsIntegral (blowUp I) := by
  classical
  set U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩ with hUdef
  set V : (blowUp I).Opens := blowUpToBase I ⁻¹ᵁ U with hVdef
  have hηU : genericPoint X ∈ U := genericPoint_notMem_supportSet I hI
  have : Nonempty U.toScheme := ⟨⟨genericPoint X, hηU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hiso : IsIso (blowUpToBase I ∣_ U) := isIso_blowUp_restrict_compl_support I
  have hVint : IsIntegral V.toScheme := IsIntegral.of_isIso (asIso (blowUpToBase I ∣_ U)).inv
  have hVirr : IsPreirreducible (V : Set (blowUp I)) := by
    simpa only [Scheme.Opens.range_ι] using isPreirreducible_range_of_preirreducibleSpace V.ι
  -- Every nonempty open of the blowup meets the inverse image of the complement of the centre:
  -- it meets some chart at a nonzero section, and so does that inverse image.
  have hmeetV : ∀ O : Set (blowUp I), IsOpen O → O.Nonempty → (V ∩ O : Set (blowUp I)).Nonempty
      := by
    rintro O hO ⟨x, hxO⟩
    obtain ⟨W, a, ha, z, hz⟩ := exists_ne_zero_mem_range_blowUpAffineChart I x
    have hint := isIntegral_spec_blowUpAffineChartRing I W a ha
    have hRirr := isPreirreducible_range_of_preirreducibleSpace (blowUpAffineChart I W a)
    have hRV : (Set.range (blowUpAffineChart I W a) ∩ (V : Set (blowUp I))).Nonempty := by
      refine ⟨blowUpAffineChart I W a
        (genericPoint (Spec (.of (blowUpAffineChartRing I W a)))), ⟨_, rfl⟩, ?_⟩
      change blowUpToBase I (blowUpAffineChart I W a _) ∈ U
      rw [blowUpToBase_genericPoint_blowUpAffineChart I W a ha]
      exact hηU
    obtain ⟨w, -, hw⟩ := hRirr (V : Set (blowUp I)) O V.isOpen hO
      hRV ⟨x, ⟨z, hz⟩, hxO⟩
    exact ⟨w, hw⟩
  have hpre : PreirreducibleSpace (blowUp I) := by
    refine ⟨fun u v hu hv hu' hv' ↦ ?_⟩
    obtain ⟨x, -, hxu⟩ := hu'
    obtain ⟨y, -, hyv⟩ := hv'
    obtain ⟨w, -, hw⟩ := hVirr u v hu hv (hmeetV u hu ⟨x, hxu⟩) (hmeetV v hv ⟨y, hyv⟩)
    exact ⟨w, Set.mem_univ w, hw⟩
  have : Nonempty (blowUp I) := Nonempty.map V.ι inferInstance
  have hirr : IrreducibleSpace (blowUp I) := by
    rw [irreducibleSpace_def]
    exact ⟨Set.univ_nonempty, hpre.isPreirreducible_univ⟩
  exact (isIntegral_iff_irreducibleSpace_and_isReduced (blowUp I)).2
    ⟨hirr, isReduced_blowUp I⟩

end AlgebraicGeometry

end
