module

public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.CompactOpenSuperset

/-!
# Irreducible components of a blowup

The blowup of a scheme `X` along a closed subscheme `Z` has one irreducible component for each
irreducible component of `X` whose generic point lies outside `Z`, and the blowup morphism is a
bijection between the two sets of generic points.

## Main results

* `AlgebraicGeometry.notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor`: an
  effective Cartier divisor contains no generic point of an irreducible component.
* `AlgebraicGeometry.bijOn_genericPoints_blowUpToBase`: the blowup morphism is a bijection from
  the generic points of the blowup onto the generic points of the base outside the centre.
* `AlgebraicGeometry.finite_irreducibleComponents_of_isCompact_blowUp`: if every quasi-compact
  open of `X` has finitely many irreducible components, so does every quasi-compact open of the
  blowup.

## References

* [Stacks Project, Tag 0BFM](https://stacks.math.columbia.edu/tag/0BFM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An open immersion sends generic points of irreducible components to generic points. -/
private theorem apply_mem_genericPoints {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] {x : X}
    (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y :=
  genericPoints_image_of_generalizingMap f.base f.isOpenEmbedding.generalizingMap hx

/-- A point whose image under an open immersion is a generic point is a generic point. -/
private theorem mem_genericPoints_of_apply_mem {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {x : X} (hx : f x ∈ genericPoints Y) : x ∈ genericPoints X :=
  _root_.mem_genericPoints_of_mem_genericPoints_image f.base f.continuous
    f.isOpenEmbedding.injective hx

/-- An effective Cartier divisor contains no generic point of an irreducible component of the
ambient scheme. -/
theorem notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor {X : Scheme.{u}}
    (I : X.IdealSheafData) (hI : Stacks.Divisors.IsEffectiveCartierDivisor I) {x : X}
    (hx : x ∈ genericPoints X) : x ∉ I.supportSet := by
  intro hxI
  obtain ⟨U, hU, hxU, f, hf, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal I).mp hI x hxI
  set p := hU.primeIdealOf ⟨x, hxU⟩ with hp
  have hsub : (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) ⊆ p.asIdeal := by
    have hz : hU.fromSpec p ∈ X.zeroLocus (U := U) (I.ideal ⟨U, hU⟩) := by
      rw [hp, hU.fromSpec_primeIdealOf]
      exact (Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hxI
    exact (hU.fromSpec_preimage_zeroLocus (I.ideal ⟨U, hU⟩)).subset hz
  have hfp : f ∈ p.asIdeal := by
    refine hsub ?_
    rw [Stacks.Divisors.ideal_eq_quotient_of_chart I U hU _ e he]
    exact Ideal.subset_span (Set.mem_singleton f)
  have hmin : p.asIdeal ∈ minimalPrimes Γ(X, U) := by
    have hgen : p ∈ genericPoints (PrimeSpectrum Γ(X, U)) :=
      _root_.mem_genericPoints_of_mem_genericPoints_image hU.fromSpec.base
        hU.fromSpec.continuous hU.fromSpec.isOpenEmbedding.injective
        (by rw [hp, hU.fromSpec_primeIdealOf]; exact hx)
    simpa using
      (PrimeSpectrum.vanishingIdeal_mem_minimalPrimes (s := ({p} : Set _))).2 hgen
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfp hmin
    (isRegular_iff_mem_nonZeroDivisors.mp hf)

/-- The blowup morphism restricts to a bijection from the generic
points of the irreducible components of the blowup onto the generic points of those irreducible
components of the base that are not contained in the centre. -/
@[stacks 0BFM]
theorem bijOn_genericPoints_blowUpToBase {X : Scheme.{u}} (I : X.IdealSheafData) :
    Set.BijOn (blowUpToBase I) (genericPoints (blowUp I)) (genericPoints X \ I.supportSet) := by
  classical
  set b := blowUpToBase I
  let U : X.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  let V : (blowUp I).Opens := b ⁻¹ᵁ U
  have hg : IsIso (b ∣_ U) := isIso_blowUp_restrict_compl_support I
  have hyV : ∀ y ∈ genericPoints (blowUp I), y ∈ V := by
    intro y hy
    have h : y ∉ (exceptionalIdeal I).support := by
      simpa only [Scheme.IdealSheafData.mem_supportSet_iff_mem_support] using
        notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor (exceptionalIdeal I)
          (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I) hy
    rwa [exceptionalIdeal, Scheme.IdealSheafData.support_comap] at h
  have hcomp (z : V.toScheme) : U.ι ((b ∣_ U) z) = b (V.ι z) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : V.toScheme ⟶ X => k z) (morphismRestrict_ι b U)
  have hnot : ∀ y ∈ genericPoints (blowUp I), b y ∉ I.supportSet := fun y hy hb ↦
    hyV y hy (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hb)
  refine ⟨fun y hy ↦ ⟨?_, hnot y hy⟩, ?_, ?_⟩
  · have hz : (⟨y, hyV y hy⟩ : V.toScheme) ∈ genericPoints V.toScheme :=
      mem_genericPoints_of_apply_mem V.ι hy
    have h2 := apply_mem_genericPoints U.ι (apply_mem_genericPoints (b ∣_ U) hz)
    rwa [hcomp ⟨y, hyV y hy⟩] at h2
  · intro y hy z hz hyz
    have hgz : (b ∣_ U) ⟨y, hyV y hy⟩ = (b ∣_ U) ⟨z, hyV z hz⟩ := by
      apply Subtype.ext
      show U.ι ((b ∣_ U) ⟨y, hyV y hy⟩) = U.ι ((b ∣_ U) ⟨z, hyV z hz⟩)
      rwa [hcomp ⟨y, hyV y hy⟩, hcomp ⟨z, hyV z hz⟩]
    simpa using congrArg V.ι ((b ∣_ U).isOpenEmbedding.injective hgz)
  · rintro x ⟨hxgen, hxoutside⟩
    have hxU : x ∈ U := fun hxS ↦
      hxoutside (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mpr hxS)
    have hw : (⟨x, hxU⟩ : U.toScheme) ∈ genericPoints U.toScheme :=
      mem_genericPoints_of_apply_mem U.ι hxgen
    have : IsOpenImmersion (inv (b ∣_ U)) := inferInstance
    refine ⟨V.ι (inv (b ∣_ U) ⟨x, hxU⟩),
      apply_mem_genericPoints V.ι (apply_mem_genericPoints (inv (b ∣_ U)) hw), ?_⟩
    rw [← hcomp]
    exact congrArg U.ι (congrArg (fun k : U.toScheme ⟶ U.toScheme => k ⟨x, hxU⟩)
      (IsIso.inv_hom_id (b ∣_ U)))

/-- If every quasi-compact open of `X` has finitely many irreducible components, so does every
quasi-compact open of the blowup of `X` along `I`. -/
theorem finite_irreducibleComponents_of_isCompact_blowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (hX : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite) :
    ∀ V : (blowUp I).Opens, IsCompact (V : Set (blowUp I)) → (irreducibleComponents V).Finite := by
  intro V hV
  classical
  set b := blowUpToBase I
  obtain ⟨W, hKW, hWcompact⟩ := exists_opens_superset_isCompact
    (K := b '' (V : Set (blowUp I))) (hV.image b.continuous)
  have hVW : ∀ y ∈ (V : Set (blowUp I)), b y ∈ (W : Set X) := fun y hy => hKW ⟨y, hy, rfl⟩
  set g : V.toScheme → W.toScheme := fun v => ⟨b v.1, hVW v.1 v.2⟩
  have hforward : ∀ v : V.toScheme, v ∈ genericPoints V.toScheme →
      g v ∈ genericPoints W.toScheme := by
    intro v hv
    have hvb' : v.1 ∈ genericPoints (blowUp I) :=
      apply_mem_genericPoints V.ι hv
    exact mem_genericPoints_of_apply_mem W.ι ((bijOn_genericPoints_blowUpToBase I).1 hvb').1
  have hinj : Set.InjOn g (genericPoints V.toScheme) := by
    intro v₁ hv₁ v₂ hv₂ heq
    have hv₁' : v₁.1 ∈ genericPoints (blowUp I) :=
      apply_mem_genericPoints V.ι hv₁
    have hv₂' : v₂.1 ∈ genericPoints (blowUp I) :=
      apply_mem_genericPoints V.ι hv₂
    exact Subtype.ext
      ((bijOn_genericPoints_blowUpToBase I).2.1 hv₁' hv₂' (congrArg Subtype.val heq))
  have hQW : QuasiSober W.toScheme := W.ι.isOpenEmbedding.quasiSober
  have hVfin : (genericPoints V.toScheme).Finite :=
    ((genericPoints.finite (hX W hWcompact)).subset
      (Set.image_subset_iff.2 hforward)).of_finite_image hinj
  have hQV : QuasiSober V.toScheme := V.ι.isOpenEmbedding.quasiSober
  have : Finite (genericPoints V.toScheme) := hVfin
  exact Finite.of_equiv (genericPoints V.toScheme) (genericPoints.equiv (α := V.toScheme))

end AlgebraicGeometry

end
