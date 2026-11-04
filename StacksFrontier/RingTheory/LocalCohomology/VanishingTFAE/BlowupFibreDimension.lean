module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.BlowUpChartCover.Cartier
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionQuasicoherent
public import StacksFrontier.AlgebraicGeometry.LerayAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeCechAcyclic.CompositeVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.ClopenCriterion
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# The cohomological dimension of an ideal is bounded by the fibres of its blowup

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `b : X' ⟶ X = Spec A` the blowup of `I`. If
every fibre of `b` has dimension at most `d - 1`, then `cd(A, I) ≤ d`.

## Main results

* `cohomologicalDimension_le_of_blowUp_fibre_dim_lt`: if every fibre of the blowup of `I` has
  dimension `< d`, then `cd(A, I) ≤ d`.

## References

* [Stacks Project, Tag 0EHU](https://stacks.math.columbia.edu/tag/0EHU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.FibreDimension
open Stacks.AlgebraicGeometry.RelativeCechAcyclic
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

namespace Stacks.LocalCohomology

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The ideal sheaf on `Spec A` cut out by an ideal `I ⊆ A`. -/
def specIdealSheaf (A : Type u) [CommRing A] (I : Ideal A) :
    (Spec (CommRingCat.of A)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- The support of `specIdealSheaf A I` is the zero locus `V(I)` of `I` in `Spec A`. -/
theorem coe_support_specIdealSheaf (A : Type u) [CommRing A] (I : Ideal A) :
    ((specIdealSheaf A I).support : Set (Spec (CommRingCat.of A)))
      = PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [specIdealSheaf, Scheme.IdealSheafData.coe_support_ofIdealTop,
    AlgebraicGeometry.Spec_zeroLocus]
  show PrimeSpectrum.zeroLocus
    ((Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) : Ideal A) : Set A) = _
  rw [Ideal.comap_map_of_surjective' (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2 I,
    (RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1]
  simp

/-- The open complement of `V(I)` in `Spec A` is the complement of the support of
`specIdealSheaf A I`. -/
theorem complementZeroLocus_eq (A : Type u) [CommRing A] (I : Ideal A) :
    complementZeroLocus A I = (specIdealSheaf A I).support.compl := by
  apply TopologicalSpace.Opens.ext
  show (PrimeSpectrum.zeroLocus (I : Set A))ᶜ = _
  rw [← coe_support_specIdealSheaf A I]
  rfl

/-- For an ideal sheaf `J` on a scheme `X` with blowup `b : X' ⟶ X`, the open immersion of the
complement `W` of the support of `J` factors as an affine morphism `W ⟶ X'` followed by `b`. -/
theorem exists_affineHom_to_blowUp {X : Scheme.{u}} (J : X.IdealSheafData) (W : X.Opens)
    (hW : W = J.support.compl) :
    ∃ j : (W : Scheme) ⟶ blowUp J, IsAffineHom j ∧ j ≫ blowUpToBase J = W.ι := by
  subst hW
  have hiso : IsIso (blowUpToBase J ∣_ J.support.compl) :=
    isIso_blowUp_restrict_compl_support J
  have hpre : blowUpToBase J ⁻¹ᵁ J.support.compl = (exceptionalIdeal J).support.compl := by
    apply TopologicalSpace.Opens.ext
    show (blowUpToBase J).base ⁻¹' ((J.support : Set X)ᶜ)
      = ((exceptionalIdeal J).support : Set (blowUp J))ᶜ
    rw [Set.preimage_compl, Scheme.IdealSheafData.support_comap]
    rfl
  have haff : IsAffineHom (blowUpToBase J ⁻¹ᵁ J.support.compl).ι := by
    rw [hpre]
    exact Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.BlowUpChartCover.isEffectiveCartierDivisor_exceptionalIdeal J)
  refine ⟨(asIso (blowUpToBase J ∣_ J.support.compl)).inv ≫
    (blowUpToBase J ⁻¹ᵁ J.support.compl).ι, inferInstance, ?_⟩
  rw [Category.assoc, ← morphismRestrict_ι (blowUpToBase J) J.support.compl]
  exact (asIso (blowUpToBase J ∣_ J.support.compl)).inv_hom_id_assoc _

/-- Let `X` be an affine locally Noetherian scheme, `J` an ideal sheaf on `X` and `W` the
complement of its support, with `W ⟶ X` quasi-compact. If every fibre of the blowup of `J` has
dimension at most `e`, then `Hⁿ(W, 𝓕) = 0` for every quasi-coherent `𝓕` on `W` and `n ≥ e + 1`.
-/
theorem isZero_hgroup_of_blowUp_fibre_dim_le
    {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X] (J : X.IdealSheafData)
    (W : X.Opens) (hW : W = J.support.compl) (hqc : QuasiCompact W.ι) (e : ℕ)
    (hdim : ∀ y : X, topologicalKrullDim ((blowUpToBase J).fiber y) ≤ (e : WithBot ℕ∞))
    (F : (W : Scheme).Modules) (hF : F.IsQuasicoherent)
    (n : ℕ) (hn : e + 1 ≤ n) :
    IsZero (Hgroup (W : Scheme).ringCatSheaf ⊤ n F) := by
  have := hF
  have := hqc
  have : QuasiSeparated W.ι := inferInstance
  obtain ⟨j, hjaff, hjcomp⟩ := exists_affineHom_to_blowUp J W hW
  have := hjaff
  have hGqc : ((Scheme.Modules.pushforward j).obj F).IsQuasicoherent := inferInstance
  have hFvan : ∀ q : ℕ, 0 < q →
      IsZero (((Scheme.Modules.pushforward j).rightDerived q).obj F) :=
    fun q hq => Stacks.AffineHigherDirectImage.isZero_rightDerived_pushforward j F q hq
  have hbvan : ∀ p : ℕ, e + 1 ≤ p →
      IsZero (((Scheme.Modules.pushforward (blowUpToBase J)).rightDerived p).obj
        ((Scheme.Modules.pushforward j).obj F)) := by
    intro p hp
    refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
      (Scheme.Modules.pushforward (blowUpToBase J)) (rfl : ((p : ℤ)) = (p : ℤ)) _).1 ?_
    refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
    exact isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent
      (blowUpToBase J) y e (hdim y) ((Scheme.Modules.pushforward j).obj F) (p : ℤ) (by omega)
  have hvan : ∀ q : ℕ, e + 1 ≤ q →
      IsZero (((Scheme.Modules.pushforward W.ι).rightDerivedPlus (q : ℤ)).obj F) := by
    intro q hq
    have hc := isZero_rightDerived_pushforward_comp_of_isZero
      j (blowUpToBase J) F (e + 1) hFvan hbvan q hq
    rw [hjcomp] at hc
    exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
      (Scheme.Modules.pushforward W.ι) (rfl : ((q : ℤ)) = (q : ℤ)) _).2 hc
  exact Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus
    W.ι (e + 1) F hvan n (by omega) hn

/-- If every fibre of the blowup of an ideal sheaf `J` on `X` is empty, then the support of `J` is
all of `X`. -/
theorem support_eq_univ_of_blowUp_fibre_isEmpty {X : Scheme.{u}} (J : X.IdealSheafData)
    (hdim : ∀ y : X, topologicalKrullDim ((blowUpToBase J).fiber y) < (0 : WithBot ℕ∞)) :
    (J.support : Set X) = Set.univ := by
  obtain ⟨j, -, hjcomp⟩ := exists_affineHom_to_blowUp J J.support.compl rfl
  refine Set.eq_univ_of_forall fun x => ?_
  by_contra hx
  have hxW : x ∈ (J.support.compl : X.Opens) := hx
  have hrangeEq : Set.range (⇑(Scheme.Opens.ι J.support.compl))
      = ((J.support.compl : X.Opens) : Set X) :=
    Scheme.Opens.range_ι (J.support.compl : X.Opens)
  have hsub : Set.range (⇑(Scheme.Opens.ι J.support.compl))
      ⊆ Set.range (⇑(blowUpToBase J)) := by
    rw [← hjcomp]
    rintro y ⟨t, ht⟩
    exact ⟨j t, by rw [← ht, Scheme.Hom.comp_apply]⟩
  obtain ⟨y, hy⟩ : x ∈ Set.range (⇑(blowUpToBase J)) := hsub (hrangeEq ▸ hxW)
  obtain ⟨z⟩ : Nonempty ((blowUpToBase J).fiber x) := ⟨hy ▸ (blowUpToBase J).asFiber y⟩
  have hnonneg : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ((blowUpToBase J).fiber x) := by
    rw [topologicalKrullDim, Order.krullDim_nonneg_iff]
    exact ⟨⟨closure ({z} : Set _), isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact absurd (hdim x) (not_lt_of_ge hnonneg)

/-- Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `b : X' ⟶ X = Spec A` the blowup of `I`.
If every fibre of `b` has dimension `< d`, that is at most `d - 1`, then the cohomological
dimension `cd(A, I)` is at most `d`.

Set `U = Spec A \ V(I)`. The canonical open immersion `j : U ⟶ X'` is affine, because the
exceptional divisor is an effective Cartier divisor, so `Rᵖ j_* 𝓕 = 0` for `p > 0` and every
quasi-coherent `𝓕` on `U`; and `Rᵠ b_* (j_* 𝓕) = 0` for `q ≥ d` by [Stacks, Tag 0E7D] part (1),
which over the locally Noetherian base `Spec A` is
`FibreDimension.isZero_stalk_rightDerivedPlus_of_fiber_dimension_le_of_isQuasicoherent`.
The Leray spectral sequence then gives `Rⁿ (b ∘ j)_* 𝓕 = 0` for `n ≥ d`, hence
`Hⁿ(U, 𝓕) = 0` for `n ≥ d`, which is `cd(A, I) ≤ d` by definition. -/
@[stacks 0EHU "cd(A, I) ≤ d from fibres of the blowup of dimension ≤ d - 1"]
theorem cohomologicalDimension_le_of_blowUp_fibre_dim_lt
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) (d : ℕ)
    (hdim : ∀ y : Spec (CommRingCat.of A),
      topologicalKrullDim ((blowUpToBase (specIdealSheaf A I)).fiber y) < (d : WithBot ℕ∞)) :
    cohomologicalDimension A I I.fg_of_isNoetherianRing ≤ (d : ℤ) := by
  have hI : I.FG := I.fg_of_isNoetherianRing
  refine cohomologicalDimension_le A I hI (d : ℤ) ⟨by omega, ?_⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · intro i hi
    refine (isClopen_zeroLocus_iff_isZero_localCohomologyModule I hI).2 ?_ i
      (by exact_mod_cast hi)
    have h := support_eq_univ_of_blowUp_fibre_isEmpty (specIdealSheaf A I)
      (by simpa using hdim)
    rw [coe_support_specIdealSheaf] at h
    rw [h]
    exact isClopen_univ
  · intro i hi
    refine isZero_localCohomologyModule_of_isZero_hgroup I hI (d : ℤ)
      (by exact_mod_cast hd) ?_ i hi
    intro F hF n hn
    have hX : IsLocallyNoetherian (Spec (CommRingCat.of A)) :=
      isLocallyNoetherian_Spec.mpr inferInstance
    have hqc : QuasiCompact (complementZeroLocus A I).ι :=
      quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp
        (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg hI))
    have hcast : ((d : ℕ) : WithBot ℕ∞) = ((d - 1 : ℕ) : WithBot ℕ∞) + 1 := by
      rw [show d = (d - 1) + 1 from by omega]
      push_cast
      ring
    refine isZero_hgroup_of_blowUp_fibre_dim_le (specIdealSheaf A I) (complementZeroLocus A I)
      (complementZeroLocus_eq A I) hqc (d - 1) (fun y => ?_) F hF n (by omega)
    exact ENat.WithBot.lt_add_one_iff.mp (hcast ▸ hdim y)

end Stacks.LocalCohomology

end
