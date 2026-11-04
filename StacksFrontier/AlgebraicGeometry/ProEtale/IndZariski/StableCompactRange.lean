module

public import Mathlib.RingTheory.LocalIso
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.DirectLimit
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.StratificationColimitCardinality
public import StacksFrontier.RingTheory.Spectrum.Prime.DirectLimit
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Realizing a quasi-compact generalization-stable subset as the image of an ind-Zariski map

Let `A` be a commutative ring and let `E ⊆ Spec A` be quasi-compact and stable under
generalization. This file builds an ind-Zariski `A`-algebra whose spectrum maps onto exactly `E`:
the colimit, over the finite subsets `𝔉 ⊆ A`, of the finite products of the localizations away
from `patternElement 𝔉 σ`, over the vanishing patterns `σ : 𝔉 → Bool` realized by a point of `E`.

## Main results

* `AlgebraicGeometry.ProEtale.exists_indZariski_range_comap_eq`: for `E ⊆ Spec A` quasi-compact
  and stable under generalization there is an ind-Zariski `A`-algebra `B` with
  `Set.range (Spec B → Spec A) = E`; with the size bound below, as
  `AlgebraicGeometry.ProEtale.exists_indZariski_range_comap_eq_and_mk_le`.
* `AlgebraicGeometry.ProEtale.mk_patternColimitRing_le`: the ind-Zariski algebra `B` constructed
  above has cardinality at most `max ℵ₀ #A`.

## References

* [Stacks Project, Tag 0A31](https://stacks.math.columbia.edu/tag/0A31)
* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.ProEtale

variable {A : Type u} [CommRing A]

/-! ## Maps between localizations away from one element -/

/-- If `a` divides `b`, then `a` becomes invertible in the localization away from `b`. -/
theorem isUnit_algebraMap_away_of_dvd {a b : A} (h : a ∣ b) :
    IsUnit (algebraMap A (Localization.Away b) a) := by
  obtain ⟨c, hc⟩ := h
  refine isUnit_of_mul_isUnit_left (y := algebraMap A (Localization.Away b) c) ?_
  rw [← map_mul, ← hc]
  exact IsLocalization.Away.algebraMap_isUnit b

/-- The canonical `A`-algebra map `A_a → A_b` for `a` dividing `b`. -/
def awayMapOfDvd {a b : A} (h : a ∣ b) :
    Localization.Away a →+* Localization.Away b :=
  IsLocalization.lift (M := Submonoid.powers a)
    (g := algebraMap A (Localization.Away b)) fun y ↦ by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, map_pow]
      exact (isUnit_algebraMap_away_of_dvd h).pow n

/-- The canonical map `A_a → A_b` is a map of `A`-algebras. -/
@[simp]
theorem awayMapOfDvd_comp_algebraMap {a b : A} (h : a ∣ b) :
    (awayMapOfDvd h).comp (algebraMap A (Localization.Away a)) =
      algebraMap A (Localization.Away b) :=
  IsLocalization.lift_comp _

/-- An `A`-algebra map out of a localization away from `a` is unique. -/
theorem awayMapOfDvd_unique {a b : A} (h : a ∣ b)
    (ψ : Localization.Away a →+* Localization.Away b)
    (hψ : ψ.comp (algebraMap A (Localization.Away a)) = algebraMap A (Localization.Away b)) :
    ψ = awayMapOfDvd h :=
  IsLocalization.ringHom_ext (Submonoid.powers a)
    (hψ.trans (awayMapOfDvd_comp_algebraMap h).symm)

/-- The canonical map `A_a → A_a` is the identity. -/
theorem awayMapOfDvd_self {a : A} (h : a ∣ a) :
    awayMapOfDvd h = RingHom.id (Localization.Away a) :=
  (awayMapOfDvd_unique h (RingHom.id _) (RingHom.id_comp _)).symm

/-- The canonical maps of localizations compose: `A_a → A_b → A_c` is `A_a → A_c`. -/
theorem awayMapOfDvd_comp_awayMapOfDvd {a b c : A} (h₁ : a ∣ b) (h₂ : b ∣ c) :
    (awayMapOfDvd h₂).comp (awayMapOfDvd h₁) = awayMapOfDvd (h₁.trans h₂) :=
  awayMapOfDvd_unique _ _ <| by
    rw [RingHom.comp_assoc, awayMapOfDvd_comp_algebraMap, awayMapOfDvd_comp_algebraMap]

/-! ## Vanishing patterns on a finite subset -/

/-- The product of the elements of `𝔉` that the pattern `σ` requires not to vanish. A prime
realizing `σ` lies in the basic open of this element. -/
def patternElement (𝔉 : Finset A) (σ : ↥𝔉 → Bool) : A :=
  ∏ g ∈ Finset.univ.filter fun g : ↥𝔉 ↦ σ g = false, (g : A)

/-- Restriction of a vanishing pattern to a smaller finite subset. -/
def patternRestrict {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) (σ : ↥𝔊 → Bool) : ↥𝔉 → Bool :=
  fun g ↦ σ ⟨g.1, h g.2⟩

/-- The inclusion of a finite subset into a larger one, as an embedding of the index types of
vanishing patterns. -/
def patternEmbedding {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) : ↥𝔉 ↪ ↥𝔊 :=
  ⟨fun g ↦ ⟨g.1, h g.2⟩, fun g g' hgg' ↦
    Subtype.ext (show (g : A) = (g' : A) from congrArg (fun x : ↥𝔊 ↦ (x : A)) hgg')⟩

/-- The element of a restricted pattern, as a product over the image of the index embedding. -/
theorem patternElement_eq_prod_map {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) (σ : ↥𝔊 → Bool) :
    patternElement 𝔉 (patternRestrict h σ) =
      ∏ x ∈ (Finset.univ.filter fun g : ↥𝔉 ↦ patternRestrict h σ g = false).map
        (patternEmbedding h), (x : A) :=
  (Finset.prod_map (Finset.univ.filter fun g : ↥𝔉 ↦ patternRestrict h σ g = false)
    (patternEmbedding h) fun x : ↥𝔊 ↦ (x : A)).symm

/-- The element of the restriction of a pattern to a smaller finite subset divides the element of
the pattern. -/
theorem patternElement_dvd {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) (σ : ↥𝔊 → Bool) :
    patternElement 𝔉 (patternRestrict h σ) ∣ patternElement 𝔊 σ := by
  have hsub : (Finset.univ.filter fun g : ↥𝔉 ↦ patternRestrict h σ g = false).map
      (patternEmbedding h) ⊆ Finset.univ.filter fun g : ↥𝔊 ↦ σ g = false := by
    intro x hx
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨g, hg, rfl⟩ := hx
    exact hg
  exact (dvd_of_eq (patternElement_eq_prod_map h σ)).trans
    (Finset.prod_dvd_prod_of_subset _ _ _ hsub)

/-- A prime contains the element of a pattern iff it contains one of the elements required not to
vanish. -/
private theorem patternElement_mem_iff {𝔉 : Finset A} {σ : ↥𝔉 → Bool} {p : PrimeSpectrum A} :
    patternElement 𝔉 σ ∈ p.asIdeal ↔ ∃ g : ↥𝔉, σ g = false ∧ (g : A) ∈ p.asIdeal := by
  simp [patternElement, Ideal.IsPrime.prod_mem_iff (hp := p.isPrime)]

/-! ## The directed system of stages -/

variable (E : Set (PrimeSpectrum A))

/-- The vanishing patterns on `𝔉` realized by some point of `E`. -/
abbrev GoodPattern (𝔉 : Finset A) : Type u :=
  {σ : ↥𝔉 → Bool // ∃ r ∈ E, ∀ g : ↥𝔉, (g.1 ∈ r.asIdeal ↔ σ g = true)}

/-- The restriction of a pattern realized on `E` is again realized on `E`, by the same point. -/
def goodRestrict {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) (σ : GoodPattern E 𝔊) : GoodPattern E 𝔉 :=
  ⟨patternRestrict h σ.1,
    σ.2.imp fun _ hr ↦ ⟨hr.1, fun g ↦ hr.2 (patternEmbedding h g)⟩⟩

/-- The stage of the construction at the finite subset `𝔉 ⊆ A`: the product of the localizations
away from `patternElement 𝔉 σ`, over the patterns whose stratum meets `E`. -/
abbrev patternStageRing (𝔉 : Finset A) : Type u :=
  ∀ σ : GoodPattern E 𝔉, Localization.Away (patternElement 𝔉 σ.1)

/-- The transition map of the system of stages, assembled from the canonical maps of
localizations. -/
def patternStageMap {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) : patternStageRing E 𝔉 →+* patternStageRing E 𝔊 :=
  Pi.ringHom fun σ ↦ (awayMapOfDvd (patternElement_dvd h σ.1)).comp
    (Pi.evalRingHom _ (goodRestrict E h σ))

/-- The transition maps of the system of stages, indexed by `𝔉 ≤ 𝔊`. -/
def patternStageHom (𝔉 𝔊 : Finset A) (h : 𝔉 ≤ 𝔊) : patternStageRing E 𝔉 →+* patternStageRing E 𝔊 :=
  patternStageMap E h

/-- The transition maps of the system of stages are maps of `A`-algebras. -/
theorem patternStageMap_comp_algebraMap {𝔉 𝔊 : Finset A} (h : 𝔉 ⊆ 𝔊) :
    (patternStageMap E h).comp (algebraMap A (patternStageRing E 𝔉)) =
      algebraMap A (patternStageRing E 𝔊) :=
  RingHom.ext fun a ↦ funext fun σ ↦
    DFunLike.congr_fun (awayMapOfDvd_comp_algebraMap (patternElement_dvd h σ.1)) a

/-- The transition map from a stage to itself is the identity. -/
theorem patternStageMap_id (𝔉 : Finset A) :
    patternStageMap E (le_refl 𝔉) = RingHom.id (patternStageRing E 𝔉) :=
  RingHom.ext fun x ↦ funext fun σ ↦
    DFunLike.congr_fun (awayMapOfDvd_self (patternElement_dvd (le_refl 𝔉) σ.1))
      (x (goodRestrict E (le_refl 𝔉) σ))

/-- The transition maps of the system of stages compose. -/
theorem patternStageMap_comp {𝔉 𝔊 ℌ : Finset A} (h₁ : 𝔉 ⊆ 𝔊) (h₂ : 𝔊 ⊆ ℌ) :
    (patternStageMap E h₂).comp (patternStageMap E h₁) = patternStageMap E (h₁.trans h₂) :=
  RingHom.ext fun x ↦ funext fun σ ↦
    DFunLike.congr_fun
      (awayMapOfDvd_comp_awayMapOfDvd (patternElement_dvd h₁ (patternRestrict h₂ σ.1))
        (patternElement_dvd h₂ σ.1))
      (x (goodRestrict E h₁ (goodRestrict E h₂ σ)))

/-- The stages and their transition maps form a directed system. -/
instance : DirectedSystem (patternStageRing E) fun 𝔉 𝔊 h ↦ patternStageHom E 𝔉 𝔊 h where
  map_self 𝔉 x := DFunLike.congr_fun (patternStageMap_id E 𝔉) x
  map_map _ _ _ h₁ h₂ x := DFunLike.congr_fun (patternStageMap_comp E h₁ h₂) x

/-- The colimit of the system of stages. Its spectrum maps onto `E`, and it is ind-Zariski over
`A`. -/
abbrev patternColimitRing : Type u :=
  Ring.DirectLimit (patternStageRing E) fun 𝔉 𝔊 h ↦ patternStageHom E 𝔉 𝔊 h

/-- The colimit is an `A`-algebra through the stage at `∅`. -/
instance : Algebra A (patternColimitRing E) :=
  ((Ring.DirectLimit.of (patternStageRing E) (fun 𝔉 𝔊 h ↦ patternStageHom E 𝔉 𝔊 h) ∅).comp
    (algebraMap A (patternStageRing E ∅))).toAlgebra

/-- The structure map of the colimit agrees with the composite through any stage. -/
theorem patternColimit_of_comp_algebraMap (𝔉 : Finset A) :
    (Ring.DirectLimit.of (patternStageRing E) (fun 𝔉 𝔊 h ↦ patternStageHom E 𝔉 𝔊 h) 𝔉).comp
        (algebraMap A (patternStageRing E 𝔉)) =
      algebraMap A (patternColimitRing E) := by
  have h₀ : (∅ : Finset A) ≤ 𝔉 := Finset.empty_subset 𝔉
  refine RingHom.ext fun a ↦ ?_
  have h1 : algebraMap A (patternStageRing E 𝔉) a =
      patternStageHom E ∅ 𝔉 h₀ (algebraMap A (patternStageRing E ∅) a) :=
    (DFunLike.congr_fun (patternStageMap_comp_algebraMap E h₀) a).symm
  rw [RingHom.comp_apply, h1, Ring.DirectLimit.of_f]
  rfl

/-- Each stage is ind-Zariski over `A`. -/
theorem isIndZariski_patternStageRing (𝔉 : Finset A) :
    Algebra.IsIndZariski A (patternStageRing E 𝔉) := by
  have : Algebra.IsLocalIso A (patternStageRing E 𝔉) :=
    Algebra.IsLocalIso.pi_of_finite A
      (fun σ : GoodPattern E 𝔉 ↦ Localization.Away (patternElement 𝔉 σ.1))
  exact Algebra.IsLocalIso.isIndZariski A (patternStageRing E 𝔉)

/-- The colimit is ind-Zariski over `A`. -/
theorem isIndZariski_patternColimitRing : Algebra.IsIndZariski A (patternColimitRing E) :=
  isIndZariski_directLimit (patternStageRing E) (patternStageHom E)
    (fun _ _ h ↦ patternStageMap_comp_algebraMap E h) (patternColimit_of_comp_algebraMap E)
    (isIndZariski_patternStageRing E)

/-! ## Cardinality of the colimit -/

/-- Each stage has cardinality at most `max ℵ₀ #A`. -/
theorem mk_patternStageRing_le (𝔉 : Finset A) :
    Cardinal.mk (patternStageRing E 𝔉) ≤ max ℵ₀ (Cardinal.mk A) := by
  classical
  have : Fintype (GoodPattern E 𝔉) := Fintype.ofFinite _
  rw [Cardinal.mk_pi, Cardinal.prod_eq_of_fintype]
  simpa using Cardinal.prod_le_of_le_of_aleph0_le
    (Finset.univ : Finset (GoodPattern E 𝔉))
    (fun σ : GoodPattern E 𝔉 ↦ Cardinal.mk (Localization.Away (patternElement 𝔉 σ.1)))
    (max ℵ₀ (Cardinal.mk A)) (le_max_left _ _)
    (fun σ _ ↦ Cardinal.mk_le_of_isLocalization (Submonoid.powers (patternElement 𝔉 σ.1)) _)

/-- The colimit ring has cardinality at most `max ℵ₀ #A`. -/
theorem mk_patternColimitRing_le :
    Cardinal.mk (patternColimitRing E) ≤ max ℵ₀ (Cardinal.mk A) := by
  classical
  have hsurj : Function.Surjective
      (fun x : Σ 𝔉 : Finset A, patternStageRing E 𝔉 ↦
        Ring.DirectLimit.of (patternStageRing E)
          (fun 𝔉 𝔊 h ↦ patternStageHom E 𝔉 𝔊 h) x.1 x.2) := by
    intro z
    obtain ⟨𝔉, x, hx⟩ := Ring.DirectLimit.exists_of
      (G := patternStageRing E) (f := fun 𝔉 𝔊 h ↦ patternStageHom E 𝔉 𝔊 h) z
    exact ⟨⟨𝔉, x⟩, hx⟩
  calc
    Cardinal.mk (patternColimitRing E)
        ≤ Cardinal.mk (Σ 𝔉 : Finset A, patternStageRing E 𝔉) :=
          Cardinal.mk_le_of_surjective hsurj
    _ = Cardinal.sum (fun 𝔉 : Finset A ↦ Cardinal.mk (patternStageRing E 𝔉)) :=
          Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : Finset A ↦ max ℵ₀ (Cardinal.mk A)) :=
          Cardinal.sum_le_sum _ _ (fun 𝔉 ↦ mk_patternStageRing_le E 𝔉)
    _ = Cardinal.mk (Finset A) * max ℵ₀ (Cardinal.mk A) := Cardinal.sum_const' _ _
    _ ≤ max ℵ₀ (Cardinal.mk A) * max ℵ₀ (Cardinal.mk A) :=
          mul_le_mul' (mk_finset_le (max ℵ₀ (Cardinal.mk A)) (le_max_left _ _)
            (le_max_right _ _)) le_rfl
    _ = max ℵ₀ (Cardinal.mk A) := Cardinal.mul_eq_self (le_max_left _ _)

/-! ## The image of the spectrum -/

/-- The image of the spectrum of a stage is the union of the basic opens of the elements of its
kept patterns. -/
theorem range_comap_algebraMap_patternStageRing (𝔉 : Finset A) :
    Set.range (PrimeSpectrum.comap (algebraMap A (patternStageRing E 𝔉))) =
      ⋃ σ : GoodPattern E 𝔉,
        (PrimeSpectrum.basicOpen (patternElement 𝔉 σ.1) : Set (PrimeSpectrum A)) := by
  rw [← PrimeSpectrum.iUnion_range_comap_comp_evalRingHom (algebraMap A (patternStageRing E 𝔉))]
  exact Set.iUnion_congr fun σ ↦ PrimeSpectrum.localization_away_comap_range
    (Localization.Away (patternElement 𝔉 σ.1)) (patternElement 𝔉 σ.1)

/-- The intersection over all finite subsets of the stage images is exactly `E`. -/
theorem iInter_iUnion_basicOpen_patternElement_eq (hE : SpectralSubset.IsStableCompact E) :
    (⋂ 𝔉 : Finset A, ⋃ σ : GoodPattern E 𝔉,
      (PrimeSpectrum.basicOpen (patternElement 𝔉 σ.1) : Set (PrimeSpectrum A))) = E := by
  classical
  refine Set.Subset.antisymm (fun p hp ↦ ?_) fun p hp ↦ ?_
  · by_contra hpE
    obtain ⟨S, hES, hS⟩ := (SpectralSubset.characterizations_equiv E).2.2.1.mp
      ((SpectralSubset.characterizations_equiv E).2.1.mp hE)
    obtain ⟨V, hVS, hpV⟩ : ∃ V ∈ S, p ∉ V := by
      rw [hES, Set.mem_sInter] at hpE
      simpa using hpE
    obtain ⟨t, ht⟩ := PrimeSpectrum.isCompact_isOpen_iff.mp ⟨(hS V hVS).2, (hS V hVS).1⟩
    have hEV : E ⊆ V := hES ▸ Set.sInter_subset_of_mem hVS
    have hpt : ∀ g ∈ t, g ∈ p.asIdeal := by
      rw [← ht, Set.mem_compl_iff, not_not, PrimeSpectrum.mem_zeroLocus] at hpV
      exact fun g hg ↦ hpV hg
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp (Set.mem_iInter.mp hp t)
    obtain ⟨r, hrE, hrs⟩ := σ.2
    have hrV : r ∉ PrimeSpectrum.zeroLocus (t : Set A) := by
      rw [← Set.mem_compl_iff, ht]
      exact hEV hrE
    obtain ⟨g₀, hg₀t, hg₀r⟩ : ∃ g ∈ t, g ∉ r.asIdeal := by
      rw [PrimeSpectrum.mem_zeroLocus] at hrV
      simpa [Set.subset_def] using hrV
    have hσg₀ : σ.1 ⟨g₀, hg₀t⟩ = false :=
      Bool.eq_false_iff.mpr fun hb ↦ hg₀r ((hrs ⟨g₀, hg₀t⟩).mpr hb)
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hσ <|
      patternElement_mem_iff.mpr ⟨⟨g₀, hg₀t⟩, hσg₀, hpt g₀ hg₀t⟩
  · refine Set.mem_iInter.mpr fun 𝔉 ↦ Set.mem_iUnion.mpr ?_
    refine ⟨⟨fun g ↦ decide (g.1 ∈ p.asIdeal), ⟨p, hp, fun g ↦ by simp⟩⟩, ?_⟩
    refine (PrimeSpectrum.mem_basicOpen _ _).mpr fun hmem ↦ ?_
    obtain ⟨g, hg, hgp⟩ := patternElement_mem_iff.mp hmem
    simp only [decide_eq_false_iff_not] at hg
    exact hg hgp

/-- The image of the spectrum of the colimit is `E`. -/
theorem range_comap_algebraMap_patternColimitRing (hE : SpectralSubset.IsStableCompact E) :
    Set.range (PrimeSpectrum.comap (algebraMap A (patternColimitRing E))) = E := by
  rw [PrimeSpectrum.range_comap_algebraMap_directLimit (patternStageRing E) (patternStageHom E)
    (fun _ _ h ↦ patternStageMap_comp_algebraMap E h) (patternColimit_of_comp_algebraMap E)]
  exact (Set.iInter_congr fun 𝔉 ↦ range_comap_algebraMap_patternStageRing E 𝔉).trans
    (iInter_iUnion_basicOpen_patternElement_eq E hE)

/-- A quasi-compact subset of `Spec A` stable under generalization is the image of the spectrum
of an ind-Zariski `A`-algebra. -/
theorem exists_indZariski_range_comap_eq (hE : SpectralSubset.IsStableCompact E) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIndZariski A B ∧
      Set.range (PrimeSpectrum.comap (algebraMap A B)) = E :=
  ⟨patternColimitRing E, inferInstance, inferInstance, isIndZariski_patternColimitRing E,
    range_comap_algebraMap_patternColimitRing E hE⟩

/-- A quasi-compact subset of `Spec A` stable under generalization is the image of the spectrum
of an ind-Zariski `A`-algebra with at most `max ℵ₀ #A` elements. -/
theorem exists_indZariski_range_comap_eq_and_mk_le (hE : SpectralSubset.IsStableCompact E) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Algebra.IsIndZariski A B ∧
      Set.range (PrimeSpectrum.comap (algebraMap A B)) = E ∧
        Cardinal.mk B ≤ max ℵ₀ (Cardinal.mk A) :=
  ⟨patternColimitRing E, inferInstance, inferInstance, isIndZariski_patternColimitRing E,
    range_comap_algebraMap_patternColimitRing E hE, mk_patternColimitRing_le E⟩

end AlgebraicGeometry.ProEtale

end
