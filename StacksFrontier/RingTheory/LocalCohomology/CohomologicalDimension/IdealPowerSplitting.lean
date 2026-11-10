module

public import Mathlib.RingTheory.Filtration
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.LocalCohomology.BasicOpenSections
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.AllModules
public import StacksFrontier.RingTheory.LocalCohomology.LongExactSequence.Triangulated
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.CechSectionsComparison
public import StacksFrontier.RingTheory.LocalCohomology.SectionsIso.Basic
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.CohomologicalDimension

/-!
# Splitting the inclusion of a power of an ideal of cohomological dimension one

Let `I = (f_1, …, f_r)` be an ideal of a Noetherian ring `A` whose cohomological dimension
`cd(A, I)` of Stacks 0DX8 is `1`. Then some positive power `I^c` carries `A`-linear maps
`φ_j : I^c → A` for which `∑ f_j φ_j : I^c → A` is the inclusion; equivalently the inclusion
`I^c ↪ I` factors through the presentation `A^r ↠ I` determined by the chosen generators.

## Main results

* `Stacks.LocalCohomology.exists_pow_linearMaps_sum_eq_self` — **Stacks 0EIA**.

## Implementation notes

The source deduces from `cd(A, I) = 1` that `U = Spec A ∖ V(I)` is affine (the affineness half of
Stacks 0DXD) and then writes `1 = ∑ f_j b_j` in `Γ(U, 𝒪_U)`. That route is unavailable here:
`StacksFrontier/RingTheory/LocalCohomology/CohomologicalDimension/AffineComplement.lean` proves only
nonemptiness and quasi-compactness of `U`, since affineness rests on Stacks 01XF (Serre's
criterion for affineness) and on the implication (1) ⇒ (3) of Stacks 0DX7, neither of which this
library carries.

Affineness is not needed. Writing `K` for the module of syzygies, so that `0 → K → A^r → I → 0`
is exact with `A^r → I` the map `c ↦ ∑ f_j c_j`, the obstruction to lifting a section of `Ĩ` on
`U` to one of `Ã^r` lies in `H^1(U, K̃) ≅ H²_{V(I)}(K)`, and that vanishes because `cd(A, I) ≤ 1`
bounds the local cohomology of *every* module
(`Stacks.LocalCohomology.isZero_homology_localCohomology_of_isLocalCohomologyBound`). So the
section of `Ĩ` that restricts to `1` does lift, by the four-term sequence of Stacks 0DWR applied
to `A^r` and to `I` together with its naturality. The proof then runs in three steps:

* `Stacks.LocalCohomology.exists_section_generatorCombination_eq_one` — the cohomological step;
* `Stacks.LocalCohomology.exists_crossRelations_of_section` — normalizing the resulting section to
  numerators `a_i` with a single exponent `N`, satisfying `f_j^N a_i = f_i^N a_j` and
  `∑_l f_l (a_i)_l = f_i^N`;
* `Stacks.LocalCohomology.exists_pow_linearMaps_of_crossRelations` — building the maps from those
  numerators. A map out of `(f_1^N, …, f_r^N)` sending `∑ c_i f_i^N` to `∑ c_i a_i` is well
  defined only modulo `I`-power torsion, so the numerators are first multiplied by `f_i^m` for an
  `m` with `I^m A^r ⊓ (I-power torsion) = 0`, which the Artin–Rees lemma
  (`Ideal.exists_pow_inf_eq_pow_smul`) supplies over a Noetherian ring.

## References

* [Stacks Project, Tag 0EIA](https://stacks.math.columbia.edu/tag/0EIA)
* [Stacks Project, Tag 0DX8](https://stacks.math.columbia.edu/tag/0DX8)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open PrimeSpectrum (basicOpen)

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {r : ℕ}

/-- The `A`-linear combination map `c ↦ ∑ f i * c i`. -/
private def generatorCombination (f : Fin r → A) : (Fin r → A) →ₗ[A] A where
  toFun c := ∑ i, f i * c i
  map_add' c d := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
private theorem generatorCombination_apply (f : Fin r → A) (c : Fin r → A) :
    generatorCombination f c = ∑ i, f i * c i := rfl

/-- The combination map, viewed as a map into the ideal containing the `f i`. -/
private def generatorCombinationIdeal (f : Fin r → A) (I : Ideal A) (hfI : ∀ i, f i ∈ I) :
    (Fin r → A) →ₗ[A] I :=
  LinearMap.codRestrict I (generatorCombination f) fun c => by
    rw [generatorCombination_apply]
    exact Submodule.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (hfI i)

/-- A generator of an ideal presented as the span of a family lies in the ideal. -/
private theorem apply_mem_of_eq_span_range {I : Ideal A} {f : Fin r → A}
    (hf : I = Ideal.span (Set.range f)) (i : Fin r) : f i ∈ I :=
  hf ▸ Ideal.subset_span ⟨i, rfl⟩

/-- Every element of the span of the family `f` is a combination `∑ f i * c i`. -/
private theorem exists_generatorCombination_eq {f : Fin r → A} {x : A}
    (hx : x ∈ Ideal.span (Set.range f)) : ∃ c, generatorCombination f c = x := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hx
  exact ⟨c, by simpa [mul_comm] using hc⟩

private theorem generatorCombinationIdeal_surjective (f : Fin r → A) (I : Ideal A)
    (hfI : ∀ i, f i ∈ I) (hf : I = Ideal.span (Set.range f)) :
    Function.Surjective (generatorCombinationIdeal f I hfI) := by
  intro x
  obtain ⟨c, hc⟩ := exists_generatorCombination_eq (hf ▸ x.2 : (x : A) ∈ Ideal.span (Set.range f))
  exact ⟨c, Subtype.ext hc⟩


/-- A module map acts on locally fractional sections by applying it to numerators. -/
private theorem powerSplittingMapApp {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (U : Opens (PrimeSpectrum.Top A)) (s : moduleSections M U) (x : U) :
    (((associatedAbPresheafMap g).app (op U)) s).1 x =
      IsLocalizedModule.map x.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g.hom (s.1 x) :=
  rfl

/-- Locally fractional sections are determined by their values at the points. -/
private theorem powerSplittingSectionsExt {M : ModuleCat.{u} A}
    (U : Opens (PrimeSpectrum.Top A)) (s t : moduleSections M U) (h : ∀ x, s.1 x = t.1 x) :
    s = t :=
  Subtype.ext (funext h)

/-- The restriction map of the low-degree sequence sends `m` to the constant fraction `m / 1`. -/
private theorem powerSplittingRestrictionCoe (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{u} A) (m : M) (x : ((complementZeroLocus A I).ι ''ᵁ ⊤)) :
    (show moduleSections M ((complementZeroLocus A I).ι ''ᵁ ⊤) from
      restrictionToComplement (localizationTriangleData.{u} A I hI) M
        (complementTilde A I M) (Iso.refl _) m).1 x = LocalizedModule.mk m 1 := by
  rw [restrictionToComplement_apply]
  rfl

/-- **The section of `Ĩ` on `U = Spec A ∖ V(I)` restricting to `1`.** Near a point at which the
generator `f i` is invertible it is the fraction `f i / f i`. -/
private theorem powerSplittingUnitSection (A : Type u) [CommRing A] (I : Ideal A) {r : ℕ}
    (f : Fin r → A) (hf : I = Ideal.span (Set.range f)) :
    ∃ t : moduleSections (ModuleCat.of A I) ((complementZeroLocus A I).ι ''ᵁ ⊤),
      ∀ x, IsLocalizedModule.map x.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A I))
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A A))
        (ModuleCat.ofHom I.subtype).hom (t.1 x) = LocalizedModule.mk 1 1 := by
  classical
  have hfI : ∀ i, f i ∈ I := apply_mem_of_eq_span_range hf
  have hW : ((complementZeroLocus A I).ι ''ᵁ ⊤) = complementZeroLocus A I :=
    Scheme.Opens.ι_image_top _
  have hpt : ∀ p : PrimeSpectrum A, p ∈ ((complementZeroLocus A I).ι ''ᵁ ⊤) →
      ∃ i, f i ∉ p.asIdeal := by
    intro p hp
    rw [hW] at hp
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine hp ?_
    change p ∈ PrimeSpectrum.zeroLocus (I : Set A)
    rw [PrimeSpectrum.mem_zeroLocus, hf]
    exact Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
  have hbasic : ∀ h ∈ I, basicOpen h ≤ ((complementZeroLocus A I).ι ''ᵁ ⊤) := by
    intro h hh p hp
    rw [hW]
    intro hcon
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((PrimeSpectrum.mem_zeroLocus _ _).1 hcon hh)
  choose jj hjj using hpt
  refine ⟨⟨fun x => LocalizedModule.mk (⟨f (jj x.1 x.2), hfI _⟩ : I)
      ⟨f (jj x.1 x.2), hjj x.1 x.2⟩, ?_⟩, ?_⟩
  · intro x
    refine ⟨basicOpen (f (jj x.1 x.2)), (PrimeSpectrum.mem_basicOpen _ _).2 (hjj x.1 x.2),
      homOfLE (hbasic _ (hfI _)), ⟨f (jj x.1 x.2), hfI _⟩, f (jj x.1 x.2), fun y => ?_⟩
    refine ⟨(PrimeSpectrum.mem_basicOpen _ _).1 y.2, ?_⟩
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by ext; simp [Submonoid.smul_def, smul_eq_mul, mul_comm]⟩
  · intro x
    rw [IsLocalizedModule.map_LocalizedModules, LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]⟩

/-- Composing the two halves of the presentation on numerators gives the combination map. -/
private theorem powerSplittingMapSubtypeComp (A : Type u) [CommRing A] (I : Ideal A) {r : ℕ}
    (f : Fin r → A) (hfI : ∀ i, f i ∈ I) (p : PrimeSpectrum A)
    (v : LocalizedModule p.asIdeal.primeCompl (ModuleCat.of A (Fin r → A))) :
    IsLocalizedModule.map p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ModuleCat.of A I))
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ModuleCat.of A A))
        (ModuleCat.ofHom I.subtype).hom
        (IsLocalizedModule.map p.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ModuleCat.of A (Fin r → A)))
          (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ModuleCat.of A I))
          (ModuleCat.ofHom (generatorCombinationIdeal f I hfI)).hom v) =
      IsLocalizedModule.map p.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ModuleCat.of A (Fin r → A)))
        (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (ModuleCat.of A A))
        (ModuleCat.ofHom (generatorCombination f)).hom v := by
  refine LocalizedModule.induction_on (fun m d => ?_) v
  rw [IsLocalizedModule.map_LocalizedModules, IsLocalizedModule.map_LocalizedModules,
      IsLocalizedModule.map_LocalizedModules]
  rfl

/-- Noetherian stabilisation of the `I`-power torsion combined with the Artin–Rees lemma: there is
an exponent `m` such that an element of `I ^ m • ⊤` annihilated by `I ^ n` for some `n ≥ m` is
zero. -/
private theorem powerSplittingExistsAnnihilatorExponent
    (A : Type u) [CommRing A] [IsNoetherianRing A] (M : Type*) [AddCommGroup M] [Module A M]
    [Module.Finite A M] (I : Ideal A) :
    ∃ m : ℕ, ∀ n : ℕ, m ≤ n → ∀ x : M, x ∈ (I ^ m : Ideal A) • (⊤ : Submodule A M) →
      (∀ y ∈ (I ^ n : Ideal A), y • x = 0) → x = 0 := by
  obtain ⟨k₀, hk₀⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian A M))
      ⟨fun n => Submodule.torsionBySet A M ((I ^ n : Ideal A) : Set A),
        fun i j h => Submodule.torsionBySet_le_torsionBySet_pow i j h I⟩
  have hstab : ∀ n, k₀ ≤ n → Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A) =
      Submodule.torsionBySet A M ((I ^ n : Ideal A) : Set A) := fun n hn => hk₀ n hn
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (M := M) I
    (Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A))
  have hkill : (I ^ k₀ : Ideal A) •
      Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr fun y hy z hz => ?_) bot_le
    simp only [Submodule.mem_torsionBySet_iff] at hz
    simpa using hz ⟨y, hy⟩
  refine ⟨k + k₀, fun n hn x hx hann => ?_⟩
  have hxT : x ∈ Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A) := by
    rw [hstab n (by omega)]
    simp only [Submodule.mem_torsionBySet_iff]
    exact fun y => hann y y.2
  have hinf : x ∈ (I ^ (k + k₀) : Ideal A) • (⊤ : Submodule A M) ⊓
      Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A) := ⟨hx, hxT⟩
  rw [hk (k + k₀) (by omega)] at hinf
  have hle : (I ^ (k + k₀ - k) : Ideal A) •
        ((I ^ k : Ideal A) • (⊤ : Submodule A M) ⊓
          Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A)) ≤
      (I ^ k₀ : Ideal A) • Submodule.torsionBySet A M ((I ^ k₀ : Ideal A) : Set A) := by
    rw [show k + k₀ - k = k₀ from by omega]
    exact Submodule.smul_mono le_rfl inf_le_right
  have hbot := hle hinf
  rw [hkill] at hbot
  simpa using hbot

/-- **Compatible numerators with a single exponent produce the splitting maps.** Multiplying the
numerators by `f i ^ m`, for an `m` with `I ^ m A^r ⊓ (I-power torsion) = 0`, makes the assignment
`∑ c i * f i ^ N ↦ ∑ c i • a i` well defined; it is then restricted to `I ^ c` for a `c` with
`I ^ c ⊆ (f_1^N, …, f_r^N)`. -/
private theorem exists_pow_linearMaps_of_crossRelations
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {r : ℕ} (f : Fin r → A) (hf : I = Ideal.span (Set.range f))
    (N : ℕ) (a : Fin r → (Fin r → A))
    (hcross : ∀ i j, f j ^ N • a i = f i ^ N • a j)
    (hsum : ∀ i, ∑ l, f l * a i l = f i ^ N) :
    ∃ c : ℕ, 1 ≤ c ∧ ∃ φ : Fin r → (I ^ c : Ideal A) →ₗ[A] A,
      ∀ x : (I ^ c : Ideal A), (∑ j, f j * φ j x) = (x : A) := by
  have hfI : ∀ i, f i ∈ I := apply_mem_of_eq_span_range hf
  obtain ⟨m, hm⟩ := powerSplittingExistsAnnihilatorExponent A (Fin r → A) I
  -- Shift the numerators by `f i ^ m`, so that they land in `I ^ m • ⊤`.
  obtain ⟨b, hb⟩ : ∃ b : Fin r → (Fin r → A), ∀ i, b i = f i ^ m • a i :=
    ⟨fun i => f i ^ m • a i, fun _ => rfl⟩
  have hcross' : ∀ i j, f j ^ (N + m) • b i = f i ^ (N + m) • b j := by
    intro i j
    have h : (f i ^ m * f j ^ m) • (f j ^ N • a i) = (f i ^ m * f j ^ m) • (f i ^ N • a j) := by
      rw [hcross i j]
    simp only [hb, smul_smul] at h ⊢
    rw [show f j ^ (N + m) * f i ^ m = f i ^ m * f j ^ m * f j ^ N from by ring,
      show f i ^ (N + m) * f j ^ m = f i ^ m * f j ^ m * f i ^ N from by ring]
    exact h
  have hsum' : ∀ i, ∑ l, f l * b i l = f i ^ (N + m) := by
    intro i
    have h1 : ∀ l : Fin r, f l * b i l = f i ^ m * (f l * a i l) := by
      intro l
      simp only [hb, Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.mul_sum, hsum i, pow_add]
    ring
  have hmem : ∀ (i : Fin r) (y : A),
      y • b i ∈ (I ^ m : Ideal A) • (⊤ : Submodule A (Fin r → A)) := by
    intro i y
    rw [hb, smul_smul]
    exact Submodule.smul_mem_smul
      (Ideal.mul_mem_left _ y (Ideal.pow_mem_pow (hfI i) m)) Submodule.mem_top
  -- Choose the exponent `c`.
  have hrad : I ≤ (Ideal.span (Set.range fun i => f i ^ (N + m))).radical := by
    rw [hf, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    exact ⟨N + m, Ideal.subset_span ⟨i, rfl⟩⟩
  obtain ⟨K, hK⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  obtain ⟨c, hc1, hcm, hcK⟩ : ∃ c : ℕ, 1 ≤ c ∧ m ≤ c ∧ K ≤ c :=
    ⟨max m K + 1, by omega, by omega, by omega⟩
  have hcJ : (I ^ c : Ideal A) ≤ Ideal.span (Set.range fun i => f i ^ (N + m)) :=
    (Ideal.pow_le_pow_right hcK).trans hK
  -- The two linear maps.
  let σ : (Fin r → A) →ₗ[A] A := generatorCombination fun i => f i ^ (N + m)
  have hσ : ∀ d, σ d = ∑ i, f i ^ (N + m) * d i := fun _ => rfl
  let τ : (Fin r → A) →ₗ[A] (Fin r → A) := Fintype.linearCombination A b
  have hτ : ∀ d, τ d = ∑ i, d i • b i := fun _ => rfl
  have hkey : ∀ (j : Fin r) (d : Fin r → A), f j ^ (N + m) • τ d = σ d • b j := by
    intro j d
    rw [hτ, hσ, Finset.smul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_comm (f j ^ (N + m)) (d i) (b i), hcross' i j, smul_smul, mul_comm (d i)]
  have hkerle : LinearMap.ker σ ≤ LinearMap.ker τ := by
    intro d hd
    have hz : ∀ j, f j ^ (N + m) • τ d = 0 := by
      intro j
      rw [hkey j d, LinearMap.mem_ker.mp hd, zero_smul]
    have hann : ∀ y ∈ (I ^ c : Ideal A), y • τ d = 0 := by
      intro y hy
      obtain ⟨g, hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hcJ hy)
      rw [← hg, Finset.sum_smul]
      exact Finset.sum_eq_zero fun i _ => by rw [mul_smul, hz i, smul_zero]
    have hin : τ d ∈ (I ^ m : Ideal A) • (⊤ : Submodule A (Fin r → A)) := by
      rw [hτ]
      exact Submodule.sum_mem _ fun i _ => hmem i (d i)
    exact LinearMap.mem_ker.mpr (hm c hcm (τ d) hin hann)
  -- The factorisation of `τ` through the range of `σ`.
  have hIc : (I ^ c : Ideal A) ≤ LinearMap.range σ := by
    intro y hy
    exact exists_generatorCombination_eq (hcJ hy)
  let Φ : (LinearMap.range σ) →ₗ[A] (Fin r → A) :=
    (Submodule.liftQ (LinearMap.ker σ) τ hkerle).comp σ.quotKerEquivRange.symm.toLinearMap
  have hΦ : ∀ d : Fin r → A, Φ ⟨σ d, LinearMap.mem_range_self σ d⟩ = τ d := by
    intro d
    change (Submodule.liftQ (LinearMap.ker σ) τ hkerle)
      (σ.quotKerEquivRange.symm ⟨σ d, LinearMap.mem_range_self σ d⟩) = τ d
    rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  let ψ : (I ^ c : Ideal A) →ₗ[A] (Fin r → A) := Φ.comp (Submodule.inclusion hIc)
  refine ⟨c, hc1, fun j => (LinearMap.proj j).comp ψ, fun x => ?_⟩
  obtain ⟨d, hd⟩ := hIc x.2
  have hψ : ψ x = τ d := by
    have hx : Submodule.inclusion hIc x =
        (⟨σ d, LinearMap.mem_range_self σ d⟩ : LinearMap.range σ) :=
      Subtype.ext (by rw [Submodule.coe_inclusion]; exact hd.symm)
    change Φ (Submodule.inclusion hIc x) = τ d
    rw [hx, hΦ]
  have hval : ∀ j : Fin r, ((LinearMap.proj j : (Fin r → A) →ₗ[A] A).comp ψ) x
      = ∑ i, d i * b i j := by
    intro j
    change (ψ x) j = _
    rw [hψ, hτ]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc ∑ j, f j * ((LinearMap.proj j : (Fin r → A) →ₗ[A] A).comp ψ) x
      = ∑ j, ∑ i, d i * (f j * b i j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hval j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ i, d i * ∑ j, f j * b i j := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = σ d := by
        rw [hσ]
        exact Finset.sum_congr rfl fun i _ => by rw [hsum' i]; ring
    _ = (x : A) := hd

/-- Applying a module map to a locally fractional section, read off at a single point: if the
scalar `c` turns the value of `s` at `x` into the constant fraction `m / 1`, then it turns the
value of the image section at `x` into `g m / 1`. -/
private theorem powerSplittingApp_smul_value {M N : ModuleCat.{u} A} (g : M ⟶ N)
    (U : Opens (PrimeSpectrum.Top A)) (s : moduleSections M U) (x : U)
    (c : A) (m : M) (h : c • s.1 x = LocalizedModule.mk m 1) :
    c • ((associatedAbPresheafMap g).app (op U) s).1 x = LocalizedModule.mk (g.hom m) 1 := by
  rw [powerSplittingMapApp g U s x, ← map_smul, h, IsLocalizedModule.map_LocalizedModules]

/-- Annihilation by a power of a ring element persists at every larger exponent. -/
private theorem powerSplittingPow_smul_eq_zero_of_le {M : Type*} [AddCommGroup M] [Module A M]
    {h : A} {z : M} {k k' : ℕ} (hk : k ≤ k') (hz : h ^ k • z = 0) : h ^ k' • z = 0 := by
  rw [← Nat.sub_add_cancel hk, pow_add, mul_smul, hz, smul_zero]

/-- The extraction step, stated over an arbitrary open containing every standard open `D (f i)`:
normalize the section to a single numerator on each `D (f i)`, compare the numerators on the
overlaps and against `1`, and clear the resulting local denominators by a power of the `f i`. -/
private theorem powerSplittingExists_crossRelations_aux
    (f : Fin r → A) (U : Opens (PrimeSpectrum.Top A)) (hle : ∀ i, basicOpen (f i) ≤ U)
    (s : moduleSections (ModuleCat.of A (Fin r → A)) U)
    (hs : (associatedAbPresheafMap (ModuleCat.ofHom (generatorCombination f))).app (op U) s =
      moduleSectionsMk (ModuleCat.of A A) U 1) :
    ∃ (N : ℕ) (a : Fin r → (Fin r → A)),
      (∀ i j, f j ^ N • a i = f i ^ N • a j) ∧ (∀ i, ∑ l, f l * a i l = f i ^ N) := by
  choose n₀ a₀ hrep using fun i => exists_pow_smul_eq_moduleSectionsMk
    (ModuleCat.of A (Fin r → A)) (f i)
    (moduleSectionsRestrict (ModuleCat.of A (Fin r → A)) (hle i) s)
  obtain ⟨n, hn⟩ : ∃ n, ∀ i, n₀ i ≤ n :=
    ⟨Finset.univ.sup n₀, fun i => Finset.le_sup (Finset.mem_univ i)⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin r → (Fin r → A), ∀ i, b i = f i ^ (n - n₀ i) • a₀ i :=
    ⟨_, fun _ => rfl⟩
  have hval : ∀ (i : Fin r) (p : PrimeSpectrum A) (hp : p ∈ basicOpen (f i)),
      f i ^ n • s.1 ⟨p, hle i hp⟩ = LocalizedModule.mk (b i) 1 := by
    intro i p hp
    have h2 : f i ^ n₀ i • s.1 ⟨p, hle i hp⟩ = LocalizedModule.mk (a₀ i) 1 :=
      congrArg (fun t => t.1 ⟨p, hp⟩) (hrep i)
    rw [hb, ← LocalizedModule.smul'_mk, ← h2, smul_smul, ← pow_add, Nat.sub_add_cancel (hn i)]
  have hcross0 : ∀ i j, ∃ k, (f i * f j) ^ k • (f j ^ n • b i - f i ^ n • b j) = 0 := by
    intro i j
    refine exists_pow_smul_eq_zero_of_forall_mem_basicOpen (f i * f j) _ fun p hp => ?_
    have hpi : p ∈ basicOpen (f i) :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr fun h => hp (Ideal.mul_mem_right _ _ h)
    have hpj : p ∈ basicOpen (f j) :=
      (PrimeSpectrum.mem_basicOpen _ _).mpr fun h => hp (Ideal.mul_mem_left _ _ h)
    have key : f j ^ n • LocalizedModule.mk (b i) (1 : p.asIdeal.primeCompl) =
        f i ^ n • LocalizedModule.mk (b j) 1 := by
      rw [← hval i p hpi, ← hval j p hpj, smul_smul, smul_smul, mul_comm]
    rw [LocalizedModule.smul'_mk, LocalizedModule.smul'_mk] at key
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp key
    simp only [Submonoid.smul_def, one_smul] at hu
    exact ⟨u.1, u.2, by rw [smul_sub, sub_eq_zero, hu]⟩
  have hsum0 : ∀ i, ∃ k, f i ^ k • (generatorCombination f (b i) - f i ^ n) = 0 := by
    intro i
    refine exists_pow_smul_eq_zero_of_forall_mem_basicOpen (f i) _ fun p hp => ?_
    have hpi : p ∈ basicOpen (f i) := (PrimeSpectrum.mem_basicOpen _ _).mpr hp
    have hpt : ((associatedAbPresheafMap (ModuleCat.ofHom (generatorCombination f))).app
        (op U) s).1 ⟨p, hle i hpi⟩ = LocalizedModule.mk (1 : A) 1 := by rw [hs]; rfl
    have key := powerSplittingApp_smul_value (ModuleCat.ofHom (generatorCombination f)) U s
      ⟨p, hle i hpi⟩ (f i ^ n) (b i) (hval i p hpi)
    rw [hpt, LocalizedModule.smul'_mk, smul_eq_mul, mul_one] at key
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp key.symm
    simp only [Submonoid.smul_def, one_smul] at hu
    exact ⟨u.1, u.2, by rw [smul_sub, sub_eq_zero]; exact hu⟩
  choose k₁ hk₁ using hcross0
  choose k₂ hk₂ using hsum0
  obtain ⟨k, hkc, hks⟩ : ∃ k, (∀ i j, (f i * f j) ^ k • (f j ^ n • b i - f i ^ n • b j) = 0) ∧
      ∀ i, f i ^ k • (generatorCombination f (b i) - f i ^ n) = 0 := by
    refine ⟨Finset.univ.sup (fun ij : Fin r × Fin r => k₁ ij.1 ij.2) ⊔ Finset.univ.sup k₂,
      fun i j => powerSplittingPow_smul_eq_zero_of_le ?_ (hk₁ i j),
      fun i => powerSplittingPow_smul_eq_zero_of_le ?_ (hk₂ i)⟩
    · exact le_trans (Finset.le_sup (f := fun ij : Fin r × Fin r => k₁ ij.1 ij.2)
        (Finset.mem_univ (i, j))) le_sup_left
    · exact le_trans (Finset.le_sup (Finset.mem_univ i)) le_sup_right
  refine ⟨n + k, fun i => f i ^ k • b i, fun i j => ?_, fun i => ?_⟩
  · have h1 := hkc i j
    rw [smul_sub, sub_eq_zero] at h1
    calc f j ^ (n + k) • (f i ^ k • b i)
        = (f i * f j) ^ k • (f j ^ n • b i) := by
          rw [smul_smul, smul_smul, show f j ^ (n + k) * f i ^ k = (f i * f j) ^ k * f j ^ n from
            by ring]
      _ = (f i * f j) ^ k • (f i ^ n • b j) := h1
      _ = f i ^ (n + k) • (f j ^ k • b j) := by
          rw [smul_smul, smul_smul, show f i ^ (n + k) * f j ^ k = (f i * f j) ^ k * f i ^ n from
            by ring]
  · have h1 := hks i
    rw [smul_sub, sub_eq_zero] at h1
    calc ∑ l, f l * (f i ^ k • b i) l
        = generatorCombination f (f i ^ k • b i) := rfl
      _ = f i ^ k • generatorCombination f (b i) := map_smul _ _ _
      _ = f i ^ k • f i ^ n := h1
      _ = f i ^ (n + k) := by rw [smul_eq_mul, ← pow_add, add_comm]

/-- **Normalizing a section of `Ã^r` on `U = Spec A ∖ V(I)` whose image under `∑ f j ·` is `1`.**
On each `D (f i)` the section is a single fraction, and clearing the local denominators by one
power of the generators gives numerators with exact cross relations and prescribed image. -/
private theorem exists_crossRelations_of_section
    (A : Type u) [CommRing A] (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : I = Ideal.span (Set.range f))
    (s : moduleSections (ModuleCat.of A (Fin r → A))
      ((complementZeroLocus A I).ι ''ᵁ ⊤))
    (hs : (associatedAbPresheafMap (ModuleCat.ofHom (generatorCombination f))).app
        (op ((complementZeroLocus A I).ι ''ᵁ ⊤)) s =
      moduleSectionsMk (ModuleCat.of A A) ((complementZeroLocus A I).ι ''ᵁ ⊤) 1) :
    ∃ (N : ℕ) (a : Fin r → (Fin r → A)),
      (∀ i j, f j ^ N • a i = f i ^ N • a j) ∧ (∀ i, ∑ l, f l * a i l = f i ^ N) := by
  refine powerSplittingExists_crossRelations_aux f _ (fun i => ?_) s hs
  have hfI := apply_mem_of_eq_span_range hf i
  rw [Scheme.Opens.ι_image_top]
  intro p hp
  simp only [PrimeSpectrum.mem_basicOpen] at hp
  exact fun hcon => hp (hcon hfI)

/-- **The cohomological step.** The vanishing of `H²_{V(I)}` on every module makes
`Γ(U, Ã^r) → Γ(U, Ĩ)` surjective, by the four-term sequence of Stacks 0DWR and its naturality, so
the section of `Ĩ` on `U = Spec A ∖ V(I)` that restricts to `1` lifts to a section of `Ã^r`. -/
private theorem exists_section_generatorCombination_eq_one
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) {r : ℕ} (f : Fin r → A)
    (hf : I = Ideal.span (Set.range f))
    (hvan : ∀ M : ModuleCat.{u} A, Limits.IsZero (localCohomologyModule A I hI M 2)) :
    ∃ s : moduleSections (ModuleCat.of A (Fin r → A))
        ((complementZeroLocus A I).ι ''ᵁ ⊤),
      (associatedAbPresheafMap (ModuleCat.ofHom (generatorCombination f))).app
          (op ((complementZeroLocus A I).ι ''ᵁ ⊤)) s =
        moduleSectionsMk (ModuleCat.of A A) ((complementZeroLocus A I).ι ''ᵁ ⊤) 1 := by
  classical
  have hfI : ∀ i, f i ∈ I := apply_mem_of_eq_span_range hf
  have hS : (generatorCombinationIdeal f I hfI).shortComplexKer.ShortExact :=
    LinearMap.shortExact_shortComplexKer (generatorCombinationIdeal_surjective f I hfI hf)
  have h1surj : Function.Surjective
      (localCohomologyModuleMap A I hI (ModuleCat.of A (Fin r → A)) (ModuleCat.of A I)
        (ModuleCat.ofHom (generatorCombinationIdeal f I hfI)) 1).hom :=
    surjective_localCohomologyModuleMap_of_isZero_X₁_succ A I hI
      (generatorCombinationIdeal f I hfI).shortComplexKer 1 hS (by simpa using hvan _)
  obtain ⟨t0, ht0⟩ := powerSplittingUnitSection A I f hf
  obtain ⟨t, htt⟩ : ∃ t : complementGlobalSections A I
      (complementTilde A I (ModuleCat.of A I)), t = t0 := ⟨t0, rfl⟩
  obtain ⟨u, hu⟩ := h1surj (localizationBoundary (localizationTriangleData.{u} A I hI)
    (ModuleCat.of A I) (complementTilde A I (ModuleCat.of A I)) (Iso.refl _) t)
  obtain ⟨s₀, hs₀⟩ := (exact_lowDegreeSequence.{u} A I hI (ModuleCat.of A (Fin r → A))
    (complementTilde A I (ModuleCat.of A (Fin r → A))) (Iso.refl _)).2.2.2 u
  obtain ⟨w, hw⟩ : ∃ w : complementGlobalSections A I
        (complementTilde A I (ModuleCat.of A I)),
      w = (associatedAbPresheafMap (ModuleCat.ofHom (generatorCombinationIdeal f I hfI))).app
        (op ((complementZeroLocus A I).ι ''ᵁ ⊤)) s₀ := ⟨_, rfl⟩
  have hnat := localizationBoundary_naturality (localizationTriangleData.{u} A I hI)
    (ModuleCat.ofHom (generatorCombinationIdeal f I hfI)) s₀
  have hkey : localizationBoundary (localizationTriangleData.{u} A I hI)
      (ModuleCat.of A I) (complementTilde A I (ModuleCat.of A I)) (Iso.refl _) w =
      localizationBoundary (localizationTriangleData.{u} A I hI)
        (ModuleCat.of A I) (complementTilde A I (ModuleCat.of A I)) (Iso.refl _) t := by
    rw [hw, hnat, hs₀]
    exact hu
  have hzero : localizationBoundary (localizationTriangleData.{u} A I hI)
      (ModuleCat.of A I) (complementTilde A I (ModuleCat.of A I)) (Iso.refl _) (t - w) = 0 := by
    rw [map_sub, hkey, sub_self]
  obtain ⟨y, hy⟩ := ((exact_lowDegreeSequence.{u} A I hI (ModuleCat.of A I)
    (complementTilde A I (ModuleCat.of A I)) (Iso.refl _)).2.2.1 _).1 hzero
  obtain ⟨z, hz⟩ := generatorCombinationIdeal_surjective f I hfI hf y
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : moduleSections (ModuleCat.of A (Fin r → A))
      ((complementZeroLocus A I).ι ''ᵁ ⊤), s₁ = s₀ := ⟨s₀, rfl⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂ : moduleSections (ModuleCat.of A (Fin r → A))
        ((complementZeroLocus A I).ι ''ᵁ ⊤),
      s₂ = restrictionToComplement (localizationTriangleData.{u} A I hI)
        (ModuleCat.of A (Fin r → A)) (complementTilde A I (ModuleCat.of A (Fin r → A)))
        (Iso.refl _) z := ⟨_, rfl⟩
  refine ⟨s₁ + s₂, powerSplittingSectionsExt _ _ _ fun x => ?_⟩
  rw [powerSplittingMapApp _ _ (s₁ + s₂) x,
    moduleSectionsMk_apply (ModuleCat.of A A) (1 : A) x]
  -- the two numerators of the chosen section at `x`
  have hval : (s₁ + s₂).1 x = s₀.1 x + LocalizedModule.mk z 1 := by
    rw [show (s₁ + s₂).1 x = s₁.1 x + s₂.1 x from rfl, hs₁, hs₂,
      powerSplittingRestrictionCoe A I hI (ModuleCat.of A (Fin r → A)) z x]
  -- the correction term, read off from the exactness step
  have hypt : LocalizedModule.mk y (1 : x.1.asIdeal.primeCompl) = t0.1 x -
      IsLocalizedModule.map x.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A (Fin r → A)))
        (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A I))
        (ModuleCat.ofHom (generatorCombinationIdeal f I hfI)).hom (s₀.1 x) := by
    have h := congrArg (fun v => (show
      moduleSections (ModuleCat.of A I) ((complementZeroLocus A I).ι ''ᵁ ⊤) from v).1 x) hy
    rw [powerSplittingRestrictionCoe A I hI (ModuleCat.of A I) y x] at h
    refine h.trans ?_
    rw [htt, hw]
    rfl
  -- apply the inclusion `I → A` to that identity
  have hA : LocalizedModule.mk (y : A) (1 : x.1.asIdeal.primeCompl) =
      LocalizedModule.mk (1 : A) 1 -
        IsLocalizedModule.map x.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A (Fin r → A)))
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A A))
          (ModuleCat.ofHom (generatorCombination f)).hom (s₀.1 x) := by
    have h : IsLocalizedModule.map x.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A I))
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A A))
          (ModuleCat.ofHom I.subtype).hom (LocalizedModule.mk y 1) =
        IsLocalizedModule.map x.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A I))
          (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A A))
          (ModuleCat.ofHom I.subtype).hom (t0.1 x -
            IsLocalizedModule.map x.1.asIdeal.primeCompl
              (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A (Fin r → A)))
              (LocalizedModule.mkLinearMap x.1.asIdeal.primeCompl (ModuleCat.of A I))
              (ModuleCat.ofHom (generatorCombinationIdeal f I hfI)).hom (s₀.1 x)) := by
      rw [hypt]
    rw [IsLocalizedModule.map_LocalizedModules, map_sub, ht0 x,
      powerSplittingMapSubtypeComp A I f hfI x.1 (s₀.1 x)] at h
    exact h
  rw [hval, map_add, IsLocalizedModule.map_LocalizedModules,
    show (ModuleCat.ofHom (generatorCombination f)) z = (y : A) by rw [← hz]; rfl, hA]
  abel

/-- **Stacks Project, Tag 0EIA.** Let `I = (f_1, …, f_r)` be an ideal of a Noetherian ring `A`
with `cd(A, I) = 1`. Then there are `c ≥ 1` and `A`-linear maps `φ_j : I^c → A` such that
`∑ f_j φ_j : I^c → I` is the inclusion map. -/
@[stacks 0EIA]
theorem exists_pow_linearMaps_sum_eq_self
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {r : ℕ} (f : Fin r → A)
    (hf : I = Ideal.span (Set.range f))
    (hcd : cohomologicalDimension A I (IsNoetherian.noetherian I) = 1) :
    ∃ c : ℕ, 1 ≤ c ∧
      ∃ φ : Fin r → (I ^ c : Ideal A) →ₗ[A] A,
        ∀ x : (I ^ c : Ideal A), (∑ j, f j * φ j x) = (x : A) := by
  have hI : I.FG := IsNoetherian.noetherian I
  have hbound : IsLocalCohomologyBound A I hI 1 := by
    have := isLocalCohomologyBound_cohomologicalDimension A I hI
    rwa [hcd] at this
  have hvan : ∀ M : ModuleCat.{u} A, Limits.IsZero (localCohomologyModule A I hI M 2) :=
    fun M => isZero_homology_localCohomology_of_isLocalCohomologyBound.{u, u} I hI 1 hbound M 2
      (by norm_num)
  obtain ⟨s, hs⟩ := exists_section_generatorCombination_eq_one A I hI f hf hvan
  obtain ⟨N, a, hcross, hsum⟩ := exists_crossRelations_of_section A I f hf s hs
  exact exists_pow_linearMaps_of_crossRelations A I f hf N a hcross hsum

end Stacks.LocalCohomology

end
