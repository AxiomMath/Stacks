module

public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksFrontier.FieldTheory.Separable.TFAE
public import StacksFrontier.RingTheory.AffineBlowup.ModelComparison
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Blowup.Defs
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Defs
public import StacksFrontier.RingTheory.Kaehler.Separable
public import StacksFrontier.RingTheory.Koszul.Blowup
public import StacksFrontier.RingTheory.Koszul.Quasiregular
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Sequence.Regular.Basic
public import StacksFrontier.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.Smooth.Localization
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.RingTheory.Smooth.RegularRing
public import StacksFrontier.RingTheory.Smooth.SmoothAt
public import StacksFrontier.RingTheory.Smoothing.NeronDesingularization
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.RingTheory.Smoothing.NeronLocalParameters.RegularParameters
import all StacksFrontier.RingTheory.Smoothing.NeronLocalParameters.RegularParameters
public import StacksFrontier.RingTheory.Smoothing.NeronLocalParameters.DifferentialBasis
import all StacksFrontier.RingTheory.Smoothing.NeronLocalParameters.DifferentialBasis

/-!
# Local parameters for a smooth Néron chart

Fix an extension `R → Λ` of discrete valuation rings of ramification index one together with a
factorization `R → A → Λ` in which `A` is flat and of finite type over `R`, let `π` be a
uniformizer of `R`, and let `𝔭 ⊆ A` be the preimage of the maximal ideal of `Λ`. If `A` is
smooth over `R` at `𝔭` and the residue-field extension `κ(R) → κ(Λ)` is separable, then after
localizing `A` on a neighbourhood of `𝔭` one can choose elements `g₁, …, g_c` that are local
parameters for the closed fibre: their number is the dimension of the closed fibre of the local
ring at `𝔭`, together with `π` they generate `𝔭`, the sequence `π, g₁, …, g_c` is regular, and
they are part of a basis of the module of relative differentials. The regularity of that
sequence presents the affine blowup chart `A[𝔭/π]` as the explicit quotient
`A[y₁, …, y_c]/(π y₁ - g₁, …, π y_c - g_c)`, each `yᵢ` corresponding to the fraction `gᵢ/π`.

## Main results

* `Stacks.Smoothing.exists_local_parameters_of_smoothAt`: the existence of the localization,
  the local parameters, their dimension count, the regular sequence, the presentation of the
  affine blowup chart and the differential basis.

## Implementation notes

Localizing on a neighbourhood of `𝔭` is represented by `Localization.Away f` for an `f ∉ 𝔭`.
The algebra `A[𝔭/π]` is the subalgebra `affineBlowupAlgebra` of the localization away from the
image of `π`, and its presentation is recorded as an algebra equivalence sending each
`affineBlowupFraction` to the corresponding variable. The dimension of the closed fibre is the
Krull dimension of the quotient of the local ring at `𝔭` by the image of `π`.

## References

* [Stacks Project, Tag 0BJ2](https://stacks.math.columbia.edu/tag/0BJ2)
* [Stacks Project, Tag 0BJ4](https://stacks.math.columbia.edu/tag/0BJ4)
-/

@[expose] public section

namespace Stacks.Smoothing

open Stacks.Smooth.FlatFibreCriterion
open Stacks.Flatness.RegularSequenceQuotient

/-- The image of an extended ideal under an algebra equivalence is the ideal extended to the
target. -/
private lemma map_map_algebraMap_algEquiv {A D C : Type*} [CommRing A] [CommRing D] [CommRing C]
    [Algebra A D] [Algebra A C] (e : D ≃ₐ[A] C) (I : Ideal A) :
    (I.map (algebraMap A D)).map e.toRingEquiv.toRingHom = I.map (algebraMap A C) := by
  rw [Ideal.map_map]
  exact congrArg (Ideal.map · I) e.toAlgHom.comp_algebraMap

/-- A map sending `a` to `a'` and each `g i` to `g' i` sends `a :: ofFn g` to `a' :: ofFn g'`. -/
private lemma map_cons_ofFn_eq {α β : Type*} (φ : α → β) {a : α} {c : ℕ} (g : Fin c → α)
    {a' : β} (g' : Fin c → β) (ha : φ a = a') (hg : ∀ i, φ (g i) = g' i) :
    (a :: List.ofFn g).map φ = a' :: List.ofFn g' := by
  simp [List.map_ofFn, ha, Function.comp_def, funext hg]

/-- A map sending each `g i` to `g' i` sends the range of `g` to the range of `g'`. -/
private lemma image_range_eq_range {α β γ : Type*} (φ : β → γ) (g : α → β) (g' : α → γ)
    (hg : ∀ i, φ (g i) = g' i) : φ '' Set.range g = Set.range g' := by
  rw [← Set.range_comp]
  exact congrArg Set.range (funext hg)

/-- Regularity of a sequence at a prime spreads to a principal neighbourhood. -/
private lemma exists_away_isRegular_of_isLocalization_atPrime {B T : Type*} [CommRing B]
    [IsNoetherianRing B] [CommRing T] [Algebra B T] (q : Ideal B) [q.IsPrime]
    [IsLocalization.AtPrime T q] (xs : List B)
    (hreg : RingTheory.Sequence.IsRegular T (xs.map (algebraMap B T))) :
    ∃ h ∉ q, RingTheory.Sequence.IsRegular (Localization.Away h)
      (xs.map (algebraMap B (Localization.Away h))) := by
  let eqLoc : Localization.AtPrime q ≃ₐ[B] T := IsLocalization.algEquiv q.primeCompl _ _
  have hxs : (xs.map (algebraMap B (Localization.AtPrime q))).map eqLoc.toRingEquiv =
      xs.map (algebraMap B T) := by
    rw [List.map_map]
    congr 1
    funext x
    exact eqLoc.commutes x
  refine exists_regular_sequence_away_of_atPrime q xs
    ((isRegular_ringEquiv_congr eqLoc.toRingEquiv _).mpr ?_)
  rwa [hxs]

/-- An ideal generating the maximal ideal at a prime agrees with the prime on a principal
neighbourhood. -/
private lemma exists_away_map_eq_of_isLocalization_atPrime {B T : Type*} [CommRing B]
    [IsNoetherianRing B] [CommRing T] [IsLocalRing T] [Algebra B T] (q : Ideal B) [q.IsPrime]
    [IsLocalization.AtPrime T q] (J : Ideal B) (hJq : J ≤ q)
    (hJ : J.map (algebraMap B T) = IsLocalRing.maximalIdeal T) :
    ∃ k ∉ q, J.map (algebraMap B (Localization.Away k)) =
      q.map (algebraMap B (Localization.Away k)) := by
  let eqLoc : Localization.AtPrime q ≃ₐ[B] T := IsLocalization.algEquiv q.primeCompl _ _
  refine exists_away_map_eq_of_map_eq q J q hJq
    (ideal_map_injective_ringEquiv eqLoc.toRingEquiv ?_)
  show Ideal.map eqLoc.toRingEquiv.toRingHom
      (Ideal.map (algebraMap B (Localization.AtPrime q)) J) =
    Ideal.map eqLoc.toRingEquiv.toRingHom
      (Ideal.map (algebraMap B (Localization.AtPrime q)) q)
  rw [map_map_algebraMap_algEquiv, map_map_algebraMap_algEquiv]
  exact hJ.trans (IsLocalization.AtPrime.map_eq_maximalIdeal q T).symm

/-- Differentials of lifts of a basis of `Ω[A_𝔭⁄R]` form a basis on every small enough principal
neighbourhood. -/
private lemma exists_bijective_linearCombination_D (S : NeronSituation) {f : S.A}
    (hf : f ∉ S.maximalIdealPreimage) {n : ℕ}
    (a : Fin n → Localization.AtPrime S.maximalIdealPreimage)
    (u : Fin n → Localization.Away f)
    (hu : letI : Algebra (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage) :=
            IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
              S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf);
      ∀ i, algebraMap (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage)
        (u i) = a i)
    (bT : Module.Basis (Fin n) (Localization.AtPrime S.maximalIdealPreimage)
      (KaehlerDifferential S.R (Localization.AtPrime S.maximalIdealPreimage)))
    (hbT : ∀ i, bT i = KaehlerDifferential.D S.R _ (a i)) :
    ∃ s ∉ S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f)),
      ∀ z, s ∣ z → Function.Bijective (LocalizedModule.map (Submonoid.powers z)
        (Finsupp.linearCombination (Localization.Away f)
          fun i => KaehlerDifferential.D S.R (Localization.Away f) (u i))) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let B := Localization.Away f
  let q : Ideal B := S.maximalIdealPreimage.map (algebraMap S.A B)
  have : q.IsPrime := isPrime_map_algebraMap_of_notMem S.maximalIdealPreimage hf
  let : Algebra B T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower S.A B T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower S.R B T := .to₁₃₄ _ S.A _ _
  have : IsLocalization.AtPrime T q :=
    isLocalization_atPrime_map_of_notMem (B := B) (C := T) hf
  have hu' : ∀ i, algebraMap B T (u i) = a i := hu
  have : IsNoetherianRing S.A := Algebra.FiniteType.isNoetherianRing S.R S.A
  have : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) B inferInstance
  have : Algebra.EssFiniteType S.R B := Algebra.EssFiniteType.comp S.R S.A B
  have : Module.FinitePresentation B (KaehlerDifferential S.R B) :=
    Module.finitePresentation_of_finite B _
  let w : Fin n → KaehlerDifferential S.R B := fun i => KaehlerDifferential.D S.R B (u i)
  let eB : (Fin n →₀ B) →ₗ[B] KaehlerDifferential S.R B := Finsupp.linearCombination B w
  let l₁ : (Fin n →₀ B) →ₗ[B] (Fin n →₀ T) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap B T)
  let l₂ : KaehlerDifferential S.R B →ₗ[B] KaehlerDifferential S.R T :=
    KaehlerDifferential.map S.R S.R B T
  let eT : (Fin n →₀ T) →ₗ[T] KaehlerDifferential S.R T :=
    IsLocalizedModule.mapExtendScalars q.primeCompl l₁ l₂ T eB
  have heT : eT = bT.repr.symm := by
    ext i
    trans IsLocalizedModule.map q.primeCompl l₁ l₂ eB (l₁ (Finsupp.single i 1))
    · simp [eT, l₁, -IsLocalizedModule.map_apply]
    · have hbT' : ∀ i, bT i = KaehlerDifferential.D S.R T (a i) := hbT
      simp [l₂, eB, w, hbT', hu']
  have hbijT : Function.Bijective eT := heT ▸ bT.repr.symm.bijective
  exact exists_bijective_map_powers q.primeCompl l₁ l₂ eB hbijT

private lemma exists_away_smooth_of_smoothAt (S : NeronSituation)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) {f : S.A}
    (hf : f ∉ S.maximalIdealPreimage) :
    ∃ t ∉ S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f)),
      Algebra.Smooth S.R (Localization.Away t) := by
  obtain ⟨a, ha, hsma⟩ := hsm
  let B := Localization.Away f
  let t : B := algebraMap S.A B a
  refine ⟨t, fun hq => ha ?_, ?_⟩
  · have hunder := IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers f) B (I := S.maximalIdealPreimage) inferInstance
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf)
    exact hunder ▸ hq
  · let : Algebra.Smooth S.R (Localization.Away a) := hsma
    have : Algebra.Smooth S.R (Localization.Away (a * f)) := smooth_away_mul a f
    have : IsLocalization.Away (a * f) (Localization.Away t) :=
      IsLocalization.Away.mul B (Localization.Away t) f a
    let e : Localization.Away (a * f) ≃ₐ[S.A] Localization.Away t :=
      Localization.algEquiv _ _
    exact Algebra.Smooth.of_equiv (e.restrictScalars S.R)

private lemma span_uniformizer_sup_le_map (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R)) {f : S.A}
    (hf : f ∉ S.maximalIdealPreimage) {c : ℕ}
    (g₀ : Fin c → Localization.AtPrime S.maximalIdealPreimage)
    (hgen : IsLocalRing.maximalIdeal (Localization.AtPrime S.maximalIdealPreimage) =
      Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _) ⊔
        Ideal.span (Set.range g₀))
    (g : Fin c → Localization.Away f)
    (hg : letI : Algebra (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage) :=
            IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
              S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf);
      ∀ i, algebraMap (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage)
        (g i) = g₀ i) :
    Ideal.span ({algebraMap S.R (Localization.Away f) π} : Set _) ⊔ Ideal.span (Set.range g) ≤
      S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f)) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let B := Localization.Away f
  let q : Ideal B := S.maximalIdealPreimage.map (algebraMap S.A B)
  have : q.IsPrime := isPrime_map_algebraMap_of_notMem S.maximalIdealPreimage hf
  let : Algebra B T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower S.A B T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsLocalization.AtPrime T q :=
    isLocalization_atPrime_map_of_notMem (B := B) (C := T) hf
  have hg' : ∀ i, algebraMap B T (g i) = g₀ i := hg
  show _ ≤ q
  refine sup_le ?_ (Ideal.span_le.mpr ?_)
  · rw [Ideal.span_singleton_le_iff_mem]
    show algebraMap S.A B (algebraMap S.R S.A π) ∈ q
    exact Ideal.mem_map_of_mem _ (uniformizer_mem_maximalIdealPreimage S π hπ)
  · rintro z ⟨i, rfl⟩
    rw [← IsLocalization.AtPrime.under_maximalIdeal T q]
    show algebraMap B T (g i) ∈ IsLocalRing.maximalIdeal T
    rw [hg' i, hgen]
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)

private lemma map_span_uniformizer_sup (S : NeronSituation) (π : S.R) {f : S.A}
    (hf : f ∉ S.maximalIdealPreimage) {c : ℕ}
    (g₀ : Fin c → Localization.AtPrime S.maximalIdealPreimage)
    (hgen : IsLocalRing.maximalIdeal (Localization.AtPrime S.maximalIdealPreimage) =
      Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _) ⊔
        Ideal.span (Set.range g₀))
    (g : Fin c → Localization.Away f)
    (hg : letI : Algebra (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage) :=
            IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
              S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf);
      ∀ i, algebraMap (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage)
        (g i) = g₀ i) :
    letI : Algebra (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage) :=
      IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
        S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
    (Ideal.span ({algebraMap S.R (Localization.Away f) π} : Set _) ⊔
        Ideal.span (Set.range g)).map
        (algebraMap (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime S.maximalIdealPreimage) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let B := Localization.Away f
  let : Algebra B T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower S.A B T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower S.R B T := .to₁₃₄ _ S.A _ _
  have hg' : ∀ i, algebraMap B T (g i) = g₀ i := hg
  rw [hgen]
  simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rw [show algebraMap B T (algebraMap S.R B π) = algebraMap S.R T π from
    (IsScalarTower.algebraMap_apply S.R B T π).symm]
  rw [image_range_eq_range _ g g₀ hg']

/-- Principal neighbourhoods of a prime carrying a regular sequence, an equality of ideals and
smoothness combine, after shrinking by one more element, into one neighbourhood carrying all
three. -/
private lemma away_mul_of_four {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (q : Ideal A) [q.IsPrime] (xs : List A) (hxs : ∀ x ∈ xs, x ∈ q) (J : Ideal A)
    {h k t s : A} (hh : h ∉ q) (hk : k ∉ q) (ht : t ∉ q) (hs : s ∉ q)
    (hreg : RingTheory.Sequence.IsRegular (Localization.Away h)
      (xs.map (algebraMap A (Localization.Away h))))
    (hJ : J.map (algebraMap A (Localization.Away k)) =
      q.map (algebraMap A (Localization.Away k)))
    [Algebra.Smooth R (Localization.Away t)] :
    h * k * t * s ∉ q ∧ Algebra.Smooth R (Localization.Away (h * k * t * s)) ∧
      RingTheory.Sequence.IsRegular (Localization.Away (h * k * t * s))
        (xs.map (algebraMap A (Localization.Away (h * k * t * s)))) ∧
      J.map (algebraMap A (Localization.Away (h * k * t * s))) =
        q.map (algebraMap A (Localization.Away (h * k * t * s))) := by
  have hq : q.IsPrime := inferInstance
  refine ⟨hq.mul_notMem (hq.mul_notMem (hq.mul_notMem hh hk) ht) hs, ?_, ?_, ?_⟩
  · rw [show h * k * t * s = t * (h * k * s) by ring]
    exact smooth_away_mul t (h * k * s)
  · rw [show h * k * t * s = h * (k * t * s) by ring]
    exact isRegular_away_mul q h (k * t * s) hh
      (hq.mul_notMem (hq.mul_notMem hk ht) hs) xs hxs hreg
  · rw [show h * k * t * s = k * (h * t * s) by ring]
    exact ideal_map_away_mul J q k (h * t * s) hJ

/-- Lifts of local parameters and of a differential basis at `𝔭` to a principal neighbourhood
keep their properties on a smaller principal neighbourhood. -/
private lemma exists_away_regular_smooth_bijective (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) {c n : ℕ}
    (g₀ : Fin c → Localization.AtPrime S.maximalIdealPreimage)
    (hgen : IsLocalRing.maximalIdeal (Localization.AtPrime S.maximalIdealPreimage) =
      Ideal.span ({algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π} : Set _) ⊔
        Ideal.span (Set.range g₀))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime S.maximalIdealPreimage)
      (algebraMap S.R (Localization.AtPrime S.maximalIdealPreimage) π :: List.ofFn g₀))
    {f : S.A} (hf : f ∉ S.maximalIdealPreimage) (g : Fin c → Localization.Away f)
    (hg : letI : Algebra (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage) :=
            IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
              S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf);
      ∀ i, algebraMap (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage)
        (g i) = g₀ i)
    (a : Fin n → Localization.AtPrime S.maximalIdealPreimage)
    (u : Fin n → Localization.Away f)
    (hu : letI : Algebra (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage) :=
            IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
              S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf);
      ∀ i, algebraMap (Localization.Away f) (Localization.AtPrime S.maximalIdealPreimage)
        (u i) = a i)
    (bT : Module.Basis (Fin n) (Localization.AtPrime S.maximalIdealPreimage)
      (KaehlerDifferential S.R (Localization.AtPrime S.maximalIdealPreimage)))
    (hbT : ∀ i, bT i = KaehlerDifferential.D S.R _ (a i)) :
    ∃ z : Localization.Away f,
      z ∉ S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f)) ∧
      Algebra.Smooth S.R (Localization.Away z) ∧
      RingTheory.Sequence.IsRegular (Localization.Away z)
        ((algebraMap S.R (Localization.Away f) π :: List.ofFn g).map
          (algebraMap (Localization.Away f) (Localization.Away z))) ∧
      (Ideal.span ({algebraMap S.R (Localization.Away f) π} : Set _) ⊔
          Ideal.span (Set.range g)).map
          (algebraMap (Localization.Away f) (Localization.Away z)) =
        (S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f))).map
          (algebraMap (Localization.Away f) (Localization.Away z)) ∧
      Function.Bijective (LocalizedModule.map (Submonoid.powers z)
        (Finsupp.linearCombination (Localization.Away f)
          fun i => KaehlerDifferential.D S.R (Localization.Away f) (u i))) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  let B := Localization.Away f
  let q : Ideal B := S.maximalIdealPreimage.map (algebraMap S.A B)
  have : IsNoetherianRing S.A := Algebra.FiniteType.isNoetherianRing S.R S.A
  have : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) B inferInstance
  have : q.IsPrime := isPrime_map_algebraMap_of_notMem S.maximalIdealPreimage hf
  let : Algebra B T :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers f)
      S.maximalIdealPreimage.primeCompl (Submonoid.powers_le.mpr hf)
  have : IsScalarTower S.A B T :=
    IsLocalization.localization_isScalarTower_of_submonoid_le ..
  have : IsScalarTower S.R B T := .to₁₃₄ _ S.A _ _
  have : IsLocalization.AtPrime T q :=
    isLocalization_atPrime_map_of_notMem (B := B) (C := T) hf
  have hg' : ∀ i, algebraMap B T (g i) = g₀ i := hg
  let J : Ideal B := Ideal.span ({algebraMap S.R B π} : Set B) ⊔ Ideal.span (Set.range g)
  have hJq : J ≤ q := span_uniformizer_sup_le_map S π hπ hf g₀ hgen g hg
  have hxsq : ∀ x ∈ algebraMap S.R B π :: List.ofFn g, x ∈ q := by
    intro x hx
    simp only [List.mem_cons, List.mem_ofFn'] at hx
    rcases hx with rfl | ⟨i, rfl⟩
    exacts [hJq (Ideal.mem_sup_left (Ideal.subset_span (Set.mem_singleton _))),
      hJq (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))]
  have hxs : (algebraMap S.R B π :: List.ofFn g).map (algebraMap B T) =
      algebraMap S.R T π :: List.ofFn g₀ :=
    map_cons_ofFn_eq _ g g₀ (IsScalarTower.algebraMap_apply S.R B T π).symm hg'
  obtain ⟨h, hh, hregh⟩ :=
    exists_away_isRegular_of_isLocalization_atPrime q _ (by rwa [hxs])
  obtain ⟨k, hk, hJk⟩ := exists_away_map_eq_of_isLocalization_atPrime q J hJq
    (map_span_uniformizer_sup S π hf g₀ hgen g hg)
  obtain ⟨t, ht, hsmt⟩ := exists_away_smooth_of_smoothAt S hsm hf
  obtain ⟨s, hs, hbij⟩ := exists_bijective_linearCombination_D S hf a u hu bT hbT
  obtain ⟨hz, hsmz, hregz, hJz⟩ :=
    away_mul_of_four (R := S.R) q _ hxsq J hh hk ht hs hregh hJk
  exact ⟨_, hz, hsmz, hregz, hJz, hbij _ (dvd_mul_left s (h * k * t))⟩

private lemma algebraMap_uniformizer_away_algEquiv (S : NeronSituation) (π : S.R) {f : S.A}
    {z : Localization.Away f} {F : S.A}
    (eF : Localization.Away F ≃ₐ[S.A] Localization.Away z) :
    eF (algebraMap S.R (Localization.Away F) π) =
      algebraMap (Localization.Away f) (Localization.Away z)
        (algebraMap S.R (Localization.Away f) π) := by
  rw [IsScalarTower.algebraMap_apply S.R S.A (Localization.Away F), eF.commutes,
    IsScalarTower.algebraMap_apply S.A (Localization.Away f) (Localization.Away z),
    IsScalarTower.algebraMap_apply S.R S.A (Localization.Away f)]

private lemma isRegular_of_away_algEquiv (S : NeronSituation) (π : S.R) {f : S.A}
    {z : Localization.Away f} {F : S.A}
    (eF : Localization.Away F ≃ₐ[S.A] Localization.Away z) {c : ℕ}
    (g : Fin c → Localization.Away f)
    (hreg : RingTheory.Sequence.IsRegular (Localization.Away z)
      ((algebraMap S.R (Localization.Away f) π :: List.ofFn g).map
        (algebraMap (Localization.Away f) (Localization.Away z)))) :
    RingTheory.Sequence.IsRegular (Localization.Away F)
      (algebraMap S.R (Localization.Away F) π ::
        List.ofFn fun i => eF.symm (algebraMap _ (Localization.Away z) (g i))) := by
  have hπeq := algebraMap_uniformizer_away_algEquiv S π eF
  apply (isRegular_ringEquiv_congr eF.toRingEquiv _).mpr
  have hseq : (algebraMap S.R (Localization.Away F) π ::
        List.ofFn fun i => eF.symm (algebraMap _ (Localization.Away z) (g i))).map
          eF.toRingEquiv =
      (algebraMap S.R (Localization.Away f) π :: List.ofFn g).map
        (algebraMap (Localization.Away f) (Localization.Away z)) := by
    refine (map_cons_ofFn_eq eF.toRingEquiv _ _ hπeq fun i => eF.apply_symm_apply _).trans ?_
    simp [List.map_ofFn, Function.comp_def]
  rwa [hseq]

private lemma map_maximalIdealPreimage_of_away_algEquiv (S : NeronSituation) (π : S.R)
    {f : S.A} {z : Localization.Away f} {F : S.A}
    (eF : Localization.Away F ≃ₐ[S.A] Localization.Away z) {c : ℕ}
    (g : Fin c → Localization.Away f)
    (hJz : (Ideal.span ({algebraMap S.R (Localization.Away f) π} : Set _) ⊔
          Ideal.span (Set.range g)).map
          (algebraMap (Localization.Away f) (Localization.Away z)) =
        (S.maximalIdealPreimage.map (algebraMap S.A (Localization.Away f))).map
          (algebraMap (Localization.Away f) (Localization.Away z))) :
    Ideal.map (algebraMap S.A (Localization.Away F)) S.maximalIdealPreimage =
      Ideal.span ({algebraMap S.R (Localization.Away F) π} : Set _) ⊔
        Ideal.span (Set.range fun i => eF.symm (algebraMap _ (Localization.Away z) (g i))) := by
  let B := Localization.Away f
  let C := Localization.Away z
  let D := Localization.Away F
  let gF : Fin c → D := fun i => eF.symm (algebraMap B C (g i))
  apply ideal_map_injective_ringEquiv eF.toRingEquiv
  show Ideal.map eF.toRingEquiv.toRingHom
      (Ideal.map (algebraMap S.A D) S.maximalIdealPreimage) =
    Ideal.map eF.toRingEquiv.toRingHom
      (Ideal.span ({algebraMap S.R D π} : Set D) ⊔ Ideal.span (Set.range gF))
  rw [map_map_algebraMap_algEquiv, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
  have hπC : eF '' ({algebraMap S.R D π} : Set D) =
      {algebraMap B C (algebraMap S.R B π)} := by
    simpa only [Set.image_singleton] using congrArg (fun x : C => ({x} : Set C))
      (algebraMap_uniformizer_away_algEquiv S π eF)
  have hgC : eF '' Set.range gF = (algebraMap B C) '' Set.range g := by
    rw [image_range_eq_range _ _ (fun i => algebraMap B C (g i)) fun i => eF.apply_symm_apply _]
    exact Set.range_comp _ _
  show Ideal.map (algebraMap S.A C) S.maximalIdealPreimage =
    Ideal.span (eF '' ({algebraMap S.R D π} : Set D)) ⊔ Ideal.span (eF '' Set.range gF)
  rw [hπC, hgC, IsScalarTower.algebraMap_eq S.A B C, ← Ideal.map_map]
  simpa only [Ideal.map_sup, Ideal.map_span, Set.image_singleton] using hJz.symm

private lemma exists_basis_of_away_algEquiv (S : NeronSituation) {f : S.A}
    {z : Localization.Away f} {F : S.A}
    (eF : Localization.Away F ≃ₐ[S.A] Localization.Away z) {n : ℕ}
    (u : Fin n → Localization.Away f)
    (hbij : Function.Bijective (LocalizedModule.map (Submonoid.powers z)
      (Finsupp.linearCombination (Localization.Away f)
        fun i => KaehlerDifferential.D S.R (Localization.Away f) (u i)))) :
    ∃ b : Module.Basis (Fin n) (Localization.Away F)
        (KaehlerDifferential S.R (Localization.Away F)),
      ∀ i, b i = KaehlerDifferential.D S.R (Localization.Away F)
        (eF.symm (algebraMap _ (Localization.Away z) (u i))) := by
  let B := Localization.Away f
  let C := Localization.Away z
  let D := Localization.Away F
  let : Algebra B D := ((eF.symm.toRingHom).comp (algebraMap B C)).toAlgebra
  let eFB : D ≃ₐ[B] C :=
    { __ := eF
      commutes' := fun b => eF.apply_symm_apply _ }
  have : IsLocalization.Away z D :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers z) eFB.symm
  have : IsScalarTower S.R B D := IsScalarTower.of_algebraMap_eq fun r => by
    apply eF.injective
    show eF (algebraMap S.R D r) = eF (eF.symm (algebraMap B C (algebraMap S.R B r)))
    rw [eF.apply_symm_apply, IsScalarTower.algebraMap_apply S.R S.A D, eF.commutes,
      IsScalarTower.algebraMap_apply S.R S.A B]
    exact IsScalarTower.algebraMap_apply S.A B C (algebraMap S.R S.A r)
  let w : Fin n → KaehlerDifferential S.R B := fun i => KaehlerDifferential.D S.R B (u i)
  let eB : (Fin n →₀ B) →ₗ[B] KaehlerDifferential S.R B := Finsupp.linearCombination B w
  let l₁D : (Fin n →₀ B) →ₗ[B] (Fin n →₀ D) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap B D)
  let l₂D : KaehlerDifferential S.R B →ₗ[B] KaehlerDifferential S.R D :=
    KaehlerDifferential.map S.R S.R B D
  let eD : (Fin n →₀ D) →ₗ[D] KaehlerDifferential S.R D :=
    IsLocalizedModule.mapExtendScalars (Submonoid.powers z) l₁D l₂D D eB
  have hbijD : Function.Bijective eD :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective l₁D l₂D).mpr hbij
  let bD : Module.Basis (Fin n) D (KaehlerDifferential S.R D) :=
    Module.Basis.ofRepr (LinearEquiv.ofBijective eD hbijD).symm
  have hbD (i : Fin n) : bD i = KaehlerDifferential.D S.R D (algebraMap B D (u i)) := by
    show (IsLocalizedModule.map (Submonoid.powers z) l₁D l₂D eB)
      (Finsupp.single i 1) = _
    rw [show eB = Finsupp.linearCombination B w from rfl,
      IsLocalizedModule.map_linearCombination]
    simp [w, l₂D]
  exact ⟨bD, hbD⟩

private lemma exists_local_parameters_and_differential_basis
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    ∃ (f : S.A), f ∉ S.maximalIdealPreimage ∧
      Algebra.Smooth S.R (Localization.Away f) ∧
      ∃ (c : ℕ) (g : Fin c → Localization.Away f),
        ringKrullDim
            ((Localization.AtPrime S.maximalIdealPreimage) ⧸
              Ideal.span ({algebraMap S.R
                (Localization.AtPrime S.maximalIdealPreimage) π} : Set _)) = c ∧
        Ideal.map (algebraMap S.A (Localization.Away f)) S.maximalIdealPreimage =
            Ideal.span ({algebraMap S.R (Localization.Away f) π} : Set _) ⊔
              Ideal.span (Set.range g) ∧
        RingTheory.Sequence.IsRegular (Localization.Away f)
          (algebraMap S.R (Localization.Away f) π :: List.ofFn g) ∧
        (∀ i, g i ∈ Ideal.map
              (algebraMap S.A (Localization.Away f)) S.maximalIdealPreimage) ∧
        ∃ (n : ℕ)
            (b : Module.Basis (Fin n) (Localization.Away f)
              (KaehlerDifferential S.R (Localization.Away f)))
            (e : Fin c → Fin n),
          Function.Injective e ∧
            ∀ i, b (e i) =
              KaehlerDifferential.D S.R (Localization.Away f) (g i) := by
  let T := Localization.AtPrime S.maximalIdealPreimage
  have : IsRegularLocalRing T := atPrime_isRegularLocalRing_of_smoothAt S hsm
  have hπmem : algebraMap S.R T π ∈ IsLocalRing.maximalIdeal T := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal S.maximalIdealPreimage T]
    exact Ideal.mem_map_of_mem _ (uniformizer_mem_maximalIdealPreimage S π hπ)
  obtain ⟨c, g₀, hdim, hgen, hreg⟩ :=
    exists_regular_parameters_of_regular_quotient T (algebraMap S.R T π)
      hπmem (uniformizer_atPrime_isSMulRegular S π hπ)
      (uniformizer_quotient_atPrime_isRegularLocalRing S π hπ hsm)
  obtain ⟨n, a, e, he, hae, bT, hbT⟩ := exists_basis_D_extend_atPrime S hsm g₀
    (linearIndependent_one_tmul_D_atPrime S π hπ hsep hsm g₀ hdim hgen)
  obtain ⟨f, hf, u, hu⟩ := exists_away_lifts_of_atPrime S.maximalIdealPreimage a
  obtain ⟨z, hz, hsmz, hregz, hJz, hbij⟩ :=
    exists_away_regular_smooth_bijective S π hπ hsm g₀ hgen hreg hf (fun i => u (e i))
      (fun i => (hu (e i)).trans (hae i)) a u hu bT hbT
  obtain ⟨F, hF, ⟨eF⟩⟩ := exists_away_algEquiv_of_away (C := Localization.Away z)
    S.maximalIdealPreimage f hf z hz
  obtain ⟨b, hb⟩ := exists_basis_of_away_algEquiv S eF u hbij
  have hIF := map_maximalIdealPreimage_of_away_algEquiv S π eF _ hJz
  refine ⟨F, hF, Algebra.Smooth.of_equiv (eF.restrictScalars S.R).symm, c, _, hdim, hIF,
    isRegular_of_away_algEquiv S π eF _ hregz, fun i => ?_, n, b, e, he, fun i => hb (e i)⟩
  rw [hIF]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)

/-- **Local parameters for a smooth Néron chart.** In a Néron situation with uniformizer `π`,
smoothness of `A` over `R` at `𝔭` and separability of the residue-field extension
`κ(R) → κ(Λ)` give, after localizing `A` away from an element outside `𝔭`, local parameters
`g₁, …, g_c` for the closed fibre: their number is the Krull dimension of the closed fibre of
the local ring at `𝔭`, together with `π` they generate `𝔭`, the sequence `π, g₁, …, g_c` is
regular, they present the affine blowup chart `A[𝔭/π]` as
`A[y₁, …, y_c]/(π y₁ - g₁, …, π y_c - g_c)` with `yᵢ` corresponding to `gᵢ/π`, and their
differentials are part of a basis of the module of relative differentials. -/
theorem exists_local_parameters_of_smoothAt
    (S : NeronSituation) (π : S.R)
    (hπ : IsLocalRing.maximalIdeal S.R = Ideal.span ({π} : Set S.R))
    (hsep : @Algebra.IsSeparableExtension
      (IsLocalRing.maximalIdeal S.R).ResidueField
      (IsLocalRing.maximalIdeal S.Λ).ResidueField _ _ S.residueFieldExtension)
    (hsm : Algebra.SmoothAt S.R S.A S.maximalIdealPreimage) :
    ∃ (f : S.A), f ∉ S.maximalIdealPreimage ∧
      Algebra.Smooth S.R (Localization.Away f) ∧
      ∃ (c : ℕ) (g : Fin c → Localization.Away f),
        ringKrullDim
            ((Localization.AtPrime S.maximalIdealPreimage) ⧸
              Ideal.span ({algebraMap S.R
                (Localization.AtPrime S.maximalIdealPreimage) π} : Set _)) = c ∧
        Ideal.map (algebraMap S.A (Localization.Away f)) S.maximalIdealPreimage =
            Ideal.span ({algebraMap S.R (Localization.Away f) π} : Set _) ⊔
              Ideal.span (Set.range g) ∧
        RingTheory.Sequence.IsRegular (Localization.Away f)
          (algebraMap S.R (Localization.Away f) π :: List.ofFn g) ∧
        ∃ (hg : ∀ i, g i ∈ Ideal.map
              (algebraMap S.A (Localization.Away f)) S.maximalIdealPreimage),
          Nonempty
            {e : affineBlowupAlgebra
                  (Ideal.map (algebraMap S.A (Localization.Away f))
                    S.maximalIdealPreimage)
                  (algebraMap S.R (Localization.Away f) π)
                  (Localization.Away (algebraMap S.R (Localization.Away f) π))
                    ≃ₐ[Localization.Away f]
                  MvPolynomial (Fin c) (Localization.Away f) ⧸
                    Ideal.span (Set.range fun i : Fin c ↦
                      MvPolynomial.C (algebraMap S.R (Localization.Away f) π) *
                          MvPolynomial.X i -
                        MvPolynomial.C (g i)) //
              ∀ i, e (affineBlowupFraction _ _ _ (hg i)) =
                Ideal.Quotient.mk _ (MvPolynomial.X i)} ∧
        ∃ (n : ℕ)
            (b : Module.Basis (Fin n) (Localization.Away f)
              (KaehlerDifferential S.R (Localization.Away f)))
            (e : Fin c → Fin n),
          Function.Injective e ∧
            ∀ i, b (e i) =
              KaehlerDifferential.D S.R (Localization.Away f) (g i) := by
  obtain ⟨f, hf, hsmf, c, g, hdim, hI, hreg, hg, n, b, e, he, hb⟩ :=
    exists_local_parameters_and_differential_basis S π hπ hsep hsm
  refine ⟨f, hf, hsmf, c, g, hdim, hI, hreg, hg, ?_, n, b, e, he, hb⟩
  exact exists_blowupChart_algEquiv_fraction _ _ _ hI hreg hg

end Stacks.Smoothing

end
