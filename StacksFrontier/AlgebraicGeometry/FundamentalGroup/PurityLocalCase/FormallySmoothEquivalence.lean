module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.ExtendFiniteEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityPowerSeriesEquivalence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PuncturedSpectrum.Defs
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.FormallySmooth.Topological

/-!
# Ramanujam--Samuel for finite étale covers of a formally smooth local algebra

Let `A → B` be a local homomorphism of Noetherian local rings. Assume `A` has depth at least
two, that `A → B` is formally smooth for the `𝔪_B`-adic topology, and that
`dim(B) > dim(A)`. For an open `V ⊆ Y = Spec B` which contains every prime `𝔮` of `B` with
`𝔮 ∩ A ≠ 𝔪_A` and contains the prime `𝔪_A B`, the functor `FÉt_Y ⟶ FÉt_V` is an equivalence;
in particular purity holds for `B`. This is [Stacks, Tag 0EYC], whose complete statement is
`isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic_of_depth` and
`hasPurity_of_formallySmoothNAdic` in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FormallySmoothPurity`. This file
supplies the source's first paragraph, the fully faithful half used there.

The source's first paragraph is proved here, and so is the density of `V` that the first
paragraph's appeal to [Stacks, Tag 0BQF] needs but the source does not verify. A prime `𝔮` of
`B` outside `V` lies over `𝔪_A`, so `A ⟶ B_𝔮` is a flat local homomorphism and therefore
`depth(B_𝔮) ≥ 2` by [Stacks, Tag 0337]; that is
`two_le_depth_of_isLocalization_atPrime_of_flat`, which feeds the local hypothesis of
[Stacks, Tag 0BQF] through [Stacks, Tag 0BLR].

## Main results

* `Stacks.FundamentalGroup.two_le_depth_of_isLocalization_atPrime_of_flat` — the local ring of
  `B` at a prime lying over `𝔪_A` has depth at least two.
* `Stacks.FundamentalGroup.two_le_depth_stalk_of_notMem_of_flat` — the same for the stalk of
  `Spec B` at a point outside such an open `V`.
* `Stacks.FundamentalGroup.map_maximalIdeal_ne_maximalIdeal_of_ringKrullDim_lt` — if
  `dim(A) < dim(B)` then `𝔪_A B ≠ 𝔪_B`.
* `Stacks.FundamentalGroup.mem_of_mem_minimalPrimes_of_two_le_depth` and
  `Stacks.FundamentalGroup.dense_of_forall_comap_ne_maximalIdeal_mem` — an open as in the tag's
  condition (1) contains every minimal prime of `B`, hence is dense.
* `Stacks.FundamentalGroup.fullyFaithful_finiteEtaleBaseChange_of_flat` — the source's first
  paragraph, unconditionally.
* `Stacks.FundamentalGroup.isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic` — the
  equivalence assembled from the fully faithful half, given flatness and essential surjectivity
  as arguments; both are proved in `FormallySmoothPurity` (flatness from formal smoothness by
  [Stacks, Tag 07NP], essential surjectivity by
  `essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic`), where
  `isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic_of_depth` supplies them.
* `Stacks.FundamentalGroup.mem_puncturedSpectrum_of_comap_ne_maximalIdeal_of_isLocalHom` and
  `Stacks.FundamentalGroup.mem_puncturedSpectrum_of_eq_map_maximalIdeal_of_ringKrullDim_lt` —
  the punctured spectrum of `B` is an open as in the tag; `hasPurity_of_formallySmoothNAdic`
  uses them for the tag's "in particular" clause.

Unlike the power series case [Stacks, Tag 0EYA], the density of `V` is proved from the depth
hypothesis and the flatness of `A → B`, see `dense_of_forall_comap_ne_maximalIdeal_mem`.

## References

* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 00LK](https://stacks.math.columbia.edu/tag/00LK)
* [Stacks Project, Tag 0BLR](https://stacks.math.columbia.edu/tag/0BLR)
* [Stacks Project, Tag 0BQF](https://stacks.math.columbia.edu/tag/0BQF)
* [Stacks Project, Tag 0EYA](https://stacks.math.columbia.edu/tag/0EYA)
* [Stacks Project, Tag 0EYB](https://stacks.math.columbia.edu/tag/0EYB)
* [Stacks Project, Tag 0EYC](https://stacks.math.columbia.edu/tag/0EYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

namespace Stacks.FundamentalGroup

/-! ### Depth at a prime lying over the maximal ideal of the base -/

/-- **Depth two at a prime of `B` lying over `𝔪_A`.** Let `A` be a Noetherian local ring of
depth at least two, let `B` be a flat Noetherian `A`-algebra and let `𝔮` be a prime of `B`
whose contraction to `A` is `𝔪_A`. Then any localization of `B` at `𝔮` has depth at least two.

Flatness of `B` over `A` and of `B_𝔮` over `B` make `A ⟶ B_𝔮` a flat local homomorphism, and
[Stacks, Tag 0337] writes `depth(B_𝔮)` as `depth(A)` plus the depth of the fibre ring. -/
public theorem two_le_depth_of_isLocalization_atPrime_of_flat (A B : Type u) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (q : Ideal B) [q.IsPrime] (hq : q.comap (algebraMap A B) = maximalIdeal A)
    (Bq : Type u) [CommRing Bq] [IsLocalRing Bq] [Algebra B Bq]
    [IsLocalization.AtPrime Bq q] :
    (2 : ℕ∞) ≤ Module.depth Bq (maximalIdeal Bq) Bq := by
  have : IsNoetherianRing Bq :=
    IsLocalization.isNoetherianRing q.primeCompl Bq inferInstance
  let : Algebra A Bq := ((algebraMap B Bq).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B Bq := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat B Bq := IsLocalization.flat Bq q.primeCompl
  have : Module.Flat A Bq := Module.Flat.trans A B Bq
  have : IsLocalHom (algebraMap A Bq) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hu
    have hmem : algebraMap A B a ∈ q := by
      have h : a ∈ maximalIdeal A := (mem_maximalIdeal a).2 hu
      rw [← hq, Ideal.mem_comap] at h
      exact h
    have hmax : algebraMap A Bq a ∈ maximalIdeal Bq :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff Bq q (algebraMap A B a)).2 hmem
    exact (mem_maximalIdeal _).1 hmax ha
  rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal A Bq]
  exact hdepth.trans le_self_add

/-- **Depth two at the stalks outside `V`.** Let `A` be a Noetherian local ring of depth at
least two, let `B` be a flat Noetherian `A`-algebra and let `V` be an open of `Spec B`
containing every prime of `B` whose contraction to `A` is not `𝔪_A`. Then the local ring of
`Spec B` at a point outside `V` has depth at least two. -/
public theorem two_le_depth_stalk_of_notMem_of_flat (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V)
    (x : Spec (.of B)) (hx : x ∉ V) :
    (2 : ℕ∞) ≤ Module.depth ((Spec (.of B)).presheaf.stalk x)
      (maximalIdeal ((Spec (.of B)).presheaf.stalk x)) ((Spec (.of B)).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let : Algebra B ((Spec (.of B)).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra (CommRingCat.of B) x
  have : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (CommRingCat.of B) x
  exact two_le_depth_of_isLocalization_atPrime_of_flat A B hdepth x.asIdeal
    (not_ne_iff.1 fun h => hx (hV₁ x h)) _

/-! ### The ideal `𝔪_A B` is not the maximal ideal of `B` -/

/-- **`𝔪_A B ≠ 𝔪_B` when `dim(A) < dim(B)`.** If the maximal ideal of `B` were generated by the
image of `𝔪_A`, then a system of parameters of `A` — a finite set of `dim(A)` elements over
which `𝔪_A` is minimal, Krull's height theorem in the form
`Ideal.exists_finset_card_eq_height_of_isNoetherianRing` — would push forward to a finite set of
`dim(A)` elements of `B` over which `𝔪_B` is minimal, whence `dim(B) ≤ dim(A)`.

Indeed `𝔪_A` is the only prime of `A` containing the system of parameters, so some power of
`𝔪_A` lies in the ideal it generates; the same power of `𝔪_B = 𝔪_A B` then lies in the ideal
generated by the images. -/
public theorem map_maximalIdeal_ne_maximalIdeal_of_ringKrullDim_lt (A B : Type u) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Algebra A B] (hdim : ringKrullDim A < ringKrullDim B) :
    Ideal.map (algebraMap A B) (maximalIdeal A) ≠ maximalIdeal B := by
  classical
  intro h
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal A)
  have hrad : maximalIdeal A ≤ (Ideal.span (s : Set A)).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro J ⟨hJle, hJp⟩
    exact hs.2 ⟨hJp, hJle⟩ (le_maximalIdeal hJp.ne_top)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  set t : Finset B := s.image (algebraMap A B) with ht
  have hspan : Ideal.span (t : Set B) = Ideal.map (algebraMap A B) (Ideal.span (s : Set A)) := by
    rw [Ideal.map_span, ht, Finset.coe_image]
  have hpow : maximalIdeal B ^ k ≤ Ideal.span (t : Set B) := by
    rw [hspan, ← h, ← Ideal.map_pow]
    exact Ideal.map_mono hk
  have hle : Ideal.span (t : Set B) ≤ maximalIdeal B := by
    rw [hspan, ← h]
    exact Ideal.map_mono hs.1.2
  have hmin : maximalIdeal B ∈ (Ideal.span (t : Set B)).minimalPrimes := by
    refine ⟨⟨inferInstance, hle⟩, ?_⟩
    rintro q ⟨hqp, hqle⟩ -
    exact hqp.le_of_pow_le (hpow.trans hqle)
  have hheight : (maximalIdeal B).height ≤ (maximalIdeal A).height := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    rw [← hcard]
    exact_mod_cast Nat.cast_le.2 Finset.card_image_le
  have hdimle : ringKrullDim B ≤ ringKrullDim A := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast WithBot.coe_le_coe.2 hheight
  exact absurd hdim (not_lt.2 hdimle)

/-! ### Density of an open satisfying the tag's condition (1) -/

/-- **An open as in the tag's condition (1) contains every minimal prime of `B`.** A minimal
prime `𝔭` of `B` lying over `𝔪_A` would make `B_𝔭` a local ring of dimension zero whose depth
is at least two by `two_le_depth_of_isLocalization_atPrime_of_flat`, contradicting
[Stacks, Tag 00LK]. -/
public theorem mem_of_mem_minimalPrimes_of_two_le_depth (A B : Type u) [CommRing A] [CommRing B]
    [IsLocalRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V)
    (p : PrimeSpectrum B) (hp : p.asIdeal ∈ minimalPrimes B) : p ∈ V := by
  by_cases hcomap : p.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A
  · exact hV₁ p hcomap
  rw [not_not] at hcomap
  exfalso
  have : p.asIdeal.IsPrime := p.isPrime
  have hdepth2 : (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) :=
    two_le_depth_of_isLocalization_atPrime_of_flat A B hdepth p.asIdeal hcomap _
  have hdim0 : ringKrullDim (Localization.AtPrime p.asIdeal) = 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),
      Ideal.height_eq_zero_iff.2 hp]
    rfl
  have hsmul : (maximalIdeal (Localization.AtPrime p.asIdeal)) •
      (⊤ : Submodule (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) ≠ ⊤ := by
    rw [Ideal.smul_top_eq_map]
    simpa using (maximalIdeal.isMaximal (Localization.AtPrime p.asIdeal)).ne_top
  have hle := Module.depth_le_supportDim (Localization.AtPrime p.asIdeal)
    (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) hsmul
  rw [Module.supportDim_self_eq_ringKrullDim, hdim0] at hle
  have hd0 : Module.depth (Localization.AtPrime p.asIdeal)
      (maximalIdeal (Localization.AtPrime p.asIdeal)) (Localization.AtPrime p.asIdeal) ≤
      (0 : ℕ∞) := by
    have hcast : ((Module.depth (Localization.AtPrime p.asIdeal)
        (maximalIdeal (Localization.AtPrime p.asIdeal))
        (Localization.AtPrime p.asIdeal) : ℕ∞) : WithBot ℕ∞) ≤ ((0 : ℕ∞) : WithBot ℕ∞) := by
      simpa using hle
    exact_mod_cast hcast
  have h20 : (2 : ℕ∞) ≤ 0 := hdepth2.trans hd0
  rw [le_zero_iff] at h20
  exact absurd h20 (by decide)

/-- **An open as in the tag's condition (1) is dense in `Spec B`.** Every prime of `B` contains
a minimal prime, and the minimal primes lie in `V` by
`mem_of_mem_minimalPrimes_of_two_le_depth`. -/
public theorem dense_of_forall_comap_ne_maximalIdeal_mem (A B : Type u) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V) :
    Dense (V : Set (Spec (.of B))) := by
  intro q
  have : q.asIdeal.IsPrime := q.isPrime
  obtain ⟨p, hp, hple⟩ :=
    Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := q.asIdeal) bot_le
  have hpprime : p.IsPrime := hp.1.1
  have hptV : (⟨p, hpprime⟩ : PrimeSpectrum B) ∈ V :=
    mem_of_mem_minimalPrimes_of_two_le_depth A B hdepth V hV₁ ⟨p, hpprime⟩ hp
  have hmem : q ∈ closure ({(⟨p, hpprime⟩ : PrimeSpectrum B)} : Set (PrimeSpectrum B)) := by
    rw [PrimeSpectrum.closure_singleton]
    exact hple
  exact closure_mono (Set.singleton_subset_iff.2 hptV) hmem

/-! ### The fully faithful half -/

/-- **The first paragraph of [Stacks, Tag 0EYC].** Let `A` be a Noetherian local ring of depth
at least two, let `B` be a flat Noetherian local `A`-algebra and let `V` be an open of `Spec B`
containing every prime of `B` whose contraction to `A` is not `𝔪_A`. Then base change of finite
étale covers along `V ⟶ Spec B` is fully faithful.

A point of `Spec B` outside `V` lies over `𝔪_A`, so its local ring has depth at least two by
`two_le_depth_stalk_of_notMem_of_flat`, which is flatness fed to [Stacks, Tag 0337];
`isConnectedPuncturedStrictHenselization_of_two_le_depth` ([Stacks, Tag 0BLR]) turns that into
the local hypothesis of [Stacks, Tag 0BQF]. The density of `V` that [Stacks, Tag 0BQF] also
requires — and that the source does not verify — is
`dense_of_forall_comap_ne_maximalIdeal_mem`. -/
public theorem fullyFaithful_finiteEtaleBaseChange_of_flat (A B : Type u) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V) :
    Nonempty (finiteEtaleBaseChange V.ι).FullyFaithful := by
  have : IsNoetherian (Spec (.of B)) := inferInstance
  exact fullyFaithful_finiteEtaleBaseChange_of_dense_of_noetherianSpace
    (Spec (.of B)) V (dense_of_forall_comap_ne_maximalIdeal_mem A B hdepth V hV₁) fun x hx =>
      isConnectedPuncturedStrictHenselization_of_two_le_depth _
        (two_le_depth_stalk_of_notMem_of_flat A B hdepth V hV₁ x hx)

/-! ### Tag 0EYC -/

/-- **Assembling the equivalence of [Stacks, Tag 0EYC].** Let `A → B` be a local homomorphism
of Noetherian local rings with `depth(A) ≥ 2`, with `A → B` formally smooth for the `𝔪_B`-adic
topology, and with `dim(B) > dim(A)`, and let `V ⊆ Y = Spec B` be an open as in the tag
(`hV₁`, `hV₂`). Given flatness of `A → B` (`hflat`) and essential surjectivity of the
restriction functor (`hessSurj`), the restriction functor `FÉt_Y ⟶ FÉt_V` is an equivalence.

The fully faithful half is the source's first paragraph,
`fullyFaithful_finiteEtaleBaseChange_of_flat`. Both remaining arguments are theorems of the
library: flatness follows from formal smoothness ([Stacks, Tag 07NP]), and essential
surjectivity is `essSurj_finiteEtaleBaseChange_of_formallySmoothNAdic`. The tag itself, with
neither argument, is `isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic_of_depth`, and
its "in particular" clause is `hasPurity_of_formallySmoothNAdic`. -/
public theorem isEquivalence_finiteEtaleBaseChange_of_formallySmoothNAdic (A B : Type u)
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) A)
    (hsmooth : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B))
    (hdim : ringKrullDim A < ringKrullDim B)
    (V : (Spec (.of B)).Opens)
    (hV₁ : ∀ q : PrimeSpectrum B, q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A → q ∈ V)
    (hV₂ : ∀ q : PrimeSpectrum B,
      q.asIdeal = Ideal.map (algebraMap A B) (maximalIdeal A) → q ∈ V)
    (hflat : Module.Flat A B)
    (hessSurj : (finiteEtaleBaseChange V.ι).EssSurj) :
    (finiteEtaleBaseChange V.ι).IsEquivalence := by
  -- The formal smoothness hypothesis, the dimension hypothesis and the tag's condition (2) are
  -- consumed by the proofs of `hflat` and `hessSurj` in `FormallySmoothPurity`.
  have : RingHom.FormallySmoothNAdic.{u} (algebraMap A B) (maximalIdeal B) := hsmooth
  have : ringKrullDim A < ringKrullDim B := hdim
  have : ∀ q : PrimeSpectrum B,
      q.asIdeal = Ideal.map (algebraMap A B) (maximalIdeal A) → q ∈ V := hV₂
  have : Module.Flat A B := hflat
  obtain ⟨hff⟩ := fullyFaithful_finiteEtaleBaseChange_of_flat A B hdepth V hV₁
  exact { faithful := hff.faithful, full := hff.full, essSurj := hessSurj }

/-! ### The punctured spectrum of `B` -/

/-- **Condition (1) of [Stacks, Tag 0EYC] for the punctured spectrum of `B`.** A prime of `B`
whose contraction to `A` is not `𝔪_A` is not the closed point of `Spec B`, because the closed
point contracts to `𝔪_A`. -/
public theorem mem_puncturedSpectrum_of_comap_ne_maximalIdeal_of_isLocalHom (A B : Type u)
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] (q : PrimeSpectrum B)
    (hq : q.asIdeal.comap (algebraMap A B) ≠ maximalIdeal A) :
    q ∈ Stacks.puncturedSpectrum B := by
  refine (Stacks.mem_puncturedSpectrum _).2 fun hc => hq ?_
  rw [show q.asIdeal = maximalIdeal B from congrArg PrimeSpectrum.asIdeal hc]
  exact IsLocalRing.maximalIdeal_comap (algebraMap A B)

/-- **Condition (2) of [Stacks, Tag 0EYC] for the punctured spectrum of `B`.** With
`dim(A) < dim(B)` the ideal `𝔪_A B` is not the maximal ideal of `B`, by
`map_maximalIdeal_ne_maximalIdeal_of_ringKrullDim_lt`, so a prime equal to `𝔪_A B` is not the
closed point of `Spec B`. -/
public theorem mem_puncturedSpectrum_of_eq_map_maximalIdeal_of_ringKrullDim_lt (A B : Type u)
    [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A]
    [IsNoetherianRing B] [Algebra A B] (hdim : ringKrullDim A < ringKrullDim B)
    (q : PrimeSpectrum B) (hq : q.asIdeal = Ideal.map (algebraMap A B) (maximalIdeal A)) :
    q ∈ Stacks.puncturedSpectrum B := by
  refine (Stacks.mem_puncturedSpectrum _).2 fun hc => ?_
  exact map_maximalIdeal_ne_maximalIdeal_of_ringKrullDim_lt A B hdim
    (hq.symm.trans (congrArg PrimeSpectrum.asIdeal hc))

end Stacks.FundamentalGroup

end
