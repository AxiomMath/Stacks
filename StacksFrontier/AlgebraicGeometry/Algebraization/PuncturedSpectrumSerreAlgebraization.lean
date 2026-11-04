module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.StalkOfIdealOnOpen
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ExtensionPrincipalDepthInequalities
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.UbiquityDualizingComplexes.AdicCompletion
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Serre.Defs
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import StacksFrontier.RingTheory.AdicCompletion.QuotientDimensionSplit

/-!
# Algebraization on the punctured spectrum from Serre's condition on the completed stalks

Let `(A, 𝔪)` be a Noetherian local ring with a dualizing complex, complete with respect to an
element `f ∈ 𝔪`, let `U` be the punctured spectrum of `A`, and let `(ℱₙ)` be an object of
`Coh(U, f𝒪_U)`. [Stacks, Tag 0EJC] asserts that `(ℱₙ)` is the completion of a coherent
`𝒪_U`-module as soon as, at every `y ∈ U ∩ V(f)` closed in `U` — equivalently with
`dim(closure {y}) = 1` — the `𝒪_{X,y}^∧`-module `ℱ_y^∧` satisfies

1. `ℱ_y^∧[1/f]` is `(S₂)` as an `𝒪_{X,y}^∧[1/f]`-module, and
2. `dim(𝒪_{X,y}^∧/𝔭) ≥ 3` for every `𝔭 ∈ Ass(ℱ_y^∧[1/f])`.

The source deduces this from [Stacks, Tag 0EJ9] and [Stacks, Tag 0EJA] in a single sentence,
and leaves implicit the step that turns (1) and (2) into the hypothesis those lemmas take,
namely the pointwise bound

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2`

for every prime `𝔭` of `𝒪_{X,y}^∧` not containing `f𝒪_{X,y}^∧`. That step is the mathematical
content of this file, and it is proved here in full.

The argument is the following. Write `R = 𝒪_{X,y}^∧`, `M = ℱ_y^∧` and `L = M[1/f]`, a finite
module over `R[1/f]`. A prime `𝔭` of `R` with `f ∉ 𝔭` is a prime of `R[1/f]`, and `𝔭` is not the
maximal ideal of `R` — which contains `f` — so `dim(R/𝔭) ≥ 1`. If `𝔭` is outside the support of
`M` the depth is `⊤` and there is nothing to prove. Otherwise choose `𝔮 ∈ Ass(L)` minimal over
the annihilator with `𝔮 ⊆ 𝔭`; by (2) we have `dim(R/𝔮) ≥ 3`, so `𝔮 ≠ 𝔭` whenever
`dim(R/𝔭) < 3`, and the chain `𝔮 < 𝔭` inside the support of `L` has length one, which by (1)
gives `depth(L_𝔭) ≥ min(2, 1) = 1`. If `dim(R/𝔭) ≥ 2` that already suffices. The remaining case
is `dim(R/𝔭) = 1`: then `𝔮` does not cover `𝔭`, since in a catenary local ring a covering pair
has coheights differing by one and `dim(R/𝔮) ≥ 3 > 2`, so a prime `𝔯` interpolates `𝔮 < 𝔯 < 𝔭`
and the chain `𝔮 < 𝔯 < 𝔭` in the support of `L` has length two, giving `depth(L_𝔭) ≥ 2` and
hence `depth + dim ≥ 3`. Finally the depth of `L_𝔭` over `R[1/f]_𝔭` is at most the depth of
`M_𝔭` over `R_𝔭`, because the two localizations agree.

The catenarity used is Serre's saturated form, which the dualizing complex of the base supplies:
a dualizing complex localizes to the stalk and base-changes to its completion, and a Noetherian
ring with a dualizing complex is universally catenary by [Stacks, Tag 0A80].

## Main definitions

* `Stacks.Algebraization.baseToPointStalk` — the map `A → 𝒪_{U,y}` through the germ at the image
  of `y` in `X`.
* `Stacks.Algebraization.adicStalkParameter` — the image in `𝒪_{X,y}^∧` of a global element of
  the base.
* `Stacks.Algebraization.HasSerreCompletedStalkConditions` — the two hypotheses of
  [Stacks, Tag 0EJC] at a point.

## Main results

* `Stacks.Algebraization.two_lt_depth_add_ringKrullDim_of_propertySkModule_away` — the step the
  source omits, over an arbitrary Noetherian local catenary ring.
* `Stacks.Algebraization.isCatenaryRingSaturated_adicCompletion_pointStalk` — the completion of
  the local ring of `U` at a point is catenary when the base has a dualizing complex.
* `Stacks.Algebraization.two_lt_depth_add_ringKrullDim_completedStalk_of_serre` — the same step
  read on the completed stalk of a coherent adic system in an algebraization situation.

## Implementation notes

The source's data `(A, 𝔪, f, U)` is presented as an algebraization situation
`Stacks.Algebraization.AlgebraizationSituation` with `A` local, `𝔞 = 𝔪` and `I = (f)`: the open
complement `S.U` of `V(𝔞)` is then the punctured spectrum on the nose, so no comparison between
two presentations of it is needed and the whole development stays in the vocabulary that
[Stacks, Tag 0EJ9] is stated in.

Condition (1) is `PropertySkModule` at `k = 2`, Serre's condition of [Stacks, Tag 031P] for a
module, and condition (2) is `IsAssociatedPrimeStacks`, the associated primes of
[Stacks, Tag 00LA]. Inverting `f` is `Localization.Away` and `LocalizedModule.Away` at the image
`Stacks.Algebraization.adicStalkParameter` of `f` in the completed local ring. The finiteness of
`ℱ_y^∧[1/f]` over `𝒪_{X,y}^∧[1/f]` is *not* assumed: it follows from the finiteness of `ℱ_y^∧`
over `𝒪_{X,y}^∧`, which is [Stacks, Tag 0EJE] in the form
`Stacks.Algebraization.finite_completedStalk`, together with the instance that a localization of
a finite module is finite over the localized ring.

The two quantities are compared in `EInt`, as in the definition of the `(a, b)`-inequalities of
[Stacks, Tag 0EJ3]: the depth of the zero module is `⊤` and both inclusions
`Stacks.Algebraization.enatToEInt` and `Stacks.Algebraization.krullDimToEInt` retain it, which
is what makes the statement true at a prime outside the support rather than vacuous there.

Chains in the support are `LTSeries (Module.support _ _)`, so that a chain of length `n` through
`𝔭` bounds `dim Supp(L_𝔭)` below by `n`, and `PropertySkModule` then bounds `depth(L_𝔭)` below
by `min(2, n)`. The comparison of `depth(L_𝔭)` with `depth(M_𝔭)` goes through the
identification of `(R[1/f])_𝔭` with `R_𝔭` of
`IsLocalization.localizationLocalizationAtPrimeIsoLocalization`, transported by a ring
isomorphism rather than an algebra map, which is why depth is compared along a semilinear
equivalence.

### What is carried

The conclusion of [Stacks, Tag 0EJC] is reached from the pointwise bound in two steps, and each
is carried as a hypothesis of the main theorem rather than supplied, because the library does
not have it in the form needed.

* `h0EJA` is the sufficiency direction of [Stacks, Tag 0EJA], that the pointwise bound at the
  points of `U ∩ Y` whose closure has dimension one implies the `(2, 3)`-inequalities. The
  library has the necessity direction,
  `Stacks.Algebraization.two_lt_depth_add_dim_of_satisfiesDepthInequalities`, and it has
  [Stacks, Tag 0EKW] as the equivalence
  `Stacks.Algebraization.satisfiesDepthInequalities_two_three_iff`, whose right-hand side is the
  bound `depth + dim + δ^Y_Z > 3` at *every* point of `U ∩ Y`. Passing from the points of
  closure-dimension one to the rest is the substance of the source's proof of
  [Stacks, Tag 0EJA]: at a point `y` with `δ^Y_Z(y) = 2` it chooses a specialization `y ⤳ y'`
  with `δ^Y_Z(y') = 1` and transports the bound along `𝒪_{X,y'}^∧ → 𝒪_{X,y}^∧` using the second
  display of [Stacks, Tag 0EHW]. Neither input is available: the library has only the first
  display of [Stacks, Tag 0EHW] (`Module.depth_localized_adicCompletion_le`, the inequality of
  depths), and while the ring theory of the specialization is in place
  (`Stacks.Algebraization.nonempty_algEquiv_completedLocalRing_of_specializes`) the base change
  `ℱ_y^∧ = ℱ_{y'}^∧ ⊗ 𝒪_{X,y}^∧` of the completed stalk along a specialization is not stated
  anywhere. The carry retains the premise that this file's own work discharges, so that what is
  assumed is exactly the implication and not its conclusion.
* The passage from the `(2, 3)`-inequalities to the conclusion is the in-particular clause of
  [Stacks, Tag 0EJ9],
  `Stacks.Algebraization.essImage_completionFunctor_of_isLocalRing_of_eq_span_singleton`, which
  takes no carried input.

## References

* [Stacks Project, Tag 0EJC](https://stacks.math.columbia.edu/tag/0EJC)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC), the situation.
* [Stacks Project, Tag 0EJ9](https://stacks.math.columbia.edu/tag/0EJ9), the algebraization.
* [Stacks Project, Tag 0EJA](https://stacks.math.columbia.edu/tag/0EJA), the unwinding.
* [Stacks Project, Tag 0EJ3](https://stacks.math.columbia.edu/tag/0EJ3), the inequalities.
* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE), the completed stalk.
* [Stacks Project, Tag 031P](https://stacks.math.columbia.edu/tag/031P), Serre's conditions.
* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA), associated primes.
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80), universal catenarity.
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G), localizing a dualizing
  complex.
* [Stacks Project, Tag 0DWD](https://stacks.math.columbia.edu/tag/0DWD), completing a dualizing
  complex.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AdicCompletionDimension

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### Catenarity in the saturated form -/

/-- A universally catenary Noetherian ring is catenary in the saturated sense of
`IsCatenaryRingSaturated`: between any two nested primes the lengths of arbitrary chains are
bounded, and all saturated chains have one and the same length.

Universal catenarity gives catenarity of the ring itself, which provides both the bound and a
common length `n` for all chains of covers; the saturated chains are chains of covers, so each
of them has length `n`. -/
private theorem isCatenaryRingSaturated_of_isUniversallyCatenary
    (R : Type u) [CommRing R] [IsNoetherianRing R] (hcat : Ring.IsUniversallyCatenary R) :
    IsCatenaryRingSaturated R := by
  have hR : Ring.IsCatenary R := hcat R
  intro p q hpq
  obtain ⟨⟨N, hN⟩, ⟨n, hn⟩⟩ := hR p q hpq
  refine ⟨⟨N, hN⟩, fun s t hsp hsq htp htq => ?_⟩
  have hsat (c : CovChain R) :
      ∀ i : Fin (covToLT c).length, (covToLT c) i.castSucc ⋖ (covToLT c) i.succ := fun i =>
    c.step i
  exact (hn (covToLT s) hsp hsq (hsat s)).trans (hn (covToLT t) htp htq (hsat t)).symm

/-! ### The dimension of the support -/

/-- A chain in the support of `M` ending below `𝔭` has length at most the dimension of the
support of `M_𝔭`: the chain is carried into the support of the localization by the inverse of
the order isomorphism between the primes of `R_𝔭` and the primes of `R` below `𝔭`. -/
private theorem supportDim_localized_ge_length {R : Type u} [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : PrimeSpectrum R)
    (s : LTSeries (Module.support R M)) (hs : (s.last : PrimeSpectrum R) ≤ p) :
    (s.length : WithBot ℕ∞) ≤
      Module.supportDim (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M) := by
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso
    (Localization.AtPrime p.asIdeal) p.asIdeal
  have hsup := (LocalizedModule.isBaseChange p.asIdeal.primeCompl M).support_eq_preimage_comap
  let t : LTSeries (Module.support (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M)) :=
    LTSeries.mk s.length
      (fun i => ⟨e.symm ⟨(s i).1,
        (show (s i).val ≤ s.last.val from s.strictMono.monotone (Fin.le_last i)).trans hs⟩, by
          rw [hsup]
          change (e (e.symm _)).val ∈ Module.support R M
          simp⟩)
      (fun i j hij => by
        change e.symm _ < e.symm _
        exact e.symm.strictMono (s.strictMono hij))
  exact Order.LTSeries.length_le_krullDim t

/-- Serre's condition `(S₂)` turns a chain of length `n` in the support of `M` ending below `𝔭`
into the lower bound `min(2, n)` for the depth of `M_𝔭`. -/
private theorem min_two_length_le_moduleDepth_localized {R : Type u} [CommRing R]
    [IsNoetherianRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hS2 : PropertySkModule R M 2) (p : PrimeSpectrum R)
    (s : LTSeries (Module.support R M)) (hs : (s.last : PrimeSpectrum R) ≤ p) (n : ℕ)
    (hn : s.length = n) :
    min (2 : ℕ∞) n ≤
      moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
  refine le_trans ?_ (hS2 p.asIdeal)
  refine min_le_min_left _ ?_
  have h := supportDim_localized_ge_length M p s hs
  rw [hn] at h
  rw [← moduleSupportDim_eq_Module_supportDim] at h
  cases hd : moduleSupportDim (Localization.AtPrime p.asIdeal)
      (LocalizedModule.AtPrime p.asIdeal M) with
  | bot => simp [hd] at h
  | coe d =>
      rw [hd] at h
      exact_mod_cast h

/-! ### Comparing depth across a semilinear equivalence -/

/-- Depth does not decrease along a semilinear equivalence of modules over local rings: the
equivalence carries regular sequences in the maximal ideal to regular sequences in the maximal
ideal. -/
private theorem moduleDepth_le_of_semilinearEquiv {R S M N : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (eM : M ≃+ N) (heM : ∀ r m, eM (r • m) = e r • eM m) :
    moduleDepth R M ≤ moduleDepth S N := by
  unfold moduleDepth
  refine iSup₂_le fun xs hs => ?_
  have hmem : ∀ s ∈ xs.map e, s ∈ IsLocalRing.maximalIdeal S := by
    rintro s hxs
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hxs
    rw [← IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective]
    exact Ideal.mem_map_of_mem e.toRingHom (hs.1 r hr)
  have hreg : RingTheory.Sequence.IsRegular N (xs.map e) :=
    (eM.isRegular_congr (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun r _ m => heM r m))).mp hs.2
  have h := le_iSup₂ (f := fun ys (_ : (∀ s ∈ ys, s ∈ IsLocalRing.maximalIdeal S) ∧
    RingTheory.Sequence.IsRegular N ys) => (ys.length : ℕ∞)) (xs.map e) ⟨hmem, hreg⟩
  simpa using h

/-- The depth of a module over a local ring, taken as a supremum over regular sequences in the
maximal ideal, is at most its depth along that maximal ideal: the latter is the former except
when it is `⊤`. -/
private theorem moduleDepth_le_depth {R M : Type u} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] : moduleDepth R M ≤ Module.depth R (IsLocalRing.maximalIdeal R) M := by
  unfold Module.depth
  split_ifs
  · exact le_top
  · exact le_rfl

/-- Localizing twice, first at a submonoid `T` and then at a prime `𝔭` of `Localization T`, is
localizing once at the contraction `𝔭₀` of `𝔭`, so the depth after the double localization is at
most the depth after the single one. -/
private theorem moduleDepth_localized_twice_le {R : Type u} [CommRing R] (T : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module R M] (p : PrimeSpectrum (Localization T))
    (p₀ : PrimeSpectrum R) (hp₀ : PrimeSpectrum.comap (algebraMap R (Localization T)) p = p₀) :
    moduleDepth (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (LocalizedModule T M)) ≤
      Module.depth (Localization.AtPrime p₀.asIdeal) (IsLocalRing.maximalIdeal _)
        (LocalizedModule.AtPrime p₀.asIdeal M) := by
  subst hp₀
  let B := Localization T
  let L := LocalizedModule T M
  let P := Localization.AtPrime p.asIdeal
  let N := LocalizedModule.AtPrime p.asIdeal L
  let q := p.asIdeal.comap (algebraMap R B)
  let Q := Localization.AtPrime q
  let g : M →ₗ[R] N :=
    ((LocalizedModule.mkLinearMap p.asIdeal.primeCompl L).restrictScalars R).comp
      (LocalizedModule.mkLinearMap T M)
  have hg : IsBaseChange P g :=
    (LocalizedModule.isBaseChange T M).comp
      (LocalizedModule.isBaseChange p.asIdeal.primeCompl L)
  have : IsLocalizedModule q.primeCompl g :=
    (isLocalizedModule_iff_isBaseChange q.primeCompl P g).mpr hg
  let er : Q ≃ₐ[R] P :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization T p.asIdeal
  let _ : Algebra Q P := er.toRingHom.toAlgebra
  let _ : IsScalarTower R Q P :=
    IsScalarTower.of_algebraMap_eq' (by ext r; exact (er.commutes r).symm)
  let _ : Module Q N := Module.compHom N (algebraMap Q P)
  let _ : IsScalarTower R Q N := IsScalarTower.of_algebraMap_smul fun r n => by
    change algebraMap Q P (algebraMap R Q r) • n = r • n
    rw [← IsScalarTower.algebraMap_apply R Q P, IsScalarTower.algebraMap_smul]
  let em : LocalizedModule.AtPrime q M ≃ₗ[Q] N :=
    (IsLocalizedModule.iso q.primeCompl g).extendScalarsOfIsLocalization q.primeCompl Q
  refine le_trans ?_ moduleDepth_le_depth
  refine moduleDepth_le_of_semilinearEquiv er.toRingEquiv.symm em.symm.toAddEquiv fun a n => ?_
  obtain ⟨b, rfl⟩ := er.surjective a
  change em.symm (er b • n) = er.symm (er b) • em.symm n
  rw [er.symm_apply_apply]
  exact em.symm.map_smul b n

/-! ### The arithmetic of the bound -/

/-- The coheight of a prime, as an element of `WithBot ℕ∞`, is the Krull dimension of the
quotient by it. -/
private theorem coheight_eq_ringKrullDim_quotient {R : Type u} [CommRing R]
    (p : PrimeSpectrum R) :
    (Order.coheight p : WithBot ℕ∞) = ringKrullDim (R ⧸ p.asIdeal) := by
  rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
  rfl

/-- The bound `3 ≤ d + c` in `ℕ∞` gives the strict bound `2 < d + c` after both summands are
placed in `EInt`. -/
private theorem two_lt_enatToEInt_add_krullDimToEInt (d c : ℕ∞) (h : 3 ≤ d + c) :
    ((2 : ℤ) : EInt) < enatToEInt d + krullDimToEInt (c : WithBot ℕ∞) := by
  induction d using ENat.recTopCoe with
  | top =>
      induction c using ENat.recTopCoe with
      | top => exact (by decide : ((2 : ℤ) : EInt) < ⊤)
      | coe c => exact (by decide : ((2 : ℤ) : EInt) < ⊤)
  | coe d =>
      induction c using ENat.recTopCoe with
      | top => exact (by decide : ((2 : ℤ) : EInt) < ⊤)
      | coe c =>
          have hnat : 3 ≤ d + c := by exact_mod_cast h
          have hint : (2 : ℤ) < (d : ℤ) + (c : ℤ) := by omega
          change ((2 : ℤ) : EInt) < (((d + c : ℕ) : ℤ) : EInt)
          exact WithBotTop.coe_strictMono (by exact_mod_cast hint)

/-! ### The step the source omits -/

/-- Serre's condition `(S₂)` together with the dimension bound on the associated primes gives
`depth(M_𝔭) + coheight(𝔭) ≥ 3` at every prime `𝔭` of the support with positive coheight.

The primes are those of a localization `Localization T` of a catenary Noetherian local ring `R`,
and coheight is measured in `R`. If the coheight of `𝔭` is already at least `3` there is nothing
to prove. Otherwise an associated prime `𝔮` minimal over the annihilator and below `𝔭` has
coheight at least `3`, hence is strictly below `𝔭`, so the chain `𝔮 < 𝔭` gives
`depth(M_𝔭) ≥ 1`; this settles the case of coheight at least `2`. In the remaining case the
coheight of `𝔭` is exactly `1`, so `𝔮` does not cover `𝔭` — covering primes have coheights
differing by one, and `3 ≤ coheight 𝔮` — and an interpolating prime extends the chain to length
two, giving `depth(M_𝔭) ≥ 2`. -/
private theorem three_le_moduleDepth_add_coheight_of_propertySkModule {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hcat : IsCatenaryRingSaturated R) (T : Submonoid R)
    (M : Type u) [AddCommGroup M] [Module (Localization T) M]
    [Module.Finite (Localization T) M] (hS2 : PropertySkModule (Localization T) M 2)
    (hbound : ∀ q : PrimeSpectrum (Localization T),
      q.asIdeal ∈ associatedPrimes (Localization T) M →
      (3 : ℕ∞) ≤ Order.coheight (PrimeSpectrum.comap (algebraMap R (Localization T)) q))
    (p : PrimeSpectrum (Localization T)) (hp : p ∈ Module.support (Localization T) M)
    (hpos : (1 : ℕ∞) ≤
      Order.coheight (PrimeSpectrum.comap (algebraMap R (Localization T)) p)) :
    (3 : ℕ∞) ≤
      moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) +
        Order.coheight (PrimeSpectrum.comap (algebraMap R (Localization T)) p) := by
  let e := IsLocalization.primeSpectrumOrderIso T (Localization T)
  let p₀ : PrimeSpectrum R := (e p).1
  change 1 ≤ Order.coheight p₀ at hpos
  change 3 ≤ _ + Order.coheight p₀
  by_cases h3 : 3 ≤ Order.coheight p₀
  · exact h3.trans (le_add_left (le_refl _))
  obtain ⟨qI, hqI, hqpI⟩ :=
    Ideal.exists_minimalPrimes_le (Module.annihilator_le_of_mem_support hp)
  let q : PrimeSpectrum (Localization T) := ⟨qI, hqI.isPrime⟩
  have hqass : q.asIdeal ∈ associatedPrimes (Localization T) M :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      (Localization T) M hqI
  have hq : q ∈ Module.support (Localization T) M :=
    Module.mem_support_iff_of_finite.mpr hqI.le
  have hq3 := hbound q hqass
  change 3 ≤ Order.coheight (e q).val at hq3
  have hqp : q < p := lt_of_le_of_ne hqpI (by
    intro heq
    exact h3 (by simpa only [heq] using hq3))
  have h1 : (1 : ℕ∞) ≤
      moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
    let s : LTSeries (Module.support (Localization T) M) :=
      (RelSeries.singleton (α := Module.support (Localization T) M) _ ⟨q, hq⟩).snoc ⟨p, hp⟩
        (by exact hqp)
    simpa using min_two_length_le_moduleDepth_localized M hS2 p s (le_refl p) 1 rfl
  by_cases h2 : 2 ≤ Order.coheight p₀
  · exact (show (3 : ℕ∞) = 1 + 2 by norm_num).le.trans (add_le_add h1 h2)
  have hc : Order.coheight p₀ = 1 :=
    le_antisymm ((ENat.lt_add_one_iff (by simp)).mp (lt_of_not_ge h2)) hpos
  have hq₀p₀ : (e q).1 < p₀ := e.strictMono hqp
  have hncov : ¬ (e q).1 ⋖ p₀ := by
    intro hcov
    have h := coheight_covby_of_catenary hcat _ _ hcov
    change (3 : ℕ∞) ≤ Order.coheight (e q).1 at hq3
    rw [h, hc] at hq3
    norm_num at hq3
  obtain ⟨r, hqr, hrp⟩ := (not_covBy_iff hq₀p₀).mp hncov
  let r' : PrimeSpectrum (Localization T) := e.symm ⟨r, (e p).2.mono_right hrp.le⟩
  have hqr' : q < r' := by
    refine e.lt_iff_lt.mp ?_
    change (e q).1 < (e r').1
    simpa [r'] using hqr
  have hrp' : r' < p := by
    refine e.lt_iff_lt.mp ?_
    change (e r').1 < (e p).1
    simpa [r', p₀] using hrp
  have hr : r' ∈ Module.support (Localization T) M := Module.mem_support_mono hqr'.le hq
  have hd2 : (2 : ℕ∞) ≤
      moduleDepth (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M) := by
    let s : LTSeries (Module.support (Localization T) M) :=
      ((RelSeries.singleton (α := Module.support (Localization T) M) _ ⟨q, hq⟩).snoc
        ⟨r', hr⟩ (by exact hqr')).snoc ⟨p, hp⟩ (by exact hrp')
    simpa using min_two_length_le_moduleDepth_localized M hS2 p s (le_refl p) 2 rfl
  exact (show (3 : ℕ∞) = 2 + 1 by norm_num).le.trans (add_le_add hd2 hpos)

/-- **The step [Stacks, Tag 0EJC] leaves implicit.** Let `R` be a Noetherian local ring that is
catenary, let `g` be an element of its maximal ideal, and let `M` be a finite `R`-module. If
`M[1/g]` satisfies Serre's condition `(S₂)` over `R[1/g]` and every associated prime of `M[1/g]`
contracts to a prime `𝔮` of `R` with `dim(R/𝔮) ≥ 3`, then

`depth(M_𝔭) + dim(R/𝔭) > 2`

for every prime `𝔭` of `R` with `g ∉ 𝔭`.

This is the implication that turns the two hypotheses of [Stacks, Tag 0EJC] into the pointwise
bound that [Stacks, Tag 0EJA] takes; the source states it nowhere. A prime avoiding `g` is not
the maximal ideal, which contains `g`, so it has positive coheight, and the bound then comes from
`three_le_moduleDepth_add_coheight_of_propertySkModule` after the depth over `R[1/g]_𝔭` is
compared with the depth over `R_𝔭`. At a prime outside the support of `M` the depth is `⊤` and
the bound is immediate. -/
public theorem two_lt_depth_add_ringKrullDim_of_propertySkModule_away {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hcat : IsCatenaryRingSaturated R) (g : R)
    (hg : g ∈ IsLocalRing.maximalIdeal R) (M : Type u) [AddCommGroup M] [Module R M]
    [Module.Finite R M]
    (hS2 : PropertySkModule (Localization.Away g) (LocalizedModule.Away g M) 2)
    (hbound : ∀ q : Ideal (Localization.Away g),
      IsAssociatedPrimeStacks (Localization.Away g) (LocalizedModule.Away g M) q →
      (3 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ q.comap (algebraMap R (Localization.Away g))))
    (p : PrimeSpectrum R) (hp : g ∉ p.asIdeal) :
    ((2 : ℤ) : EInt) <
      enatToEInt (Module.depth (Localization.AtPrime p.asIdeal)
          (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
          (LocalizedModule.AtPrime p.asIdeal M)) +
        krullDimToEInt (ringKrullDim (R ⧸ p.asIdeal)) := by
  rw [← coheight_eq_ringKrullDim_quotient p]
  refine two_lt_enatToEInt_add_krullDimToEInt _ _ ?_
  by_cases hsupp : p ∈ Module.support R M
  · let e := IsLocalization.primeSpectrumOrderIso (Submonoid.powers g) (Localization.Away g)
    have hdis : Disjoint (Submonoid.powers g : Set R) (p.asIdeal : Set R) :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := p.asIdeal) g).mpr hp
    let q := e.symm ⟨p, hdis⟩
    have hq : PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q = p := by
      change (e q).1 = p
      simp [q]
    have hqsupp : q ∈ Module.support (Localization.Away g) (LocalizedModule.Away g M) := by
      rw [(LocalizedModule.isBaseChange (Submonoid.powers g) M).support_eq_preimage_comap]
      change PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q ∈ Module.support R M
      rwa [hq]
    have hpos : (1 : ℕ∞) ≤ Order.coheight p := by
      refine Order.one_le_iff_ne_zero.mpr fun h => ?_
      have heq : p = IsLocalRing.closedPoint R :=
        (Order.coheight_eq_zero.mp h).eq_of_le
          (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)
      exact hp (heq ▸ hg)
    have hass : ∀ q' : PrimeSpectrum (Localization.Away g),
        q'.asIdeal ∈ associatedPrimes (Localization.Away g) (LocalizedModule.Away g M) →
        (3 : ℕ∞) ≤
          Order.coheight (PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q') := by
      intro q' hq'
      obtain ⟨hq'prime, m, hm⟩ := Submodule.isAssociatedPrime_iff.mp hq'
      have hb := hbound q'.asIdeal
        ⟨hq'prime, m, by simpa only [Submodule.colon_span] using hm.symm⟩
      have hb' : (3 : WithBot ℕ∞) ≤ ringKrullDim
          (R ⧸ (PrimeSpectrum.comap (algebraMap R (Localization.Away g)) q').asIdeal) := by
        rwa [PrimeSpectrum.comap_asIdeal]
      rw [← coheight_eq_ringKrullDim_quotient] at hb'
      exact WithBot.coe_le_coe.mp hb'
    have h := three_le_moduleDepth_add_coheight_of_propertySkModule hcat (Submonoid.powers g)
      (LocalizedModule.Away g M) hS2 hass q hqsupp (by rwa [hq])
    rw [hq] at h
    exact h.trans (add_le_add (moduleDepth_localized_twice_le (Submonoid.powers g) M q p hq)
      (le_refl (Order.coheight p)))
  · have := Module.notMem_support_iff.mp hsupp
    have hsub : (⊤ : Submodule (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)) = ⊥ := by
      ext x
      simp [Subsingleton.elim x 0]
    simp [Module.depth, hsub]

/-! ### The local ring of `U` at a point, and its dualizing complex -/

/-- A dualizing complex stays dualizing after transport along a ring isomorphism: an isomorphism
is a localization at the submonoid of units. -/
private theorem isDualizingComplex_of_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    [IsNoetherianRing R] [IsNoetherianRing T] (e : R ≃+* T)
    (K : DerivedCategory (ModuleCat.{u} R)) (hK : Dualizing.IsDualizingComplex K) :
    Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars e.toRingHom).obj K) := by
  let _ : Algebra R T := e.toRingHom.toAlgebra
  let M₀ : Submonoid T := IsUnit.submonoid T
  have _ : IsLocalization M₀ T := inferInstance
  let M : Submonoid R := M₀.map e.symm.toRingHom
  have _ : IsLocalization M T := IsLocalization.isLocalization_of_base_ringEquiv M₀ T e.symm
  exact Dualizing.isDualizingComplex_localization M K hK

/-- The local ring of `U` at a point has a dualizing complex when `A` does: localize at the
prime under the point, then transport along the identification of the stalk with that
localization. -/
private theorem exists_isDualizingComplex_pointStalk (S : AlgebraizationSituation.{u})
    (y : S.U.toScheme)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K) :
    ∃ K : DerivedCategory (ModuleCat.{u} (S.U.toScheme.presheaf.stalk y)),
      Dualizing.IsDualizingComplex K := by
  obtain ⟨K, hK⟩ := hdual
  have hNoethLoc : IsNoetherianRing (Localization.AtPrime (underlyingPrime S y).asIdeal) :=
    IsLocalization.isNoetherianRing (underlyingPrime S y).asIdeal.primeCompl _ inferInstance
  have hNoethStalk : IsNoetherianRing (S.U.toScheme.presheaf.stalk y) :=
    isNoetherianRing_of_ringEquiv _ (pointStalkRingEquiv S y).symm
  exact ⟨(StacksDraft.PseudoCoherence.derivedExtensionScalars
      (pointStalkRingEquiv S y).symm.toRingHom).obj
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap S.A (Localization.AtPrime (underlyingPrime S y).asIdeal))).obj K),
    isDualizingComplex_of_ringEquiv (pointStalkRingEquiv S y).symm _
      (Dualizing.isDualizingComplex_localizationAtPrime.{u, u} K hK (underlyingPrime S y))⟩

/-- **The completed local ring of `U` at a point is catenary** when the base has a dualizing
complex. A dualizing complex localizes to the stalk and base-changes to the completion of the
stalk along any ideal by [Stacks, Tag 0DWD], and a Noetherian ring with a dualizing complex is
universally catenary by [Stacks, Tag 0A80]. -/
public theorem isCatenaryRingSaturated_adicCompletion_pointStalk
    (S : AlgebraizationSituation.{u}) (y : S.U.toScheme)
    (J : Ideal (S.U.toScheme.presheaf.stalk y))
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K) :
    IsCatenaryRingSaturated (AdicCompletion J (S.U.toScheme.presheaf.stalk y)) := by
  obtain ⟨K, hK⟩ := exists_isDualizingComplex_pointStalk S y hdual
  have hNoethStalk : IsNoetherianRing (S.U.toScheme.presheaf.stalk y) :=
    isNoetherianRing_of_ringEquiv _ (pointStalkRingEquiv S y).symm
  have hNoethComp : IsNoetherianRing (AdicCompletion J (S.U.toScheme.presheaf.stalk y)) :=
    AdicCompletion.isNoetherianRing J
  exact isCatenaryRingSaturated_of_isUniversallyCatenary _
    (Dualizing.isUniversallyCatenary_of_isDualizingComplex
      (Dualizing.isDualizingComplex_adicCompletion J K hK))

/-! ### The stalk of `I𝒪_U` and the image of the parameter -/

/-- The image in the completed local ring `𝒪_{X,y}^∧` of a global element `f` of the base. When
`I = (f)` this is a generator of `I𝒪_{X,y}^∧`, and inverting it is the operation written
`-[1/f]` in [Stacks, Tag 0EJC]. -/
public def adicStalkParameter (S : AlgebraizationSituation.{u}) (f : S.A)
    (y : S.U.toScheme) : completedLocalRing (idealOnOpen S) y :=
  algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y)
    (baseToPointStalk S y f)

/-- When `I = (f)` the stalk of `I𝒪_U` at `y` is generated by the image of `f`. -/
private theorem stalk_idealOnOpen_eq_span_singleton (S : AlgebraizationSituation.{u})
    (f : S.A) (hI : S.I = Ideal.span {f}) (y : S.U.toScheme) :
    IdealSheafData.stalk (idealOnOpen S) y = Ideal.span {baseToPointStalk S y f} := by
  rw [stalk_idealOnOpen_eq_map, hI, Ideal.map_span, Set.image_singleton]

/-- When `I = (f)` the image of `f` in the completed local ring at a point of `U ∩ Y` lies in the
maximal ideal: it generates `I𝒪_{X,y}^∧`, which is contained in the Jacobson radical of the
completion and so in its maximal ideal. -/
private theorem adicStalkParameter_mem_maximalIdeal (S : AlgebraizationSituation.{u})
    (f : S.A) (hI : S.I = Ideal.span {f}) (y : S.U.toScheme) (z : S.Y)
    (hyz : S.U.ι.base y = S.Yι.base z) :
    have := isLocalRing_adicCompletion_of_le_maximalIdeal
      (IdealSheafData.stalk (idealOnOpen S) y) (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
    adicStalkParameter S f y ∈
      IsLocalRing.maximalIdeal (completedLocalRing (idealOnOpen S) y) := by
  have := isLocalRing_adicCompletion_of_le_maximalIdeal
    (IdealSheafData.stalk (idealOnOpen S) y) (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
  have : IsAdicComplete (completedLocalIdeal (idealOnOpen S) y)
      (completedLocalRing (idealOnOpen S) y) :=
    AdicCompletion.isAdicComplete_self _
      (Ideal.fg_of_isNoetherianRing (IdealSheafData.stalk (idealOnOpen S) y))
  have hjac : completedLocalIdeal (idealOnOpen S) y ≤
      IsLocalRing.maximalIdeal (completedLocalRing (idealOnOpen S) y) := by
    refine (IsAdicComplete.le_jacobson_bot
      (I := completedLocalIdeal (idealOnOpen S) y)).trans ?_
    change sInf {N : Ideal (completedLocalRing (idealOnOpen S) y) |
      (⊥ : Ideal (completedLocalRing (idealOnOpen S) y)) ≤ N ∧ N.IsMaximal} ≤ _
    exact sInf_le ⟨bot_le,
      IsLocalRing.maximalIdeal.isMaximal (completedLocalRing (idealOnOpen S) y)⟩
  exact hjac (Ideal.mem_map_of_mem _
    ((stalk_idealOnOpen_eq_span_singleton S f hI y).ge
      (Ideal.subset_span (Set.mem_singleton _))))

/-! ### The two conditions of Stacks 0EJC at a point -/

/-- **The hypotheses of [Stacks, Tag 0EJC] at a point `y` of `U ∩ Y`.** With `R = 𝒪_{X,y}^∧`,
`M = ℱ_y^∧` and `g` the image of `f` in `R`, these are the two conditions

1. `M[1/g]` is `(S₂)` as an `R[1/g]`-module, and
2. `dim(R/𝔭) ≥ 3` for every `𝔭 ∈ Ass(M[1/g])`,

where in (2) the prime `𝔭` of `R[1/g]` is read in `R` through its contraction, as the source
does when it writes `𝔭 ⊂ 𝒪_{X,y}^\wedge`.

The finiteness of `M` over `R`, which Serre's condition is stated for, is supplied here from
[Stacks, Tag 0EJE] rather than assumed, and the finiteness of `M[1/g]` over `R[1/g]` follows
because a localization of a finite module is finite over the localized ring. -/
public def HasSerreCompletedStalkConditions (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (y : S.U.toScheme) : Prop :=
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have : Module.Finite (completedLocalRing (idealOnOpen S) y)
      (completedStalk (idealOnOpen S) F y) := finite_completedStalk (idealOnOpen S) F y
  PropertySkModule (Localization.Away (adicStalkParameter S f y))
      (LocalizedModule.Away (adicStalkParameter S f y)
        (completedStalk (idealOnOpen S) F y)) 2 ∧
    ∀ q : Ideal (Localization.Away (adicStalkParameter S f y)),
      IsAssociatedPrimeStacks (Localization.Away (adicStalkParameter S f y))
          (LocalizedModule.Away (adicStalkParameter S f y)
            (completedStalk (idealOnOpen S) F y)) q →
        (3 : WithBot ℕ∞) ≤ ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸
          q.comap (algebraMap (completedLocalRing (idealOnOpen S) y)
            (Localization.Away (adicStalkParameter S f y))))

/-- **The pointwise bound of [Stacks, Tag 0EJA] from the hypotheses of [Stacks, Tag 0EJC].** At a
point `y` of `U ∩ Y`, Serre's condition on `ℱ_y^∧[1/f]` and the dimension bound on its associated
primes give

`depth((ℱ_y^∧)_𝔭) + dim(𝒪_{X,y}^∧/𝔭) > 2`

for every prime `𝔭` of `𝒪_{X,y}^∧` not containing `I𝒪_{X,y}^∧`.

This is `two_lt_depth_add_ringKrullDim_of_propertySkModule_away` read on the completed stalk: the
completed local ring is local because the stalk of `I𝒪_U` is proper at a point of `U ∩ Y`, it is
catenary because the base has a dualizing complex, the image of `f` generates `I𝒪_{X,y}^∧` and so
lies in its maximal ideal, and a prime not containing `I𝒪_{X,y}^∧` does not contain that
image. -/
public theorem two_lt_depth_add_ringKrullDim_completedStalk_of_serre
    (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S)) (f : S.A)
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K)
    (hI : S.I = Ideal.span {f})
    (y : S.U.toScheme) (z : S.Y) (hyz : S.U.ι.base y = S.Yι.base z)
    (hserre : HasSerreCompletedStalkConditions S F f y)
    (p : PrimeSpectrum (completedLocalRing (idealOnOpen S) y))
    (hp : ¬ completedLocalIdeal (idealOnOpen S) y ≤ p.asIdeal) :
    ((2 : ℤ) : EInt) < enatToEInt (completedStalkDepth (idealOnOpen S) F y p) +
      krullDimToEInt (ringKrullDim (completedLocalRing (idealOnOpen S) y ⧸ p.asIdeal)) := by
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  have : Module.Finite (completedLocalRing (idealOnOpen S) y)
      (completedStalk (idealOnOpen S) F y) := finite_completedStalk (idealOnOpen S) F y
  have : IsLocalRing (completedLocalRing (idealOnOpen S) y) :=
    isLocalRing_adicCompletion_of_le_maximalIdeal
      (IdealSheafData.stalk (idealOnOpen S) y) (stalk_idealOnOpen_le_maximalIdeal S y z hyz)
  obtain ⟨hS2, hass⟩ := hserre
  have hgmax : adicStalkParameter S f y ∈
      IsLocalRing.maximalIdeal (completedLocalRing (idealOnOpen S) y) :=
    adicStalkParameter_mem_maximalIdeal S f hI y z hyz
  have hgnot : adicStalkParameter S f y ∉ p.asIdeal := fun hg =>
    hp (Ideal.map_le_iff_le_comap.mpr
      ((stalk_idealOnOpen_eq_span_singleton S f hI y).le.trans
        (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hg))))
  exact two_lt_depth_add_ringKrullDim_of_propertySkModule_away
    (isCatenaryRingSaturated_adicCompletion_pointStalk S y
      (IdealSheafData.stalk (idealOnOpen S) y) hdual)
    (adicStalkParameter S f y) hgmax (completedStalk (idealOnOpen S) F y) hS2 hass p hgnot

/-! ### Stacks 0EJC -/

end Stacks.Algebraization

end
