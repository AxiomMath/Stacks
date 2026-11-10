module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.EtaleNodalChart
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableNodalChartOfNodal
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import Mathlib.Data.Multiset.DershowitzManna
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Resolving an at-worst-nodal family over a discrete valuation ring by point blowups

This file proves [Stacks, Tag 0CDE]: a quasi-compact scheme `X` which is at-worst-nodal of
relative dimension one over a discrete valuation ring `R`, with smooth generic fibre, becomes
regular after finitely many blowups, each in a closed point at which the current scheme is
singular, and every intermediate scheme is again at-worst-nodal of relative dimension one over
`R`.

## The argument

Following the source, the singular points are first located: `X` is smooth over `R`, hence
regular, away from the relative singular subscheme `Sing(f)`; the generic fibre being smooth, the
remaining singular points lie in the special fibre, where `Sing(f)` is unramified over the residue
field, so they form a finite set of closed points. At each of them [Stacks, Tag 0CDD] gives an
étale nodal chart `R'[u, v]/(uv - h)`; the case `h = 0` would produce a singular point of the
generic fibre, and for `h = πⁿ` the singular point lies over the origin with `n ≥ 2`.

Blowing up a singular point with a chart of exponent `n` keeps the family at-worst-nodal and
replaces that singular point by finitely many singular points, each with a chart of exponent
`n - 2` (`Stacks.SemistableReduction.blowUp_nodalChartAt`); away from the centre nothing changes.
The multiset of the exponents of the charts at the singular points therefore drops in the
Dershowitz–Manna order, which is well founded, and the process stops at a regular scheme. This
replaces the source's double induction (on the number of singular points and on the exponent) by
a single well-founded induction, and avoids having to show that only one singular point appears
over the centre.

## Main definitions

* `Stacks.SemistableReduction.NodalBlowupChain` — a finite sequence of blowups, each in a closed
  point at which the current scheme is singular, with every member at-worst-nodal of relative
  dimension one over the base.

## Main results

* `Stacks.SemistableReduction.finite_setOf_not_isRegularLocalRing` — the singular points of a
  quasi-compact nodal family whose singular points lie over the closed point form a finite set of
  closed points.
* `Stacks.SemistableReduction.nonempty_nodalChartAt_of_not_isRegularLocalRing` — an étale nodal
  chart at every singular point.
* `Stacks.SemistableReduction.exists_nodalBlowupChain_isRegular` — **Tag 0CDE.**

## References

* [Stacks Project, Tag 0CDE](https://stacks.math.columbia.edu/tag/0CDE)
* [Stacks Project, Tag 0CDD](https://stacks.math.columbia.edu/tag/0CDD)
* [Stacks Project, Tag 0CDC](https://stacks.math.columbia.edu/tag/0CDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing
  MvPolynomial

universe u

namespace Stacks.SemistableReduction

open Scheme.IdealSheafData

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-! ### Regularity of the nodal chart ring -/

/-- **The nodal chart ring is regular at every prime not containing both coordinates**, for any
parameter `h` over a regular ring: one of the two partial derivatives of `xy - h` is then a unit at
the prime. -/
public theorem isRegularLocalRing_localization_nodalChartRing_of_not_and {A : Type u}
    [CommRing A] [IsRegularRing A] (h : A) (q : Ideal (nodalChartRing A h)) [q.IsPrime]
    (hq : ¬ (nodalGen A h 0 ∈ q ∧ nodalGen A h 1 ∈ q)) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  refine isRegularLocalRing_localization_quotient_span_singleton_of_notMem_sq _ q ?_
  set p := q.comap (Ideal.Quotient.mk (Ideal.span {nodalEquation A h})) with hpdef
  have : p.IsPrime := Ideal.IsPrime.comap _
  have hgen (i : Fin 2) : X i ∈ p ↔ nodalGen A h i ∈ q := Iff.rfl
  have key (i : Fin 2) (hi : (MvPolynomial.pderiv (R := A) i) (nodalEquation A h) ∉ p) :=
    notMem_sq_of_derivation ((MvPolynomial.pderiv (R := A) i).restrictScalars ℤ) hi
  by_cases hx0 : X 0 ∈ p
  · have hx1 : X 1 ∉ p := fun hx1 ↦ hq ⟨(hgen 0).mp hx0, (hgen 1).mp hx1⟩
    exact key 0 (by simpa [nodalEquation_def] using hx1)
  · exact key 1 (by simpa [nodalEquation_def] using hx0)

/-- **A regular local ring cut by an element of the square of its maximal ideal, read on the
quotient ring.** If `A` is a regular domain, `f ≠ 0` lies in `p²` for a prime `p`, and `q` is the
prime of `A ⧸ (f)` above `p`, then the localization of `A ⧸ (f)` at `q` is not regular. -/
public theorem not_isRegularLocalRing_localization_quotient_of_mem_sq {A : Type u} [CommRing A]
    [IsRegularRing A] [IsDomain A] {f : A} (hf0 : f ≠ 0) (p : Ideal A) [p.IsPrime]
    (hf2 : f ∈ p ^ 2) (q : Ideal (A ⧸ Ideal.span {f})) [q.IsPrime]
    (hq : q.comap (Ideal.Quotient.mk (Ideal.span {f})) = p) :
    ¬ IsRegularLocalRing (Localization.AtPrime q) := by
  intro hreg
  have hsq :
      algebraMap A (Localization.AtPrime p) f ∈ maximalIdeal (Localization.AtPrime p) ^ 2 := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf2
  have hnzd :
      algebraMap A (Localization.AtPrime p) f ∈ nonZeroDivisors (Localization.AtPrime p) := by
    refine mem_nonZeroDivisors_of_ne_zero fun h ↦ hf0 ?_
    refine IsLocalization.injective (Localization.AtPrime p)
      (Ideal.primeCompl_le_nonZeroDivisors p) ?_
    rw [h, map_zero]
  let : IsLocalization q.primeCompl
      (Localization.AtPrime p ⧸ (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) :=
    isLocalization_quotient_atPrime_of_mem_iff f (fun r ↦ by rw [← Ideal.mem_comap, hq])
  have hJ : (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))
      = Ideal.span {algebraMap A (Localization.AtPrime p) f} := by
    simp [Ideal.map_span]
  have h' : IsRegularLocalRing
      (Localization.AtPrime p ⧸ (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p))) :=
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
        (Localization.AtPrime p ⧸
          (Ideal.span {f}).map (algebraMap A (Localization.AtPrime p)))).toRingEquiv
  rw [hJ] at h'
  exact not_isRegularLocalRing_quotient_span_singleton_of_mem_sq hnzd hsq h'

/-! ### Locating the singular points -/

section Singular

variable {X : Scheme.{u}}

/-- At a point where a morphism to the spectrum of a discrete valuation ring is smooth, the local
ring is regular ([Stacks, Tag 056S]). -/
@[ega "IV 17.5.8" "(iii), special case", sga "1 II 3.1" "special case"]
public theorem isRegularLocalRing_stalk_of_smoothAt (f : X ⟶ Spec (.of R)) (y : X)
    (hsm : InfinitesimalLifting.SmoothAt f y) : IsRegularLocalRing (X.presheaf.stalk y) := by
  obtain ⟨U, hyU, hU⟩ := (InfinitesimalLifting.smoothAt_iff_exists_open_smooth_comp f y).mp hsm
  have : Smooth (U.ι ≫ f) := hU
  have hreg : IsRegular U.toScheme := isRegular_of_smooth_over_regular (U.ι ≫ f)
  exact (isRegularLocalRing_stalk_iff_of_isOpenImmersion U.ι ⟨y, hyU⟩).mp
    (hreg.isRegularLocalRing_stalk _)

/-- **The singular points of a nodal family form a finite set of closed points.** Let
`f : X ⟶ Spec R` be at-worst-nodal of relative dimension one with `X` quasi-compact, and suppose
every point at which `X` is not regular lies over the closed point. Away from the relative
singular subscheme `Sing(f)` the morphism is smooth, so `X` is regular there; and the points of
`Sing(f)` over the closed point form a discrete closed subset of the quasi-compact scheme
`Sing(f)`, because `Sing(f)` is unramified over `R`. -/
public theorem finite_setOf_not_isRegularLocalRing [CompactSpace X] (f : X ⟶ Spec (.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hgen : ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → f.base y = closedPoint R) :
    {y : X | ¬ IsRegularLocalRing (X.presheaf.stalk y)}.Finite ∧
      ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → IsClosed ({y} : Set X) := by
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  set ι := (relativeSingularIdeal f).subschemeι with hι
  have : Unramified (ι ≫ f) := hf.2
  have : CompactSpace (relativeSingularIdeal f).subscheme := ι.isClosedEmbedding.compactSpace
  set F : Set (relativeSingularIdeal f).subscheme := (ι ≫ f).base ⁻¹' {closedPoint R} with hF
  have hFd : _root_.IsDiscrete F := (ι ≫ f).isDiscrete_preimage_singleton _
  have hFc : IsClosed F := (isClosed_singleton_closedPoint R).preimage (ι ≫ f).continuous
  have hFfin : F.Finite := hFc.isCompact.finite hFd
  have hsub : {y : X | ¬ IsRegularLocalRing (X.presheaf.stalk y)} ⊆ ι.base '' F := by
    intro y hy
    have hy' : ¬ InfinitesimalLifting.SmoothAt (f.fiberToSpecResidueField (f y)) (f.asFiber y) :=
      fun h ↦ hy (isRegularLocalRing_stalk_of_smoothAt f y
        (smoothAt_of_flat_of_smoothAt_fiber f (flat hf.1.1) y h))
    obtain ⟨z, hz⟩ :=
      (Stacks.NodalEtaleLocalStructure.mem_relativeSingular_iff_not_smoothAt_fiber f hf y).mpr hy'
    refine ⟨z, ?_, hz⟩
    change (ι ≫ f).base z ∈ ({closedPoint R} : Set (Spec (.of R)))
    rw [Scheme.Hom.comp_apply, hz]
    exact hgen y hy
  refine ⟨hFfin.image _ |>.subset hsub, fun y hy ↦ ?_⟩
  obtain ⟨z, hzF, rfl⟩ := hsub hy
  have hz : IsClosed ({z} : Set (relativeSingularIdeal f).subscheme) := by
    obtain ⟨V, hV, hVF⟩ := isDiscrete_iff_forall_mem_exists_isClosed.mp hFd {z}
      (Set.singleton_subset_iff.mpr hzF)
    rw [← hVF]
    exact hV.inter hFc
  simpa using ι.isClosedEmbedding.isClosedMap _ hz

/-- **An étale nodal chart at every singular point.** Let `f : X ⟶ Spec R` be at-worst-nodal of
relative dimension one, and suppose every point at which `X` is not regular lies over the closed
point. At such a point [Stacks, Tag 0CDD] gives an étale chart `R'[u, v]/(uv - h)` with `h = 0` or
`h = πⁿ`. The image of the chosen point in the chart is a singular point, so it contains both
coordinates. If `h = 0` the prime `(u, v)` it contains is a singular point of the generic fibre,
and an étale neighbourhood of the chosen point reaches it, contradicting the hypothesis; so
`h = πⁿ`, and the image is the origin `(π, u, v)`. -/
public theorem nonempty_nodalChartAt_of_not_isRegularLocalRing (f : X ⟶ Spec (.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hgen : ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → f.base y = closedPoint R)
    (x : X) (hx : ¬ IsRegularLocalRing (X.presheaf.stalk x)) :
    ∃ n, Nonempty (NodalChartAt f x n) := by
  obtain ⟨R', _, _, _, _, hext, _, h, hh, U, g, j, x', hg, hj, hgx, hcomm⟩ :=
    Stacks.Models.exists_etale_nodalChart_pow_uniformizer_of_isAtWorstNodal f hf x (hgen x hx)
  have hx'bad : ¬ IsRegularLocalRing (U.presheaf.stalk x') := by
    rw [isRegularLocalRing_stalk_iff_of_etale g, hgx]
    exact hx
  rw [isRegularLocalRing_stalk_iff_of_etale j] at hx'bad
  set w := j.base x' with hw
  have := w.isPrime
  have hcoord : nodalGen R' h 0 ∈ w.asIdeal ∧ nodalGen R' h 1 ∈ w.asIdeal := by
    by_contra hc
    exact hx'bad ((isRegularLocalRing_stalk_spec_iff w).mpr
      (isRegularLocalRing_localization_nodalChartRing_of_not_and h w.asIdeal hc))
  have hhw : algebraMap R' (nodalChartRing R' h) h ∈ w.asIdeal := by
    rw [← nodalGen_zero_mul_nodalGen_one]
    exact Ideal.mul_mem_right _ _ hcoord.1
  rcases hh with rfl | ⟨π, n, hπ, rfl⟩
  · -- The case `h = 0` does not occur.
    exfalso
    let p₀ : Ideal (MvPolynomial (Fin 2) R') := RingHom.ker (MvPolynomial.constantCoeff)
    have hp₀ : p₀.IsPrime := RingHom.ker_isPrime _
    have hX (i : Fin 2) : (MvPolynomial.X i : MvPolynomial (Fin 2) R') ∈ p₀ := by
      simp [p₀, RingHom.mem_ker]
    have hker : RingHom.ker (Ideal.Quotient.mk (Ideal.span {nodalEquation R' 0})) ≤ p₀ := by
      rw [Ideal.mk_ker, Ideal.span_le, Set.singleton_subset_iff]
      simp [p₀, RingHom.mem_ker, nodalEquation_def]
    let q : Ideal (nodalChartRing R' 0) := p₀.map (Ideal.Quotient.mk _)
    have hq : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hqc : q.comap (Ideal.Quotient.mk (Ideal.span {nodalEquation R' 0})) = p₀ := by
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
      refine sup_eq_left.mpr ?_
      rw [← RingHom.ker_eq_comap_bot]
      exact hker
    have hne : nodalEquation R' 0 ≠ 0 := by
      rw [nodalEquation_def, map_zero, sub_zero]
      exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    have hsq : nodalEquation R' 0 ∈ p₀ ^ 2 := by
      rw [nodalEquation_def, map_zero, sub_zero, pow_two]
      exact Ideal.mul_mem_mul (hX 0) (hX 1)
    have hqbad : ¬ IsRegularLocalRing (Localization.AtPrime q) :=
      not_isRegularLocalRing_localization_quotient_of_mem_sq hne p₀ hsq q hqc
    have hqw : q ≤ w.asIdeal := by
      rw [Ideal.map_le_iff_le_comap]
      intro F hF
      have hF' : F ∈ Ideal.span (MvPolynomial.X '' Set.univ) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hcon
        push Not at hcon
        have hm0 : m = 0 := by
          ext i
          simpa using hcon i
        subst hm0
        refine (MvPolynomial.mem_support_iff.mp hm) ?_
        rw [← MvPolynomial.constantCoeff_eq]
        exact hF
      refine (Ideal.span_le.mpr ?_) hF'
      rintro _ ⟨i, -, rfl⟩
      fin_cases i
      · exact hcoord.1
      · exact hcoord.2
    let η : Spec (.of (nodalChartRing R' 0)) := ⟨q, hq⟩
    have hηw : η ⤳ w := (PrimeSpectrum.le_iff_specializes η w).mp hqw
    have hopen : IsOpen (Set.range j.base) := j.isOpenMap.isOpen_range
    obtain ⟨u, hu⟩ : η ∈ Set.range j.base := hηw.mem_open hopen ⟨x', rfl⟩
    have hubad : ¬ IsRegularLocalRing (U.presheaf.stalk u) := by
      rw [isRegularLocalRing_stalk_iff_of_etale j, hu, isRegularLocalRing_stalk_spec_iff η]
      exact hqbad
    have hgu := hgen (g.base u) (by rwa [← isRegularLocalRing_stalk_iff_of_etale g])
    have hcomp := congrArg (fun k : U ⟶ Spec (.of R) ↦ (k.base u).asIdeal) hcomm
    simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] at hcomp
    rw [hgu, hu] at hcomp
    have hbot : (PrimeSpectrum.comap (algebraMap R' (nodalChartRing R' 0)) η).asIdeal = ⊥ := by
      change q.comap (algebraMap R' (nodalChartRing R' 0)) = ⊥
      ext r
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      rw [algebraMap_nodalChartRing_eq, ← Ideal.mem_comap]
      change MvPolynomial.C r ∈ q.comap (Ideal.Quotient.mk (Ideal.span {nodalEquation R' 0})) ↔ _
      rw [hqc]
      simp [p₀, RingHom.mem_ker]
    have hinj : Function.Injective (algebraMap R R') :=
      FaithfulSMul.algebraMap_injective R R'
    have hmax : maximalIdeal R = ⊥ := by
      refine hcomp.trans ?_
      change Ideal.comap (algebraMap R R')
        (PrimeSpectrum.comap (algebraMap R' (nodalChartRing R' 0)) η).asIdeal = ⊥
      rw [hbot, ← RingHom.ker_eq_comap_bot]
      exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
    exact IsDiscreteValuationRing.not_a_field R hmax
  · -- The image of the chosen point is the origin.
    have hmaxπ : (Ideal.span {π}).IsMaximal := isMaximal_span_singleton_of_irreducible hπ
    have hn : 1 ≤ n := by
      by_contra hn0
      have hn0 : n = 0 := by omega
      subst hn0
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      simpa using hhw
    have hπw : algebraMap R' (nodalChartRing R' (π ^ n)) π ∈ w.asIdeal := by
      rw [map_pow] at hhw
      exact w.isPrime.mem_of_pow_mem n hhw
    have horigin : nodalModelOrigin R' π n = w.asIdeal := by
      refine (isMaximal_nodalModelOrigin hmaxπ hn).eq_of_le w.isPrime.ne_top ?_
      rw [nodalModelOrigin, Ideal.span_le]
      rintro _ (rfl | rfl | rfl)
      · exact hπw
      · exact hcoord.1
      · exact hcoord.2
    exact ⟨n, ⟨{
      R' := R'
      π := π
      irreducible := hπ
      U := U
      toX := g
      toModel := j
      etale_toX := hg
      etale_toModel := hj
      comm := hcomm
      pt := x'
      pt_mem := hgx
      pt_origin := horigin.symm }⟩⟩

end Singular

/-! ### Chains of blowups at singular points -/

/-- **A sequence of blowups at singular closed points, through at-worst-nodal families.** For
`f : X ⟶ Spec R`, `NodalBlowupChain f Y h` says that `h : Y ⟶ X` is a composite
`Y = X_m ⟶ ⋯ ⟶ X_1 ⟶ X_0 = X` in which each `X_{i+1} ⟶ X_i` is the blowup of `X_i` in a closed
point at which `X_i` is singular (its local ring is not regular), and each `X_{i+1} ⟶ Spec R` is
at-worst-nodal of relative dimension one. -/
public inductive NodalBlowupChain {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) :
    ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop
  | refl : NodalBlowupChain f X (𝟙 X)
  | step {W : Scheme.{u}} {h : W ⟶ X} (hh : NodalBlowupChain f W h) (w : W)
      (hw : IsClosed ({w} : Set W)) (hsing : ¬ IsRegularLocalRing (W.presheaf.stalk w))
      (hnodal : IsAtWorstNodalOfRelativeDimensionOne
        (blowUpToBase (vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ h ≫ f)) :
      NodalBlowupChain f (blowUp (vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
        (blowUpToBase (vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ≫ h)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- A chain over the blowup of `X` in a singular closed point, preceded by that blowup, is a chain
over `X`. -/
public theorem NodalBlowupChain.of_blowUp {X : Scheme.{u}} {f : X ⟶ Spec (.of R)} {x : X}
    (hx : IsClosed ({x} : Set X)) (hsing : ¬ IsRegularLocalRing (X.presheaf.stalk x))
    (hnodal : IsAtWorstNodalOfRelativeDimensionOne
      (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) ≫ f))
    {Y : Scheme.{u}} {h : Y ⟶ blowUp (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))}
    (hc : NodalBlowupChain (blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) ≫ f) Y h) :
    NodalBlowupChain f Y (h ≫ blowUpToBase (vanishingIdeal (⟨{x}, hx⟩ : Closeds X))) := by
  induction hc with
  | refl =>
    rw [Category.id_comp]
    exact NodalBlowupChain.refl.step x hx hsing (by simpa using hnodal)
  | step hh w hw hs hn ih =>
    rw [Category.assoc]
    exact ih.step w hw hs (by simpa [Category.assoc] using hn)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The last member of a chain is at-worst-nodal of relative dimension one over the base. -/
public theorem NodalBlowupChain.isAtWorstNodalOfRelativeDimensionOne {X : Scheme.{u}}
    {f : X ⟶ Spec (.of R)} (hf : IsAtWorstNodalOfRelativeDimensionOne f) {Y : Scheme.{u}}
    {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) :
    IsAtWorstNodalOfRelativeDimensionOne (h ≫ f) := by
  cases hc with
  | refl => simpa using hf
  | step hh w hw hs hn => simpa [Category.assoc] using hn

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- Over a locally Noetherian scheme the composite of a chain of blowups is proper. -/
public theorem NodalBlowupChain.isProper {X : Scheme.{u}} [IsLocallyNoetherian X]
    {f : X ⟶ Spec (.of R)} {Y : Scheme.{u}} {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) :
    IsProper h := by
  induction hc with
  | refl => infer_instance
  | step hh w hw hs hn ih =>
    have := ih
    have : IsLocallyNoetherian _ := LocallyOfFiniteType.isLocallyNoetherian ‹_ ⟶ X›
    infer_instance

/-- If `g` is an isomorphism over an open `V`, local rings at points over `V` are regular
exactly when the local rings at their images are. -/
private theorem isRegularLocalRing_stalk_iff_of_isIso_morphismRestrict {Y X : Scheme.{u}}
    (g : Y ⟶ X) (V : X.Opens) (hg : IsIso (g ∣_ V)) (y : Y) (hy : y ∈ g ⁻¹ᵁ V) :
    IsRegularLocalRing (Y.presheaf.stalk y) ↔ IsRegularLocalRing (X.presheaf.stalk (g.base y)) := by
  let y₀ : (g ⁻¹ᵁ V).toScheme := ⟨y, hy⟩
  have h₁ := isRegularLocalRing_stalk_iff_of_isOpenImmersion (g ⁻¹ᵁ V).ι y₀
  have h₂ := isRegularLocalRing_stalk_iff_of_etale (g ∣_ V) y₀
  have h₃ := isRegularLocalRing_stalk_iff_of_isOpenImmersion V.ι ((g ∣_ V).base y₀)
  have hpt : V.ι.base ((g ∣_ V).base y₀) = g.base y := by
    rw [← Scheme.Hom.comp_apply, morphismRestrict_ι]
    rfl
  rw [hpt] at h₃
  exact h₁.symm.trans (h₂.trans h₃)

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- **A chain of blowups at singular points is an isomorphism over any open of regular points**:
none of its centres lies over such an open. -/
public theorem NodalBlowupChain.isIso_morphismRestrict {X : Scheme.{u}} {f : X ⟶ Spec (.of R)}
    {Y : Scheme.{u}} {h : Y ⟶ X} (hc : NodalBlowupChain f Y h) (V : X.Opens)
    (hV : ∀ y ∈ V, IsRegularLocalRing (X.presheaf.stalk y)) : IsIso (h ∣_ V) := by
  induction hc with
  | refl => infer_instance
  | @step W h hh w hw hs hn ih =>
    have := ih
    rw [morphismRestrict_comp]
    have : IsIso (blowUpToBase (vanishingIdeal (⟨{w}, hw⟩ : Closeds W)) ∣_ h ⁻¹ᵁ V) := by
      refine isIso_blowUpToBase_restrict_of_subset_compl_support _ _ ?_
      rw [coe_support_vanishingIdeal]
      intro z hz hzw
      have hzw' : z = w := hzw
      rw [hzw'] at hz
      exact hs ((isRegularLocalRing_stalk_iff_of_isIso_morphismRestrict h V ih w hz).mpr
        (hV _ hz))
    exact IsIso.comp_isIso' this ih

/-- The induction of [Stacks, Tag 0CDE], on the multiset of the exponents of charts at the
singular points, in the Dershowitz–Manna order. -/
private theorem exists_nodalBlowupChain_isRegular_aux (M : Multiset ℕ) :
    ∀ (X : Scheme.{u}) [CompactSpace X] (f : X ⟶ Spec (.of R)),
      IsAtWorstNodalOfRelativeDimensionOne f →
      (∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → f.base y = closedPoint R) →
      ∀ (S : Finset X), (∀ y, y ∈ S ↔ ¬ IsRegularLocalRing (X.presheaf.stalk y)) →
      ∀ ν : X → ℕ, (∀ y ∈ S, Nonempty (NodalChartAt f y (ν y))) → S.val.map ν = M →
      ∃ (Y : Scheme.{u}) (h : Y ⟶ X), NodalBlowupChain f Y h ∧ IsRegular Y := by
  classical
  refine (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction
    (C := fun M ↦ ∀ (X : Scheme.{u}) [CompactSpace X] (f : X ⟶ Spec (.of R)),
      IsAtWorstNodalOfRelativeDimensionOne f →
      (∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → f.base y = closedPoint R) →
      ∀ (S : Finset X), (∀ y, y ∈ S ↔ ¬ IsRegularLocalRing (X.presheaf.stalk y)) →
      ∀ ν : X → ℕ, (∀ y ∈ S, Nonempty (NodalChartAt f y (ν y))) → S.val.map ν = M →
      ∃ (Y : Scheme.{u}) (h : Y ⟶ X), NodalBlowupChain f Y h ∧ IsRegular Y) M ?_
  intro M ih X _ f hf hgen S hS ν hν hM
  have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have hnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  by_cases hSe : S = ∅
  · refine ⟨X, 𝟙 X, .refl, (isRegular_iff_regular_stalks X).mpr ⟨hnoeth, fun y ↦ ?_⟩⟩
    by_contra hy
    rw [← hS, hSe] at hy
    exact Finset.notMem_empty y hy
  obtain ⟨x, hxS⟩ := Finset.nonempty_iff_ne_empty.mpr hSe
  have hxbad := (hS x).mp hxS
  obtain ⟨c⟩ := hν x hxS
  have hn := c.two_le_of_not_isRegularLocalRing hxbad
  have hxC := (finite_setOf_not_isRegularLocalRing f hf hgen).2 x hxbad
  set I := vanishingIdeal (⟨{x}, hxC⟩ : Closeds X) with hI
  set b := blowUpToBase I with hb
  obtain ⟨hnodal', hE⟩ := blowUp_nodalChartAt hxC hf c hn
  have : QuasiCompact (blowUpToBase I) := inferInstance
  have : CompactSpace (blowUp I) := QuasiCompact.compactSpace_of_compactSpace (blowUpToBase I)
  -- Away from the centre, the blowup is singular exactly where the base is.
  have hiff (y : blowUp I) (hyx : b.base y ≠ x) :=
    not_congr (isRegularLocalRing_stalk_blowUp_iff_of_ne hxC y hyx)
  -- The singular points of the blowup lie over the closed point.
  have hgen' : ∀ y : blowUp I, ¬ IsRegularLocalRing ((blowUp I).presheaf.stalk y) →
      (b ≫ f).base y = closedPoint R := by
    intro y hy
    rw [Scheme.Hom.comp_apply]
    by_cases hyx : b.base y = x
    · rw [hyx]
      exact hgen x hxbad
    · exact hgen _ ((hiff y hyx).mp hy)
  obtain ⟨hfin', -⟩ := finite_setOf_not_isRegularLocalRing (b ≫ f) hnodal' hgen'
  set S' := hfin'.toFinset with hS'def
  have hS' : ∀ y, y ∈ S' ↔ ¬ IsRegularLocalRing ((blowUp I).presheaf.stalk y) := fun y ↦ by
    rw [hS'def, Set.Finite.mem_toFinset]
    rfl
  have hmem (y : blowUp I) (hyx : b.base y ≠ x) :=
    (hS' y).trans ((hiff y hyx).trans (hS _).symm)
  let ν' : blowUp I → ℕ := fun y ↦ if b.base y = x then ν x - 2 else ν (b.base y)
  have hν' : ∀ y ∈ S', Nonempty (NodalChartAt (b ≫ f) y (ν' y)) := by
    intro y hy
    by_cases hyx : b.base y = x
    · simp only [ν', ite_eq_left hyx]
      exact hE y hyx ((hS' y).mp hy)
    · simp only [ν', ite_eq_right hyx]
      obtain ⟨c'⟩ := hν (b.base y) ((hmem y hyx).mp hy)
      exact NodalChartAt.nonempty_blowUp_of_ne f hxC y hyx c'
  -- The exponents drop in the Dershowitz–Manna order.
  have hoff : (S'.val.filter (fun y ↦ ¬ b.base y = x)).map b.base = S.val.erase x := by
    refine (Multiset.Nodup.ext ?_ (S.nodup.erase x)).mpr fun t ↦ ?_
    · refine (S'.nodup.filter _).map_on fun y₁ hy₁ y₂ _ h ↦ ?_
      exact blowUpToBase_injective_of_ne hxC (Multiset.mem_filter.mp hy₁).2 h
    · rw [Multiset.mem_map, (S.nodup).mem_erase_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        obtain ⟨hyS', hyx⟩ := Multiset.mem_filter.mp hy
        exact ⟨hyx, (hmem y hyx).mp hyS'⟩
      · rintro ⟨htx, htS⟩
        obtain ⟨y, rfl⟩ := exists_blowUpToBase_eq_of_ne hxC htx
        exact ⟨y, Multiset.mem_filter.mpr ⟨(hmem y htx).mpr htS, htx⟩, rfl⟩
  have hDM : Multiset.IsDershowitzMannaLT (S'.val.map ν') M := by
    refine ⟨(S.val.erase x).map ν, (S'.val.filter (fun y ↦ b.base y = x)).map ν', {ν x},
      Multiset.singleton_ne_zero _, ?_, ?_, ?_⟩
    · have hsplit : S'.val.map ν' = (S'.val.filter (fun y ↦ ¬ b.base y = x)).map ν' +
          (S'.val.filter (fun y ↦ b.base y = x)).map ν' := by
        rw [← Multiset.map_add, add_comm, Multiset.filter_add_not]
      rw [hsplit, ← hoff, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun y hy ↦ ?_
      simp only [Function.comp_apply, ν', ite_eq_right (Multiset.mem_filter.mp hy).2]
    · rw [← hM, ← Multiset.cons_erase hxS, Multiset.map_cons, Multiset.erase_cons_head,
        add_comm, Multiset.singleton_add]
    · intro k hk
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hk
      refine ⟨ν x, Multiset.mem_singleton_self _, ?_⟩
      simp only [ν', ite_eq_left (Multiset.mem_filter.mp hy).2]
      omega
  obtain ⟨Y, h, hchain, hreg⟩ := ih _ hDM (blowUp I) (b ≫ f) hnodal' hgen' S' hS' ν' hν' rfl
  exact ⟨Y, h ≫ b, NodalBlowupChain.of_blowUp hxC hxbad hnodal' hchain, hreg⟩

/-- **[Stacks, Tag 0CDE], with the generic fibre hypothesis read on local rings.** If `X` is
quasi-compact, `f : X ⟶ Spec R` is at-worst-nodal of relative dimension one, and `X` is regular at
every point not over the closed point, then `X` is resolved by a chain of blowups at singular
closed points through at-worst-nodal families. -/
public theorem exists_nodalBlowupChain_isRegular_of_isRegularLocalRing {X : Scheme.{u}}
    [CompactSpace X] (f : X ⟶ Spec (.of R)) (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hreg : ∀ y : X, f.base y ≠ closedPoint R → IsRegularLocalRing (X.presheaf.stalk y)) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ X), NodalBlowupChain f Y h ∧ IsRegular Y := by
  classical
  have hgen : ∀ y : X, ¬ IsRegularLocalRing (X.presheaf.stalk y) → f.base y = closedPoint R :=
    fun y hy ↦ by_contra fun h ↦ hy (hreg y h)
  obtain ⟨hfin, -⟩ := finite_setOf_not_isRegularLocalRing f hf hgen
  let ν : X → ℕ := fun y ↦
    if hy : ¬ IsRegularLocalRing (X.presheaf.stalk y) then
      (nonempty_nodalChartAt_of_not_isRegularLocalRing f hf hgen y hy).choose
    else 0
  refine exists_nodalBlowupChain_isRegular_aux _ X f hf hgen hfin.toFinset
    (fun y ↦ by rw [Set.Finite.mem_toFinset]; rfl) ν (fun y hy ↦ ?_) rfl
  have hy : ¬ IsRegularLocalRing (X.presheaf.stalk y) := by
    rw [Set.Finite.mem_toFinset] at hy
    exact hy
  simp only [ν, dite_eq_left hy]
  exact (nonempty_nodalChartAt_of_not_isRegularLocalRing f hf hgen y hy).choose_spec

/-- **Stacks Project, Tag 0CDE.** Let `R` be a discrete valuation ring and let `X` be a
quasi-compact scheme which is at-worst-nodal of relative dimension one over `R`, with smooth
generic fibre. Then there is a finite sequence `X_m ⟶ ⋯ ⟶ X_1 ⟶ X_0 = X` such that
1. each `X_{i+1} ⟶ X_i` is the blowing up of `X_i` in a closed point at which `X_i` is singular,
2. each `X_i ⟶ Spec R` is at-worst-nodal of relative dimension one, and
3. `X_m` is regular.

The sequence is `Stacks.SemistableReduction.NodalBlowupChain f Y h` with `h : Y ⟶ X` its
composite, which records (1) and (2) at every step, and (3) is `IsRegular Y`. The generic fibre is
the fibre of `f` over the generic point `⊥` of `Spec R`. -/
@[stacks 0CDE]
public theorem exists_nodalBlowupChain_isRegular {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of R)) (hf : IsAtWorstNodalOfRelativeDimensionOne f)
    (hsmooth : Smooth (f.fiberToSpecResidueField (⊥ : PrimeSpectrum R))) :
    ∃ (Y : Scheme.{u}) (h : Y ⟶ X), NodalBlowupChain f Y h ∧ IsRegular Y := by
  have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  refine exists_nodalBlowupChain_isRegular_of_isRegularLocalRing f hf fun y hy ↦ ?_
  have h0 : (f.base y).asIdeal = ⊥ := by
    by_contra h0
    exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h0 (f.base y).isPrime)))
  have h : f.base y = (⊥ : PrimeSpectrum R) := PrimeSpectrum.ext h0
  refine isRegularLocalRing_stalk_of_smoothAt f y
    (smoothAt_of_flat_of_smoothAt_fiber f (flat hf.1.1) y ?_)
  have hs := hsmooth
  rw [← h] at hs
  exact (InfinitesimalLifting.smooth_iff_forall_smoothAt _).mp hs _

end Stacks.SemistableReduction

end
