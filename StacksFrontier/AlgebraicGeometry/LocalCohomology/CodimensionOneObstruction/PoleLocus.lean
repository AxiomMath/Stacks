module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Pole loci at a codimension-one point

Let `X` be an integral scheme, `z` a point whose local ring has dimension at most one, and `S` an
open subset avoiding `z`. The opens `S ⊓ D(g)`, for `g` a function regular near `z` and not
vanishing at `z`, are cofinal among the opens of `X` that contain the generic point and are
contained in `S`: for every such open `W` there is a `g` with `S ⊓ D(g) ≤ W`.

Geometrically this is the one-dimensionality of `𝒪_{X, z}` read as "a divisor through `z` has no
other component through `z`": the locus where a nonzero function `b` vanishes meets a small
neighbourhood of `z` only inside the closure of `z`, which `S` avoids.

## Main results

All names are in the namespace `Stacks.AlgebraicGeometry.CodimensionOneObstruction`.

* `exists_notMem_forall_le_of_height_le_one`: for `q` a prime of height at most one in a
  Noetherian domain and `b ≠ 0`, there is a `g ∉ q` such that every prime containing `b` but not
  `g` contains `q`.
* `exists_notMem_inter_basicOpen_subset`: the cofinality statement on a prime spectrum.
* `exists_basicOpen_inter_le`: the cofinality statement on a scheme.
* `mem_basicOpen_iff_notMem_primeIdealOf`: a point of an affine open lies in a basic open exactly
  when the function is outside the prime of the point.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CodimensionOneObstruction

/-! ### The pole locus of a function at a codimension-one prime -/

/-- Let `R` be a Noetherian domain, `q` a prime of height at most one
and `b ≠ 0`. Then there is `g ∉ q` such that every prime containing `b` and not containing `g`
contains `q`.

On `Spec R` this says that the vanishing locus of `b` meets the basic open `D(g)` only inside the
closure of `q`. -/
theorem exists_notMem_forall_le_of_height_le_one {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] {q : Ideal R} [hqp : q.IsPrime] (hq : q.height ≤ 1) {b : R}
    (hb0 : b ≠ 0) :
    ∃ g, g ∉ q ∧ ∀ p : Ideal R, p.IsPrime → b ∈ p → g ∉ p → q ≤ p := by
  classical
  set E : Set (Ideal R) := {p | p.IsPrime ∧ b ∈ p ∧ ¬ q ≤ p} with hE
  set J : Ideal R := sInf E with hJdef
  have hbJ : b ∈ J := Submodule.mem_sInf.mpr fun p hp => hp.2.1
  have hqfh : q.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    exact Or.inr fun h => by rw [h] at hq; exact absurd hq (by simp)
  have key : ¬ J ≤ q := by
    intro hJq
    have hqmin : q ∈ J.minimalPrimes := by
      obtain ⟨p₀, hp₀, hp₀q⟩ := Ideal.exists_minimalPrimes_le hJq
      have hp₀p : p₀.IsPrime := hp₀.1.1
      have hbp₀ : b ∈ p₀ := hp₀.1.2 hbJ
      have hp₀h : p₀.height ≠ 0 := by
        intro h
        rw [Ideal.height_eq_zero_iff] at h
        rw [show minimalPrimes R = (⊥ : Ideal R).minimalPrimes from rfl,
          Ideal.minimalPrimes_eq_subsingleton_self] at h
        have h' : p₀ = ⊥ := h
        exact hb0 (by simpa [h'] using hbp₀)
      have hp₀eq : p₀ = q := by
        by_contra hne
        have : p₀.FiniteHeight := Ideal.finiteHeight_of_le hp₀q hqp.ne_top'
        exact hp₀h (Order.lt_one_iff.mp
          (lt_of_lt_of_le (Ideal.height_strict_mono_of_isPrime
            (lt_of_le_of_ne hp₀q hne)) hq))
      exact hp₀eq ▸ hp₀
    set T : Set (Ideal R) := J.minimalPrimes \ {q} with hT
    have hTfin : T.Finite :=
      (Ideal.finite_minimalPrimes_of_isNoetherianRing R J).subset Set.sdiff_subset
    have hTprime : ∀ p₀ ∈ T, Ideal.IsPrime p₀ := fun p₀ hp₀ => hp₀.1.1.1
    have hchoice : ∀ p₀ ∈ T, ∃ a, a ∈ p₀ ∧ a ∉ q := by
      intro p₀ hp₀
      by_contra hcon
      push Not at hcon
      have hle : p₀ ≤ q := fun x hx => hcon x hx
      have hge : q ≤ p₀ := hqmin.2 ⟨hp₀.1.1.1, hp₀.1.1.2⟩ hle
      exact hp₀.2 (le_antisymm hle hge)
    choose! a hamem hanot using hchoice
    set s : R := ∏ p₀ ∈ hTfin.toFinset, a p₀ with hs
    have hsq : s ∉ q := by
      intro h
      rw [hs, Ideal.IsPrime.prod_mem_iff] at h
      obtain ⟨p₀, hp₀, hmem⟩ := h
      exact hanot p₀ (hTfin.mem_toFinset.mp hp₀) hmem
    have hsT : ∀ p₀ ∈ T, s ∈ p₀ := by
      intro p₀ hp₀
      have := hTprime p₀ hp₀
      exact Ideal.IsPrime.prod_mem_iff.mpr ⟨p₀, hTfin.mem_toFinset.mpr hp₀, hamem p₀ hp₀⟩
    have hsJ : s ∈ J := by
      refine Submodule.mem_sInf.mpr fun p hp => ?_
      have hpp : Ideal.IsPrime p := hp.1
      obtain ⟨p₁, hp₁, hp₁p⟩ := Ideal.exists_minimalPrimes_le (sInf_le hp : J ≤ p)
      have hne : p₁ ≠ q := fun h => hp.2.2 (h ▸ hp₁p)
      exact hp₁p (hsT p₁ ⟨hp₁, hne⟩)
    exact hsq (hJq hsJ)
  obtain ⟨g, hgJ, hgq⟩ := Set.not_subset.mp key
  refine ⟨g, hgq, fun p hp hbp hgp => ?_⟩
  by_contra hqle
  exact hgp (sInf_le (show p ∈ E from ⟨hp, hbp, hqle⟩) hgJ)

/-- Let `B` be a Noetherian domain,
`q` a prime of height at most one, `x` the generic point and `S` an open set avoiding `q`. Then
every open `W` containing `x` contains `S ∩ D(g)` for some `g ∉ q`. -/
theorem exists_notMem_inter_basicOpen_subset {B : Type u} [CommRing B] [IsDomain B]
    [IsNoetherianRing B] {q x : PrimeSpectrum B} (hq : q.asIdeal.height ≤ 1)
    (hxbot : x.asIdeal = ⊥) {S W : Set (PrimeSpectrum B)} (hS : IsOpen S) (hqS : q ∉ S)
    (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ g : B, g ∉ q.asIdeal ∧
      S ∩ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum B)) ⊆ W := by
  classical
  set I : Ideal B := PrimeSpectrum.vanishingIdeal Wᶜ with hI
  have hzl : PrimeSpectrum.zeroLocus (I : Set B) = Wᶜ := by
    rw [hI, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hW.isClosed_compl.closure_eq
  have hInb : ∃ b ∈ I, b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hmem : x ∈ PrimeSpectrum.zeroLocus (I : Set B) := by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro b hb
      rw [hxbot]
      simpa using hcon b hb
    rw [hzl] at hmem
    exact hmem hxW
  obtain ⟨b, hbI, hb0⟩ := hInb
  obtain ⟨g, hgq, hg⟩ := exists_notMem_forall_le_of_height_le_one (q := q.asIdeal) hq hb0
  refine ⟨g, hgq, ?_⟩
  rintro p ⟨hpS, hpg⟩
  by_contra hpW
  have hbp : b ∈ p.asIdeal :=
    (PrimeSpectrum.mem_zeroLocus _ _).mp (by rw [hzl]; exact hpW) hbI
  have hqp' : q.asIdeal ≤ p.asIdeal :=
    hg p.asIdeal p.isPrime hbp ((PrimeSpectrum.mem_basicOpen g p).mp hpg)
  exact hqS (((PrimeSpectrum.le_iff_specializes q p).mp hqp').mem_open hS hpS)

/-! ### Reading basic opens off the prime of a point -/

/-- A point of an affine open lies in an open `U` exactly when its prime lies in the preimage of `U`
under `fromSpec`. -/
private theorem mem_iff_primeIdealOf_mem_fromSpec_preimage {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) (U : X.Opens) :
    x ∈ U ↔ hV.primeIdealOf ⟨x, hx⟩ ∈ hV.fromSpec ⁻¹ᵁ U := by
  change _ ↔ hV.fromSpec.base (hV.primeIdealOf ⟨x, hx⟩) ∈ U
  rw [hV.fromSpec_primeIdealOf ⟨x, hx⟩]

/-- A point of an affine open lies in the basic open of a function exactly when the function does
not lie in the prime ideal attached to the point. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) (f : Γ(X, V)) :
    x ∈ X.basicOpen f ↔ f ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  rw [← PrimeSpectrum.mem_basicOpen f (hV.primeIdealOf ⟨x, hx⟩),
    ← hV.fromSpec_preimage_basicOpen f]
  exact mem_iff_primeIdealOf_mem_fromSpec_preimage hV hx _

/-! ### Cofinality of the basic opens through `z` on a scheme -/

/-- Let `X` be an integral locally Noetherian scheme, `V₀` an affine
open containing a point `z` whose local ring has dimension at most one, and `S` an open subset
avoiding `z`. Then every open `W` containing the generic point contains `S ⊓ D(g)` for some
`g : Γ(X, V₀)` with `z ∈ D(g)`.

This is the first paragraph of [Stacks, Tag 0AWC] in geometric form. -/
theorem exists_basicOpen_inter_le {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    {V₀ : X.Opens} (hV₀ : IsAffineOpen V₀) {z : X} (hz : z ∈ V₀)
    (hdim : ringKrullDim (X.presheaf.stalk z) ≤ 1) {S W : X.Opens} (hzS : z ∉ S)
    (hW : genericPoint X ∈ W) :
    ∃ g : Γ(X, V₀), z ∈ X.basicOpen g ∧ S ⊓ X.basicOpen g ≤ W := by
  classical
  have hne : Nonempty V₀ := ⟨⟨z, hz⟩⟩
  have : IsDomain Γ(X, V₀) := IsIntegral.component_integral V₀
  have : IsNoetherianRing Γ(X, V₀) := IsLocallyNoetherian.component_noetherian ⟨V₀, hV₀⟩
  have hgenV₀ : genericPoint X ∈ V₀ :=
    ((genericPoint_spec X).mem_open_set_iff V₀.isOpen).mpr (by simpa using hne)
  set q := hV₀.primeIdealOf ⟨z, hz⟩ with hqdef
  set xg := hV₀.primeIdealOf ⟨genericPoint X, hgenV₀⟩ with hxgdef
  have hxbot : xg.asIdeal = ⊥ := by
    rw [hxgdef, hV₀.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    exact PrimeSpectrum.asIdeal_bot
  have hqh : q.asIdeal.height ≤ 1 := by
    let := X.presheaf.algebra_section_stalk (⟨z, hz⟩ : V₀)
    have := hV₀.isLocalization_stalk ⟨z, hz⟩
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal (X.presheaf.stalk z)] at hdim
    exact_mod_cast hdim
  obtain ⟨g, hgq, hsub⟩ := exists_notMem_inter_basicOpen_subset (q := q) (x := xg) hqh hxbot
    (S := (hV₀.fromSpec ⁻¹ᵁ S : (Spec Γ(X, V₀)).Opens).carrier)
    (W := (hV₀.fromSpec ⁻¹ᵁ W : (Spec Γ(X, V₀)).Opens).carrier)
    (hV₀.fromSpec ⁻¹ᵁ S).isOpen
    (fun hmem => hzS ((mem_iff_primeIdealOf_mem_fromSpec_preimage hV₀ hz S).mpr hmem))
    (hV₀.fromSpec ⁻¹ᵁ W).isOpen
    ((mem_iff_primeIdealOf_mem_fromSpec_preimage hV₀ hgenV₀ W).mp hW)
  refine ⟨g, (mem_basicOpen_iff_notMem_primeIdealOf hV₀ hz g).mpr hgq, ?_⟩
  intro p hp
  obtain ⟨hpS, hpg⟩ := hp
  obtain ⟨p', hp'⟩ : p ∈ Set.range hV₀.fromSpec.base := by
    rw [hV₀.range_fromSpec]; exact X.basicOpen_le g hpg
  have h1 : p' ∈ (hV₀.fromSpec ⁻¹ᵁ S : (Spec Γ(X, V₀)).Opens) := by
    change hV₀.fromSpec p' ∈ S
    rw [hp']; exact hpS
  have h2 : p' ∈ (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum Γ(X, V₀))) := by
    rw [← hV₀.fromSpec_preimage_basicOpen g]
    change hV₀.fromSpec p' ∈ X.basicOpen g
    rw [hp']; exact hpg
  have h3 := hsub ⟨h1, h2⟩
  change p ∈ W
  rw [← hp']
  exact h3

end Stacks.AlgebraicGeometry.CodimensionOneObstruction

end
