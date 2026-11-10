module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.Topology.Dimension.Krull
public import StacksFrontier.RingTheory.Fitting.Rank
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# A local equation on a one-dimensional component of a curve

Let `R` be a Noetherian Jacobson ring of dimension at most one and `𝔭 ⊊ 𝔮` two primes of `R`.
Then there are a maximal ideal `𝔪 ⊇ 𝔭` and a nonzerodivisor `f ∈ 𝔪` whose zero locus is isolated
at `𝔪`: for some `g ∉ 𝔪`, the only prime containing `f` and not `g` is `𝔪`.

The maximal ideals containing `𝔭` are infinitely many (`R/𝔭` is a Jacobson domain which is not a
field), only finitely many of them are associated primes of `R`, and a maximal ideal which is not
an associated prime contains a nonzerodivisor by prime avoidance. The zero locus of a
nonzerodivisor `f` of a ring of dimension at most one consists of maximal ideals (`f` lies in no
minimal prime), all of them minimal over `(f)`, so it is finite; a `g` in all of them but `𝔪`
isolates `𝔪`.

On a proper curve `X` over a field this produces, on each one-dimensional irreducible component,
a closed point at which `X` has a local equation of a divisor meeting the component in an
isolated point. This is the input of the proof that families of curves are étale locally schemes
(Stacks 0E6F) which places one local divisor on each one-dimensional component of the fibre.

## Main results

* `Ideal.exists_isMaximal_mem_nonZeroDivisors_isolated`: the statement above.
* `AlgebraicGeometry.exists_isRegular_isolated_of_mem_genericPointsOne`: on a locally Noetherian
  Jacobson scheme of dimension at most one, on the closure of a generic point `ζ` of a
  one-dimensional component, a point `x` with an affine open neighbourhood `A` and a nonzerodivisor
  `f` of `Γ(A)` vanishing at `x` whose zero locus is isolated at `x`.
* `AlgebraicGeometry.exists_isRegular_isolated_of_flat_of_locallyQuasiFinite`: such an equation
  pulls back along a flat locally quasi-finite morphism (for instance an étale one) to an equation
  of the same kind at any point over `x`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
-/

@[expose] public section

open scoped nonZeroDivisors

namespace Ideal

variable {R : Type*} [CommRing R]

/-- In a ring of dimension at most one there is no chain of three primes. -/
theorem not_lt_lt_of_ringKrullDim_le_one (hR : ringKrullDim R ≤ 1) {P₀ P P' : Ideal R}
    [P₀.IsPrime] [P.IsPrime] [P'.IsPrime] (h₀ : P₀ < P) (h₁ : P < P') : False := by
  rcases (Order.krullDim_le_one_iff.1 hR) (⟨P, inferInstance⟩ : PrimeSpectrum R) with h | h
  · exact h.not_lt (show (⟨P₀, inferInstance⟩ : PrimeSpectrum R) < ⟨P, inferInstance⟩ from h₀)
  · exact h.not_lt (show (⟨P, inferInstance⟩ : PrimeSpectrum R) < ⟨P', inferInstance⟩ from h₁)

/-- **A prime containing a nonzerodivisor in a ring of dimension at most one is maximal.** -/
theorem isMaximal_of_mem_nonZeroDivisors [IsNoetherianRing R] (hR : ringKrullDim R ≤ 1)
    {f : R} (hf : f ∈ R⁰) {P : Ideal R} [hP : P.IsPrime] (hfP : f ∈ P) : P.IsMaximal := by
  obtain ⟨P₀, hP₀, hP₀P⟩ := Ideal.exists_minimalPrimes_le (J := P) bot_le
  have : P₀.IsPrime := hP₀.1.1
  have h₀ : P₀ < P := lt_of_le_of_ne hP₀P fun h =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes (h ▸ hfP) hP₀ hf
  obtain ⟨M, hM, hPM⟩ := P.exists_le_maximal hP.ne_top
  rcases eq_or_lt_of_le hPM with h | h
  · exact h ▸ hM
  · exact (not_lt_lt_of_ringKrullDim_le_one hR h₀ h).elim

/-- A finite intersection of ideals contained in a prime has one of its members contained in it. -/
private theorem exists_mem_le_of_sInf_le {S : Set (Ideal R)} (hS : S.Finite) {P : Ideal R}
    [hP : P.IsPrime] (h : sInf S ≤ P) : ∃ Q ∈ S, Q ≤ P := by
  have := (IsPrime.inf_le' hP (s := hS.toFinset) (f := id)).1
    (by rwa [Finset.inf_id_eq_sInf, Set.Finite.coe_toFinset])
  simpa using this

/-- **A local equation isolated at a maximal ideal over a non-maximal prime.** Let `R` be a
Noetherian Jacobson ring of dimension at most one and `𝔭 ⊊ 𝔮` primes of `R`. There are a maximal
ideal `𝔪 ⊇ 𝔭`, a nonzerodivisor `f ∈ 𝔪` and `g ∉ 𝔪` such that `𝔪` is the only prime containing
`f` and not containing `g`. -/
theorem exists_isMaximal_mem_nonZeroDivisors_isolated [IsNoetherianRing R] [IsJacobsonRing R]
    (hR : ringKrullDim R ≤ 1) {p q : Ideal R} [hp : p.IsPrime] [hq : q.IsPrime] (hpq : p < q) :
    ∃ m : Ideal R, m.IsMaximal ∧ p ≤ m ∧ ∃ f ∈ m, f ∈ R⁰ ∧ ∃ g ∉ m,
      ∀ P : Ideal R, P.IsPrime → f ∈ P → g ∉ P → P = m := by
  classical
  -- infinitely many maximal ideals contain `p`
  have hinf : {m : Ideal R | p ≤ m ∧ m.IsMaximal}.Infinite := by
    intro hfin
    obtain ⟨m, hm, hmp⟩ := exists_mem_le_of_sInf_le hfin
      (isJacobsonRing_iff_prime_eq.1 inferInstance p hp).le
    have hpm : p = m := le_antisymm hm.1 hmp
    exact hpq.ne (hpm.trans (hm.2.eq_of_le hq.ne_top (hpm ▸ hpq.le)))
  -- one of them is not an associated prime
  obtain ⟨m, ⟨hpm, hmax⟩, hmAss⟩ :=
    (hinf.sdiff (associatedPrimes.finite R R)).nonempty
  -- it contains a nonzerodivisor
  have hf : ∃ f ∈ m, f ∈ R⁰ := by
    by_contra hcon
    push Not at hcon
    have hsub : (m : Set R) ⊆ ⋃ P ∈ ((associatedPrimes.finite R R).toFinset : Set (Ideal R)),
        id P := by
      intro f hfm
      have h2 : f ∈ (⋃ P ∈ associatedPrimes R R, (P : Set R)) := by
        rw [biUnion_associatedPrimes_eq_compl_nonZeroDivisors]
        exact hcon f hfm
      simpa [Set.Finite.coe_toFinset] using h2
    obtain ⟨P, hP, hmP⟩ := (subset_union_prime (f := id) ⊥ ⊥ (fun P hP _ _ =>
      ((Set.Finite.mem_toFinset _).1 hP).isPrime)).1 hsub
    rw [Set.Finite.mem_toFinset] at hP
    exact hmAss (hmax.eq_of_le hP.isPrime.ne_top hmP ▸ hP)
  obtain ⟨f, hfm, hf⟩ := hf
  -- the zero locus of `f` is a finite set of maximal ideals
  have hmaxf : ∀ P : Ideal R, P.IsPrime → f ∈ P → P.IsMaximal := fun P hP hfP =>
    isMaximal_of_mem_nonZeroDivisors hR hf (hP := hP) hfP
  have hZfin : {P : Ideal R | P.IsPrime ∧ f ∈ P}.Finite := by
    refine (Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {f})).subset ?_
    rintro P ⟨hP, hfP⟩
    refine ⟨⟨hP, (Ideal.span_singleton_le_iff_mem _).2 hfP⟩, fun Q ⟨hQ, hfQ⟩ hQP => ?_⟩
    exact ((hmaxf Q hQ ((Ideal.span_singleton_le_iff_mem _).1 hfQ)).eq_of_le
      (hmaxf P hP hfP).ne_top hQP).symm.le
  have hnle : ¬ sInf ({P : Ideal R | P.IsPrime ∧ f ∈ P} \ {m}) ≤ m := by
    intro hle
    obtain ⟨P, hP, hPm⟩ := exists_mem_le_of_sInf_le hZfin.sdiff hle
    exact hP.2 ((hmaxf P hP.1.1 hP.1.2).eq_of_le hmax.ne_top hPm)
  obtain ⟨g, hgT, hgm⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  refine ⟨m, hmax, hpm, f, hfm, hf, g, hgm, fun P hP hfP hgP => ?_⟩
  by_contra hPm
  exact hgP (Submodule.mem_sInf.1 hgT P ⟨⟨hP, hfP⟩, hPm⟩)

end Ideal

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

/-- **A local equation on a one-dimensional component.** Let `V` be a locally Noetherian scheme
whose space is Jacobson, of dimension at most one, and `ζ` the generic point of an irreducible
component of dimension one. There are a point `x` of the closure of `ζ`, an affine open `A ∋ x`
and a nonzerodivisor `f` of `Γ(V, A)` vanishing at `x` whose zero locus in `A` is `{x}` near
`x`. -/
theorem exists_isRegular_isolated_of_mem_genericPointsOne {V : Scheme.{u}} [IsLocallyNoetherian V]
    [JacobsonSpace V] (hdim : topologicalKrullDim V ≤ 1) {ζ : V} (hζ : ζ ∈ genericPointsOne V) :
    ∃ (A : V.Opens) (_ : IsAffineOpen A) (f : Γ(V, A)) (x : V), x ∈ A ∧ x ∈ closure {ζ} ∧
      IsRegular f ∧ x ∉ V.basicOpen f ∧
        ∃ O : V.Opens, x ∈ O ∧ ∀ y ∈ O, y ∈ A → y ∉ V.basicOpen f → y = x := by
  obtain ⟨-, hζd⟩ := mem_genericPointsOne_iff.1 hζ
  -- a second point of the closure of `ζ`
  obtain ⟨x₁, hx₁, hx₁ζ⟩ : ∃ x₁ ∈ closure ({ζ} : Set V), x₁ ≠ ζ := by
    by_contra hcon
    push Not at hcon
    have hsub : closure ({ζ} : Set V) = {ζ} :=
      Set.Subset.antisymm hcon subset_closure
    have : Subsingleton (closure ({ζ} : Set V)) := by
      rw [hsub]
      infer_instance
    have : Nonempty (closure ({ζ} : Set V)) := ⟨⟨ζ, subset_closure rfl⟩⟩
    have h0 : topologicalKrullDim (closure ({ζ} : Set V)) = 0 :=
      topologicalKrullDim_eq_zero_of_discreteTopology_nonempty
    exact zero_ne_one (h0 ▸ hζd)
  obtain ⟨A, hA, hx₁A, -⟩ := exists_isAffineOpen_mem_and_subset (x := x₁) (U := ⊤) trivial
  have hζx₁ : ζ ⤳ x₁ := specializes_iff_mem_closure.2 hx₁
  have hζA : ζ ∈ A := hζx₁.mem_open A.isOpen hx₁A
  let R := Γ(V, A)
  have : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  have hemb : Topology.IsOpenEmbedding hA.fromSpec := hA.fromSpec.isOpenEmbedding
  have : JacobsonSpace (PrimeSpectrum R) := JacobsonSpace.of_isOpenEmbedding hemb
  have : IsJacobsonRing R := PrimeSpectrum.isJacobsonRing_iff_jacobsonSpace.2 inferInstance
  have hR : ringKrullDim R ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hemb.isInducing.topologicalKrullDim_le.trans hdim
  let Pζ := hA.primeIdealOf ⟨ζ, hζA⟩
  let P₁ := hA.primeIdealOf ⟨x₁, hx₁A⟩
  have hPζ : hA.fromSpec Pζ = ζ := hA.fromSpec_primeIdealOf ⟨ζ, hζA⟩
  have hP₁ : hA.fromSpec P₁ = x₁ := hA.fromSpec_primeIdealOf ⟨x₁, hx₁A⟩
  have hlt : Pζ.asIdeal < P₁.asIdeal := by
    refine lt_of_le_of_ne ?_ fun h => hx₁ζ ?_
    · exact (PrimeSpectrum.le_iff_specializes Pζ P₁).2
        (hemb.isInducing.specializes_iff.1 (by rwa [hPζ, hP₁]))
    · rw [← hP₁, ← hPζ]
      exact congrArg hA.fromSpec (PrimeSpectrum.ext h.symm)
  obtain ⟨m, hm, hζm, f, hfm, hf, g, hgm, hiso⟩ :=
    Ideal.exists_isMaximal_mem_nonZeroDivisors_isolated hR hlt
  let M : PrimeSpectrum R := ⟨m, hm.isPrime⟩
  have hmem : ∀ (h : R) (P : PrimeSpectrum R), hA.fromSpec P ∈ V.basicOpen h ↔ h ∉ P.asIdeal := by
    intro h P
    change P ∈ hA.fromSpec ⁻¹ᵁ V.basicOpen h ↔ _
    rw [hA.fromSpec_preimage_basicOpen]
    rfl
  refine ⟨A, hA, f, hA.fromSpec M, ?_, ?_, isRegular_iff_mem_nonZeroDivisors.2 hf, ?_,
    V.basicOpen g, (hmem g M).2 hgm, ?_⟩
  · exact hA.range_fromSpec.subset ⟨M, rfl⟩
  · rw [← specializes_iff_mem_closure, ← hPζ]
    exact ((PrimeSpectrum.le_iff_specializes Pζ M).1 hζm).map hA.fromSpec.continuous
  · exact fun h => (hmem f M).1 h hfm
  · intro y hyO hyA hyf
    obtain ⟨P, rfl⟩ := hA.range_fromSpec.symm.subset hyA
    rw [hmem g P] at hyO
    rw [hmem f P] at hyf
    exact congrArg hA.fromSpec (PrimeSpectrum.ext (hiso P.asIdeal P.isPrime (not_not.1 hyf) hyO))

/-- **An isolated local equation pulls back along a flat locally quasi-finite morphism.** Let
`h : F ⟶ V` be flat and locally quasi-finite, `A` an affine open of `V`, `f` a nonzerodivisor of
`Γ(V, A)` vanishing at `x ∈ A` whose zero locus in `A` is `{x}` near `x`, and `y ∈ F` over `x`.
Then on some affine open `N ∋ y` of `F` the pullback `b` of `f` is a nonzerodivisor of `Γ(F, N)`
vanishing at `y` whose zero locus in `N` is `{y}` near `y`. -/
theorem exists_isRegular_isolated_of_flat_of_locallyQuasiFinite {F V : Scheme.{u}} (h : F ⟶ V)
    [Flat h] [LocallyQuasiFinite h] {A : V.Opens} (hA : IsAffineOpen A) (f : Γ(V, A))
    (hf : IsRegular f) {x : V} (hxA : x ∈ A) (hx : x ∉ V.basicOpen f) (O : V.Opens) (hxO : x ∈ O)
    (hiso : ∀ y ∈ O, y ∈ A → y ∉ V.basicOpen f → y = x) (y : F) (hy : h y = x) :
    ∃ (N : F.Opens) (_ : IsAffineOpen N) (b : Γ(F, N)), y ∈ N ∧ IsRegular b ∧
      y ∉ F.basicOpen b ∧ ∃ O' : F.Opens, y ∈ O' ∧
        ∀ y' ∈ O', y' ∈ N → y' ∉ F.basicOpen b → y' = y := by
  obtain ⟨N, hN, hyN, hNA⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := h ⁻¹ᵁ A) (by simpa [hy] using hxA)
  let b : Γ(F, N) := h.appLE A N hNA f
  have hb : IsRegular b := by
    have hflat : (h.appLE A N hNA).hom.Flat := Flat.flat_appLE h hA hN hNA
    algebraize [(h.appLE A N hNA).hom]
    exact Stacks.Fitting.isRegular_algebraMap_of_flat hf
  have hmemb : ∀ y', y' ∈ F.basicOpen b ↔ y' ∈ N ∧ h y' ∈ V.basicOpen f := by
    intro y'
    rw [show F.basicOpen b = N ⊓ h ⁻¹ᵁ V.basicOpen f from Scheme.basicOpen_appLE h N A hNA f]
    rfl
  obtain ⟨u, hu, hu'⟩ := (isDiscrete_iff_forall_mem_exists_isOpen.1
    (h.isDiscrete_preimage_singleton x)) y (by simpa using hy)
  refine ⟨N, hN, b, hyN, hb, fun hyb => hx (hy ▸ ((hmemb y).1 hyb).2),
    ⟨u, hu⟩ ⊓ h ⁻¹ᵁ O, ⟨(hu'.symm.subset (Set.mem_singleton y)).1, by simpa [hy] using hxO⟩,
    ?_⟩
  rintro y' ⟨hy'u, hy'O⟩ hy'N hy'b
  exact hu'.subset ⟨hy'u, hiso (h y') hy'O (hNA hy'N) fun hf' => hy'b ((hmemb y').2 ⟨hy'N, hf'⟩)⟩

end AlgebraicGeometry
