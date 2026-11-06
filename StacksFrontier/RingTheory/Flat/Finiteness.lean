module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.TorsionFree
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.GradedFinitePresentation
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.Flat.OpenFlatLocusNoetherian
public import StacksFrontier.RingTheory.GradedAlgebra.ReesModel
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.Separation

@[expose] public section

/-!
# Flatness and finiteness conditions

Throughout, `R` is a commutative ring satisfying the standing hypothesis of
[Stacks, Section 15.25]: there are finitely many primes `p₁, …, p_m` of `R` for which the
map `R → ∏ⱼ R_{pⱼ}` is injective.  This is packaged as `HasFiniteDetectingPrimes R`.

Under that hypothesis a module which is finite over a polynomial ring `R[x₁, …, x_n]` and flat
over `R` is finitely presented as soon as it is finitely presented after localizing at every
prime of `R`, and the same holds for algebras of finite type and for nonnegatively graded
algebras with finite degree-zero part.  Specializing to a valuation ring `A` — where the zero
ideal alone detects elements — gives Nagata's theorem: a flat algebra of finite type over `A` is
finitely presented, and the corresponding statement for essentially-of-finite-type algebras.

## Main definitions

* `HasFiniteDetectingPrimes`: the standing hypothesis of [Stacks, Section 15.25], that finitely
  many prime localizations jointly detect the elements of the ring.

## Main results

* `Module.finitePresentation_of_flat_of_localized` (Tag 053A): a finite module over
  `R[x₁, …, x_n]` which is flat over `R` and finitely presented after localizing at every prime
  of `R` is finitely presented.
* `Module.exists_away_finitePresentation_flat_of_flat_atPrime`: the flat-at-a-point form of the
  preceding result.  For `R → S` of finite presentation and `M` a finite `S`-module which is
  flat over `R` only at one prime `q` of `S`, there is a `g ∉ q` with `M_g` finitely presented
  over `S_g` and flat over `R`.
* `Algebra.FinitePresentation.of_flat_of_localized` (Tag 053B): the same statement for a flat
  algebra of finite type.
* `finitePresentation_of_flat_of_finiteType_of_finite_degreeZero` (Tag 053D): the graded version,
  for a nonnegatively graded `R`-algebra of finite type with finite degree-zero part, together
  with its finite graded modules.
* `finitePresentation_of_flat_of_finiteType_of_valuationRing` (Tag 053E): Nagata's theorem over a
  valuation ring, for algebras of finite type and for finite modules over them.
* `essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing` (Tag 0GSE):
  the essentially-of-finite-type version of the preceding result.
* `hasFiniteDetectingPrimes_of_standard_conditions` (Tag 05GS): local rings, Noetherian rings,
  domains, reduced rings with finitely many minimal primes and rings with finitely many weakly
  associated primes all satisfy the standing hypothesis.

## Implementation notes

The polynomial ring in finitely many variables is `MvPolynomial (Fin n) R`, and localizing it at
a prime `p` of `R` means localizing at `Algebra.algebraMapSubmonoid _ p.asIdeal.primeCompl`, the
image of the complement of `p`.

For a graded algebra the algebra grading is indexed by `ℕ` and the module grading by `ℤ`, with
the degree action `(n, d) ↦ (n : ℤ) + d`.  Mathlib provides no `VAdd ℕ ℤ`; the one used here is
`natVAddInt`, taken from `StacksFrontier.RingTheory.GradedAlgebra.ReesModel` so that the graded Rees
model of Tag 052N feeds directly into Tag 053D.

Tags 053E and 0GSE are proved by descending from the graded Rees model of Tag 052N
(`StacksFrontier.RingTheory.GradedAlgebra.ReesModel`); the graded algebra `reesS A B gens` produced
there lives in `Type (max u v)` for `A : Type u` and `B : Type v`, so Tag 053D is applied at that
universe.

## References

* [Nagata, *A general theory of algebraic geometry over Dedekind domains. II*][Nagata-Finitely]
* [Stacks Project, Tag 053A](https://stacks.math.columbia.edu/tag/053A)
* [Stacks Project, Tag 053B](https://stacks.math.columbia.edu/tag/053B)
* [Stacks Project, Tag 053D](https://stacks.math.columbia.edu/tag/053D)
* [Stacks Project, Tag 053E](https://stacks.math.columbia.edu/tag/053E)
* [Stacks Project, Tag 05GS](https://stacks.math.columbia.edu/tag/05GS)
* [Stacks Project, Tag 0GSE](https://stacks.math.columbia.edu/tag/0GSE)
-/

universe u v w

open TensorProduct

attribute [local instance] natVAddInt

/-- The degree action of `ℕ` on `ℤ` used for graded modules over a nonnegatively graded algebra
adds the cast: `n +ᵥ d = (n : ℤ) + d`.  Mathlib supplies no `VAdd ℕ ℤ`, so the instance is
`natVAddInt` from the graded Rees model, which carries no `AddAction` simp lemmas. -/
private theorem natVAdd_eq (n : ℕ) (d : ℤ) : n +ᵥ d = (n : ℤ) + d := rfl

/-! ### The standing hypothesis of Section 15.25 -/

/-- **The standing hypothesis of [Stacks, Section 15.25].** A commutative ring `R` *has finite
detecting primes* if there is a finite set of primes `p₁, …, p_m` of `R` such that the map
`R → ∏ⱼ R_{pⱼ}` into the product of the localizations is injective.  This is the hypothesis
shared by Tags 053A, 053B and 053D, and is supplied by Tag 05GS for the usual classes of
rings. -/
def HasFiniteDetectingPrimes (R : Type u) [CommRing R] : Prop :=
  ∃ primes : Finset (PrimeSpectrum R),
    Function.Injective fun r : R ↦ fun p : primes ↦
      algebraMap R (Localization.AtPrime p.1.asIdeal) r

/-- In a local ring the complement of the maximal ideal consists of regular elements, so the
single localization at the maximal ideal already detects elements. -/
theorem HasFiniteDetectingPrimes.of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    HasFiniteDetectingPrimes R := by
  let p : PrimeSpectrum R := ⟨IsLocalRing.maximalIdeal R, inferInstance⟩
  refine ⟨{p}, fun x y hxy => ?_⟩
  have hreg : p.asIdeal.primeCompl ≤ nonZeroDivisors R := by
    intro s hs
    exact isRegular_iff_mem_nonZeroDivisors.mp (IsLocalRing.notMem_maximalIdeal.mp hs).isRegular
  exact (IsLocalization.injective (M := p.asIdeal.primeCompl)
    (Localization.AtPrime p.asIdeal) hreg) (congrFun hxy ⟨p, Finset.mem_singleton_self p⟩)

/-- In a domain the localization at the zero ideal is the fraction field, which detects
elements. -/
theorem HasFiniteDetectingPrimes.of_isDomain (R : Type u) [CommRing R] [IsDomain R] :
    HasFiniteDetectingPrimes R := by
  let p : PrimeSpectrum R := ⟨⊥, inferInstance⟩
  refine ⟨{p}, fun x y hxy => ?_⟩
  apply IsLocalization.injective (M := p.asIdeal.primeCompl)
    (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl_le_nonZeroDivisors
  exact congrFun hxy ⟨p, Finset.mem_singleton_self p⟩

/-- If `R` has only finitely many weakly associated primes — primes minimal over the annihilator
of an element of `R` — then those primes detect elements of `R`. -/
theorem HasFiniteDetectingPrimes.of_finite_weaklyAssociatedPrimes {R : Type u} [CommRing R]
    (hfin : {p : Ideal R | ∃ x : R, p ∈ (R ∙ x).annihilator.minimalPrimes}.Finite) :
    HasFiniteDetectingPrimes R := by
  let W : Set (PrimeSpectrum R) :=
    {p | ∃ x : R, p.asIdeal ∈ (R ∙ x).annihilator.minimalPrimes}
  have hW : W.Finite := by
    apply Set.Finite.preimage (f := fun p : PrimeSpectrum R => p.asIdeal) ?_ hfin
    intro p _ q _ hpq
    exact PrimeSpectrum.ext hpq
  let primes := hW.toFinset
  refine ⟨primes, fun x y hxy => ?_⟩
  let f : ∀ p : {p : PrimeSpectrum R // p ∈ W},
      R →ₗ[R] Localization.AtPrime p.1.asIdeal :=
    fun p => Algebra.linearMap R (Localization.AtPrime p.1.asIdeal)
  apply Module.injective_pi_localization_weaklyAssociatedPrimes f
  ext p
  show algebraMap R (Localization.AtPrime p.1.asIdeal) x =
    algebraMap R (Localization.AtPrime p.1.asIdeal) y
  exact congrFun hxy ⟨p.1, hW.mem_toFinset.mpr p.2⟩

/-! ### Shared finiteness and valuation-ring helpers -/

/-- Finite presentation passes up a finite extension: if `S` is a finite `P`-algebra and `M` is a
finitely presented `P`-module, then `M` is a finitely presented `S`-module. -/
private theorem finitePresentation_of_restrictScalars_of_finite
    {P : Type*} {S : Type*} {M : Type*} [CommRing P] [Ring S]
    [Algebra P S] [AddCommGroup M] [Module S M] [Module P M]
    [IsScalarTower P S M] [Module.Finite P S]
    [Module.FinitePresentation P M] :
    Module.FinitePresentation S M := by
  classical
  have : Module.Finite S M := Module.Finite.of_restrictScalars_finite P S M
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' S M
  have hker : (LinearMap.ker (f.restrictScalars P)).FG :=
    Module.FinitePresentation.fg_ker (f.restrictScalars P) hf
  have hkerS : (LinearMap.ker f).FG := by
    rw [← Module.Finite.iff_fg] at hker ⊢
    have hkerP : Module.Finite P (LinearMap.ker f) := by
      rw [show LinearMap.ker (f.restrictScalars P) =
        (LinearMap.ker f).restrictScalars P from rfl] at hker
      exact hker
    exact Module.Finite.of_restrictScalars_finite P S _
  exact Module.finitePresentation_of_surjective f hf hkerS

/-- A valuation ring is a Bézout domain, so over it torsion-freeness is equivalent to
flatness. -/
@[ega "0 6.3.4" "converse when A is a DVR", sga "1 IV 1.3" "(ii)"]
public theorem Module.Flat.of_isTorsionFree_of_valuationRing
    {A : Type*} {X : Type*} [CommRing A] [IsDomain A] [ValuationRing A]
    [AddCommGroup X] [Module A X] [Module.IsTorsionFree A X] :
    Module.Flat A X := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
    ← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-! ### Tag 053A: finite presentation over a polynomial ring -/

/-- The quotient of a finitely presented module by a finitely generated submodule is finitely
presented. -/
private theorem finitePresentation_quotient_of_fg
    {P : Type*} [CommRing P] {F : Type*}
    [AddCommGroup F] [Module P F] [Module.FinitePresentation P F]
    (K : Submodule P F) (hK : K.FG) :
    Module.FinitePresentation P (F ⧸ K) := by
  apply Module.finitePresentation_of_surjective K.mkQ K.mkQ_surjective
  simpa only [Submodule.ker_mkQ] using hK

/-- A finite module admits a finitely presented flat approximation near each prime at which it
is flat over the base.  Flatness is needed only at the prime `q`, not globally:  what the proof
uses is flatness of `M_q`, which is where the openness of the relative flat locus is applied. -/
private theorem exists_away_finitePresentation
    {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M]
    (primes : Finset (PrimeSpectrum R))
    (hprimes : Function.Injective (fun r : R ↦ fun p : primes ↦
      algebraMap R (Localization.AtPrime p.1.asIdeal) r))
    [Module.Finite S M]
    (hlocal : ∀ p : PrimeSpectrum R,
      Module.FinitePresentation
        (Localization (Algebra.algebraMapSubmonoid S
          p.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid S
          p.asIdeal.primeCompl) M))
    (q : PrimeSpectrum S)
    (hflat : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    ∃ g ∉ q.asIdeal, Module.FinitePresentation (Localization.Away g)
      (LocalizedModule.Away g M) ∧ Module.Flat R (LocalizedModule.Away g M) := by
  classical
  let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R S) q
  let ps := insert p primes
  let T : PrimeSpectrum R → Submonoid S := fun p ↦
    Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' S M
  have hK : ∀ i : ps, ((LinearMap.ker f).localized (T i)).FG := by
    intro i
    have := hlocal i
    exact Submodule.fg_localized_ker (T i) f hf
  obtain ⟨L, hL, hLfg, hLeq⟩ :=
    Submodule.exists_fg_le_forall_localized_eq (fun i : ps ↦ T i) (LinearMap.ker f) hK
  have hden (i : ps) (x : Fin k → S) (hx : x ∈ LinearMap.ker f) :
      ∃ t : T i, (t : S) • x ∈ L :=
    Submodule.exists_smul_mem_of_localized_le (T i) (le_of_eq (hLeq i).symm) hx
  have hfp : Module.FinitePresentation S ((Fin k → S) ⧸ L) :=
    finitePresentation_quotient_of_fg L hLfg
  let f' := L.liftQ f hL
  have hf' : Function.Surjective f' := by
    intro m
    obtain ⟨x, rfl⟩ := hf m
    exact ⟨L.mkQ x, rfl⟩
  have hqi : Function.Injective (LocalizedModule.map q.asIdeal.primeCompl f') := by
    apply Submodule.localized_liftQ_injective q.asIdeal.primeCompl f L hL
    intro x hx
    obtain ⟨t, ht⟩ := hden ⟨p, Finset.mem_insert_self p primes⟩ x hx
    obtain ⟨r, hr, he⟩ := t.property
    have htq : (t : S) ∈ q.asIdeal.primeCompl := by
      rw [← he]
      exact hr
    apply (IsLocalizedModule.eq_zero_iff q.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap q.asIdeal.primeCompl ((Fin k → S) ⧸ L))).mpr
    refine ⟨⟨t, htq⟩, ?_⟩
    show (t : S) • L.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero L).mpr ht
  have hflatqM : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M) := hflat
  have hflatq : Module.Flat R (LocalizedModule.AtPrime q.asIdeal ((Fin k → S) ⧸ L)) :=
    Module.Flat.of_linearEquiv ((LinearEquiv.ofBijective
      (LocalizedModule.map q.asIdeal.primeCompl f')
      ⟨hqi, LocalizedModule.map_surjective q.asIdeal.primeCompl f' hf'⟩).restrictScalars R)
  obtain ⟨g, hg, hflatg⟩ := Module.exists_away_flat_of_flat_atPrime (R := R) q hflatq
  have hgi : Function.Injective (LocalizedModule.map (Submonoid.powers g) f') := by
    apply Submodule.localized_liftQ_injective (Submonoid.powers g) f L hL
    intro x hx
    apply Module.eq_zero_of_forall_exists_smul_eq_zero_of_flat
      (fun i : primes ↦ i.1.asIdeal.primeCompl) hprimes
    intro i
    obtain ⟨t, ht⟩ := hden ⟨i, Finset.mem_insert_of_mem i.property⟩ x hx
    obtain ⟨r, hr, he⟩ := t.property
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [← algebraMap_smul S r, he, LocalizedModule.smul'_mk, ← map_smul]
    rw [show L.mkQ ((t : S) • x) = 0 from (Submodule.Quotient.mk_eq_zero L).mpr ht]
    exact LocalizedModule.zero_mk _
  have e := LinearEquiv.ofBijective (LocalizedModule.map (Submonoid.powers g) f')
    ⟨hgi, LocalizedModule.map_surjective (Submonoid.powers g) f' hf'⟩
  exact ⟨g, hg, Module.FinitePresentation.of_equiv e,
    Module.Flat.of_linearEquiv (e.restrictScalars R).symm⟩

/-- **Stacks Tag 053A.** Let `S = R[x₁, …, x_n]` and let `M` be a finite `S`-module which is flat
over `R`.  If finitely many prime localizations jointly detect elements of `R` and `M` is
finitely presented over `S` after localizing at every prime of `R`, then `M` is finitely
presented over `S`. -/
@[stacks 053A]
theorem Module.finitePresentation_of_flat_of_localized
    {R : Type u} [CommRing R] {n : ℕ} {M : Type v} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) R) M] [Module R M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (hprimes : HasFiniteDetectingPrimes R)
    [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M]
    (hlocal : ∀ p : PrimeSpectrum R,
      Module.FinitePresentation
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl) M)) :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  classical
  obtain ⟨primes, hprimes⟩ := hprimes
  let s : Set (MvPolynomial (Fin n) R) := {g |
    Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) hne
    obtain ⟨g, hgq, hgf, -⟩ :=
      exists_away_finitePresentation primes hprimes hlocal ⟨q, hq.isPrime⟩
        (Module.Flat.of_isLocalizedModule_of_tower (Ideal.primeCompl q)
          (LocalizedModule.mkLinearMap (Ideal.primeCompl q) M))
    exact hgq (hle (Ideal.subset_span hgf))
  exact Module.FinitePresentation.of_localizationSpan s hs (fun g ↦ g.property)

/-- **Finite presentation and flatness on a basic open around a prime of relative flatness.**
Let `R → S` be of finite presentation, let `M` be a finite `S`-module, and suppose finitely many
prime localizations jointly detect the elements of `R` and that `M` is finitely presented after
localizing at every prime of `R`.  If `M` is flat over `R` at a prime `q` of `S`, then there is
a `g ∉ q` such that `M_g` is a finitely presented `S_g`-module and flat over `R`.

This is the flat-at-a-point form of Tag 053A:  the hypothesis of global flatness is replaced by
flatness of the single localization `M_q`, which is all that the proof of Tag 053A uses, and the
flatness of the resulting `M_g` is recorded alongside its finite presentation. -/
theorem Module.exists_away_finitePresentation_flat_of_flat_atPrime
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S] {M : Type w} [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M] [Module.Finite S M]
    (hprimes : HasFiniteDetectingPrimes R)
    (hlocal : ∀ p : PrimeSpectrum R,
      Module.FinitePresentation
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))
        (LocalizedModule (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) M))
    (q : PrimeSpectrum S) (hq : Module.Flat R (LocalizedModule.AtPrime q.asIdeal M)) :
    ∃ g ∉ q.asIdeal,
      Module.FinitePresentation (Localization.Away g) (LocalizedModule.Away g M) ∧
        Module.Flat R (LocalizedModule.Away g M) :=
  let ⟨primes, hinj⟩ := hprimes
  exists_away_finitePresentation primes hinj hlocal q hq

/-! ### Tag 053B: finite presentation of a flat algebra of finite type -/

/-- **Stacks Tag 053B.** Let `R → S` be a flat ring map of finite type.  Suppose finitely many
prime localizations jointly detect elements of `R`, and that for every prime `p` of `R` the
localization of `S` at `p` is finitely presented over `R` localized at `p`.  Then `S` is
finitely presented over `R`. -/
@[stacks 053B]
theorem Algebra.FinitePresentation.of_flat_of_localized
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    (hprimes : HasFiniteDetectingPrimes R)
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hlocal : ∀ p : PrimeSpectrum R,
      Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) :
    Algebra.FinitePresentation R S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  let : Algebra (MvPolynomial (Fin n) R) S := f.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) S :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite (MvPolynomial (Fin n) R) S :=
    RingHom.Finite.of_surjective f.toRingHom hf
  have hm : Module.FinitePresentation (MvPolynomial (Fin n) R) S := by
    apply Module.finitePresentation_of_flat_of_localized hprimes
    intro p
    have hp := hlocal p
    let floc := IsLocalization.mapₐ p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
        p.asIdeal.primeCompl))
      (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) f
    have hfloc : Function.Surjective floc :=
      IsLocalization.mapₐ_surjective_of_surjective p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) f hf
    let : Algebra
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) :=
      floc.toRingHom.toAlgebra
    have : IsScalarTower (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext r
        exact (floc.commutes r).symm)
    have : IsScalarTower (MvPolynomial (Fin n) R)
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) :=
      IsScalarTower.of_algebraMap_eq'
        (R := MvPolynomial (Fin n) R)
        (S := Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (A := Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) (by
        apply RingHom.ext
        intro x
        show algebraMap (MvPolynomial (Fin n) R)
          (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) x =
            floc (algebraMap (MvPolynomial (Fin n) R)
              (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
                p.asIdeal.primeCompl)) x)
        calc
          _ = algebraMap S (Localization (Algebra.algebraMapSubmonoid S
              p.asIdeal.primeCompl)) (f x) := by
            simpa [RingHom.algebraMap_toAlgebra] using
              (IsScalarTower.algebraMap_apply (MvPolynomial (Fin n) R) S
                (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) x)
          _ = _ := by simp [floc, IsLocalization.mapₐ_coe])
    have : IsLocalization
        (p.asIdeal.primeCompl.map (algebraMap R (MvPolynomial (Fin n) R)))
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl)) := by
      simpa [Algebra.algebraMapSubmonoid] using
        (inferInstance : IsLocalization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)
          (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
            p.asIdeal.primeCompl)))
    have : Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl)) := by
      rw [← RingHom.finitePresentation_algebraMap]
      exact RingHom.finitePresentation_localizationPreserves
        (algebraMap R (MvPolynomial (Fin n) R)) p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl)) (by rw [RingHom.finitePresentation_algebraMap]; infer_instance)
    have : Module.FinitePresentation
        (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
          p.asIdeal.primeCompl))
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)) :=
      Module.finitePresentation_of_surjective (Algebra.linearMap _ _) hfloc
        (Algebra.FinitePresentation.ker_fG_of_surjective floc hfloc)
    let g : S →ₗ[MvPolynomial (Fin n) R]
        Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) :=
      (IsScalarTower.toAlgHom (MvPolynomial (Fin n) R) S
        (Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))).toLinearMap
    have : IsLocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) g := by
      apply isLocalizedModule_iff_isLocalization.mpr
      have hsub : Algebra.algebraMapSubmonoid S
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) =
          Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl := by
        simp
      rw [hsub]
      infer_instance
    let e : LocalizedModule
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) S ≃ₗ[
          Localization
            (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)]
        Localization (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) :=
      IsLocalizedModule.linearEquiv
        (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)
        (LocalizedModule.mkLinearMap
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl) S) g
        |>.extendScalarsOfIsLocalization
          (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R) p.asIdeal.primeCompl)
          (Localization (Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) R)
            p.asIdeal.primeCompl))
    exact Module.FinitePresentation.of_equiv e.symm
  apply Algebra.FinitePresentation.of_surjective hf
  exact Module.FinitePresentation.fg_ker (Algebra.linearMap (MvPolynomial (Fin n) R) S) hf

/-! ### Tag 053D: finite presentation of flat graded algebras and modules -/

/-- The image of a weighted homogeneous polynomial under an algebra map sending each variable to
a homogeneous element of the corresponding degree is homogeneous. -/
private theorem aeval_mem_graded
    {R S σ ι : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    [AddCommMonoid ι] (𝒜 : ι → Submodule R S) [SetLike.GradedMonoid 𝒜]
    (w : σ → ι) (x : σ → S) (hx : ∀ i, x i ∈ 𝒜 (w i))
    {d : ι} {f : MvPolynomial σ R}
    (hf : f ∈ MvPolynomial.weightedHomogeneousSubmodule R w d) :
    MvPolynomial.aeval x f ∈ 𝒜 d := by
  classical
  rw [f.as_sum, map_sum]
  apply Submodule.sum_mem
  intro k hk
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  apply Submodule.smul_mem
  have hd := hf (MvPolynomial.mem_support_iff.mp hk)
  rw [← hd, Finsupp.weight_apply]
  exact SetLike.prod_pow_mem_graded 𝒜 w x k (fun i _ ↦ hx i)

/-- A nonnegatively graded algebra of finite type with finite degree-zero part is a finite
module over a weighted polynomial ring, by a graded surjection with positive weights. -/
private theorem exists_finite_weightedPolynomial
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (𝒜 : ℤ → Submodule R S) [GradedAlgebra 𝒜]
    (hnonnegative : ∀ d < 0, 𝒜 d = ⊥)
    [Algebra.FiniteType R S] [Module.Finite R (𝒜 0)] :
    ∃ (n : ℕ) (w : Fin n → ℤ) (φ : MvPolynomial (Fin n) R →ₐ[R] S),
      (∀ i, 0 < w i) ∧
      (∀ d f, f ∈ MvPolynomial.weightedHomogeneousSubmodule R w d → φ f ∈ 𝒜 d) ∧
      (let : Module (MvPolynomial (Fin n) R) S := Module.compHom S φ.toRingHom
       Module.Finite (MvPolynomial (Fin n) R) S) := by
  classical
  have : IsScalarTower R (𝒜 0) S :=
    { smul_assoc := fun _ _ _ ↦ by simp [Algebra.smul_def, mul_assoc] }
  have : Algebra.FiniteType (𝒜 0) S := Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  obtain ⟨s, hs, hdeg⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  have hpos : ∀ i : s, ∃ d : ℤ, 0 < d ∧ (i : S) ∈ 𝒜 d := by
    intro i
    obtain ⟨d, hd, hi⟩ := hdeg i i.2
    by_cases h : 0 < d
    · exact ⟨d, h, hi⟩
    · have hi0 : (i : S) = 0 := by simpa [hnonnegative d (by omega)] using hi
      exact ⟨1, by omega, hi0 ▸ (𝒜 1).zero_mem⟩
  choose w hw hx using hpos
  let e := Fintype.equivFin s
  let x : Fin (Fintype.card s) → S := fun i ↦ (e.symm i : S)
  let φ : MvPolynomial (Fin (Fintype.card s)) R →ₐ[R] S := MvPolynomial.aeval x
  refine ⟨Fintype.card s, w ∘ e.symm, φ, fun i ↦ hw _, ?_, ?_⟩
  · intro d f hf
    exact aeval_mem_graded 𝒜 _ x (fun i ↦ hx _) hf
  · let P := MvPolynomial (Fin (Fintype.card s)) R
    let : Algebra P S := φ.toRingHom.toAlgebra
    have : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq (fun r ↦ (φ.commutes r).symm)
    have : Algebra.FiniteType P S := Algebra.FiniteType.of_restrictScalars_finiteType R _ _
    have : Algebra.IsIntegral P S := ⟨fun z ↦ by
      have hz : z ∈ Algebra.adjoin (𝒜 0) (s : Set S) := by rw [hs]; trivial
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        have heq : algebraMap P S (MvPolynomial.X (e ⟨z, hz⟩)) = z := by
          show MvPolynomial.aeval x (MvPolynomial.X _) = z
          simp [x]
        rw [← heq]
        exact isIntegral_algebraMap
      | algebraMap a =>
        exact (IsIntegral.map (IsScalarTower.toAlgHom R (𝒜 0) S)
          (IsIntegral.of_finite R a)).tower_top
      | add a b _ _ ha hb => exact ha.add hb
      | mul a b _ _ ha hb => exact ha.mul hb⟩
    exact Algebra.IsIntegral.finite

/-- Base change of a graded module over a weighted polynomial ring along a base-ring map, with
its grading, finiteness and compatibility with the original action. -/
private theorem exists_baseChange_weightedModule
    {R A M σ ι : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
    [AddCommMonoid M] [AddCommMonoid ι] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]
    (w : σ → ι) (ℳ : ι → Submodule R M)
    [SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule R w) ℳ]
    [Module.Finite (MvPolynomial σ R) M] :
    ∃ hModule : Module (MvPolynomial σ A) (A ⊗[R] M),
      let := hModule
      IsScalarTower A (MvPolynomial σ A) (A ⊗[R] M) ∧
      Module.Finite (MvPolynomial σ A) (A ⊗[R] M) ∧
      SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule A w)
        (fun d ↦ (ℳ d).baseChange A) ∧
      ∀ (f : MvPolynomial σ R) (m : M),
        MvPolynomial.map (algebraMap R A) f • (1 ⊗ₜ[R] m : A ⊗[R] M) =
          1 ⊗ₜ[R] (f • m) := by
  classical
  let P := MvPolynomial σ R
  let P' := MvPolynomial σ A
  let N := A ⊗[R] M
  let ψ : P →ₐ[R] Module.End A N :=
    (Module.End.baseChangeHom R A M).comp (Algebra.lsmul R R M)
  let ψ' : P' →ₐ[A] Module.End A N :=
    (AlgHom.liftEquiv R A P (Module.End A N) ψ).comp
      (MvPolynomial.algebraTensorAlgEquiv R A).symm.toAlgHom
  let : Module P' N := Module.compHom N ψ'.toRingHom
  have hsmul (a : A) (k : σ →₀ ℕ) (m : M) :
      (MvPolynomial.monomial k a : P') • (1 ⊗ₜ[R] m : N) =
        a ⊗ₜ[R] ((MvPolynomial.monomial k 1 : P) • m) := by
    show ψ' (MvPolynomial.monomial k a) (1 ⊗ₜ[R] m) = _
    show ((AlgHom.liftEquiv R A P (Module.End A N)) ψ)
      ((MvPolynomial.algebraTensorAlgEquiv R A).symm (MvPolynomial.monomial k a))
      (1 ⊗ₜ[R] m) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_monomial, AlgHom.liftEquiv_tmul]
    show a • ((1 : A) ⊗ₜ[R] ((MvPolynomial.monomial k 1 : P) • m)) = _
    simp [smul_tmul']
  have htower : IsScalarTower A P' N := IsScalarTower.of_algebraMap_smul (fun a m ↦ by
    show ψ' (algebraMap A P' a) m = a • m
    rw [ψ'.commutes]
    rfl)
  have hcompat (f : P) (m : M) :
      MvPolynomial.map (algebraMap R A) f • (1 ⊗ₜ[R] m : N) = 1 ⊗ₜ[R] (f • m) := by
    show ψ' (MvPolynomial.map (algebraMap R A) f) (1 ⊗ₜ[R] m) = _
    show ((AlgHom.liftEquiv R A P (Module.End A N)) ψ)
      ((MvPolynomial.algebraTensorAlgEquiv R A).symm (MvPolynomial.map (algebraMap R A) f))
      (1 ⊗ₜ[R] m) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_symm_map, AlgHom.liftEquiv_tmul]
    simp only [one_smul]
    rfl
  refine ⟨inferInstance, htower, ?_, ?_, hcompat⟩
  · let : Algebra P P' := MvPolynomial.algebraMvPolynomial
    let : Module P N := Module.compHom N (algebraMap P P')
    have : IsScalarTower P P' N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    let f : M →ₗ[P] N :=
      { toFun := fun m ↦ 1 ⊗ₜ[R] m
        map_add' := fun _ _ ↦ tmul_add _ _ _
        map_smul' := fun p m ↦ (hcompat p m).symm }
    let F : P' ⊗[P] M →ₗ[P'] N := f.liftBaseChange P'
    apply Module.Finite.of_surjective F
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a m =>
      refine ⟨MvPolynomial.C a ⊗ₜ[P] m, ?_⟩
      show (MvPolynomial.C a : P') • (1 ⊗ₜ[R] m : N) = a ⊗ₜ[R] m
      rw [show (MvPolynomial.C a : P') = algebraMap A P' a from rfl, algebraMap_smul]
      simp [smul_tmul']
    | add y z hy hz =>
      obtain ⟨y', rfl⟩ := hy
      obtain ⟨z', rfl⟩ := hz
      exact ⟨y' + z', map_add _ _ _⟩
  · constructor
    intro i j p m hp hm
    rw [Submodule.baseChange_eq_span] at hm
    induction hm using Submodule.span_induction with
    | mem m hm =>
      obtain ⟨m, hm, rfl⟩ := hm
      rw [p.as_sum, Finset.sum_smul]
      apply Submodule.sum_mem
      intro k hk
      show (MvPolynomial.monomial k (p.coeff k) : P') •
        (1 ⊗ₜ[R] m : N) ∈ _
      rw [hsmul]
      apply Submodule.tmul_mem_baseChange_of_mem
      apply SetLike.GradedSMul.smul_mem
        (A := MvPolynomial.weightedHomogeneousSubmodule R w) (B := ℳ)
        (MvPolynomial.isWeightedHomogeneous_monomial w k 1
          (hp (MvPolynomial.mem_support_iff.mp hk))) hm
    | zero => simp
    | add m n _ _ hm hn => simpa [smul_add] using Submodule.add_mem _ hm hn
    | smul a m _ hm =>
      simpa [smul_comm p a m] using ((ℳ (i + j)).baseChange A).smul_mem a hm

/-- Finite presentation transfers from a localization presented as a base change to the
canonical `LocalizedModule`. -/
private theorem finitePresentation_localizedModule
    {P A M N : Type*} [CommRing P] [CommRing A] [Algebra P A]
    [AddCommGroup M] [Module P M] [AddCommGroup N] [Module P N]
    [Module A N] [IsScalarTower P A N]
    (U : Submonoid P) [IsLocalization U A]
    (f : M →ₗ[P] N) [IsLocalizedModule U f] [Module.FinitePresentation A N] :
    Module.FinitePresentation (Localization U) (LocalizedModule U M) := by
  let e := IsLocalization.algEquiv U (Localization U) A
  let : Algebra (Localization U) A := e.toRingHom.toAlgebra
  let : Module (Localization U) N := Module.compHom N e.toRingHom
  have : IsScalarTower (Localization U) A N := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have : IsScalarTower P (Localization U) N := IsScalarTower.of_algebraMap_smul (fun r m ↦ by
    show e (algebraMap P (Localization U) r) • m = r • m
    rw [e.commutes, algebraMap_smul])
  have : Module.FinitePresentation (Localization U) A :=
    Module.FinitePresentation.of_equiv
      (LinearEquiv.ofBijective (Algebra.linearMap (Localization U) A) e.bijective)
  have : Module.FinitePresentation (Localization U) N :=
    Module.FinitePresentation.trans (Localization U) N A
  exact Module.FinitePresentation.of_equiv
    ((IsLocalizedModule.iso U f).extendScalarsOfIsLocalization U (Localization U)).symm

/-- If the base change of a module over a polynomial ring to a localization of the base ring is
finitely presented, then so is the localized module. -/
private theorem finitePresentation_localizedModule_of_tensorProduct
    {R M : Type*} {σ : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]
    (T : Submonoid R) (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization T Rₛ]
    [Module (MvPolynomial σ Rₛ)
      (Rₛ ⊗[R] M)]
    [IsScalarTower Rₛ (MvPolynomial σ Rₛ)
      (Rₛ ⊗[R] M)]
    [Module.FinitePresentation (MvPolynomial σ Rₛ)
      (Rₛ ⊗[R] M)]
    (hcompat : ∀ (f : MvPolynomial σ R) (m : M),
      (MvPolynomial.map (algebraMap R Rₛ) f) • (1 ⊗ₜ[R] m : Rₛ ⊗[R] M) =
        (1 ⊗ₜ[R] (f • m) : Rₛ ⊗[R] M)) :
    Module.FinitePresentation
      (Localization (Algebra.algebraMapSubmonoid (MvPolynomial σ R) T))
      (LocalizedModule (Algebra.algebraMapSubmonoid (MvPolynomial σ R) T) M) := by
  let P := MvPolynomial σ R
  let Pₚ := MvPolynomial σ Rₛ
  let Mₚ := Rₛ ⊗[R] M
  let : Algebra P Pₚ := MvPolynomial.algebraMvPolynomial
  have hmap : algebraMap P Pₚ = MvPolynomial.map (algebraMap R Rₛ) :=
    MvPolynomial.algebraMap_def
  let : Module P Mₚ := Module.compHom Mₚ (algebraMap P Pₚ)
  have : IsScalarTower P Pₚ Mₚ := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have : IsScalarTower R P Mₚ := IsScalarTower.of_algebraMap_smul (fun r x ↦ by
    show (algebraMap P Pₚ (MvPolynomial.C r)) • x = r • x
    rw [hmap]
    rw [MvPolynomial.map_C]
    show (algebraMap Rₛ Pₚ (algebraMap R Rₛ r)) • x = r • x
    rw [algebraMap_smul, algebraMap_smul])
  let f : M →ₗ[P] Mₚ :=
    { toFun := fun m ↦ 1 ⊗ₜ[R] m
      map_add' := fun _ _ ↦ TensorProduct.tmul_add _ _ _
      map_smul' := fun r m ↦ by
        show (1 ⊗ₜ[R] (r • m) : Mₚ) = (algebraMap P Pₚ r) • (1 ⊗ₜ[R] m : Mₚ)
        rw [hmap]
        exact (hcompat r m).symm }
  have : IsLocalizedModule T (f.restrictScalars R) :=
    IsLocalization.tensorProduct_isLocalizedModule T Rₛ
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid P T) f :=
    IsLocalizedModule.of_restrictScalars T f
  have : IsLocalization (Algebra.algebraMapSubmonoid P T) Pₚ :=
    MvPolynomial.isLocalization T Rₛ
  exact finitePresentation_localizedModule (A := Pₚ) _ f

/-- A finite graded module over a weighted polynomial ring which is flat over the base is
finitely presented, by Tag 053A and the local case of Tag 053C. -/
@[ega "IV 11.2.9.4" "Sufficiency direction"]
private theorem finitePresentation_of_flat_weightedPolynomial
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {n : ℕ} [Module (MvPolynomial (Fin n) R) M]
    [IsScalarTower R (MvPolynomial (Fin n) R) M]
    (weight : Fin n → ℤ) (hweight : ∀ i, 0 < weight i)
    (ℳ : ℤ → Submodule R M)
    [SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule R weight) ℳ]
    [DirectSum.Decomposition ℳ]
    (hprimes : HasFiniteDetectingPrimes R)
    [Module.Finite (MvPolynomial (Fin n) R) M] [Module.Flat R M] :
    Module.FinitePresentation (MvPolynomial (Fin n) R) M := by
  apply Module.finitePresentation_of_flat_of_localized hprimes
  intro p
  obtain ⟨hModule, hTower, hFinite, hGraded, hcompat⟩ :=
    exists_baseChange_weightedModule (A := Localization.AtPrime p.asIdeal) weight ℳ
  let := hModule
  have := hTower
  have := hFinite
  have := hGraded
  have : Module.FinitePresentation (MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal))
      (Localization.AtPrime p.asIdeal ⊗[R] M) :=
    finitePresentation_of_finite_flat_of_isLocalRing _ n weight hweight _
      (fun d ↦ (ℳ d).baseChange (Localization.AtPrime p.asIdeal))
  exact finitePresentation_localizedModule_of_tensorProduct p.asIdeal.primeCompl
    (Localization.AtPrime p.asIdeal) hcompat

/-- The integer-graded form of Tag 053D: for a grading indexed by `ℤ` which vanishes in negative
degrees, flatness over `R` gives finite presentation of the algebra and of its finite graded
modules. -/
@[ega "IV 11.2.9.4" "Module clause"]
private theorem finitePresentation_of_intGrading
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [AddCommGroup M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
    (𝒜 : ℤ → Submodule R S) [GradedAlgebra 𝒜]
    (hnonnegative : ∀ d < 0, 𝒜 d = ⊥)
    (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
    [Algebra.FiniteType R S] [Module.Finite R (𝒜 0)]
    (hprimes : HasFiniteDetectingPrimes R) :
    (Module.Flat R S → Algebra.FinitePresentation R S) ∧
      (Module.Flat R M → Module.Finite S M → Module.FinitePresentation S M) := by
  obtain ⟨n, weight, φ, hweight, hgraded, hfinite⟩ :=
    exists_finite_weightedPolynomial 𝒜 hnonnegative
  let P := MvPolynomial (Fin n) R
  let : Algebra P S := φ.toRingHom.toAlgebra
  have : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq (fun r ↦ (φ.commutes r).symm)
  have : Module.Finite P S := hfinite
  constructor
  · intro hflat
    have := hflat
    have : SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule R weight) 𝒜 :=
      ⟨fun _ _ _ _ hp hs ↦ SetLike.mul_mem_graded (hgraded _ _ hp) hs⟩
    have : Module.FinitePresentation P S :=
      finitePresentation_of_flat_weightedPolynomial weight hweight 𝒜 hprimes
    exact Algebra.FinitePresentation.trans R P S
  · intro hflat hfiniteM
    have := hflat
    have := hfiniteM
    let : Module P M := Module.compHom M φ.toRingHom
    have : IsScalarTower P S M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    have : IsScalarTower R P M := IsScalarTower.of_algebraMap_smul (fun r m ↦ by
      show φ (algebraMap R P r) • m = r • m
      rw [φ.commutes, algebraMap_smul])
    have : Module.Finite P M := Module.Finite.trans (R := P) S M
    have : SetLike.GradedSMul (MvPolynomial.weightedHomogeneousSubmodule R weight) ℳ := by
      constructor
      intro i j p m hp hm
      show φ p • m ∈ ℳ (i + j)
      exact SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) (hgraded i p hp) hm
    have : Module.FinitePresentation P M :=
      finitePresentation_of_flat_weightedPolynomial weight hweight ℳ hprimes
    exact finitePresentation_of_restrictScalars_of_finite (P := P)

/-- **Stacks Tag 053D.** Let `S = ⨁_d 𝒜 d` be a nonnegatively graded `R`-algebra of finite type
whose degree-zero part is finite over `R`, and suppose a finite family of prime localizations
jointly detects elements of `R`.  Then an `R`-flat `S` is finitely presented as an `R`-algebra,
and every finite graded `S`-module which is flat over `R` is finitely presented as an
`S`-module. -/
@[stacks 053D, ega "IV 11.2.9.4" "Module clause"]
theorem finitePresentation_of_flat_of_finiteType_of_finite_degreeZero
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S]
    [AddCommGroup M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
    (𝒜 : ℕ → Submodule R S) [GradedAlgebra 𝒜]
    (ℳ : ℤ → Submodule R M) [SetLike.GradedSMul 𝒜 ℳ] [DirectSum.Decomposition ℳ]
    [Algebra.FiniteType R S] [Module.Finite R (𝒜 0)]
    (hprimes : HasFiniteDetectingPrimes R) :
    (Module.Flat R S → Algebra.FinitePresentation R S) ∧
      (Module.Flat R M → Module.Finite S M → Module.FinitePresentation S M) := by
  classical
  -- Extend the algebra grading by zero to use the integer-weighted polynomial reduction.
  let 𝒜' : ℤ → Submodule R S := fun d ↦ if 0 ≤ d then 𝒜 d.toNat else ⊥
  have hnat (n : ℕ) : 𝒜' n = 𝒜 n := by simp [𝒜']
  have hneg (d : ℤ) (hd : d < 0) : 𝒜' d = ⊥ := by simp [𝒜', not_le.mpr hd]
  have hi := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSupIndep
  have hs := (DirectSum.Decomposition.isInternal 𝒜).submodule_iSup_eq_top
  have hi' : iSupIndep 𝒜' := by
    intro d
    by_cases hd : 0 ≤ d
    · rw [show 𝒜' d = 𝒜 d.toNat by simp [𝒜', hd]]
      apply (hi d.toNat).mono_right
      refine iSup₂_le fun e he ↦ ?_
      by_cases he' : 0 ≤ e
      · rw [show 𝒜' e = 𝒜 e.toNat by simp [𝒜', he']]
        exact le_iSup_of_le e.toNat (le_iSup_of_le (by omega : e.toNat ≠ d.toNat) le_rfl)
      · simp [𝒜', he']
    · simp [𝒜', hd]
  have hs' : iSup 𝒜' = ⊤ := by
    apply top_unique
    rw [← hs]
    exact iSup_le fun n ↦ by rw [← hnat n]; exact le_iSup 𝒜' (n : ℤ)
  let : DirectSum.Decomposition 𝒜' :=
    (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi' hs').chooseDecomposition
  have : SetLike.GradedMonoid 𝒜' := by
    refine { one_mem := ?_, mul_mem := ?_ }
    · simpa [𝒜'] using (SetLike.one_mem_graded 𝒜 : (1 : S) ∈ 𝒜 0)
    · intro i j a b ha hb
      by_cases hi : 0 ≤ i
      · by_cases hj : 0 ≤ j
        · simp only [𝒜', ite_eq_left hi] at ha
          simp only [𝒜', ite_eq_left hj] at hb
          simpa [𝒜', add_nonneg hi hj, Int.toNat_add hi hj] using
            SetLike.mul_mem_graded ha hb
        · have hb0 : b = 0 := by simpa [𝒜', hj] using hb
          simp [hb0]
      · have ha0 : a = 0 := by simpa [𝒜', hi] using ha
        simp [ha0]
  let : GradedAlgebra 𝒜' := { }
  have : Module.Finite R (𝒜' 0) := by simpa [𝒜'] using
    (inferInstance : Module.Finite R (𝒜 0))
  have : SetLike.GradedSMul 𝒜' ℳ := by
    constructor
    intro i j a m ha hm
    show a • m ∈ ℳ (i + j)
    by_cases hi : 0 ≤ i
    · have ha' : a ∈ 𝒜 i.toNat := by simpa [𝒜', hi] using ha
      have h := SetLike.GradedSMul.smul_mem (A := 𝒜) (B := ℳ) ha' hm
      change a • m ∈ ℳ ((i.toNat : ℤ) + j) at h
      simpa only [Int.toNat_of_nonneg hi] using h
    · have ha0 : a = 0 := by simpa [𝒜', hi] using ha
      simp [ha0]
  exact finitePresentation_of_intGrading 𝒜' hneg ℳ hprimes

/-! ### Tag 053E: Nagata's theorem over a valuation ring

The proof runs through the graded Rees model of Tag 052N
(`StacksFrontier.RingTheory.GradedAlgebra.ReesModel`): the algebra `B` is recovered from the graded
algebra `reesS A B gens` by dehomogenizing `X ↦ 1`, and the module `M` from the graded module
`reesNfin A B M gens` by reading off the coefficient sum.  Both identifications have kernel
generated by `f - 1`, so Tag 053D applies to the graded model and descends. -/

section ValuationRing

open Polynomial ReesGrad5 ReesGrad8

-- The graded Rees model is built from nested subobjects of `A × B[X]`, so unification in this
-- section has to see through the coercions and recurses deeply.
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  (gens : Finset B)

/-- Dehomogenization `X ↦ 1` of the graded Rees algebra of Tag 052N. -/
private noncomputable def reesDehom : reesS A B gens →ₐ[A] B where
  toRingHom := (Polynomial.evalRingHom 1).comp (ReesGrad5.reesPi A B gens)
  commutes' r := by
    change ((algebraMap A (reesS A B gens) r : A × B[X]).2).eval 1 = _
    change (Polynomial.C (algebraMap A B r)).eval 1 = _
    simp

/-- Dehomogenization evaluates the polynomial component at `1`. -/
private theorem reesDehom_apply (s : reesS A B gens) :
    reesDehom gens s = (s : A × B[X]).2.eval 1 := rfl

/-- Dehomogenization is surjective when `gens` generates `B` over `A`. -/
private theorem reesDehom_surjective (hgens : Algebra.adjoin A (gens : Set B) = ⊤) :
    Function.Surjective (reesDehom (A := A) gens) := by
  intro c
  obtain ⟨d, hd⟩ := ReesGrad6.exists_homog_mem A B gens hgens c
  exact ⟨⟨_, hd⟩, by simp [reesDehom_apply]⟩

/-- Positive powers of the degree-one element `f` have vanishing degree-zero component. -/
private theorem reesFS_pow_fst (k : ℕ) (hk : k ≠ 0) :
    ((reesFS A B gens ^ k : reesS A B gens) : A × B[X]).1 = 0 := by
  rw [SubmonoidClass.coe_pow]
  show ((reesF A B) ^ k).1 = 0
  unfold reesF
  rw [Prod.pow_def]
  exact zero_pow hk

/-- `x - 1` divides `1 - xⁿ`. -/
private theorem dvd_one_sub_pow {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    x - 1 ∣ 1 - x ^ n := by
  have h := sub_one_dvd_pow_sub_one x n
  rwa [← dvd_neg, neg_sub] at h

/-- If `y = ∑ₙ pₙ` and `∑ₙ fᴷ⁻ⁿ pₙ = 0`, then `y` lies in `(f - 1) N`. -/
private theorem mem_span_smul_top_of_sum {S N : Type*} [CommRing S] [AddCommGroup N] [Module S N]
    (f : S) (K : ℕ) (p : ℕ → N) (y : N) (hsum : y = ∑ n ∈ Finset.range (K + 1), p n)
    (htop : ∑ n ∈ Finset.range (K + 1), f ^ (K - n) • p n = 0) :
    y ∈ Ideal.span {f - 1} • (⊤ : Submodule S N) := by
  have : y = ∑ n ∈ Finset.range (K + 1), (1 - f ^ (K - n)) • p n := by
    simp only [sub_smul, one_smul, Finset.sum_sub_distrib, htop, sub_zero]
    exact hsum
  rw [this]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨c, hc⟩ := dvd_one_sub_pow f (K - n)
  rw [hc, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

/-- The kernel of dehomogenization is generated by `f - 1`. -/
private theorem ker_reesDehom :
    RingHom.ker (reesDehom gens).toRingHom = Ideal.span {reesFS A B gens - 1} := by
  classical
  apply le_antisymm
  · intro s hs
    rw [RingHom.mem_ker] at hs
    change reesDehom gens s = 0 at hs
    set K := (s : A × B[X]).2.natDegree + 1 with hK
    let piece : ℕ → reesS A B gens := fun d =>
      ⟨pcomp A B d s, ReesGrad.pcomp_mem_reesS A B gens d s s.2⟩
    have hsum : s = ∑ d ∈ Finset.range (K + 1), piece d := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (ReesGrad.sum_pcomp_eq A B K s (by omega)).symm
    have htop : ∑ d ∈ Finset.range (K + 1), piece d * reesFS A B gens ^ (K - d) = 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      apply Prod.ext
      · rw [Prod.fst_sum]
        apply Finset.sum_eq_zero
        intro d hd
        rw [Subalgebra.coe_mul, Prod.fst_mul]
        by_cases hdK : d = K
        · subst hdK
          show (pcomp A B _ s).1 * _ = 0
          rw [ReesGrad.pcomp_fst, ite_eq_right (by omega), zero_mul]
        · rw [reesFS_pow_fst gens _ (by rw [Finset.mem_range] at hd; omega), mul_zero]
      · rw [Prod.snd_sum]
        have h1 : ∀ d ∈ Finset.range (K + 1),
            ((piece d * reesFS A B gens ^ (K - d) : reesS A B gens) : A × B[X]).2 =
              C ((s : A × B[X]).2.coeff d) * X ^ K := by
          intro d hd
          rw [Finset.mem_range] at hd
          rw [Subalgebra.coe_mul, Prod.snd_mul, ReesGrad6.reesFS_pow_coe_snd]
          show (pcomp A B d s).2 * X ^ (K - d) = _
          unfold pcomp
          split_ifs with h0
          · subst h0; simp
          · rw [mul_assoc, ← pow_add]; congr 2; omega
        have hev : ∑ d ∈ Finset.range (K + 1), (s : A × B[X]).2.coeff d =
            reesDehom gens s := by
          rw [reesDehom_apply, eval_eq_sum_range' (n := K + 1) (by omega)]
          simp
        rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← map_sum, hev, hs]
        simp
    have := mem_span_smul_top_of_sum (reesFS A B gens) K piece s hsum (by
      simpa only [smul_eq_mul, mul_comm] using htop)
    simpa using this
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    show reesDehom gens _ = 0
    rw [map_sub, map_one, reesDehom_apply]
    show (reesF A B).2.eval 1 - 1 = 0
    simp [reesF]

/-- The degree-zero part of the Rees algebra is a finite module over the base. -/
private theorem finite_reesGrading_zero :
    Module.Finite A (reesGrading A B gens 0) := by
  have h1 : (1 : reesS A B gens) ∈ reesGrading A B gens 0 :=
    ReesGrad.one_mem_reesGrading A B gens
  let g : A →ₗ[A] reesGrading A B gens 0 := LinearMap.toSpanSingleton A _ ⟨1, h1⟩
  refine Module.Finite.of_surjective g ?_
  rintro ⟨x, hx⟩
  have hx' : x ∈ (Set.range (algebraMap A (reesS A B gens))) := by
    rw [reesS_algebraMap_range]; exact hx
  obtain ⟨r, rfl⟩ := hx'
  exact ⟨r, Subtype.ext (by simp [g, Algebra.algebraMap_eq_smul_one])⟩

/-- The Rees algebra is of finite type over the base. -/
private theorem finiteType_reesS : Algebra.FiniteType A (reesS A B gens) := by
  obtain ⟨gs, -, hgs⟩ := reesS_property3 A B gens
  exact ⟨⟨gs, hgs⟩⟩

variable {M : Type w} [AddCommGroup M] [Module B M]

/-- Reading off the coefficient sum is `B[X]`-semilinear over evaluation at `1`. -/
private theorem reesValSum_poly_smul (p : B[X]) (y : reesN B M) :
    reesValSum B M (p • y) = p.eval 1 • reesValSum B M y := by
  induction p using Polynomial.induction_on' generalizing y with
  | add p q hp hq => rw [add_smul, map_add, hp, hq, eval_add, add_smul]
  | monomial n b =>
    induction y using Finsupp.induction_linear with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
    | single k m =>
      show reesValSum B M (reesActHom B M (monomial n b) (Finsupp.single k m)) = _
      rw [← C_mul_X_pow_eq_monomial, reesActHom_C_mul_X_pow_single, reesValSum_single,
        reesValSum_single]
      simp

/-- Constants of `B[X]` act on the Rees module through `B`. -/
private theorem C_smul_reesN (b : B) (y : reesN B M) :
    (C b : B[X]) • y = b • y := by
  show reesActHom B M (C b) y = _
  rw [reesActHom, Polynomial.aeval_C, Module.algebraMap_end_apply]

section FiniteModule

variable [Module.Finite B M]

/-- Read-off `N → M`, `∑ m_e X^e ↦ ∑ m_e`, as a semilinear map over dehomogenization. -/
private noncomputable def reesNfinReadOff :
    reesNfin A B M gens →ₛₗ[(reesDehom (A := A) gens).toRingHom] M where
  toFun y := reesValSum B M y.1
  map_add' x y := map_add _ _ _
  map_smul' s y := by
    change reesValSum B M ((s : reesS A B gens) • (y : reesN B M)) = _
    rw [reesN_smul_def, reesValSum_poly_smul]
    rfl

/-- The read-off map is surjective when `gens` generates `B` over `A`. -/
private theorem reesNfinReadOff_surjective (hgens : Algebra.adjoin A (gens : Set B) = ⊤) :
    Function.Surjective (reesNfinReadOff (A := A) (M := M) gens) := by
  obtain ⟨ga⟩ := reesGrading_gradedAlgebra A B gens
  intro m
  obtain ⟨D, hD⟩ := exists_single_mem_reesNfin A B M gens hgens m
  exact ⟨⟨_, hD⟩, reesValSum_single B M D m⟩

/-- Multiples of `f - 1` are killed by the read-off map. -/
private theorem reesFS_sub_one_smul_mem (y : reesNfin A B M gens) :
    reesValSum B M ((reesFS A B gens - 1) • y : reesNfin A B M gens).1 = 0 := by
  show reesValSum B M ((reesFS A B gens - 1) • (y : reesN B M)) = 0
  rw [sub_smul, one_smul, map_sub, reesValSum_f_smul, sub_self]

/-- The kernel of the read-off map is `(f - 1)` times the whole graded module. -/
private theorem mem_span_of_readOff_eq_zero (y : reesNfin A B M gens)
    (hy : reesValSum B M y.1 = 0) :
    y ∈ (Ideal.span {reesFS A B gens - 1}) • (⊤ : Submodule (reesS A B gens) _) := by
  classical
  obtain ⟨g, hg⟩ := y
  change reesValSum B M g = 0 at hy
  let g' : ℕ →₀ M := g
  set K := g'.support.sup id with hK
  let comp : ℕ → reesNfin A B M gens := fun n =>
    ⟨reesComp B M n g, reesNfin_homogeneous A B M gens hg n⟩
  have hcomp (n : ℕ) : ((comp n : reesNfin A B M gens) : reesN B M) =
      Finsupp.single n (g' n) := rfl
  have hsupp : g'.support ⊆ Finset.range (K + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have := Finset.le_sup (f := id) hn
    simp only [id] at this
    omega
  have hsum : (⟨g, hg⟩ : reesNfin A B M gens) = ∑ n ∈ Finset.range (K + 1), comp n := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [hcomp]
    show g' = ∑ n ∈ Finset.range (K + 1), Finsupp.single n (g' n)
    conv_lhs => rw [← Finsupp.sum_single g']
    exact Finsupp.sum_of_support_subset _ hsupp _ (by simp)
  have htop : ∑ n ∈ Finset.range (K + 1), reesFS A B gens ^ (K - n) • comp n = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    have h1 : ∀ n ∈ Finset.range (K + 1),
        ((reesFS A B gens ^ (K - n) • comp n : reesNfin A B M gens) : reesN B M) =
          Finsupp.single K (g' n) := by
      intro n hn
      rw [Finset.mem_range] at hn
      show (reesFS A B gens ^ (K - n)) • ((comp n : reesNfin A B M gens) : reesN B M) = _
      rw [reesFS_pow_smul_single A B M gens (K - n) n _ _ (hcomp n)]
      congr 1; omega
    rw [Finset.sum_congr rfl h1]
    show ∑ n ∈ Finset.range (K + 1), Finsupp.single K (g' n) = (0 : ℕ →₀ M)
    rw [← Finsupp.single_finsetSum]
    have hval : reesValSum B M g = ∑ n ∈ Finset.range (K + 1), g' n := by
      show (Finsupp.liftAddHom (fun _ : ℕ => AddMonoidHom.id M)) g' = _
      rw [Finsupp.liftAddHom_apply]
      exact Finsupp.sum_of_support_subset _ hsupp _ (by simp)
    rw [← hval, hy, Finsupp.single_zero]
  exact mem_span_smul_top_of_sum (reesFS A B gens) K comp _ hsum htop

end FiniteModule

section Assembly

variable [IsDomain A] [ValuationRing A] [Module A M] [IsScalarTower A B M] [Module.Finite B M]

/-- The Rees algebra of a flat algebra is finitely presented, by Tag 053D. -/
private theorem reesS_finitePresentation [Module.Flat A B] :
    Algebra.FinitePresentation A (reesS A B gens) := by
  classical
  obtain ⟨ga⟩ := reesGrading_gradedAlgebra A B gens
  let := ga
  have : Algebra.FiniteType A (reesS A B gens) := finiteType_reesS gens
  have : Module.Finite A (reesGrading A B gens 0) := finite_reesGrading_zero gens
  have : Module.IsTorsionFree A B := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree A (reesS A B gens) := inferInstance
  have : SetLike.GradedSMul (reesGrading A B gens) (fun _ : ℤ => (⊤ : Submodule A PUnit)) :=
    ⟨fun {_ _ _ _} _ _ => Submodule.mem_top⟩
  let : DirectSum.Decomposition (fun _ : ℤ => (⊤ : Submodule A PUnit)) :=
    { decompose' := 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _ }
  exact (finitePresentation_of_flat_of_finiteType_of_finite_degreeZero
    (reesGrading A B gens) (fun _ : ℤ => (⊤ : Submodule A PUnit))
    (HasFiniteDetectingPrimes.of_isDomain A)).1 Module.Flat.of_isTorsionFree_of_valuationRing

/-- The finite graded Rees module of a flat module is finitely presented, by Tag 053D. -/
private theorem reesNfin_finitePresentation [Module.Flat A M] :
    Module.FinitePresentation (reesS A B gens) (reesNfin A B M gens) := by
  classical
  obtain ⟨ga⟩ := reesGrading_gradedAlgebra A B gens
  let := ga
  have : Algebra.FiniteType A (reesS A B gens) := finiteType_reesS gens
  have : Module.Finite A (reesGrading A B gens 0) := finite_reesGrading_zero gens
  let : Module A (reesNfin A B M gens) := Module.compHom _ (algebraMap A (reesS A B gens))
  have : IsScalarTower A (reesS A B gens) (reesNfin A B M gens) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hA0 (a : A) : algebraMap A (reesS A B gens) a ∈ reesGrading A B gens 0 := by
    rw [← SetLike.mem_coe, ← reesS_algebraMap_range]; exact ⟨a, rfl⟩
  let ℳ : ℤ → Submodule A (reesNfin A B M gens) := fun n =>
    { toAddSubmonoid := (reesBfin A B M gens n).toAddSubmonoid
      smul_mem' := fun a x hx => by
        have := (reesBfin_gradedSMul A B M gens).smul_mem (hA0 a) hx
        simpa [natVAdd_eq] using this }
  have : SetLike.GradedSMul (reesGrading A B gens) ℳ :=
    ⟨fun {_ _ _ _} ha hb => (reesBfin_gradedSMul A B M gens).smul_mem ha hb⟩
  let dec := reesFinDecomposition A B M gens
  let : DirectSum.Decomposition ℳ :=
    { decompose' := dec.decompose'
      left_inv := dec.left_inv
      right_inv := dec.right_inv }
  have : Module.Finite (reesS A B gens) (reesNfin A B M gens) := reesNfin_finite A B M gens
  have : Module.IsTorsionFree A M := Module.Flat.isTorsionFree
  have : Module.IsTorsionFree A (reesNfin A B M gens) := by
    refine Function.Injective.moduleIsTorsionFree (N := ℕ →₀ M)
      (fun y => (y : reesN B M)) Subtype.val_injective fun a y => ?_
    show ((algebraMap A (reesS A B gens) a) • (y : reesN B M) : ℕ →₀ M) = _
    rw [reesN_smul_def]
    show ((C (algebraMap A B a) : B[X]) • (y : reesN B M) : ℕ →₀ M) = _
    rw [C_smul_reesN]
    apply Finsupp.ext
    intro n
    simp only [reesN, Finsupp.smul_apply, algebraMap_smul]
  exact (finitePresentation_of_flat_of_finiteType_of_finite_degreeZero
    (M := reesNfin A B M gens)
    (reesGrading A B gens) ℳ (HasFiniteDetectingPrimes.of_isDomain A)).2
    (Module.Flat.of_isTorsionFree_of_valuationRing (A := A) (X := reesNfin A B M gens))
    inferInstance

end Assembly

/-- **Stacks Tag 053E (Nagata).** Let `A` be a valuation ring, `B` an `A`-algebra of finite type,
and `M` a `B`-module.  If `B` is flat over `A`, then `B` is finitely presented as an
`A`-algebra.  If `M` is finite over `B` and flat over `A`, then `M` is finitely presented as a
`B`-module. -/
@[stacks 053E]
theorem finitePresentation_of_flat_of_finiteType_of_valuationRing
    {A : Type u} {B : Type v} {M : Type w} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.FiniteType A B] [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] :
    (Module.Flat A B → Algebra.FinitePresentation A B) ∧
      (Module.Flat A M → Module.Finite B M → Module.FinitePresentation B M) := by
  classical
  obtain ⟨gens, hgens⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B).FG)
  have hker : (RingHom.ker (reesDehom (A := A) gens).toRingHom).FG := by
    rw [ker_reesDehom]; exact ⟨{reesFS A B gens - 1}, by simp⟩
  constructor
  · intro hB
    have := reesS_finitePresentation (A := A) gens
    exact Algebra.FinitePresentation.of_surjective (reesDehom_surjective gens hgens) hker
  · intro hM hMfin
    have := reesNfin_finitePresentation (A := A) (M := M) gens
    let : Algebra (reesS A B gens) B := (reesDehom (A := A) gens).toRingHom.toAlgebra
    let : Module (reesS A B gens) M := Module.compHom M (algebraMap (reesS A B gens) B)
    have : IsScalarTower (reesS A B gens) B M :=
      ⟨fun s b m => by change (_ * b) • m = _ • (b • m); rw [mul_smul]; rfl⟩
    let l : reesNfin A B M gens →ₗ[reesS A B gens] M :=
      { toFun := reesNfinReadOff gens
        map_add' := map_add _
        map_smul' := fun s y => (reesNfinReadOff gens).map_smulₛₗ s y }
    have hl : Function.Surjective l := reesNfinReadOff_surjective gens hgens
    have hlker : (LinearMap.ker l).FG := by
      have heq : LinearMap.ker l =
          Ideal.span {reesFS A B gens - 1} • (⊤ : Submodule (reesS A B gens) _) := by
        apply le_antisymm
        · intro y hy
          exact mem_span_of_readOff_eq_zero gens y hy
        · rw [Submodule.smul_le]
          intro r hr y _
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
          rw [LinearMap.mem_ker, mul_smul, map_smul]
          have h0 : l ((reesFS A B gens - 1) • y) = 0 := reesFS_sub_one_smul_mem gens y
          rw [h0, smul_zero]
      rw [heq]
      exact Submodule.FG.smul ⟨{reesFS A B gens - 1}, by simp⟩
        (Module.finite_def.mp inferInstance)
    have : Module.FinitePresentation (reesS A B gens) M :=
      Module.finitePresentation_of_surjective (M := reesNfin A B M gens) (N := M)
        l hl hlker
    have : Module.Finite (reesS A B gens) B :=
      RingHom.Finite.of_surjective (reesDehom (A := A) gens).toRingHom
        (reesDehom_surjective (A := A) gens hgens)
    exact finitePresentation_of_restrictScalars_of_finite (P := reesS A B gens)

/-! ### Tag 0GSE: the essentially-of-finite-type version -/

/-- **Stacks Tag 0GSE.** Let `A` be a valuation ring, `B` an essentially-of-finite-type
`A`-algebra, and `M` a `B`-module.  If `B` is flat over `A`, then `A → B` is essentially of
finite presentation.  If `M` is finite over `B` and flat over `A`, then `M` is finitely presented
over `B`. -/
@[stacks 0GSE]
theorem essentiallyOfFinitePresentation_and_finitePresentation_of_flat_of_valuationRing
    {A : Type u} {B : Type v} {M : Type w} [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B] [AddCommGroup M] [Module B M]
    [Module A M] [IsScalarTower A B M] :
    (Module.Flat A B → (algebraMap A B).EssentiallyOfFinitePresentation) ∧
      (Module.Flat A M → Module.Finite B M → Module.FinitePresentation B M) := by
  classical
  obtain ⟨B₀, S, hB₀ft, hB₀loc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra A B).mp inferInstance
  let : Algebra.FiniteType A B₀ := hB₀ft
  let : IsLocalization S B := hB₀loc
  constructor
  · intro hflat
    let : Module.Flat A B := hflat
    have : Module.IsTorsionFree A B := Module.Flat.isTorsionFree
    have : Module.Flat A B₀ := Module.Flat.of_isTorsionFree_of_valuationRing
    have : Algebra.FinitePresentation A B₀ :=
      (finitePresentation_of_flat_of_finiteType_of_valuationRing
        (A := A) (B := B₀) (M := B₀)).1 inferInstance
    let oldAlgAB : Algebra A B := inferInstance
    obtain ⟨C, instRingC, instAlgAC, instAlgCB, towerACB, fpC, T, locTB⟩ :=
      essFP_reuniverse (R := A) (T := B) B₀ S
    rw [RingHom.EssentiallyOfFinitePresentation]
    let : Algebra A B := (algebraMap A B).toAlgebra
    refine ⟨C, instRingC, instAlgAC, instAlgCB, ?_, fpC, T, locTB⟩
    refine @IsScalarTower.mk A C B _ _ _ ?_
    intro a c b
    simp only [Algebra.smul_def]
    rw [map_mul,
      ← @IsScalarTower.algebraMap_apply A C B _ _ _ instAlgAC instAlgCB oldAlgAB towerACB,
      mul_assoc]
    rfl
  · intro hflat hfinite
    let : Module.Flat A M := hflat
    let : Module.Finite B M := hfinite
    have : IsLocalizedModule S (LinearMap.id : M →ₗ[B₀] M) :=
      isLocalizedModule_id (R := B₀) S M B
    obtain ⟨M₀, instAddM₀, instModuleM₀, φ, hM₀finite, hφloc, -⟩ :=
      Module.exists_finite_isLocalizedModule_comp S B (LinearMap.id : M →ₗ[B₀] M)
    let : AddCommGroup M₀ := instAddM₀
    let : Module B₀ M₀ := instModuleM₀
    let : Module.Finite B₀ M₀ := hM₀finite
    let N : Submodule B₀ M := LinearMap.range φ
    let : Module.Finite B₀ N := Module.Finite.range φ
    let ι : N →ₗ[B₀] M := N.subtype
    let hιloc : IsLocalizedModule S ι := {
      map_units s := IsLocalizedModule.map_units (LinearMap.id : M →ₗ[B₀] M) s
      surj m := by
        obtain ⟨⟨m₀, s⟩, hm₀⟩ := IsLocalizedModule.surj S (LinearMap.id ∘ₗ φ) m
        exact ⟨(⟨φ m₀, ⟨m₀, rfl⟩⟩, s), by simpa [ι] using hm₀⟩
      exists_of_eq h := ⟨1, by simpa using Subtype.ext h⟩ }
    have : Module.IsTorsionFree A M := Module.Flat.isTorsionFree
    have : Module.Flat A N := Module.Flat.of_isTorsionFree_of_valuationRing
    have : Module.FinitePresentation B₀ N :=
      (finitePresentation_of_flat_of_finiteType_of_valuationRing
        (A := A) (B := B₀) (M := N)).2 inferInstance inferInstance
    exact FinitePresentation.of_isBaseChange ι
      ((isLocalizedModule_iff_isBaseChange S B ι).mp hιloc)

end ValuationRing

/-! ### Tag 05GS: rings satisfying the standing hypothesis -/

/-- **Stacks Tag 05GS.** Let `R` be a commutative ring.  If `R` is local, Noetherian, a domain,
reduced with finitely many minimal primes, or has finitely many weakly associated primes, then
finitely many prime localizations jointly detect elements of `R`, so that Tags 053A, 053B and
053D apply to `R`. -/
@[stacks 05GS]
theorem hasFiniteDetectingPrimes_of_standard_conditions
    {R : Type u} [CommRing R]
    (h : IsLocalRing R ∨ IsNoetherianRing R ∨ IsDomain R ∨
      (IsReduced R ∧ (minimalPrimes R).Finite) ∨
      {p : Ideal R | ∃ x : R, p ∈ (R ∙ x).annihilator.minimalPrimes}.Finite) :
    HasFiniteDetectingPrimes R := by
  rcases h with hlocal | hnoeth | hdomain | hreduced | hweak
  · let _ := hlocal
    exact HasFiniteDetectingPrimes.of_isLocalRing R
  · let _ := hnoeth
    apply HasFiniteDetectingPrimes.of_finite_weaklyAssociatedPrimes
    rw [← associatedPrimes_eq_setOf_exists_mem_minimalPrimes_annihilator]
    exact associatedPrimes.finite R R
  · let _ := hdomain
    exact HasFiniteDetectingPrimes.of_isDomain R
  · let _ := hreduced.1
    apply HasFiniteDetectingPrimes.of_finite_weaklyAssociatedPrimes
    -- the set on the left is `weaklyAssociatedPrimes R R` unfolded, so tag `0EMA` applies
    have heq : {p : Ideal R | ∃ x : R,
        p ∈ (R ∙ x).annihilator.minimalPrimes} = minimalPrimes R :=
      weakAss_eq_minimalPrimes0EMA (R := R)
    rw [heq]
    exact hreduced.2
  · exact HasFiniteDetectingPrimes.of_finite_weaklyAssociatedPrimes hweak
