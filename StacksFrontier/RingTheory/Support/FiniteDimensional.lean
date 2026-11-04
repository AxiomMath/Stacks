module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Topology.JacobsonSpace
public import StacksFrontier.RingTheory.Support.Finite

/-!
# Finite modules that are finite-dimensional over a base field

Let `P` be a commutative ring and `M` a finite `P`-module. Two measurements of how small `M`
is turn out to agree.

Over a Noetherian ring, `M` has finite length exactly when its support is a finite set of
closed points of `Spec(P)`: a composition series contributes one closed point per simple
factor, and conversely a prime-quotient filtration of `M` has all its primes in the support,
hence maximal, hence all its factors simple.

If moreover `P` is of finite type over a field `k` and `M` is viewed as a `k`-module through
`P`, then `M` is finite-dimensional over `k` exactly when it has finite length over `P`.
Noetherian and Artinian both descend along the tower in one direction; in the other, Zariski's
lemma makes each residue field `P ⧸ 𝔪` of a composition factor finite over `k`, so each
factor is finite-dimensional and hence so is `M`.

Combining the two gives a support criterion for finite-dimensionality over the base field,
which is how dimension-zero conditions on `Spec(P)` are recognized in deformation theory.

## Main results

* `Module.isFiniteLength_iff_support_finite_subset_closedPoints`: over a Noetherian ring,
  finite length is finiteness of the support together with closedness of its points.
* `Module.finiteDimensional_iff_isFiniteLength`: over a finite type algebra over a field,
  finite-dimensionality over the field is finite length over the algebra.
* `Module.finiteDimensional_iff_support_finite_subset_closedPoints`: the resulting support
  criterion for finite-dimensionality over the base field.

## Implementation notes

The `k`-module structure on `M` is an arbitrary one compatible with the `P`-action, i.e. one
making `k`, `P`, `M` a scalar tower, rather than the restriction of scalars along
`algebraMap k P`. The two agree (`Module.ext'`), and the compatible form is what a `k`-module
arising in nature satisfies, so the hypothesis is the weaker and more usable one. The
restriction of scalars is used only inside the induction over `IsFiniteLength`, whose motive
ranges over `P`-modules carrying no `k`-structure of their own.

A set of primes consisting of finitely many closed points is expressed as the conjunction of
`Set.Finite` and containment in `closedPoints`, rather than as containment in some finite set
of closed points.
-/

@[expose] public section

universe u v w

namespace Module

/-- A prime lies in the support of `P ⧸ I` if and only if it contains `I`. -/
private theorem mem_support_quotient_iff (P : Type v) [CommRing P] (I : Ideal P)
    (q : PrimeSpectrum P) : q ∈ Module.support P (P ⧸ I) ↔ I ≤ q.asIdeal := by
  rw [Module.support_eq_zeroLocus (M := P ⧸ I), Ideal.annihilator_quotient,
    PrimeSpectrum.mem_zeroLocus]
  rfl

/-- A finite module over a commutative Noetherian ring has finite length if and only if its
support is a finite set of closed points of the prime spectrum. -/
theorem isFiniteLength_iff_support_finite_subset_closedPoints
    (P : Type v) (M : Type w) [CommRing P] [IsNoetherianRing P]
    [AddCommGroup M] [Module P M] [Module.Finite P M] :
    IsFiniteLength P M ↔
      (Module.support P M).Finite ∧
        Module.support P M ⊆ closedPoints (PrimeSpectrum P) := by
  constructor
  · intro h
    induction h with
    | of_subsingleton => simp [Module.support_eq_empty_iff.mpr inferInstance]
    | @of_simple_quotient N _ _ Q _ _ ih =>
        obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
          (inferInstance : IsSimpleModule P (N ⧸ Q))
        have hquot : Module.support P (P ⧸ I) = {⟨I, hI.isPrime⟩} := by
          ext q
          rw [mem_support_quotient_iff, Set.mem_singleton_iff]
          exact ⟨fun hq => PrimeSpectrum.ext (hI.eq_of_le q.isPrime.ne_top hq).symm,
            fun hq => hq ▸ le_rfl⟩
        rw [Module.support_of_exact (LinearMap.exact_subtype_mkQ Q)
          (Submodule.subtype_injective Q) (Submodule.mkQ_surjective Q), e.support_eq, hquot]
        refine ⟨ih.1.union (Set.finite_singleton _), Set.union_subset ih.2 ?_⟩
        rintro _ rfl
        exact mem_closedPoints_iff.mpr
          ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hI)
  · rintro ⟨_, hclosed⟩
    obtain ⟨s, hhead, hlast⟩ :=
      IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime P M
    have key : ∀ t : RelSeries {(N₁, N₂) : Submodule P M × Submodule P M |
        N₁.IsQuotientEquivQuotientPrime N₂},
        t.head = ⊥ → IsFiniteLength P ↥t.last := by
      intro t
      induction t using RelSeries.inductionOn' with
      | singleton x =>
          intro hx
          rw [RelSeries.head_singleton] at hx
          rw [RelSeries.last_singleton, hx]
          exact IsFiniteLength.of_subsingleton
      | snoc t' x htx ih =>
          intro hhd
          rw [RelSeries.head_snoc] at hhd
          rw [RelSeries.last_snoc]
          obtain ⟨hle, q, ⟨e⟩⟩ := htx
          have hq_mem : q ∈ Module.support P M := by
            have hquot : q ∈ Module.support P (↥x ⧸ t'.last.submoduleOf x) := by
              rw [e.support_eq, mem_support_quotient_iff]
            exact Module.support_subset_of_injective x.subtype x.subtype_injective
              (Module.support_subset_of_surjective _ (Submodule.mkQ_surjective _) hquot)
          have : IsSimpleModule P (P ⧸ q.asIdeal) :=
            isSimpleModule_iff_quot_maximal.mpr
              ⟨q.asIdeal, (PrimeSpectrum.isClosed_singleton_iff_isMaximal q).mp
                (mem_closedPoints_iff.mp (hclosed hq_mem)), ⟨LinearEquiv.refl P (P ⧸ q.asIdeal)⟩⟩
          have : IsSimpleModule P (↥x ⧸ t'.last.submoduleOf x) := IsSimpleModule.congr e
          exact IsFiniteLength.of_simple_quotient
            ((Submodule.submoduleOfEquivOfLe hle).symm.isFiniteLength (ih hhd))
    exact Submodule.topEquiv.isFiniteLength (hlast ▸ key s hhead)

/-- Finite-dimensionality over the base field is finite length over the algebra, for the
restriction of scalars along `algebraMap k P`. This is the shape in which the induction over
`IsFiniteLength` can be run; `Module.finiteDimensional_iff_isFiniteLength` is the usable
statement. -/
private theorem finiteDimensional_compHom_iff_isFiniteLength
    (k : Type u) (P : Type v) (M : Type w) [Field k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] [AddCommGroup M] [Module P M]
    [Module.Finite P M] :
    letI : Module k M := Module.compHom M (algebraMap k P)
    FiniteDimensional k M ↔ IsFiniteLength P M := by
  let : Module k M := Module.compHom M (algebraMap k P)
  constructor
  · intro _
    have : IsScalarTower k P M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact ⟨isNoetherian_of_tower k inferInstance, isArtinian_of_tower k inferInstance⟩
  · intro h
    show Module.Finite k M
    induction h with
    | of_subsingleton => exact Module.Finite.of_finite
    | @of_simple_quotient N _ _ Q _ _ ih =>
        let : Module k N := Module.compHom N (algebraMap k P)
        have : IsScalarTower k P N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
        obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp
          (inferInstance : IsSimpleModule P (N ⧸ Q))
        let : Field (P ⧸ I) := Ideal.Quotient.field I
        have hquot : Module.Finite k (P ⧸ I) :=
          finite_of_finite_type_of_isJacobsonRing k (P ⧸ I)
        have : Module.Finite k (N ⧸ Q) :=
          Module.Finite.equiv (e.restrictScalars k).symm
        have : Module.Finite k (N ⧸ Q.restrictScalars k) :=
          Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv k Q).symm
        have : Module.Finite k ↥(Q.restrictScalars k) := ih
        exact Module.Finite.of_submodule_quotient (Q.restrictScalars k)

/-- A finite module over an algebra of finite type over a field is finite-dimensional over the
field if and only if it has finite length over the algebra. -/
theorem finiteDimensional_iff_isFiniteLength
    (k : Type u) (P : Type v) (M : Type w) [Field k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] [AddCommGroup M] [Module P M]
    [Module k M] [IsScalarTower k P M] [Module.Finite P M] :
    FiniteDimensional k M ↔ IsFiniteLength P M := by
  have hmod : Module.compHom M (algebraMap k P) = (inferInstance : Module k M) :=
    Module.ext' _ _ fun r x => algebraMap_smul P r x
  have key := finiteDimensional_compHom_iff_isFiniteLength k P M
  rwa [hmod] at key

/-- A finite module over an algebra of finite type over a field is finite-dimensional over the
field if and only if its support is a finite set of closed points of the prime spectrum of the
algebra. -/
theorem finiteDimensional_iff_support_finite_subset_closedPoints
    (k : Type u) (P : Type v) (M : Type w) [Field k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] [AddCommGroup M] [Module P M]
    [Module k M] [IsScalarTower k P M] [Module.Finite P M] :
    FiniteDimensional k M ↔
      (Module.support P M).Finite ∧
        Module.support P M ⊆ closedPoints (PrimeSpectrum P) := by
  have : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  rw [finiteDimensional_iff_isFiniteLength k P M,
    isFiniteLength_iff_support_finite_subset_closedPoints P M]

end Module

end
