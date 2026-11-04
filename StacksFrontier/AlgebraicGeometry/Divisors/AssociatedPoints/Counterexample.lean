module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Functoriality
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.RingTheory.SquareZeroQuotient
public import StacksCore.Tactic.StacksAttribute

/-!
# A local ring with locally nilpotent maximal ideal and no associated prime

For a field `k`, the quotient of the polynomial ring in countably many variables by the squares
of those variables is a local ring whose maximal ideal is locally nilpotent, yet no element has
that ideal as its annihilator. Consequently the ring has no associated primes and the spectrum
has no associated points: this is the example showing that a nonzero module can fail to have an
associated point.

## Main results

* `AlgebraicGeometry.maximalIdeal_locallyNilpotent`: its maximal ideal is locally nilpotent.
* `AlgebraicGeometry.no_maximalIdeal_annihilator`: no element has the maximal ideal as its
  annihilator.
* `AlgebraicGeometry.spectrum_associatedPoints_eq_empty`: the spectrum has no associated points.

## Implementation notes

The ring is the existing `S k`, the quotient of `MvPolynomial ℕ k` by `sqIdeal k`; the
ring-theoretic half of the example, `assExact_S_eq_empty`, is already in the library. That the
ring is local — the augmentation `aug k` sends every variable to zero, and its kernel is the
nilradical, which is therefore maximal — is `Stacks.SquareZero.isLocalRing`, which carries the
"local ring" clause of this tag; it and the nilpotence facts it rests on live in
`StacksFrontier.RingTheory.SquareZeroQuotient`, shared with the auto-associated example of tag
05GL.

The scheme-theoretic conclusion transports an associated point of the structure sheaf on
`Spec (S k)` back to an associated prime of `S k` itself: the stalk at any point is `S k`, since
every element outside the maximal ideal is a unit.

## References

* [Stacks Project, Tag 05AI](https://stacks.math.columbia.edu/tag/05AI)
-/

@[expose] public section

open AlgebraicGeometry MvPolynomial Stacks.SquareZero

universe u

namespace AlgebraicGeometry

/-- The maximal ideal of the quotient is its nilradical. -/
private theorem maximalIdeal_eq_nilradical (k : Type u) [Field k] [IsLocalRing (S k)] :
    IsLocalRing.maximalIdeal (S k) = nilradical (S k) := by
  rw [nilradical_eq_ker_aug k]
  exact (IsLocalRing.ker_eq_maximalIdeal (aug k).toRingHom (aug_surjective k)).symm

/-- Every prime of the quotient is its maximal ideal. -/
private theorem prime_eq_maximalIdeal (k : Type u) [Field k] (p : PrimeSpectrum (S k))
    [IsLocalRing (S k)] : p.asIdeal = IsLocalRing.maximalIdeal (S k) :=
  le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal)
    ((maximalIdeal_eq_nilradical k).trans_le (nilradical_le_prime p.asIdeal))

/-- The colon ideal `(⊥ : Submodule R M) : span {m}` is the annihilator `annElem m`. -/
private theorem bot_colon_span_singleton_eq_annElem {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (m : M) : (⊥ : Submodule R M).colon (Submodule.span R {m}) = annElem m := by
  ext
  simp [mem_annElem]

/-- An exact-annihilator associated prime transports along a ring equivalence. -/
private theorem associatedPrimeStacks_of_ringEquiv {R T : Type*} [CommRing R] [CommRing T]
    (e : R ≃+* T) {p : Ideal R} {q : Ideal T} (hp : p.IsPrime) (heq : ∀ r, r ∈ p ↔ e r ∈ q)
    (h : IsAssociatedPrimeStacks T T q) : IsAssociatedPrimeStacks R R p := by
  obtain ⟨_, t, ht⟩ := h
  refine ⟨hp, e.symm t, ?_⟩
  rw [bot_colon_span_singleton_eq_annElem] at ht ⊢
  ext r
  rw [mem_annElem, smul_eq_mul, heq, ← ht, mem_annElem, smul_eq_mul,
    ← map_eq_zero_iff e e.injective, map_mul, e.apply_symm_apply]

/-- An exact-annihilator associated prime transports along a linear equivalence. -/
private theorem associatedPrimeStacks_of_linearEquiv {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (E : M ≃ₗ[R] N)
    {p : Ideal R} (h : IsAssociatedPrimeStacks R M p) : IsAssociatedPrimeStacks R N p := by
  obtain ⟨hprime, m, hm⟩ := h
  refine ⟨hprime, E m, ?_⟩
  rw [bot_colon_span_singleton_eq_annElem] at hm ⊢
  ext a
  rw [← hm, mem_annElem, mem_annElem, ← E.map_smul, map_eq_zero_iff E E.injective]

/-- **Stacks 05AI.** The maximal ideal of the square-zero-variable quotient is locally
nilpotent. -/
@[stacks 05AI "locally nilpotent maximal ideal"]
theorem maximalIdeal_locallyNilpotent (k : Type u) [Field k] :
    (IsLocalRing.maximalIdeal (S k)).LocallyNilpotent := by
  rw [maximalIdeal_eq_nilradical k]
  exact fun _ => mem_nilradical.mp

/-- **Stacks 05AI.** No element of the quotient has its maximal ideal as annihilator. -/
@[stacks 05AI "no maximal-ideal annihilator"]
theorem no_maximalIdeal_annihilator (k : Type u) [Field k] (s : S k) :
    annElem s ≠ IsLocalRing.maximalIdeal (S k) := by
  intro hs
  have hmem : IsLocalRing.maximalIdeal (S k) ∈ assExact (S k) (S k) :=
    ⟨(IsLocalRing.maximalIdeal.isMaximal (S k)).isPrime, s, hs.symm⟩
  simp [assExact_S_eq_empty k] at hmem

add_to_stacks 05AI "no associated primes" assExact_S_eq_empty

/-- **Stacks 05AI.** The spectrum of the square-zero-variable quotient has no associated
points. -/
@[stacks 05AI "no associated points"]
theorem spectrum_associatedPoints_eq_empty (k : Type u) [Field k] :
    Stacks.Divisors.schemeAssociatedPoints (Spec (.of (S k))) = ∅ := by
  classical
  let : CommSemiring (S k) := (inferInstance : CommRing (S k)).toCommSemiring
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [Stacks.Divisors.mem_schemeAssociatedPoints_iff,
    Stacks.Divisors.IsAssociatedPoint] at hx
  let p : PrimeSpectrum (S k) := x
  let X := Spec (.of (S k))
  let T := X.presheaf.stalk x
  let : Algebra (S k) T := StructureSheaf.stalkAlgebra (S k) p
  let : IsLocalization.AtPrime T p.asIdeal := StructureSheaf.IsLocalization.to_stalk (S k) p
  let : IsLocalRing T := IsLocalization.AtPrime.isLocalRing T p.asIdeal
  have hnotmem : p.asIdeal.primeCompl ≤ IsUnit.submonoid (S k) :=
    fun _ hs => IsLocalRing.notMem_maximalIdeal.mp <| by
      simpa [prime_eq_maximalIdeal k p] using hs
  let e : S k ≃+* T := (IsLocalization.atUnits (S k) p.asIdeal.primeCompl hnotmem).toRingEquiv
  let mT : Ideal T := IsLocalRing.maximalIdeal T
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let U := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let : Module T U :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Module (S k) U := Module.compHom U (algebraMap (S k) T)
  let : IsScalarTower (S k) T U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hassoc : IsAssociatedPrimeStacks T U mT := by
    change IsAssociatedPrimeStacks ((Spec (.of (S k))).presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit (Spec (.of (S k))).ringCatSheaf).val.presheaf x)
      (IsLocalRing.maximalIdeal ((Spec (.of (S k))).presheaf.stalk x)) at hx
    simpa [T, U, mT, X] using hx
  have heq : ∀ r : S k, r ∈ IsLocalRing.maximalIdeal (S k) ↔ e r ∈ mT :=
    fun r => by simp [mT, IsLocalRing.mem_maximalIdeal, e]
  let E : U ≃ₗ[S k] T := StructureSheaf.commRingCatStalkEquivModuleStalk (S k) x
  let E' : U ≃ₗ[T] T := E.toAddEquiv.toLinearEquiv fun a m => by
    have hr : algebraMap (S k) T (e.symm a) = a := e.apply_symm_apply a
    rw [← hr, IsScalarTower.algebraMap_smul]
    simp [Algebra.smul_def, E.map_smul (e.symm a) m]
  obtain ⟨-, s, hs⟩ :=
    associatedPrimeStacks_of_ringEquiv e (IsLocalRing.maximalIdeal.isMaximal (S k)).isPrime
      heq (associatedPrimeStacks_of_linearEquiv E' hassoc)
  exact no_maximalIdeal_annihilator k s ((bot_colon_span_singleton_eq_annElem s).symm.trans hs)

end AlgebraicGeometry
