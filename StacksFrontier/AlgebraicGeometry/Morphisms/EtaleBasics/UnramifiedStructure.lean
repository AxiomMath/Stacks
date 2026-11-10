module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure
public import StacksCore.Tactic.StacksAttribute

/-!
# Local structure of an unramified homomorphism of local rings

An unramified local homomorphism of local rings is a quotient of the localization at a prime of
a standard étale algebra. This is the unramified counterpart of the structure theorem for étale
local homomorphisms, which exhibits the target as such a localization outright.

## Main results

* `Algebra.exists_standardEtalePair_localization_surjection` produces a standard étale pair over
  the base together with a surjective algebra homomorphism from the localization of its ring at
  a prime onto the given local algebra.

## References

* [Stacks Project, Tag 039O](https://stacks.math.columbia.edu/tag/039O)
-/

@[expose] public section

namespace Algebra

/-- An unramified local algebra over a local ring is a quotient of the localization at a prime of
a standard étale algebra. -/
@[stacks 039O, sga "1 I 7.7" "unramified ⇒ quotient"]
theorem exists_standardEtalePair_localization_surjection
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B] :
    ∃ (P : StandardEtalePair A) (q : Ideal P.Ring) (hq : q.IsPrime),
      letI := hq
      ∃ φ : Localization.AtPrime q →ₐ[A] B, Function.Surjective φ := by
  let C : Subalgebra A B := Algebra.EssFiniteType.subalgebra A B
  let qC : Ideal C := (IsLocalRing.maximalIdeal B).comap (algebraMap C B)
  have : qC.IsPrime := Ideal.IsPrime.comap (algebraMap C B)
  have : IsLocalization qC.primeCompl B := by
    convert Algebra.EssFiniteType.isLocalization A B using 1
    ext x
    exact IsLocalRing.notMem_maximalIdeal
  have : Algebra.IsUnramifiedAt A qC := Algebra.FormallyUnramified.of_equiv
    ((IsLocalization.algEquiv qC.primeCompl B (Localization.AtPrime qC)).restrictScalars A)
  obtain ⟨f, hfq, ⟨P, φ, hφ⟩⟩ :=
    Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := A) qC
  let j : Localization.Away f →ₐ[A] B := IsLocalization.Away.liftAlgHom f
    (f := IsScalarTower.toAlgHom A C B)
    (IsLocalRing.notMem_maximalIdeal.mp (by simpa [qC] using hfq))
  let ξ : P.Ring →ₐ[A] B := j.comp φ
  let qP : Ideal P.Ring := (IsLocalRing.maximalIdeal B).comap ξ
  have : qP.IsPrime := Ideal.IsPrime.comap ξ
  have hden (s : qP.primeCompl) : IsUnit (ξ s) := IsLocalRing.notMem_maximalIdeal.mp s.2
  refine ⟨P, qP, inferInstance, IsLocalization.liftAlgHom (M := qP.primeCompl)
    (S := Localization.AtPrime qP) (f := ξ) hden, ?_⟩
  refine (IsLocalization.lift_surjective_iff hden).2 fun b => ?_
  obtain ⟨⟨c, s⟩, hs⟩ := IsLocalization.surj (M := Algebra.EssFiniteType.submonoid A B) b
  obtain ⟨a, ha⟩ := hφ (algebraMap C (Localization.Away f) c)
  obtain ⟨d, hd⟩ := hφ (algebraMap C (Localization.Away f) s)
  refine ⟨⟨a, d, IsLocalRing.notMem_maximalIdeal.mpr (by
    simpa [qP, ξ, j, hd, IsLocalization.Away.lift_eq] using IsLocalization.map_units B s)⟩, ?_⟩
  change b * ξ d = ξ a
  simpa [ξ, j, ha, hd, IsLocalization.Away.lift_eq] using hs

end Algebra
