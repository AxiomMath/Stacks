module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Category

/-!
# Completions of finite type algebras (Stacks 0AJQ)

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `C` a finite type `A`-algebra. The
`I`-adic completion of `C` — that is, the completion of `C` along the extension of `I` to
`C` — is adically complete for the ideal extended directly from `A`, and its reduction
modulo that ideal is of finite type over `A ⧸ I`. Together these say that the completion of
a finite type algebra is an object of the category `Rig.AdicFiniteTypeAlgebra A I` of
Stacks 0AL4.

## Main results

* `Rig.adicCompletion_isAdicallyComplete`: the completion is adically complete for the ideal
  extended from `A`.
* `Rig.adicCompletion_finiteType_quotient`: the reduction of the completion modulo that ideal is of
  finite type over `A ⧸ I`.

## References

* [Stacks Project, Lemma 88.3.2 (Tag 0AJQ)](https://stacks.math.columbia.edu/tag/0AJQ)
-/

@[expose] public section

universe u v

namespace Rig

/-- The completion of a finite type algebra over a Noetherian ring is complete for the ideal
extended directly from the base ring. -/
@[stacks 0AJQ "finite_type_completions"]
public theorem adicCompletion_isAdicallyComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type v) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    IsAdicComplete
      (I.map (algebraMap A (AdicCompletion (I.map (algebraMap A C)) C)))
      (AdicCompletion (I.map (algebraMap A C)) C) := by
  let J : Ideal C := I.map (algebraMap A C)
  let S : Type v := AdicCompletion J C
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  show IsAdicComplete (I.map (algebraMap A S)) S
  rw [IsScalarTower.algebraMap_eq A C S, ← Ideal.map_map,
    IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (IsNoetherian.noetherian J)

/-- The quotient modulo the ideal from the base ring of the completion of a finite type algebra
is of finite type over the quotient of the base ring. -/
@[stacks 0AJQ "finite_type_completions"]
public theorem adicCompletion_finiteType_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type v) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    Algebra.FiniteType (A ⧸ I)
      ((AdicCompletion (I.map (algebraMap A C)) C) ⧸
        I.map (algebraMap A (AdicCompletion (I.map (algebraMap A C)) C))) := by
  let J : Ideal C := I.map (algebraMap A C)
  have : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing A C
  have : Algebra.FiniteType C
      ((AdicCompletion J C) ⧸ J.map (algebraMap C (AdicCompletion J C))) :=
    (inferInstance : Algebra.FiniteType C (C ⧸ J)).equiv
      ((Ideal.quotientEquivAlgOfEq C
        (AdicCompletion.ker_evalOneₐ_eq_map J (Ideal.fg_of_isNoetherianRing J)).symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective
          (AdicCompletion.evalOneₐ_surjective J))).symm
  have : Algebra.FiniteType A
      ((AdicCompletion J C) ⧸ I.map (algebraMap A (AdicCompletion J C))) := by
    rw [IsScalarTower.algebraMap_eq A C _, ← Ideal.map_map]
    exact (inferInstance : Algebra.FiniteType A C).trans inferInstance
  exact Algebra.FiniteType.of_restrictScalars_finiteType A (A ⧸ I) _

end Rig

end
