module

public import StacksFrontier.AlgebraicGeometry.Different.NoetherDifferent.JacobianDualizingModuleDescent
public import StacksFrontier.RingTheory.TateMap.DetNL

/-!
# The Tate map on a localized complete intersection

Let `A` be a Noetherian ring and `B ≅ A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` quasi-finite over `A`.
Then `det(NL_{B/A})` and the relative dualizing module `ω_{B/A}` are both free of rank one, with
generators carrying the Jacobian determinant `det(∂f_i/∂x_j)` to `δ(NL_{B/A})` and to the trace
element `τ_{B/A}` respectively (Remark 0FKC and Lemma 0BWH). Matching the generators gives an
isomorphism `det(NL_{B/A}) ≅ ω_{B/A}` carrying `δ(NL_{B/A})` to `τ_{B/A}`: the local input of
the Tate map of Stacks, Section 0FKB.

## Main results

* `Stacks.TateMap.syntomic_of_algEquiv_localizedCompleteIntersection`: such a `B` is syntomic
  over `A`.
* `Stacks.TateMap.exists_linearEquiv_detNL_dualizingModule_deltaNL`: the isomorphism
  `det(NL_{B/A}) ≅ ω_{B/A}` carrying `δ(NL_{B/A})` to `τ_{B/A}`.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
* [Stacks Project, Tag 0FKC](https://stacks.math.columbia.edu/tag/0FKC)
* [Stacks Project, Tag 0BWH](https://stacks.math.columbia.edu/tag/0BWH)
-/

@[expose] public noncomputable section

open Stacks.Discriminant

universe u

namespace Stacks.TateMap

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} {h : MvPolynomial (Fin n) A} {f : Fin n → MvPolynomial (Fin n) A}

/-- An algebra isomorphic to a quasi-finite `A[x_1, …, x_n, 1/h]/(f_1, …, f_n)` is syntomic: it
is a relative global complete intersection. -/
theorem syntomic_of_algEquiv_localizedCompleteIntersection
    (e : B ≃ₐ[A] localizedCompleteIntersection A n h f) [Algebra.QuasiFinite A B] :
    Algebra.Syntomic A B :=
  have : Algebra.QuasiFinite A (localizedCompleteIntersection A n h f) :=
    (Algebra.QuasiFinite.iff_of_algEquiv e).mp inferInstance
  have := Algebra.IsRelativeGlobalCompleteIntersection.of_algEquiv e.symm
  Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection A B

/-- **The local Tate map.** Let `A` be a Noetherian ring and `B ≅ A[x_1, …, x_n, 1/h]/(f_1, …,
f_n)` quasi-finite over `A`. For every finite-open factorization `F` of `A → B` there is an
isomorphism `det(NL_{B/A}) ≅ ω_{B/A}` carrying `δ(NL_{B/A})` to the trace element `τ_{B/A}`.

The `letI`s are derivations, not hypotheses: `B` is syntomic over `A` by
`Stacks.TateMap.syntomic_of_algEquiv_localizedCompleteIntersection`, hence flat and of finite
presentation, hence Noetherian. -/
theorem exists_linearEquiv_detNL_dualizingModule_deltaNL [IsNoetherianRing A]
    (e : B ≃ₐ[A] localizedCompleteIntersection A n h f) [Algebra.QuasiFinite A B] :
    letI := syntomic_of_algEquiv_localizedCompleteIntersection e
    letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
    ∀ F : FiniteOpenFactorization.{u, u, u} A B,
      ∃ c : detNL A B ≃ₗ[B] dualizingModule F,
        c (deltaNL A B) = dualizingModule.traceElement F := by
  let := syntomic_of_algEquiv_localizedCompleteIntersection e
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  intro F
  have : Module.FinitePresentation A F.middle := Module.finitePresentation_of_finite A _
  obtain ⟨b, hb⟩ := exists_basis_deltaNL_eq_jacobianDet e
  obtain ⟨ε, hε⟩ := exists_linearEquiv_traceCandidate_of_algEquiv A n h f e.symm F
  refine ⟨b.equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) B B ≪≫ₗ ε, ?_⟩
  have hb' : deltaNL A B = e.symm (jacobianDet n h f) • b 0 := hb
  have h1 : LinearEquiv.funUnique (Fin 1) B B (b.equivFun (b 0)) = 1 := by simp
  rw [hb', LinearEquiv.trans_apply, LinearEquiv.trans_apply, map_smul, map_smul, h1,
    smul_eq_mul, mul_one]
  exact hε

end Stacks.TateMap
