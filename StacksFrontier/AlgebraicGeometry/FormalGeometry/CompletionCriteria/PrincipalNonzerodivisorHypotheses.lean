module

public import StacksFrontier.AlgebraicGeometry.Algebraization.LefschetzSerreConditionSpecialCases
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.CutoffCriterionAffine

/-!
# Conditions (2) and (3) of the principal-ideal extension criterion

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U`, and consider the conditions

1. `I = (f)` for a nonzerodivisor `f ∈ 𝔞`,
2. `F_n` is a finite locally free `𝒪_U/f^n𝒪_U`-module,
3. `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite `A`-modules.

This file shows that condition (3) makes `H⁰(U, 𝒪_U/f𝒪_U)` and `H¹(U, 𝒪_U/f𝒪_U)` finite
`A`-modules, and that condition (2), stated as `Stacks.Algebraization.IsFiniteLocallyFreeAdic`
for `Stacks.Algebraization.idealOnOpen`, makes the stalks of the terms free over the stalks of
the corresponding quotients of the structure sheaf.

## Main definitions

* `Stacks.Algebraization.baseQuotient` — the `A`-module `A/fA`.
* `Stacks.Algebraization.localCohomologyBaseQuotient` — the local cohomology `H^i_𝔞(A/fA)`.
* `Stacks.Algebraization.complementCohomologyBaseQuotient` — `H^p(U, 𝒪_U/f𝒪_U)`, as an
  `A`-module.

## Main results

* `Stacks.Algebraization.U_eq_zeroLocusCompl` — the open complement of the situation is
  `zeroLocusCompl 𝔞`.
* `Stacks.Algebraization.finite_complementCohomologyBaseQuotient_iff` — `H^p(U, 𝒪_U/f𝒪_U)` is a
  finite `A`-module exactly when `H^(p+1)_𝔞(A/fA)` is.
* `Stacks.Algebraization.finite_complementCohomologyBaseQuotient_of_finite_localCohomology` — if
  `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite, then so are `H⁰(U, 𝒪_U/f𝒪_U)` and
  `H¹(U, 𝒪_U/f𝒪_U)`.
* `Stacks.Algebraization.free_stalk_quotient_of_isFiniteLocallyFreeAdic` — under condition (2),
  at a point `y` of `U ∩ Y` the stalk of `F_(n+1)` modulo `I_y^(n+1)` is a free
  `𝒪_{U,y}/I_y^(n+1)`-module.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0BLT](https://stacks.math.columbia.edu/tag/0BLT)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
* [Stacks Project, Tag 0EL6](https://stacks.math.columbia.edu/tag/0EL6)
* [Stacks Project, Tag 0H39](https://stacks.math.columbia.edu/tag/0H39)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-! ### Condition (3) -/

/-- The quotient `A/fA` of the base ring, as an `A`-module. -/
abbrev baseQuotient (f : S.A) : ModuleCat.{u} S.A :=
  ModuleCat.of S.A (S.A ⧸ Ideal.span {f})

/-- `A/fA` is a finite `A`-module. -/
theorem finite_baseQuotient (f : S.A) : Module.Finite S.A (baseQuotient S f) :=
  Module.Finite.of_surjective (Submodule.mkQ (Ideal.span {f})) (Submodule.mkQ_surjective _)

/-- The local cohomology `H^i_𝔞(A/fA)`, as an `A`-module. -/
abbrev localCohomologyBaseQuotient (f : S.A) (i : ℕ) : ModuleCat.{u} S.A :=
  Stacks.LocalCohomology.localCohomologyWithSupportIn.{u, u} (CommRingCat.of S.A)
    (PrimeSpectrum.zeroLocus (S.a : Set S.A))
    ((DerivedCategory.singleFunctor (ModuleCat.{u} S.A) 0).obj (baseQuotient S f)) (i : ℤ)

/-- The cohomology `H^p(U, 𝒪_U/f𝒪_U)` of the structure sheaf of the closed subscheme cut out by
`f`, as an `A`-module; the sheaf is the restriction to `U` of the quasi-coherent sheaf attached
to `A/fA`. -/
abbrev complementCohomologyBaseQuotient (f : S.A) (p : ℕ) : ModuleCat.{u} S.A :=
  Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of S.A) S.a
    (baseQuotient S f) p

/-- The open complement `U = X \ V(𝔞)` of the situation is `zeroLocusCompl 𝔞`. -/
theorem U_eq_zeroLocusCompl : S.U = zeroLocusCompl S.a := rfl

/-- `H^p(U, 𝒪_U/f𝒪_U)` is a finite `A`-module exactly when the local cohomology
`H^(p+1)_𝔞(A/fA)` is. -/
theorem finite_complementCohomologyBaseQuotient_iff (f : S.A) (p : ℕ) :
    Module.Finite S.A (complementCohomologyBaseQuotient S f p) ↔
      Module.Finite S.A (localCohomologyBaseQuotient S f (p + 1)) :=
  have := finite_baseQuotient S f
  (Stacks.LocalCohomologySequence.moduleFinite_complementCohomologyBase_iff_isCoherent
      (A := CommRingCat.of S.A) S.a (baseQuotient S f) p).trans
    (Stacks.LocalCohomologySequence.isCoherent_rightDerived_iff_finite_localCohomology
      (A := CommRingCat.of S.A) S.a (baseQuotient S f) p)

/-- If `H¹_𝔞(A/fA)` and `H²_𝔞(A/fA)` are finite `A`-modules, then so are `H⁰(U, 𝒪_U/f𝒪_U)` and
`H¹(U, 𝒪_U/f𝒪_U)`. -/
theorem finite_complementCohomologyBaseQuotient_of_finite_localCohomology (f : S.A)
    (h₁ : Module.Finite S.A (localCohomologyBaseQuotient S f 1))
    (h₂ : Module.Finite S.A (localCohomologyBaseQuotient S f 2)) :
    ∀ p : ℕ, p < 2 → Module.Finite S.A (complementCohomologyBaseQuotient S f p) := by
  intro p hp
  interval_cases p
  · exact (finite_complementCohomologyBaseQuotient_iff S f 0).mpr h₁
  · exact (finite_complementCohomologyBaseQuotient_iff S f 1).mpr h₂

/-! ### Condition (2) -/

/-- If the terms of the system are finite locally free over the infinitesimal neighbourhoods,
then at a point `y` of `U ∩ Y` the stalk of `F_(n+1)` modulo `I_y^(n+1)` is a free
`𝒪_{U,y}/I_y^(n+1)`-module. -/
theorem free_stalk_quotient_of_isFiniteLocallyFreeAdic
    (hfree : IsFiniteLocallyFreeAdic (idealOnOpen S) F) (n : ℕ)
    {y : S.U.toScheme} (hy : y ∈ (idealOnOpen S).support) :
    Module.Free
      (S.U.toScheme.presheaf.stalk y ⧸ IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1))
      ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))) ⧸
        (IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op (n + 1))))))) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hfree n
  have : (F.obj.obj (op (n + 1))).IsQuasicoherent := F.property.isQuasicoherent (n + 1)
  exact free_quotient_stalk_of_pushforward_iso (idealOnOpen S) (F.obj.obj (op (n + 1)))
    (Nat.succ_ne_zero n) hy N hN (F.property.quotientIso n ≪≫ e.symm)

end Stacks.Algebraization

end
