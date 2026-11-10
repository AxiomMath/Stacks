module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.CoefficientCohomology

/-!
# The canonical twist of projective space with coefficients

For `T(M) = 𝒪(-n-1) ⊗ p^*M~` on `ℙⁿ_R`, the cohomology `Hᑫ(ℙⁿ_R, T(M))` vanishes for `q ≠ n`,
and `Hⁿ(ℙⁿ_R, T(-))` carries injections to injections. Below the top degree this is dimension
shifting along a free presentation; the degree `n - 1` step uses that the top-degree functor is
tensoring with a free module of rank one.

## Main results

* `Stacks.Duality.ProjCoeff.injective_H_T_map`.
* `Stacks.Duality.ProjCoeff.isZero_H_T_canonical_of_lt`,
  `Stacks.Duality.ProjCoeff.isZero_H_T_canonical_of_gt`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.TopDegreeBaseChange
open Stacks.Cohomology.AffineBase

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **`Hⁿ(ℙⁿ_R, 𝒪(-n-1) ⊗ p^*(-))` preserves injections.** It is tensoring with a free module
of rank one. -/
theorem injective_H_T_map {L L' : ModuleCat.{u} R} (f : L ⟶ L') (hf : Function.Injective f.hom) :
    Function.Injective ((H R n n).map ((T R n (-(n : ℤ) - 1)).map f)).hom := by
  let e := topFunctorIso R n
  have hI : Module.Flat R (Stacks.ProjectiveSpace.Cohomology.twistCohomology R n
      (-(n : ℤ) - 1) n) :=
    Module.Flat.of_linearEquiv
      (Stacks.ProjectiveSpace.Cohomology.twistCohomologyCanonicalIsoCoeff R n).toLinearEquiv
  have h2 : Function.Injective ((MonoidalCategory.tensorLeft (C := ModuleCat.{u} R)
      (Stacks.ProjectiveSpace.Cohomology.twistCohomology R n (-(n : ℤ) - 1) n)).map f).hom :=
    Module.Flat.lTensor_preserves_injective_linearMap f.hom hf
  have h1 : Function.Injective (e.inv.app L).hom := (e.app L).toLinearEquiv.symm.injective
  have h3 : Function.Injective (e.hom.app L').hom := (e.app L').toLinearEquiv.injective
  have hnat := e.inv.naturality f
  have : (e.inv.app L ≫ (MonoidalCategory.tensorLeft (C := ModuleCat.{u} R)
      (Stacks.ProjectiveSpace.Cohomology.twistCohomology R n (-(n : ℤ) - 1) n)).map f ≫
        e.hom.app L') = (affineTopDegreeFunctor R (W R n) n
          (geometricFactor R (W R n) (Oqc R n (-(n : ℤ) - 1)))).map f := by
    rw [← Category.assoc, ← hnat, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  change Function.Injective (ModuleCat.Hom.hom ((affineTopDegreeFunctor R (W R n) n
    (geometricFactor R (W R n) (Oqc R n (-(n : ℤ) - 1)))).map f))
  rw [← this]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp]
  exact (h3.comp h2).comp h1

/-- The canonical twist `𝒪(-n-1)` has no cohomology outside the top degree `n`. -/
theorem isZero_H_O_canonical (q : ℕ) (hq : q ≠ n) :
    IsZero ((H R n q).obj (O R n (-(n : ℤ) - 1))) :=
  (isZero_H_O_iff R n _ q).2
    (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_canonical R n q hq)

/-- The free cover of `L` has no `T`-cohomology outside the top degree. -/
private theorem isZero_H_T_canonical_freeCover (q : ℕ) (hq : q ≠ n) (L : ModuleCat.{u} R) :
    IsZero ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj (freeCover L))) :=
  isZero_H_T_freeCover R n _ q (isZero_H_O_canonical R n q hq) L

/-- The case `q = n - 1` of `isZero_H_T_canonical_of_lt`. -/
theorem isZero_H_T_canonical_pred (q : ℕ) (hq : q + 1 = n) (L : ModuleCat.{u} R) :
    IsZero ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj L)) := by
  let E := Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor (P R n)
  have hS : ((freeCoverShortComplex L).map (T R n (-(n : ℤ) - 1))).ShortExact :=
    (freeCoverShortComplex_shortExact L).map_of_exact _
  have hfree : IsZero ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj (freeCover L))) :=
    isZero_H_T_canonical_freeCover R n q (by omega) L
  have hinj : Function.Injective ((H R n n).map
      ((T R n (-(n : ℤ) - 1)).map (kernel.ι (freeCoverπ L)))).hom :=
    injective_H_T_map R n _ ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have hδ : E.δ hS q = 0 := by
    have hz := E.δ_map_f hS q
    ext x
    apply (show Function.Injective ((E.functor (q + 1)).map
      ((freeCoverShortComplex L).map (T R n (-(n : ℤ) - 1))).f).hom by
        subst hq; exact hinj)
    have := congrArg (fun φ => φ.hom x) hz
    simpa using this
  exact (E.exact_δ₁ hS q).isZero_X₂ (hfree.eq_of_src _ _) hδ

/-- **The canonical twist with coefficients has no cohomology below the top degree.** -/
theorem isZero_H_T_canonical_of_lt (q : ℕ) (hq : q < n) (L : ModuleCat.{u} R) :
    IsZero ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj L)) := by
  have key : ∀ m q : ℕ, q + 1 + m = n → ∀ L : ModuleCat.{u} R,
      IsZero ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj L)) := by
    intro m
    induction m with
    | zero => intro q hq L; exact isZero_H_T_canonical_pred R n q (by omega) L
    | succ m ih =>
      intro q hq L
      exact isZero_of_isZero_free_of_isZero_succ
        (Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor (P R n)) _ q
        (fun L' => isZero_H_T_canonical_freeCover R n q (by omega) L')
        (fun L' => ih (q + 1) (by omega) L') L
  exact key (n - 1 - q) q (by omega) L

/-- **The canonical twist with coefficients has no cohomology above the top degree**, the
quasi-coherent cohomology of `ℙⁿ_R` vanishing above degree `n`. -/
theorem isZero_H_T_canonical_of_gt (q : ℕ) (hq : n < q) (L : ModuleCat.{u} R) :
    IsZero ((H R n q).obj ((T R n (-(n : ℤ) - 1)).obj L)) := by
  have := isQuasicoherent_T R n (-(n : ℤ) - 1) L
  exact isZero_rightDerived_of_lt R n _ q hq

end Stacks.Duality.ProjCoeff
