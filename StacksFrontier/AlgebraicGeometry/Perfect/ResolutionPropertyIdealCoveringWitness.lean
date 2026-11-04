module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.PerfectRepresentativeUnconditional
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCoveringSubstantial

/-!
# A named inhabitant of the hypotheses of the substantial direction of Stacks 0F89

`AlgebraicGeometry.hasResolutionProperty_of_isIdealAffineCovering` quantifies over a finite
affine open covering, finite type quasi-coherent sheaves of ideals cutting out the complements
of its members, and finite locally free resolutions of those ideals.  This file exhibits all of
that data at once at the named scheme `Spec (ULift ℤ)`.

The module is separate from the theorem's because the input it uses,
`AlgebraicGeometry.hasResolutionProperty_of_isAffine`, sits in a much larger import closure.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

/-- **Every binder of `AlgebraicGeometry.hasResolutionProperty_of_isIdealAffineCovering` is
inhabited at once**, at the named scheme `Spec (ULift ℤ)`: the one-member covering by `⊤`, the
unit sheaf of ideals, and the resolution of it that the immediate direction of
[Stacks, Tag 0F89] produces from the resolution property of an affine scheme.

This certifies satisfiability, not non-triviality: the covering has one member and the sheaf of
ideals is the unit ideal, so the instance is structurally degenerate.  The non-degenerate
instances of the hypothesis structure are the ones
`AlgebraicGeometry.Scheme.IsAmpleFamily.exists_isIdealAffineCovering` produces, where the
members of the covering are the nonvanishing loci of global sections of invertible modules and
the ideals are proper. -/
theorem exists_isIdealAffineCovering_specULiftInt :
    ∃ (m : ℕ) (U : Fin m → (Spec (CommRingCat.of (ULift.{u} ℤ))).Opens)
      (I : Fin m → (Spec (CommRingCat.of (ULift.{u} ℤ))).IdealSheafData)
      (_ : IsIdealAffineCovering (Spec (CommRingCat.of (ULift.{u} ℤ))) U I)
      (E : Fin m → (Spec (CommRingCat.of (ULift.{u} ℤ))).Modules)
      (_ : ∀ j, SheafOfModules.IsFiniteLocallyFree
          (R := (Spec (CommRingCat.of (ULift.{u} ℤ))).ringCatSheaf) (E j))
      (q : ∀ j, E j ⟶ idealPow (I j) 1), ∀ j, Epi (q j) := by
  set X : Scheme.{u} := Spec (CommRingCat.of (ULift.{u} ℤ))
  have hcov : IsIdealAffineCovering X (fun _ : Fin 1 => (⊤ : X.Opens))
      (fun _ : Fin 1 => (⊤ : X.IdealSheafData)) := by
    refine isIdealAffineCovering_of_isFiniteType _ _ (fun _ => isAffineOpen_top X) (by simp)
      (fun _ V => ?_) (fun _ => ?_)
    · rw [Scheme.IdealSheafData.ideal_top]
      exact ⟨{1}, by simp⟩
    · rw [Scheme.IdealSheafData.support_top]
      simp
  have _ : HasResolutionProperty X := hasResolutionProperty_of_isAffine X
  choose E hE q hq using fun j : Fin 1 =>
    exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering hcov j
  exact ⟨1, _, _, hcov, E, hE, q, hq⟩

end AlgebraicGeometry

end
