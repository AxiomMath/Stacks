module

public import StacksFrontier.AlgebraicGeometry.DeRham.Comparison.Rigidity
public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMapDeterminantLine
public import StacksFrontier.RingTheory.NaiveCotangent.DeterminantBaseChange

/-!
# The maps of Remark 0FL9 with values in `det(NL_{B/A})`

Let `B = A[x_1, …, x_n]/(f_1, …, f_n)` be a square presentation of an `A`-algebra which is a
relative global complete intersection. The construction of Remark 0FL9
(`Stacks.DeRham.presentationFunnyMap`) gives canonical `B`-linear maps
`Ω^p_{B/ℤ} → Ω^p_{A/ℤ} ⊗_A det(NL(P))` with values in the determinant line of the two-term
complex `NL(P)` of the presentation, written as `⋀ⁿ(Ω_{P/A} ⊗ B) ⊗ (⋀ⁿ(I/I²))^∨`. This file
moves the target to the determinant `det(NL_{B/A})` of the naive cotangent complex, along the
canonical identification of the two determinant lines, which carries the canonical element of
Tag 0FL8 to `δ(NL_{B/A})`. The resulting maps satisfy conditions (0H9C) and (0H9D) of
Section 0FL7 on the nose.

## Main definitions

* `Stacks.DeRham.presentationDetNLEquiv`: the identification
  `⋀ⁿ(Ω_{P/A} ⊗ B) ⊗ (⋀ⁿ(I/I²))^∨ ≃ det(NL_{B/A})`.
* `Stacks.DeRham.presentationDetNLMap`: the maps
  `⋀ᵖ Ω[B⁄ℤ] → ⋀ᵖ (B ⊗[A] Ω[A⁄ℤ]) ⊗[B] det(NL_{B/A})` of Remark 0FL9.

## Main results

* `Stacks.DeRham.presentationDetNLEquiv_cotangentDeterminantElement`: the identification carries
  the canonical element of Tag 0FL8 to `δ(NL_{B/A})`.
* `Stacks.DeRham.isFunnyMapFamily_presentationDetNLMap`: the maps satisfy (0H9C) and (0H9D) for
  `δ = δ(NL_{B/A})`.

## References

* [Stacks Project, Tag 0FL9](https://stacks.math.columbia.edu/tag/0FL9)
* [Stacks Project, Section 0FL7](https://stacks.math.columbia.edu/tag/0FL7)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Stacks.DeRham

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin n)) [P.IsRelativeGlobalCompleteIntersection]

/-- The conormal module of a square relative global complete intersection presentation is
free. -/
theorem nonempty_basis_cotangent :
    Nonempty (Module.Basis (Fin n) B P.toExtension.Cotangent) :=
  ⟨(Algebra.Presentation.exists_basis_cotangent_relation P).choose⟩

omit [P.IsRelativeGlobalCompleteIntersection] in
/-- The cotangent space of a presentation by `n` variables is free of rank `n`. -/
theorem nonempty_basis_cotangentSpace :
    Nonempty (Module.Basis (Fin n) B P.toExtension.CotangentSpace) :=
  ⟨Algebra.Generators.cotangentSpaceBasis P.toGenerators⟩

/-- The conormal module of the presentation is a finite `B`-module. -/
instance : Module.Finite B P.toExtension.Cotangent :=
  Module.Finite.of_basis (Classical.choice (nonempty_basis_cotangent P))

/-- The conormal module of the presentation is a projective `B`-module. -/
instance : Module.Projective B P.toExtension.Cotangent :=
  Module.Projective.of_basis (Classical.choice (nonempty_basis_cotangent P))

/-- The cotangent space of the presentation is a finite `B`-module. -/
instance : Module.Finite B P.toExtension.CotangentSpace :=
  Module.Finite.of_basis (Algebra.Generators.cotangentSpaceBasis P.toGenerators)

/-- The cotangent space of the presentation is a projective `B`-module. -/
instance : Module.Projective B P.toExtension.CotangentSpace :=
  Module.Projective.of_basis (Algebra.Generators.cotangentSpaceBasis P.toGenerators)

variable [Algebra.Syntomic A B]

/-- **The determinant line of the presentation is `det(NL_{B/A})`**: the determinant line
`⋀ⁿ(Ω_{P/A} ⊗ B) ⊗ (⋀ⁿ(I/I²))^∨` of Tag 0FL8 of the two-term complex `NL(P)` is identified with
the determinant line `Hom(det(I/I²), det(Ω_{P/A} ⊗ B))` of More on Algebra, Section 0FJI, which
is `det(NL_{B/A})`. -/
noncomputable def presentationDetNLEquiv :
    twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace ≃ₗ[B]
      NaiveCotangent.detNL A B :=
  (twoTermDeterminantEquivDeterminantLine n P.toExtension.cotangentComplex
      (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P)).trans
    (NaiveCotangent.detNLEquiv P.toExtension
      (P.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom).symm

/-- Read through `NaiveCotangent.detNLEquiv`, the identification `presentationDetNLEquiv` is
`twoTermDeterminantEquivDeterminantLine`. -/
theorem detNLEquiv_presentationDetNLEquiv
    (t : twoTermDeterminant B n P.toExtension.Cotangent P.toExtension.CotangentSpace) :
    NaiveCotangent.detNLEquiv P.toExtension
        (P.toGenerators.defaultHom (Algebra.Generators.self A B)).toExtensionHom
        (presentationDetNLEquiv P t) =
      twoTermDeterminantEquivDeterminantLine n P.toExtension.cotangentComplex
        (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P) t :=
  LinearEquiv.apply_symm_apply _ _

/-- The identification of determinant lines carries the canonical element of Tag 0FL8 to
`δ(NL_{B/A})`. -/
theorem presentationDetNLEquiv_cotangentDeterminantElement [Algebra.QuasiFinite A B] :
    presentationDetNLEquiv P (cotangentDeterminantElement P) = NaiveCotangent.deltaNL A B := by
  have hK : TwoTermComplex.IsRankZero P.toExtension.cotangentComplex :=
    isRankZero_of_basis _ (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P)
  show (NaiveCotangent.detNLEquiv P.toExtension _).symm
    (twoTermDeterminantEquivDeterminantLine n P.toExtension.cotangentComplex
      (nonempty_basis_cotangentSpace P) (nonempty_basis_cotangent P)
      (twoTermDeterminantElement B P.toExtension.cotangentComplex
        (nonempty_basis_cotangent P))) = _
  rw [twoTermDeterminantEquivDeterminantLine_twoTermDeterminantElement _ _ _ _ hK]
  exact (LinearEquiv.symm_apply_eq _).2 (NaiveCotangent.detNLEquiv_deltaNL _ _ hK).symm

/-- **The maps of Remark 0FL9 with values in `det(NL_{B/A})`**:
`⋀ᵖ Ω[B⁄ℤ] → ⋀ᵖ (B ⊗[A] Ω[A⁄ℤ]) ⊗[B] det(NL_{B/A})`, the maps
`Stacks.DeRham.presentationFunnyMap` of the presentation followed by the identification
`Stacks.DeRham.presentationDetNLEquiv` of determinant lines. -/
noncomputable def presentationDetNLMap (p : ℕ) :
    (⋀[B]^p Ω[B⁄ℤ]) →ₗ[B] (⋀[B]^p (B ⊗[A] Ω[A⁄ℤ])) ⊗[B] NaiveCotangent.detNL A B :=
  (presentationDetNLEquiv P).toLinearMap.lTensor _ ∘ₗ presentationFunnyMap P p

/-- The map `presentationDetNLMap P p` sends `η` to the image of `presentationFunnyMap P p η`
under the identification `presentationDetNLEquiv P` applied to the second tensor factor. -/
theorem presentationDetNLMap_apply (p : ℕ) (η : ⋀[B]^p Ω[B⁄ℤ]) :
    presentationDetNLMap P p η =
      (presentationDetNLEquiv P).toLinearMap.lTensor _ (presentationFunnyMap P p η) :=
  rfl

/-- **The maps of Remark 0FL9 satisfy (0H9C) and (0H9D)**: the empty wedge goes to
`1 ⊗ δ(NL_{B/A})`, and the maps commute with wedging on the left by base-changed forms on
`A`. -/
theorem isFunnyMapFamily_presentationDetNLMap [Algebra.QuasiFinite A B] :
    IsFunnyMapFamily (KaehlerDifferential.mapBaseChange ℤ A B) (NaiveCotangent.deltaNL A B)
      (presentationDetNLMap P) where
  map_zero := (congrArg ((presentationDetNLEquiv P).toLinearMap.lTensor _)
      (IsFunnyMapFamily.presentationFunnyMap P).map_zero).trans
    (congrArg (exteriorPower.ιMulti B 0 (fun j ↦ Fin.elim0 j) ⊗ₜ[B] ·)
      (presentationDetNLEquiv_cotangentDeterminantElement P))
  map_wedge q p ω η :=
    (congrArg ((presentationDetNLEquiv P).toLinearMap.lTensor _)
      ((IsFunnyMapFamily.presentationFunnyMap P).map_wedge q p ω η)).trans
    (LinearMap.congr_fun ((LinearMap.lTensor_comp_rTensor
      (f := exteriorPower.wedgeMul (R := B) q p ω)
      (g := (presentationDetNLEquiv P).toLinearMap)).trans
      (LinearMap.rTensor_comp_lTensor (f := exteriorPower.wedgeMul (R := B) q p ω)
        (g := (presentationDetNLEquiv P).toLinearMap)).symm) _)

end Stacks.DeRham

end
