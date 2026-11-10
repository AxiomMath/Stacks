module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.LimitExactFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharpolyRootsExact

/-!
# Weights along exact sequences of ℓ-adic limits

The compactly supported ℓ-adic cohomology `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is
`(limₙ Hⁱ_c(X_k̄, Fₙ)) ⊗_{ℤ_ℓ} ℚ_ℓ`, and the geometric Frobenius acts through a natural
endomorphism of the tower `n ↦ Hⁱ_c(X_k̄, Fₙ)`.  For a sequence of towers exact at every level
with finite first term, the rational limits form an exact sequence, along which bounds on the
weights of compatible endomorphisms pass from the outer terms to the middle one.

## Main results

* `Stacks.EtaleCohomology.exact_rationalLimMap_of_finite`: the rational limits
  `(lim A) ⊗ ℚ_ℓ → (lim B) ⊗ ℚ_ℓ → (lim C) ⊗ ℚ_ℓ` of a levelwise exact sequence of towers of
  `ℤ_ℓ`-modules with finite first term form an exact sequence.
* `Stacks.EtaleCohomology.isCharpolyNormMixedOfWeightLE_rationalLimMap_of_exact`: for towers with
  compatible endomorphisms, the bound on absolute values of the characteristic roots of the
  induced endomorphisms passes from the two outer rational limits to the middle one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v

namespace Stacks.EtaleCohomology

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- The rational limit `(lim A) ⊗_{ℤ_ℓ} ℚ_ℓ` of a tower of `ℤ_ℓ`-modules, as a functor of the
tower. -/
public abbrev rationalLim [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} ℤ_[ℓ])] :
    (ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) ⥤ ModuleCat.{v} ℚ_[ℓ] :=
  lim ⋙ ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])

/-- Extension of scalars from `ℤ_ℓ` to `ℚ_ℓ` preserves exactness. -/
public theorem exact_extendScalars_padic {M N P : ModuleCat.{v} ℤ_[ℓ]} {f : M ⟶ N} {g : N ⟶ P}
    (h : Function.Exact f g) :
    Function.Exact ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map f)
      ((ModuleCat.extendScalars.{0, 0, v} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map g) := by
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  change Function.Exact (LinearMap.lTensor ℚ_[ℓ] f.hom) (LinearMap.lTensor ℚ_[ℓ] g.hom)
  exact Module.Flat.lTensor_exact ℚ_[ℓ] h

variable [HasLimitsOfShape ℕᵒᵖ (ModuleCat.{v} ℤ_[ℓ])] {A B C : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]}

/-- **Rational limits of levelwise exact sequences of towers with finite first term are exact.** -/
public theorem exact_rationalLimMap_of_finite (α : A ⟶ B) (β : B ⟶ C)
    (hex : ∀ n, Function.Exact (α.app n) (β.app n)) (hfin : ∀ n, Finite (A.obj n)) :
    Function.Exact ((rationalLim (ℓ := ℓ)).map α) ((rationalLim (ℓ := ℓ)).map β) :=
  exact_extendScalars_padic (ModuleCat.exact_limMap_of_finite α β hex hfin)

/-- **Weights along an exact sequence of towers.**  Let `α : A ⟶ B`, `β : B ⟶ C` be maps of towers
of `ℤ_ℓ`-modules, exact at every level, with every `A n` finite, intertwining endomorphisms
`φA`, `φB`, `φC` of the towers.  If the induced endomorphisms of the finite-dimensional rational
limits of `A` and `C` have characteristic roots along `ι` of absolute values `q ^ (w / 2)` with
`w ≤ i`, so does the one of `B`. -/
public theorem isCharpolyNormMixedOfWeightLE_rationalLimMap_of_exact (α : A ⟶ B) (β : B ⟶ C)
    (hex : ∀ n, Function.Exact (α.app n) (β.app n)) (hfin : ∀ n, Finite (A.obj n))
    (φA : A ⟶ A) (φB : B ⟶ B) (φC : C ⟶ C) (hα : φA ≫ α = α ≫ φB) (hβ : φB ≫ β = β ≫ φC)
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj A)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj B)]
    [FiniteDimensional ℚ_[ℓ] ((rationalLim (ℓ := ℓ)).obj C)] {q : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {i : ℤ}
    (hA : IsCharpolyNormMixedOfWeightLE q ι i ((rationalLim (ℓ := ℓ)).map φA).hom)
    (hC : IsCharpolyNormMixedOfWeightLE q ι i ((rationalLim (ℓ := ℓ)).map φC).hom) :
    IsCharpolyNormMixedOfWeightLE q ι i ((rationalLim (ℓ := ℓ)).map φB).hom := by
  refine IsCharpolyNormMixedOfWeightLE.of_exact_of_exact hA hC
    (j := ((rationalLim (ℓ := ℓ)).map α).hom)
    (p := ((rationalLim (ℓ := ℓ)).map β).hom) (fun a => ?_) (fun b => ?_)
    (exact_rationalLimMap_of_finite α β hex hfin)
  · have h := congrArg (fun t => (ModuleCat.Hom.hom ((rationalLim (ℓ := ℓ)).map t)) a) hα
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h
  · have h := congrArg (fun t => (ModuleCat.Hom.hom ((rationalLim (ℓ := ℓ)).map t)) b) hβ
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h
    exact h

end Stacks.EtaleCohomology

end
