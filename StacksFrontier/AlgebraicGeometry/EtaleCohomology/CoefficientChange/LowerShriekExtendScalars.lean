module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedExtensionOfScalars
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.LowerShriekRestrictScalars
public import StacksFrontier.Algebra.Homology.DerivedCategory.FaithfulConservative
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Cohomology with compact support and derived extension of coefficients

Let `φ : Λ₁ → Λ₂` be a homomorphism of commutative rings, `f : X ⟶ Y` a morphism of schemes and
`j` a compactification of `X` over `Y`, with `Rf_! = R(f̄)_* ∘ Rj_!`.  The second diagram of
[Stacks, Remark 0GL6] compares `Rf_!` with derived extension of coefficients
`- ⊗^L_{Λ₁} Λ₂`.  This file constructs the comparison map
`Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)`: it is the mate, for the adjunctions
`- ⊗^L_{Λ₁} Λ₂ ⊣ res_φ` on `X` and on `Y`, of the first diagram of the remark
(`Stacks.EtaleCohomology.derivedLowerShriekUnboundedRestrictScalarsIso`).

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedExtendScalarsMap`: the comparison map.

## Main results

* `Stacks.EtaleCohomology.isIso_derivedLowerShriekUnboundedExtendScalarsMap_app_iff`: the
  comparison map is invertible exactly when it is after restriction of coefficients, restriction
  of coefficients being conservative.

## References

* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable {Λ₁ Λ₂ : Type r} [CommRing Λ₁] [CommRing Λ₂] (φ : Λ₁ →+* Λ₂)
  {X Y : Scheme.{u}} (f : X ⟶ Y) (j : CompactificationOf (Over.mk f))

/-- **The comparison of the second diagram of [Stacks, Remark 0GL6]**,
`Rf_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rf_!(E ⊗^L_{Λ₁} Λ₂)`: the mate, for derived extension of coefficients
left adjoint to restriction of coefficients on `X` and on `Y`, of the first diagram of the
remark. -/
def derivedLowerShriekUnboundedExtendScalarsMap :
    derivedLowerShriekUnbounded.{u, r} f j Λ₁ ⋙ etaleModuleDerivedExtendScalars.{u, r} φ Y ⟶
      etaleModuleDerivedExtendScalars.{u, r} φ X ⋙ derivedLowerShriekUnbounded.{u, r} f j Λ₂ :=
  ((mateEquiv (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y)).symm
    (TwoSquare.mk _ _ _ _
      (derivedLowerShriekUnboundedRestrictScalarsIso.{u, r} φ f j).inv)).natTrans

/-- The comparison of extension by zero with derived extension of coefficients,
`j_!(E) ⊗^L_{Λ₁} Λ₂ ⟶ j_!(E ⊗^L_{Λ₁} Λ₂)`: the mate of the square of extension by zero and
restriction of coefficients. -/
def derivedExtensionByZeroUnboundedExtendScalarsMap {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] :
    etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j ⋙
        etaleModuleDerivedExtendScalars.{u, r} φ X ⟶
      etaleModuleDerivedExtendScalars.{u, r} φ U ⋙
        etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₂ j :=
  ((mateEquiv (etaleModuleDerivedExtendRestrictAdj.{u, r} φ U)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)).symm
    (TwoSquare.mk _ _ _ _
      (etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso.{u, r} φ j).inv)).natTrans

/-- The comparison of the unbounded derived direct image with derived extension of coefficients,
`Rg_*(E) ⊗^L_{Λ₁} Λ₂ ⟶ Rg_*(E ⊗^L_{Λ₁} Λ₂)`: the mate of the square of the derived direct
image and restriction of coefficients. -/
def derivedDirectImageUnboundedExtendScalarsMap {X Y : Scheme.{u}} (g : X ⟶ Y) :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₁ g ⋙
        etaleModuleDerivedExtendScalars.{u, r} φ Y ⟶
      etaleModuleDerivedExtendScalars.{u, r} φ X ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ g :=
  ((mateEquiv (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y)).symm
    (TwoSquare.mk _ _ _ _
      (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ g).inv)).natTrans

/-- The comparison for `Rf_! = R(f̄)_* ∘ Rj_!` is the comparison for `R(f̄)_*` at `Rj_!(E)`
followed by `R(f̄)_*` of the comparison for `Rj_!`: mates are compatible with pasting squares. -/
theorem derivedLowerShriekUnboundedExtendScalarsMap_app
    (E : DerivedCategory (EtaleModules.{u, r} Λ₁ X)) :
    (derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j).app E =
      (derivedDirectImageUnboundedExtendScalarsMap.{u, r} φ j.toBase).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j.immersion).obj E) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ₂ j.toBase).map
          ((derivedExtensionByZeroUnboundedExtendScalarsMap.{u, r} φ j.immersion).app E) := by
  have h := mateEquiv_vcomp (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ j.space)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y)
    ((mateEquiv (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)
      (etaleModuleDerivedExtendRestrictAdj.{u, r} φ j.space)).symm
      (TwoSquare.mk _ _ _ _
        (etaleModuleDerivedExtensionByZeroUnboundedRestrictScalarsIso.{u, r} φ j.immersion).inv))
    ((mateEquiv (etaleModuleDerivedExtendRestrictAdj.{u, r} φ j.space)
      (etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y)).symm
      (TwoSquare.mk _ _ _ _
        (etaleModuleDerivedDirectImageUnboundedRestrictScalarsIso.{u, r} φ j.toBase).inv))
  simp only [Equiv.apply_symm_apply] at h
  have h' := congrArg (fun w => ((mateEquiv (etaleModuleDerivedExtendRestrictAdj.{u, r} φ X)
    (etaleModuleDerivedExtendRestrictAdj.{u, r} φ Y)).symm w).natTrans.app E) h
  simp only [Equiv.symm_apply_apply] at h'
  refine Eq.trans ?_ (h'.symm.trans ?_)
  · dsimp only [derivedLowerShriekUnboundedExtendScalarsMap]
    congr 3
    ext K
    simp [derivedLowerShriekUnboundedRestrictScalarsIso, TwoSquare.vComp]
  · simp [TwoSquare.hComp, derivedDirectImageUnboundedExtendScalarsMap,
      derivedExtensionByZeroUnboundedExtendScalarsMap]

/-- The comparison for `Rf_!` is invertible as soon as the comparisons for `Rj_!` and for
`R(f̄)_*` are. -/
theorem isIso_derivedLowerShriekUnboundedExtendScalarsMap_app_of_isIso
    (E : DerivedCategory (EtaleModules.{u, r} Λ₁ X))
    (hj : IsIso ((derivedExtensionByZeroUnboundedExtendScalarsMap.{u, r} φ j.immersion).app E))
    (hf : IsIso ((derivedDirectImageUnboundedExtendScalarsMap.{u, r} φ j.toBase).app
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, r} Λ₁ j.immersion).obj E))) :
    IsIso ((derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j).app E) := by
  rw [derivedLowerShriekUnboundedExtendScalarsMap_app]
  infer_instance

/-- Restriction of coefficients reflects isomorphisms of the unbounded derived category: it is
faithful and exact. -/
theorem isIso_of_isIso_etaleModuleDerivedRestrictScalars_map (Z : Scheme.{u})
    {K L : DerivedCategory (EtaleModules.{u, r} Λ₂ Z)} (g : K ⟶ L)
    (hg : IsIso ((etaleModuleDerivedRestrictScalars.{u, r} φ Z).map g)) : IsIso g :=
  Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_map_of_faithful _ g hg

/-- **The comparison of the second diagram of [Stacks, Remark 0GL6] is invertible exactly when
it is after restriction of coefficients.** -/
theorem isIso_derivedLowerShriekUnboundedExtendScalarsMap_app_iff
    (E : DerivedCategory (EtaleModules.{u, r} Λ₁ X)) :
    IsIso ((derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j).app E) ↔
      IsIso ((etaleModuleDerivedRestrictScalars.{u, r} φ Y).map
        ((derivedLowerShriekUnboundedExtendScalarsMap.{u, r} φ f j).app E)) :=
  ⟨fun _ => inferInstance, isIso_of_isIso_etaleModuleDerivedRestrictScalars_map φ Y _⟩

end Stacks.EtaleCohomology

end
