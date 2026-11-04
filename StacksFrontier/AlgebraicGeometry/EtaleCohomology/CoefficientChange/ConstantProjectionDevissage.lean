module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.DerivedConstantSheaf
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimensionDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleHigherDirectImageColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperDirectImageDirectSums
public import StacksFrontier.Homology.Devissage.ModuleShiftsNatTrans

/-!
# The projection formula against constant coefficients, by dévissage

Let `g : X ⟶ Y` be a quasi-compact quasi-separated morphism of schemes whose direct image `g_*`
on sheaves of `Λ`-modules has finite cohomological dimension, and let `E ∈ D(X_étale, Λ)`.  The
two functors of `M ∈ D(Λ)`

* `M ↦ Rg_*E ⊗^L_Λ M̲` and
* `M ↦ Rg_*(E ⊗^L_Λ M̲)`,

where `M ↦ M̲` is the derived constant sheaf functor, are exact and commute with direct sums.
Hence a morphism between them, for instance the projection-formula map of [Stacks, Tag 0F0G] at
constant coefficients, is invertible as soon as it is invertible at every shift `Λ[k]`
([Stacks, Tag 09PB]).  This is how the `R(f̄)_*` half of the second diagram of
[Stacks, Remark 0GL6] avoids proper base change: the coefficient module `Λ₂` is reached from `Λ₁`
by dévissage, and at `Λ₁[k]` the projection formula is the shift of the identity.

## Main results

* `Stacks.EtaleCohomology.preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded`:
  `Rg_*` commutes with direct sums when `g_*` has finite cohomological dimension
  ([Stacks, Tag 0F11] (1), with its input 09Z1 supplied).
* `Stacks.EtaleCohomology.isIso_app_of_isIso_app_shifts_constantSheaf`: the dévissage.

## References

* [Stacks Project, Tag 0F11](https://stacks.math.columbia.edu/tag/0F11)
* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Remark 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/- `Stacks.EtaleCohomology.hasSheafifyEtale` is stated at the coefficient universe `u + 1`;
instance search would try to unify the coefficient universe `max (u + 1) r` with it and fail on
the universe constraint, so it is switched off here. -/
attribute [-instance] Stacks.EtaleCohomology.hasSheafifyEtale

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- **The unbounded derived direct image commutes with direct sums** along a quasi-compact
quasi-separated morphism whose direct image has finite cohomological dimension: [Stacks, Tag 0F11]
(1), with each `R^q g_*` commuting with direct sums by
`preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ`. -/
theorem preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded
    [QuasiCompact g] [QuasiSeparated g]
    (hcd : ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ g).rightDerived q).obj F))
    (I : Type (max (u + 1) r)) :
    PreservesColimitsOfShape (Discrete I) (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g) := by
  have := etaleModules_isGrothendieckAbelian.{u, r} Λ X
  exact preservesColimitsOfShape_of_finiteCohomologicalDimension_directImage Λ g hcd
    (fun q I ↦ preservesColimitsOfShape_discrete_rightDerived_etaleModuleDirectImage_univ Λ g q I)
    (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g)
    (Stacks.Injectives.KInjectiveResolution.homotopyCategoryUnit
      (etaleModuleDirectImage.{u, r} Λ g) _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ g))
    I

/-- **The projection formula at constant coefficients, by dévissage.**  Let `g` be
quasi-compact and quasi-separated with `g_*` of finite cohomological dimension, and
`E ∈ D(X_étale, Λ)`.  A morphism from `M ↦ Rg_*E ⊗^L_Λ M̲` to `M ↦ Rg_*(E ⊗^L_Λ M̲)` which is
invertible at every shift of `Λ` is invertible at every `M ∈ D(Λ)`: both functors are exact and
commute with direct sums ([Stacks, Tag 09PB]). -/
theorem isIso_app_of_isIso_app_shifts_constantSheaf [QuasiCompact g] [QuasiSeparated g]
    (hcd : ∃ d : ℕ, ∀ q : ℕ, d ≤ q → ∀ F : EtaleModules.{u, r} Λ X,
      IsZero (((etaleModuleDirectImage.{u, r} Λ g).rightDerived q).obj F))
    (E : DerivedCategory (EtaleModules.{u, r} Λ X))
    (Φ : etaleModuleDerivedConstantSheaf.{u, r} Λ Y ⋙ (etaleModuleDerivedTensor.{u, r} Λ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).obj E) ⟶
      etaleModuleDerivedConstantSheaf.{u, r} Λ X ⋙ (etaleModuleDerivedTensor.{u, r} Λ X).obj E ⋙
        etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g)
    (hΦ : ∀ k : ℤ, IsIso (Φ.app (((DerivedCategory.singleFunctor
      (ModuleCat.{max (u + 1) r} Λ) 0).obj (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ)))⟦k⟧)))
    (M : DerivedCategory (ModuleCat.{max (u + 1) r} Λ)) : IsIso (Φ.app M) := by
  obtain ⟨sY, hY⟩ := CochainComplex.KFlatBifunctor.derivedBifunctor_exact_right
    (etaleModuleTensor.{u, r} Λ Y) ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g).obj E)
  obtain ⟨sX, hX⟩ := CochainComplex.KFlatBifunctor.derivedBifunctor_exact_right
    (etaleModuleTensor.{u, r} Λ X) E
  let := sY
  let := sX
  let := etaleModuleDerivedDirectImageUnboundedCommShift.{u, r} Λ g
  have := etaleModuleDerivedDirectImageUnbounded_isTriangulated.{u, r} Λ g
  have := preservesColimitsOfShape_etaleModuleDerivedDirectImageUnbounded Λ g hcd
  exact StacksDraft.NatTransDevissage.isIso_app_of_isIso_app_shifts_regular _ _ inferInstance
    inferInstance inferInstance inferInstance (fun I ↦ comp_preservesColimitsOfShape _ _)
    (fun I ↦ by
      have := comp_preservesColimitsOfShape (J := Discrete I)
        ((etaleModuleDerivedTensor.{u, r} Λ X).obj E)
        (etaleModuleDerivedDirectImageUnbounded.{u, r} Λ g)
      exact comp_preservesColimitsOfShape _ _) Φ hΦ M

end Stacks.EtaleCohomology

end
