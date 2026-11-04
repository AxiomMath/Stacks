module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportDegreeZeroBridge

/-!
# Naturality of the map on `H²_c` induced by a map on `X̄_k̄`

For `ψ : R →+* Λ`, sheaves `F` of `Λ`-modules and `G` of `R`-modules on `X`, and
`θ : res_ψ((j_! F)|_{X̄_k̄}) ⟶ (j_! G)|_{X̄_k̄}`, the map
`H²_c(X_k̄, F) ⟶ H²_c(X_k̄, G)` induced by `θ`
(`Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar`) is natural in both sheaves.

## Main results

* `Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar_map_right`.
* `Stacks.EtaleCohomology.galoisCompactSupportRestrictScalarsMapOfBar_map_left`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.Frobenius

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.EtaleCohomology.etaleModulesEnoughInjectivesZeroTraceTwist
  Stacks.EtaleCohomology.moduleCatHasColimitsOfSizeSmallEtale
  Stacks.EtaleCohomology.hasGlobalSectionsFunctorSmallEtaleModuleCat

namespace Stacks.EtaleCohomology

section Naturality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  {R Λ : Type} [Ring R] [Ring Λ] (ψ : R →+* Λ)

/-- **The map on `H²_c` induced by `θ` is natural in the target**: `H²_c(g)` after it is the map
induced by `θ` followed by `(j_! g)|_{X̄_k̄}`. -/
theorem galoisCompactSupportRestrictScalarsMapOfBar_map_right (F : EtaleModules.{u, 0} Λ X)
    {G G' : EtaleModules.{u, 0} R X} (g : G ⟶ G')
    (θ : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F)) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} R) ((2 : ℕ) : ℤ)).map
        (galoisCompactSupportCohomologyMap R f j kbar
          ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g))).hom
        (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ x) =
      galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G'
        (θ ≫ (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleExtensionByZero.{u, 0} R j.immersion).map g)) x := by
  apply (ModuleCat.mono_iff_injective (galoisCompactSupportSingleIso f j kbar R G'
    ((2 : ℕ) : ℤ)).hom).1 inferInstance
  have hs := congrArg
    (fun φ => φ.hom (galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G θ x))
    (galoisCompactSupportSingleIso_hom_naturality R f j kbar g ((2 : ℕ) : ℤ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  rw [hs, galoisCompactSupportRestrictScalarsMapOfBar_apply,
    galoisCompactSupportRestrictScalarsMapOfBar_apply, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

/-- **The map on `H²_c` induced by `θ'` is natural in the source**: before `H²_c(g)` it is the map
induced by `res_ψ((j_! g)|_{X̄_k̄})` followed by `θ'`. -/
theorem galoisCompactSupportRestrictScalarsMapOfBar_map_left {F F' : EtaleModules.{u, 0} Λ X}
    (g : F ⟶ F') (G : EtaleModules.{u, 0} R X)
    (θ' : (etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F')) ⟶
      (etaleModuleInverseImage.{u, 0} R (pullback.fst j.toBase (specAlgebraMap k kbar))).obj
        ((etaleModuleExtensionByZero.{u, 0} R j.immersion).obj G))
    (x : galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) ((2 : ℕ) : ℤ)) :
    galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F' G θ'
        (((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 : ℕ) : ℤ)).map
          (galoisCompactSupportCohomologyMap Λ f j kbar
            ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map g))).hom x) =
      galoisCompactSupportRestrictScalarsMapOfBar f j kbar ψ F G
        ((etaleModuleRestrictScalars ψ (pullback j.toBase (specAlgebraMap k kbar))).map
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst j.toBase (specAlgebraMap k kbar))).map
            ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map g)) ≫ θ') x := by
  apply (ModuleCat.mono_iff_injective (galoisCompactSupportSingleIso f j kbar R G
    ((2 : ℕ) : ℤ)).hom).1 inferInstance
  have hs := congrArg (fun φ => φ.hom x)
    (galoisCompactSupportSingleIso_hom_naturality Λ f j kbar g ((2 : ℕ) : ℤ))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hs
  rw [galoisCompactSupportRestrictScalarsMapOfBar_apply,
    galoisCompactSupportRestrictScalarsMapOfBar_apply, hs,
    etaleModuleCohomologyRestrictScalars_naturality, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

end Naturality

end Stacks.EtaleCohomology

end
