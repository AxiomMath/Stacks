module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural

/-!
# The Galois action on `RΓ_c(X_k̄, K)` is natural in `K`

The action of `σ ∈ Aut_k(k̄)` on `RΓ(Y_k̄, C|_{Y_k̄})`
(`Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo`) commutes with the maps induced by
morphisms of complexes `C ⟶ C'`, and so does the action on `RΓ_c(X_k̄, K)` and on `H^i_c(X_k̄, K)`.

## Main results

* `Stacks.EtaleCohomology.galoisRestrictionCohomologyEndo_naturality`.
* `Stacks.EtaleCohomology.galoisCompactSupportAction_naturality`.
* `Stacks.EtaleCohomology.galoisCompactSupportGroupAction_naturality`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Twist

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The twist of complexes is natural.** -/
theorem selfMapComplexTwist_naturality {S T : Scheme.{u}} (f : T ⟶ S) (φ : T ⟶ T) (w : φ ≫ f = f)
    {C C' : CochainComplex.Plus (EtaleModules.{u, r} Λ S)} (ψ : C ⟶ C') :
    selfMapComplexTwist.{u, r} Λ f φ w C ≫
        (etaleModuleDirectImage.{u, r} Λ φ).mapCochainComplexPlus.map
          ((etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.map ψ) =
      (etaleModuleInverseImage.{u, r} Λ f).mapCochainComplexPlus.map ψ ≫
        selfMapComplexTwist.{u, r} Λ f φ w C' := by
  ext : 1
  exact ((NatTrans.mapHomologicalComplex (selfMapTwist.{u, r} Λ f φ w)
    (ComplexShape.up ℤ)).naturality ψ.hom).symm

/-- **The canonical morphism `C|_{Y_k̄} ⟶ R(s_σ)_*(C|_{Y_k̄})` is natural in `C`.** -/
theorem galoisRestrictionDerivedMap_naturality
    {C C' : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)} (ψ : C ⟶ C') :
    galoisRestrictionDerivedMap.{u, r} Λ Y kbar σ C ≫
        (etaleModuleDerivedDirectImage.{u, r} Λ (galoisBaseChange Y kbar σ)).map
          (DerivedCategory.Plus.Q.map
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map ψ)) =
      DerivedCategory.Plus.Q.map
          ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
            ψ) ≫
        galoisRestrictionDerivedMap.{u, r} Λ Y kbar σ C' := by
  have h1 := (Functor.mapCochainComplexPlusDerivedUnit
    (etaleModuleDirectImage.{u, r} Λ (galoisBaseChange Y kbar σ))).naturality
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map ψ)
  have h2 := congrArg DerivedCategory.Plus.Q.map (selfMapComplexTwist_naturality Λ
    (fieldBaseChangeProj Y kbar) (galoisBaseChange Y kbar σ) (galoisBaseChange_comp_fst Y kbar σ) ψ)
  simp only [Functor.map_comp] at h2
  simp only [Functor.comp_map] at h1
  rw [galoisRestrictionDerivedMap, galoisRestrictionDerivedMap, Category.assoc, ← h1,
    ← Category.assoc, ← Category.assoc, h2]

/-- **The action of `σ` on `RΓ(Y_k̄, C|_{Y_k̄})` is natural in `C`.** -/
theorem galoisRestrictionCohomologyEndo_naturality
    {C C' : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)} (ψ : C ⟶ C') :
    galoisRestrictionCohomologyEndo.{u, r} Λ Y kbar σ C ≫
        (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
          (DerivedCategory.Plus.Q.map
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map ψ)) =
      (etaleModuleDerivedGlobalSections.{u, r} Λ (fieldBaseChange Y kbar)).map
          (DerivedCategory.Plus.Q.map
            ((etaleModuleInverseImage.{u, r} Λ
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map ψ)) ≫
        galoisRestrictionCohomologyEndo.{u, r} Λ Y kbar σ C' := by
  have h3 := (etaleModuleDerivedGlobalSectionsCompIso.{u, r} Λ
      (galoisBaseChange Y kbar σ)).inv.naturality
    (DerivedCategory.Plus.Q.map
      ((etaleModuleInverseImage.{u, r} Λ (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map ψ))
  simp only [Functor.comp_map] at h3
  rw [galoisRestrictionCohomologyEndo, galoisRestrictionCohomologyEndo, Category.assoc, ← h3,
    ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
    galoisRestrictionDerivedMap_naturality]

end Twist

section CompactSupport

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] (σ : kbar ≃ₐ[k] kbar)

/-- **The action of `σ` on `RΓ_c(X_k̄, K)` is natural in `K`.** -/
theorem galoisCompactSupportAction_naturality
    {K K' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (φ : K ⟶ K') :
    galoisCompactSupportAction.{u, r} Λ f j kbar σ K ≫
        galoisCompactSupportCohomologyMap.{u, r} Λ f j kbar φ =
      galoisCompactSupportCohomologyMap.{u, r} Λ f j kbar φ ≫
        galoisCompactSupportAction.{u, r} Λ f j kbar σ K' :=
  galoisRestrictionCohomologyEndo_naturality.{u, r} Λ (Over.mk j.toBase) kbar σ
    ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.map φ)

/-- **The action of `σ` on `H^i_c(X_k̄, K)` is natural in `K`.** -/
theorem galoisCompactSupportGroupAction_naturality
    {K K' : CochainComplex.Plus (EtaleModules.{u, r} Λ X)} (φ : K ⟶ K') (i : ℤ) :
    galoisCompactSupportGroupAction.{u, r} Λ f j kbar σ K i ≫
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
          (galoisCompactSupportCohomologyMap.{u, r} Λ f j kbar φ) =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i).map
          (galoisCompactSupportCohomologyMap.{u, r} Λ f j kbar φ) ≫
        galoisCompactSupportGroupAction.{u, r} Λ f j kbar σ K' i := by
  rw [galoisCompactSupportGroupAction, galoisCompactSupportGroupAction, ← Functor.map_comp,
    ← Functor.map_comp, galoisCompactSupportAction_naturality]

end CompactSupport

end Stacks.EtaleCohomology

end
