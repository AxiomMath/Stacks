module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisEquivariantDerivedGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Comparison.DerivedFunctor

/-!
# `RΓ_c(X_k̄, -)` with its Galois action, compared with the base's `RΓ_c(X_k̄, -)`

Let `k` be a field, `k̄` a separable algebraic extension, `X` a scheme over `k` with a
compactification `j : X ⟶ X̄` over `k`, and `Λ` a ring. The Galois-equivariant
`RΓ^Gal_c(X_k̄, K) = RΓ^Gal(X̄_k̄, j_! K)` (`Stacks.EtaleCohomology.galoisDerivedCompactSupport`)
lives in the bounded below derived category of discrete `Λ[Aut_k(k̄)]`-modules. This file shows
that forgetting the action it is the complex
`Stacks.EtaleCohomology.galoisCompactSupportCohomology` of Remark 03UI (2), naturally in the
bounded below complex `K`, and so that its cohomology modules are the base's `H^i_c(X_k̄, K)`.

## Main definitions

* `Stacks.EtaleCohomology.galoisCompactSupportForgetNatIso` — the comparison, as a natural
  isomorphism of functors of `K`.
* `Stacks.EtaleCohomology.galoisCompactSupportForgetIso` — its component at `K`.
* `Stacks.EtaleCohomology.galoisCompactSupportGroupForgetIso` — the underlying module of the
  Galois module `H^i(RΓ^Gal_c(X_k̄, K))` is `H^i_c(X_k̄, K)`.

## Implementation notes

The base's `RΓ_c(X_k̄, -)` is at `CategoryTheory.HasDerivedCategory.standard`, which is therefore
the model used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  Stacks.GroupCohomology.preservesFiniteLimits_continuousModuleToModuleCat
  Stacks.GroupCohomology.preservesFiniteColimits_continuousModuleToModuleCat

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar] [Algebra.IsSeparable k kbar]

/-- **Forgetting the Galois action on `RΓ^Gal_c(X_k̄, -)` gives `RΓ_c(X_k̄, -)`**, naturally in the
bounded below complex: the composite of `K ↦ RΓ^Gal(X̄_k̄, j_! K)` with the forgetful functor to
`D⁺(Λ)` is `K ↦ RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`, the functor of
`Stacks.EtaleCohomology.galoisCompactSupportCohomology`. -/
def galoisCompactSupportForgetNatIso :
    (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ galoisDerivedGlobalSections Λ (Over.mk j.toBase) kbar ⋙
          (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ
            (kbar ≃ₐ[k] kbar)).mapDerivedCategoryPlus ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).mapCochainComplexPlus ⋙
        (etaleModuleInverseImage.{u, 0} Λ
          (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q ⋙
            etaleModuleDerivedGlobalSections.{u, 0} Λ (fieldBaseChange (Over.mk j.toBase) kbar) :=
  Functor.isoWhiskerLeft _
    (Functor.isoWhiskerLeft _ (galoisDerivedGlobalSectionsForgetIso Λ (Over.mk j.toBase) kbar) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryPlusQIso
        (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar))) _ ≪≫
      Functor.associator _ _ _)

/-- **`RΓ^Gal_c(X_k̄, K)`, forgetting the action, is `RΓ_c(X_k̄, K)`** of Remark 03UI (2). -/
def galoisCompactSupportForgetIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k]
        kbar)).mapDerivedCategoryPlus.obj
        (galoisDerivedCompactSupport Λ f j kbar K) ≅
      galoisCompactSupportCohomology.{u, 0} Λ f j kbar K :=
  (galoisCompactSupportForgetNatIso Λ f j kbar).app K

/-- **`H^i_c(X_k̄, K)` as a Galois module**: the underlying `Λ`-module of the `i`-th cohomology
of `RΓ^Gal_c(X_k̄, K)` in discrete `Λ[Aut_k(k̄)]`-modules is the base's
`H^i_c(X_k̄, K) = H^i(RΓ_c(X_k̄, K))`. -/
def galoisCompactSupportGroupForgetIso (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (i : ℤ) :
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λ (kbar ≃ₐ[k] kbar)).obj
        ((DerivedCategory.Plus.homologyFunctor (GaloisModules Λ k kbar) i).obj
          (galoisDerivedCompactSupport Λ f j kbar K)) ≅
      galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar K i :=
  ((Stacks.DerivedFunctor.derivedHomologyIso (Stacks.Injectives.continuousModuleUnderlying.{0, u, u
      + 1}
      Λ (kbar ≃ₐ[k] kbar)) i).app
        (DerivedCategory.Plus.ι.obj (galoisDerivedCompactSupport Λ f j kbar K))).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
      (galoisCompactSupportForgetIso Λ f j kbar K)

end Stacks.EtaleCohomology

end
