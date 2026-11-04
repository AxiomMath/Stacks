module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison

/-!
# Normalising the scalar map of the associated-sheaf functor

For a ringed space `X` and a ring map `α : R → Γ(X, 𝒪_X)`, the functor of Stacks 01BH,
construction (3), which sends an `R`-module `M` to the sheafification of `U ↦ 𝒪_X(U) ⊗_R M`,
factors as extension of scalars along `α` followed by the same construction for the identity map
of `Γ(X, 𝒪_X)`. Both that functor and its right adjoint are additive.

## Main definitions

* `Stacks.AssociatedSheaf.globalSectionsFunctorIsoRestrictScalars`:
  `Γ(X, -) with scalars along the identity, then restricted along α ≅ Γ(X, -) with scalars
  along α`.
* `Stacks.AssociatedSheaf.associatedSheafFunctorIsoExtendScalars`:
  `(-)^~_α ≅ (Γ(X, 𝒪_X) ⊗_R -) ⋙ (-)^~_{id}`.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace Stacks.AssociatedSheaf

universe u

variable {X : RingedSpace.{u, u}} {R : Type u} [CommRing R]
  (α : R →+* X.presheaf.obj (op ⊤))

/-- Global sections with scalars restricted along `α` is additive. -/
instance globalSectionsFunctor_additive : (globalSectionsFunctor.{u, u} X α).Additive where
  map_add := rfl

/-- The associated-sheaf functor is additive. -/
instance associatedSheafFunctor_additive : (associatedSheafFunctor.{u, u} X α).Additive :=
  (associatedSheafAdjunction.{u, u} X α).left_adjoint_additive

/-- Global sections with scalars along the identity of `Γ(X, 𝒪_X)`, then restricted along `α`,
is global sections with scalars along `α`. -/
def globalSectionsFunctorIsoRestrictScalars :
    globalSectionsFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤))) ⋙
        ModuleCat.restrictScalars α ≅
      globalSectionsFunctor.{u, u} X α := by
  refine NatIso.ofComponents (fun F => ?_) ?_
  · dsimp only [globalSectionsFunctor,
      Stacks.PresheafOfModules.ChangeOfRings.restrictScalars, PresheafOfModules.restrictScalars,
      PresheafOfModules.restrictScalarsObj, PresheafOfModules.evaluation, Functor.comp]
    exact (ModuleCat.restrictScalars α).mapIso
        (ModuleCat.restrictScalarsId'App _ (by ext; simp [globalSectionsMap]; rfl) _) ≪≫
      ((ModuleCat.restrictScalarsCongr (by ext; simp [globalSectionsMap]; rfl)).app _).symm
  · intro F G h
    ext x
    rfl

/-- **The scalar map of the associated-sheaf functor normalises to the identity.** The sheaf
associated to an `R`-module along `α : R → Γ(X, 𝒪_X)` is the sheaf associated along the identity
of `Γ(X, 𝒪_X)` to the module obtained by extension of scalars along `α`. -/
def associatedSheafFunctorIsoExtendScalars :
    associatedSheafFunctor.{u, u} X α ≅
      ModuleCat.extendScalars α ⋙
        associatedSheafFunctor.{u, u} X (RingHom.id (X.presheaf.obj (op ⊤))) :=
  Adjunction.leftAdjointUniq (associatedSheafAdjunction.{u, u} X α)
    (((ModuleCat.extendRestrictScalarsAdj α).comp
      (associatedSheafAdjunction.{u, u} X
        (RingHom.id (X.presheaf.obj (op ⊤))))).ofNatIsoRight
      (globalSectionsFunctorIsoRestrictScalars α))

end Stacks.AssociatedSheaf

end
