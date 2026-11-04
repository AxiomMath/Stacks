module

public import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion

/-!
# Quasi-coherent modules on an affine scheme from their global sections

On a scheme satisfying `AlgebraicGeometry.IsAffine` the global-sections functor
`AlgebraicGeometry.moduleGlobalSections` is full on quasi-coherent modules and reflects
invertibility, so two quasi-coherent modules whose modules of global sections are isomorphic over
`Γ(X, ⊤)` are themselves isomorphic.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleLimits.isoOfGlobalSectionsIso`: **an isomorphism of the modules
  of global sections of two quasi-coherent modules on an affine scheme yields an isomorphism of
  the modules themselves.**

## Implementation notes

Fullness, `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`, produces a morphism of
sheaves of modules realising the given linear equivalence on global sections, and the affine
criterion `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top` makes that morphism
invertible.  The two are crossed by
`CategoryTheory.ConcreteCategory.isIso_iff_bijective`: the criterion asks for invertibility of the
morphism on sections, which for a morphism of abelian groups is bijectivity, and bijectivity is
what a linear equivalence supplies.

Nothing is stated about the action of the resulting isomorphism on sections.  Fullness is proved
through a choice, so the morphism realising the equivalence is not canonical; what is canonical is
only the fact that one exists.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-- A morphism of quasi-coherent modules on an affine scheme which acts on global sections as a
linear equivalence is an isomorphism. -/
theorem isIso_of_app_top_eq_linearEquiv {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (w : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(N, ⊤)) (χ : M ⟶ N)
    (hχ : ∀ a : Γ(M, ⊤), χ.app ⊤ a = w.toLinearMap a) : IsIso χ :=
  Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top χ
    ((ConcreteCategory.isIso_iff_bijective _).mpr
      (by
        rw [show (ConcreteCategory.hom (χ.app (⊤ : X.Opens)) : Γ(M, ⊤) → Γ(N, ⊤)) =
            (w.toLinearMap : Γ(M, ⊤) → Γ(N, ⊤)) from funext hχ]
        exact w.bijective))

/-- **Two quasi-coherent modules on an affine scheme whose modules of global sections are
isomorphic are isomorphic.** -/
def isoOfGlobalSectionsIso {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (e : (moduleGlobalSections X).obj M ≅ (moduleGlobalSections X).obj N) : M ≅ N :=
  have hex : ∃ χ : M ⟶ N, ∀ a : Γ(M, ⊤), χ.app ⊤ a = e.toLinearEquiv.toLinearMap a :=
    exists_hom_app_top_eq (X := X) (F := M) (G := N) e.toLinearEquiv.toLinearMap
  haveI : IsIso hex.choose :=
    isIso_of_app_top_eq_linearEquiv e.toLinearEquiv hex.choose hex.choose_spec
  asIso hex.choose

end Stacks.AlgebraicGeometry.ModuleLimits

end
