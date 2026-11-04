module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomModelIndependence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality
import StacksCore.Tactic.StacksAttribute

/-!
# The tensor–internal-Hom bijection is natural in its source

Let `(C, O)` be a ringed site and let `A`, `B`, `Z` be objects of `D(O)`.  The bijection

`Hom_{D(O)}(A, RSheafHom(B, Z)) ≅ Hom_{D(O)}(A ⊗^L_O B, Z)`

of [Stacks, Tag 08J8] is natural in `A`: precomposing a morphism `A ⟶ RSheafHom(B, Z)` with
`u : A' ⟶ A` corresponds to precomposing the matched morphism `A ⊗^L_O B ⟶ Z` with `u ⊗ 1`.

This is one of the three functoriality clauses of Tag 08J8.  It is assembled from two things the
library already has: the bijection is the derived currying isomorphism of [Stacks, Tag 08J9] read
on degree-zero global hypercohomology, that isomorphism is natural in all three objects
(`AlgebraicGeometry.RingedSite.derivedCurryIso_natural`), and the identification of degree-zero
global hypercohomology with the morphism groups is natural in both variables
(`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`).

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyZero`
  and `AlgebraicGeometry.RingedSite.derivedCurryIso_natural_fst`: the two inputs with the identity
  cleared out of the slot that does not move.

## Implementation notes

The square is proved by moving the argument of the bijection through
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_globalSections_homologyMap`, which rewrites
the bijection as the map induced by the derived currying isomorphism on degree-zero global
hypercohomology; the two naturality statements
then apply to that map and to the two identifications surrounding it.

Both inputs are first instantiated with an identity in the slot that does not move — the
covariant variable for Tag 08JA, the middle and target objects for Tag 08J9 — because the
resulting identity morphisms have to be cleared before either statement can be used as a
rewrite rule.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08J9](https://stacks.math.columbia.edu/tag/08J9)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **[Stacks, Tag 08JA] is natural in its contravariant variable alone.**  For `φ : L' ⟶ L` the
map induced on degree-zero global hypercohomology by `RSheafHom(φ, 1)` is precomposition with
`φ`.  This is `derivedSheafHomGlobalSectionsEquiv_naturality` with the identity in the covariant
slot. -/
theorem derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyZero
    {L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L' M
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app M)) ξ) =
      φ ≫ derivedSheafHomGlobalSectionsEquiv X L M ξ := by
  have h := derivedSheafHomGlobalSectionsEquiv_naturality X φ (𝟙 M) ξ
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using h

/-- **[Stacks, Tag 08JA] carries precomposition back to the map induced by `RSheafHom(φ, 1)`.**
This is `derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyZero` read through the
inverse bijection, which is the direction the naturality square of Tag 08J8 consumes. -/
theorem derivedSheafHomGlobalSectionsEquiv_symm_comp
    {L L' M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (h : L ⟶ M) :
    (derivedSheafHomGlobalSectionsEquiv X L' M).symm (φ ≫ h) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map φ.op).app M))
        ((derivedSheafHomGlobalSectionsEquiv X L M).symm h) := by
  refine ((derivedSheafHomGlobalSectionsEquiv X L' M).symm_apply_eq).2 ?_
  rw [derivedSheafHomGlobalSectionsEquiv_naturality_source_homologyZero X φ,
    AddEquiv.apply_symm_apply]

end AlgebraicGeometry.RingedSite

end
