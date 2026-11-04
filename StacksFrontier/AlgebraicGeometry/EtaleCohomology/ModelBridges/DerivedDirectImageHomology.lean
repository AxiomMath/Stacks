module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ForgetEtaleModuleStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Higher direct images of étale sheaves of modules and of their underlying abelian sheaves

Let `Λ` be a ring and `f : X ⟶ Y` a morphism of schemes. For an object `K` of the unbounded
derived category `D(X_étale, Λ)` of sheaves of `Λ`-modules on Mathlib's small étale site
(`Stacks.EtaleCohomology.EtaleModules`), the underlying abelian sheaf of the cohomology sheaf
`H^q(Rf_* K)` is the cohomology sheaf `H^q(Rf_* K_ab)` of the derived direct image of abelian
sheaves of the underlying complex `K_ab`, naturally in `K`.

This combines the commutation of `Rf_*` with forgetting the module structure
(`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageForgetIsoUnconditional`, [Stacks, Tag 0D6J]
part (3)) with the commutation of the exact forgetful functor with cohomology sheaves
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`).

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetHomologyDerivedDirectImageIso` — the natural
  isomorphism `H^q(Rf_* K)_ab ≅ H^q(Rf_* K_ab)`.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **Forgetting the module structure commutes with higher direct images.** For a morphism of
schemes `f : X ⟶ Y`, an object `K` of `D(X_étale, Λ)` and an integer `q`, the underlying abelian
sheaf of `H^q(Rf_* K)` is `H^q(Rf_* K_ab)`, naturally in `K`. -/
def etaleModuleForgetHomologyDerivedDirectImageIso (q : ℤ) :
    etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f ⋙
        DerivedCategory.homologyFunctor (EtaleModules.{u, r} Λ Y) q ⋙
          etaleModuleForgetAb.{u, r} Λ Y ≅
      etaleModuleForgetDerived.{u, r} Λ X ⋙ etaleAbelianDerivedDirectImage.{u, r} f ⋙
        DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) q :=
  Functor.isoWhiskerLeft _
      ((etaleModuleForgetAb.{u, r} Λ Y).mapDerivedCategoryHomologyIso q).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (etaleModuleDerivedDirectImageForgetIsoUnconditional.{u, r} Λ f) _ ≪≫
    Functor.associator _ _ _

end Stacks.EtaleCohomology

end
