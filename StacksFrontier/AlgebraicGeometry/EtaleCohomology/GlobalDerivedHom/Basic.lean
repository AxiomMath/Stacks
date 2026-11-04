module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalDerivedHom.Leray

/-!
# The global derived hom on `D(X_étale, Λ)`

Let `X` be a scheme and `Λ` a commutative ring. For `K`, `L` in the unbounded derived category
`D(X_étale, Λ)` the construction of [Stacks, Tag 0B6E] gives the *global derived hom*

`RHom_X(K, L) = RΓ(X, RHom_Λ(K, L))`,

the derived global sections of the derived internal Hom, an object of `D(Λ)`.

For a morphism `f : X ⟶ Y`, the Leray isomorphism
(`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnboundedLerayIso`) rewrites it as
`RΓ(Y, Rf_*RHom_Λ(K, L))`; this is the first step of the proof of [Stacks, Tag 0GLD].

## Main definitions

* `Stacks.EtaleCohomology.etaleGlobalDerivedHom`: the bifunctor `RHom_X(-, -)` on
  `D(X_étale, Λ)` with values in `D(Λ)`.
* `Stacks.EtaleCohomology.etaleGlobalDerivedHomLerayIso`: `RHom_X(K, L) ≅ RΓ(Y, Rf_*RHom_Λ(K, L))`.

## Implementation notes

`RHom_Λ(-, -)` is `Stacks.EtaleCohomology.etaleDerivedHom`, the derived internal Hom of the
constant ringed site `(X_étale, Λ̲)` read on `D(X_étale, Λ)`, and `RΓ(X, -)` is
`Stacks.EtaleCohomology.etaleModuleDerivedGlobalSectionsUnbounded`, the total right derived
functor of global sections on the whole unbounded derived category. The source places
`RHom_X(K, L)` in `D(Γ(X, Λ̲))`; it is read here in `D(Λ)` through `Λ ⟶ Γ(X, Λ̲)`, which is the
reading in which the two sides of [Stacks, Tag 0GLD], living over `X` and over `Y`, are compared.

## References

* [Stacks Project, Tag 0B6E](https://stacks.math.columbia.edu/tag/0B6E)
* [Stacks Project, Tag 0GLD](https://stacks.math.columbia.edu/tag/0GLD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

/-- **The global derived hom `RHom_X(K, L) = RΓ(X, RHom_Λ(K, L))` on `D(X_étale, Λ)`**, the
construction of [Stacks, Tag 0B6E]: the derived internal Hom followed by the unbounded derived
global sections, with values in `D(Λ)`. -/
def etaleGlobalDerivedHom (X : Scheme.{u}) :
    (DerivedCategory (EtaleModules.{u, r} Λ X))ᵒᵖ ⥤ DerivedCategory (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory (ModuleCat.{max (u + 1) r} Λ) :=
  etaleDerivedHom.{u, r} Λ X ⋙
    (Functor.whiskeringRight _ _ _).obj (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X)

/-- The global derived hom `RHom_X(K, L)` is `RΓ(X, RHom_Λ(K, L))`. -/
theorem etaleGlobalDerivedHom_obj_obj (X : Scheme.{u})
    (K L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ((etaleGlobalDerivedHom.{u, r} Λ X).obj (op K)).obj L =
      (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ X).obj
        (((etaleDerivedHom.{u, r} Λ X).obj (op K)).obj L) :=
  rfl

/-- **Leray for the global derived hom**: `RHom_X(K, L) ≅ RΓ(Y, Rf_*RHom_Λ(K, L))` for a
morphism `f : X ⟶ Y`. -/
def etaleGlobalDerivedHomLerayIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K L : DerivedCategory (EtaleModules.{u, r} Λ X)) :
    ((etaleGlobalDerivedHom.{u, r} Λ X).obj (op K)).obj L ≅
      (etaleModuleDerivedGlobalSectionsUnbounded.{u, r} Λ Y).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, r} Λ f).obj
          (((etaleDerivedHom.{u, r} Λ X).obj (op K)).obj L)) :=
  (etaleModuleDerivedGlobalSectionsUnboundedLerayIso.{u, r} Λ f).app _

end Stacks.EtaleCohomology

end
