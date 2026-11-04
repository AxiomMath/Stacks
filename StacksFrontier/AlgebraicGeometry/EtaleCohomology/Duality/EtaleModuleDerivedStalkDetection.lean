module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedStalkConservativity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback

/-!
# Derived stalks at geometric points detect isomorphisms in `D(X_étale, Λ)`

Let `X` be a scheme and `Λ` a commutative ring. A morphism `φ : M ⟶ N` of the derived category of
sheaves of `Λ`-modules on the small étale site of `X` is an isomorphism as soon as the derived
stalk of its underlying morphism of complexes of abelian sheaves is an isomorphism at every
geometric point of `X`
(`Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleDerivedStalk`). Geometric points have
algebraically closed residue fields (`AlgebraicGeometry.GeometricPoint`), so this is the stalk
criterion at algebraically closed points.

The forgetful functor `U` to abelian sheaves is exact and reflects isomorphisms
(`Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleUnderlyingAbelian_map`), so `φ` is an
isomorphism once `U(φ)` is (`CategoryTheory.Functor.isIso_mapDerivedCategory_map_iff`), and
derived stalks detect isomorphisms of `D(X_étale)`
(`Stacks.EtaleCohomology.isIso_of_forall_isIso_smallEtaleDerivedStalkAb`, Tag 03PU).

This is the stalk criterion for the duality morphism `Rf̄_* Λ ⟶ RHom(Rf̄_* Λ, Λ)[-2]` of a smooth
projective curve `f̄ : X̄ ⟶ S`, in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statement consumes the derived stalk `Stacks.EtaleCohomology.smallEtaleDerivedStalkAb`, defined
in the standard model `HasDerivedCategory.standard` of the derived category, as a local instance.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleUnderlyingAbelian_map`.
* `Stacks.EtaleCohomology.isIso_of_forall_isIso_etaleModuleDerivedStalk`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable {X : Scheme.{u}} {Λ : Type} [CommRing Λ]

/-- **The forgetful functor to abelian sheaves reflects isomorphisms**: a morphism of sheaves of
`Λ`-modules whose underlying morphism of abelian sheaves is invertible is invertible. -/
theorem isIso_of_isIso_etaleModuleUnderlyingAbelian_map {F G : EtaleModules.{u, 0} Λ X}
    (g : F ⟶ G) (h : IsIso ((etaleModuleUnderlyingAbelian X Λ).map g)) : IsIso g := by
  have h₁ : ∀ U, IsIso (((sheafToPresheaf _ _).map g).app U) := fun U => by
    have : IsIso ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map (g.hom.app U)) :=
      inferInstanceAs (IsIso (((sheafToPresheaf _ _).map
        ((etaleModuleUnderlyingAbelian X Λ).map g)).app U))
    exact isIso_of_reflects_iso _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  have : IsIso ((sheafToPresheaf _ _).map g) := NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso g (sheafToPresheaf _ _)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **Derived stalks at geometric points detect isomorphisms in `D(X_étale, Λ)`**: a morphism
`φ : M ⟶ N` whose underlying morphism in `D(X_étale)` has an invertible derived stalk at every
geometric point of `X` is an isomorphism. -/
theorem isIso_of_forall_isIso_etaleModuleDerivedStalk
    {M N : DerivedCategory (EtaleModules.{u, 0} Λ X)} (φ : M ⟶ N)
    (h : ∀ x : GeometricPoint X, IsIso ((smallEtaleDerivedStalkAb x.hom).map
      ((etaleModuleUnderlyingAbelian X Λ).mapDerivedCategory.map φ))) :
    IsIso φ := by
  have hU := isIso_of_forall_isIso_smallEtaleDerivedStalkAb _ h
  rw [Functor.isIso_mapDerivedCategory_map_iff] at hU
  rw [DerivedCategory.isIso_iff]
  exact fun n => isIso_of_isIso_etaleModuleUnderlyingAbelian_map _ (hU n)

end Derived

end Stacks.EtaleCohomology

end
