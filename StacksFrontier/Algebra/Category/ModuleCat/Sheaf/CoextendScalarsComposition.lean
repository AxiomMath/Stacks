module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsCoextension

/-!
# Coextension of scalars composes

Let `φ : O ⟶ O'` and `ψ : O' ⟶ O''` be morphisms of sheaves of rings on a site. Coextension of
scalars `F ↦ SheafHom_O(O', F)` of Stacks Tag 0932 turns the composite `φ ≫ ψ` into the
composite of the two coextensions:

`SheafHom_O(O'', H) = SheafHom_{O'}(O'', SheafHom_O(O', H))`.

Restriction of scalars along a composite *is* the composite of the restrictions — the two
functors are equal, not merely isomorphic — so the two readings are right adjoints of one and
the same functor, and the identification is the uniqueness of a right adjoint. In particular
coextension along `𝟙` is the identity functor, and coextension along an isomorphism of sheaves
of rings is an equivalence of the categories of modules: the transport of a module along that
identification of the structure sheaves.

## Main definitions

* `Stacks.SheafOfModules.CoextendScalars.sheafCoextendScalarsCompIso`: **coextension along a
  composite is the composite of the coextensions.**
* `Stacks.SheafOfModules.CoextendScalars.sheafCoextendScalarsIdIso`: coextension along the
  identity is the identity functor.
* `Stacks.SheafOfModules.CoextendScalars.sheafCoextendScalarsEquivalence`: coextension along an
  isomorphism of sheaves of rings, as an equivalence of categories of sheaves of modules.

## Implementation notes

Both isomorphisms of functors are derived from adjunctions rather than written out on
components: a component of either would be an isomorphism of internal Hom sheaves, whose
naturality in the module is exactly what `CategoryTheory.Adjunction.rightAdjointUniq` provides
for free from the two adjunctions of Tag 0932.

The equivalence attached to an isomorphism `e` of sheaves of rings is assembled with
`CategoryTheory.Equivalence.mk`, which repairs the coherence between the unit and the counit on
its own; the two isomorphisms handed to it are the composition law at `e.hom ≫ e.inv` and at
`e.inv ≫ e.hom`.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.SheafOfModules.CoextendScalars

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O O' O'' : Sheaf J RingCat.{u}}

/-- Restriction of scalars along a composite of morphisms of sheaves of rings is the composite
of the restrictions of scalars, as an equality of functors. -/
theorem restrictScalars_comp (φ : O ⟶ O') (ψ : O' ⟶ O'') :
    SheafOfModules.restrictScalars.{u} ψ ⋙ SheafOfModules.restrictScalars.{u} φ =
      SheafOfModules.restrictScalars.{u} (φ ≫ ψ) :=
  rfl

/-- Restriction of scalars along the identity is the identity functor. -/
theorem restrictScalars_id : SheafOfModules.restrictScalars.{u} (𝟙 O) = 𝟭 _ := rfl

/-- **Coextension of scalars composes.** For morphisms `φ : O ⟶ O'` and `ψ : O' ⟶ O''` of
sheaves of rings on a site, `SheafHom_O(O'', -)` is `SheafHom_{O'}(O'', SheafHom_O(O', -))`.
Both are right adjoint to restriction of scalars along `φ ≫ ψ`, which is the composite of the
two restrictions of scalars. -/
def sheafCoextendScalarsCompIso (φ : O ⟶ O') (ψ : O' ⟶ O'') :
    coextendScalars.{u} (φ ≫ ψ) ≅
      coextendScalars.{u} φ ⋙ coextendScalars.{u} ψ :=
  Adjunction.rightAdjointUniq (restrictScalars_coextendScalars_adjunction (φ ≫ ψ))
    ((restrictScalars_coextendScalars_adjunction ψ).comp
      (restrictScalars_coextendScalars_adjunction φ))

/-- Coextension of scalars along the identity of a sheaf of rings is the identity functor:
`SheafHom_O(O, H) = H`. -/
def sheafCoextendScalarsIdIso (O : Sheaf J RingCat.{u}) :
    coextendScalars.{u} (𝟙 O) ≅ 𝟭 (SheafOfModules.{u} O) :=
  Adjunction.rightAdjointUniq (restrictScalars_coextendScalars_adjunction (𝟙 O)) Adjunction.id

/-- Coextension of scalars along an isomorphism `e` of sheaves of rings is an equivalence of the
categories of sheaves of modules, with inverse the coextension along `e.inv`. It is the
transport of a sheaf of modules along the identification `e` of the two sheaves of rings. -/
def sheafCoextendScalarsEquivalence (e : O ≅ O') :
    SheafOfModules.{u} O ≌ SheafOfModules.{u} O' :=
  CategoryTheory.Equivalence.mk (coextendScalars.{u} e.hom) (coextendScalars.{u} e.inv)
    ((sheafCoextendScalarsIdIso O).symm ≪≫
      eqToIso (congrArg coextendScalars.{u} e.hom_inv_id).symm ≪≫
      sheafCoextendScalarsCompIso e.hom e.inv)
    ((sheafCoextendScalarsCompIso e.inv e.hom).symm ≪≫
      eqToIso (congrArg coextendScalars.{u} e.inv_hom_id) ≪≫
      sheafCoextendScalarsIdIso O')

end Stacks.SheafOfModules.CoextendScalars

end
