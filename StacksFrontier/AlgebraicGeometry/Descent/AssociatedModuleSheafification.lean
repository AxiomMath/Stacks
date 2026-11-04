module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor

/-!
# The associated-module functor as a sheafification

The associated-module functor of the big fppf site of `S` is defined as the pullback of sheaves
of modules along the morphism of ringed sites `((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`, that is, as a
left adjoint.  This file records the description of that left adjoint as the sheafification of
the pullback of *presheaves* of modules, and turns it into a criterion: an identification of the
presheaf-level pullback with any other functor into presheaves of modules identifies the
associated-module functor with the sheafification of the latter.

## Main results

* `AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso`: the associated-module
  functor is the sheafification of the pullback of presheaves of modules.
* `AlgebraicGeometry.BigFppfOver.associatedModuleIsoOfPresheafIso`: consequently, a description
  of the presheaf-level pullback yields a description of the associated-module functor as the
  sheafification of that description.

## Implementation notes

Sheafification of presheaves of modules asks the comparison of presheaves of rings to be locally
bijective, and here that comparison is an identity, hence an isomorphism, hence locally
bijective.  Both halves are nonetheless given names below, because instance search finds neither
while the type of `AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso` is being
elaborated: the sheaf of rings is determined there only by unifying it against the projection
`CategoryTheory.Sheaf.obj` of the identity's source, and the generic instance for an isomorphism
is not applied.  Each goal is found by instance search once it is stated on its own, which is
what the second instance records; the locally injective half is proved from injectivity in each
component, where the component is the identity only up to an unfolding, so its proof is `exact`,
which elaborates at default transparency, rather than `simp`.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
-/


@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The identity of the underlying presheaf of rings of the structure sheaf of the big fppf site
is locally injective, being injective in each component. -/
public instance isLocallyInjective_id_structureSheaf :
    Presheaf.IsLocallyInjective (topology B S hS) (𝟙 (structureSheaf B S hS).obj) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h => by exact h

/-- The identity of the underlying presheaf of rings of the structure sheaf of the big fppf site
is locally surjective, being an isomorphism. -/
public instance isLocallySurjective_id_structureSheaf :
    Presheaf.IsLocallySurjective (topology B S hS) (𝟙 (structureSheaf B S hS).obj) :=
  inferInstance

/-- The associated-module functor of the big fppf site of `S` is the sheafification of the
pullback of presheaves of modules along the structure-sheaf comparison.  Both functors are left
adjoint to restriction along the inclusion of the small Zariski site. -/
public noncomputable def associatedModuleSheafificationIso :
    associatedModule B S hS ≅
      SheafOfModules.forget S.ringCatSheaf ⋙
        PresheafOfModules.pullback.{u} (structureMap B S hS).hom ⋙
          PresheafOfModules.sheafification (𝟙 (structureSheaf B S hS).obj) :=
  SheafOfModules.pullbackIso.{u} (structureMap B S hS)

/-- A description of the pullback of presheaves of modules along the structure-sheaf comparison
describes the associated-module functor as the sheafification of that description. -/
public noncomputable def associatedModuleIsoOfPresheafIso
    (G : S.Modules ⥤ PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (e : SheafOfModules.forget S.ringCatSheaf ⋙
      PresheafOfModules.pullback.{u} (structureMap B S hS).hom ≅ G) :
    associatedModule B S hS ≅
      G ⋙ PresheafOfModules.sheafification (𝟙 (structureSheaf B S hS).obj) :=
  associatedModuleSheafificationIso B S hS ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _

end AlgebraicGeometry.BigFppfOver

end
