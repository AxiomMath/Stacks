module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiModelSiteHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ZariskiSitePresentedPullback
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite

/-!
# Pullback of modules across the equi-universe model of the total Zariski site

`AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom` is the morphism of ringed sites between
the equi-universe models of the total Zariski sites of two simplicial schemes attached to a
morphism `f : V ⟶ U`, and `AlgebraicGeometry.SimplicialScheme.zariskiModulesEquivModelModules`
identifies the sheaves of `𝒪_X`-modules on the total Zariski site with the sheaves of modules on
the model. This file proves that the two pullbacks agree under those identifications:

`model(f)^* ≅ e_U⁻¹ ⋙ f^* ⋙ e_V`.

It is the last of the four steps that Stacks 07TI in general needs, and it is where the choice
of the structure map of `zariskiModelSiteHom` pays for itself. Both sides are left adjoints, so
it suffices to identify the two *pushforwards*, and the pushforward of a morphism of ringed
sites, read in its site presentation, is Mathlib's `SheafOfModules.pushforward`; so is each half
of the model equivalence of sheaves of modules, which is a reindexing. Mathlib's
`SheafOfModules.pushforwardComp` is the identity isomorphism, so a composite of pushforwards is
the pushforward of the composite *on the nose*, and the right-hand composite

`e_V⁻¹ ⋙ f_* ⋙ e_U`

is the pushforward along `e_U ⋙ f⁻¹ ⋙ e_V⁻¹`, which is exactly the functor of
`zariskiModelSiteHom`, with exactly its structure map. The two pushforwards are therefore
*equal*, not merely isomorphic, and that equality is
`AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom_pushforwardTopos_eq`.

## Main definitions

* `AlgebraicGeometry.SimplicialScheme.zariskiModelPullbackIso`: **the pullback along the
  morphism of the equi-universe models is the pullback along `f` conjugated by the two model
  equivalences of sheaves of modules.**
* `AlgebraicGeometry.SimplicialScheme.zariskiModelPullbackObjIso`: the same comparison in the
  form a single module needs it, with the unit of the model equivalence absorbed.

## Main results

* `AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom_pushforwardTopos_eq`: the pushforward
  along the morphism of the models *is* the conjugate of the pushforward along `f`.

## Implementation notes

The equality of pushforwards is a large definitional unfolding, so it is stated once, as its own
declaration, and then used through `CategoryTheory.eqToIso`: asking
`CategoryTheory.Adjunction.leftAdjointUniq` to see it as part of a larger unification exhausts
the heartbeat budget, and asking it twice does so even when the composite of adjunctions is
bracketed to match. The adjunctions are composed as `(e_U⁻¹ ∘ f) ∘ e_V` precisely so that the
resulting right adjoint is bracketed as `e_V⁻¹ ⋙ (f_* ⋙ e_U)`, which is the right-hand side of
the equality as stated.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 07TI](https://stacks.math.columbia.edu/tag/07TI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SimplicialScheme

variable {V U : SimplicialObject Scheme.{u}}

/-- **The pushforward along the morphism of the equi-universe models is the conjugate, by the
two model equivalences of sheaves of modules, of the pushforward along `f`.** Both sides are
Mathlib's `SheafOfModules.pushforward` along `e_U ⋙ f⁻¹ ⋙ e_V⁻¹` with the same structure map:
a composite of pushforwards is the pushforward of the composite on the nose, and the structure
map of `AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom` was chosen to be the composite
that arises. -/
public theorem zariskiModelSiteHom_pushforwardTopos_eq (f : V ⟶ U) :
    (zariskiModelSiteHom f).toRingedToposSiteHom.pushforwardTopos =
      (zariskiModulesEquivModelModules V).inverse ⋙
        (zariskiRingedToposSiteHom f).pushforwardTopos ⋙
          (zariskiModulesEquivModelModules U).functor :=
  rfl

/-- **Pullback of sheaves of modules commutes with the passage to the equi-universe model.**
The pullback along `AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom` is the pullback `f^*`
of `AlgebraicGeometry.SimplicialScheme.modulePullback` conjugated by the two model equivalences
of sheaves of modules.

Both sides are left adjoints — on the right of the composite of three adjunctions, the model
equivalence of `U` taken backwards, the pullback along `f`, and the model equivalence of `V` —
and the two right adjoints are equal by
`AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom_pushforwardTopos_eq`, so this is
uniqueness of left adjoints. -/
public def zariskiModelPullbackIso (f : V ⟶ U) :
    (zariskiModelSiteHom f).toRingedToposSiteHom.pullbackTopos ≅
      ((zariskiModulesEquivModelModules U).inverse ⋙
        (zariskiRingedToposSiteHom f).pullbackToposGeneral) ⋙
          (zariskiModulesEquivModelModules V).functor :=
  Adjunction.leftAdjointUniq
    (zariskiModelSiteHom f).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos
    (Adjunction.ofNatIsoRight
      ((((zariskiModulesEquivModelModules U).symm.toAdjunction).comp
        ((zariskiRingedToposSiteHom f).pullbackPushforwardAdjunctionToposGeneral)).comp
          (zariskiModulesEquivModelModules V).toAdjunction)
      (eqToIso (zariskiModelSiteHom_pushforwardTopos_eq f).symm))

/-- **Pullback of sheaves of modules commutes with the passage to the equi-universe model, at
one module.** The pullback along
`AlgebraicGeometry.SimplicialScheme.zariskiModelSiteHom` of the transport of a sheaf of
`𝒪_U`-modules to the model is the transport of its pullback `f^*F` to the model.

This is `AlgebraicGeometry.SimplicialScheme.zariskiModelPullbackIso` with the unit of the model
equivalence of `U` used to remove the round trip `e_U⁻¹ e_U F`, and with
`AlgebraicGeometry.SimplicialScheme.modulePullbackToposGeneralIso` used to return from the
site-presented pullback to `AlgebraicGeometry.SimplicialScheme.modulePullback`. -/
public def zariskiModelPullbackObjIso (f : V ⟶ U) (F : Modules U) :
    (zariskiModelSiteHom f).toRingedToposSiteHom.pullbackTopos.obj
        ((zariskiModulesEquivModelModules U).functor.obj F) ≅
      (zariskiModulesEquivModelModules V).functor.obj ((modulePullback f).obj F) :=
  (zariskiModelPullbackIso f).app ((zariskiModulesEquivModelModules U).functor.obj F) ≪≫
    (zariskiModulesEquivModelModules V).functor.mapIso
      ((zariskiRingedToposSiteHom f).pullbackToposGeneral.mapIso
          ((zariskiModulesEquivModelModules U).unitIso.app F).symm ≪≫
        ((modulePullbackToposGeneralIso f).app F).symm)

end AlgebraicGeometry.SimplicialScheme

end
