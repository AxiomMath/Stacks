module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunctionCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModulePushforwardCocontinuous
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaCaseB
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.TransitionRingFsharp
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekExactUnconditional

/-!
# The summand of the componentwise direct sum for modules, case (B)

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `P` be a sheaf of commutative rings on its total site. Stacks 0D72 presents
the restriction to degree `m` of module lower shriek from degree `n` as the direct sum, over the
simplex maps `φ : [n] ⟶ [m]`, of the module pullbacks along the transitions, and this development
carries two readings of that summand, exactly as case (A) does: the one the formula is proved for
(`CategoryTheory.CocontinuousSimplicialSite.transitionModulePullbackB`, built from the
presheaf-level pullback along the transition functor) and the one Stacks 0D74 and Stacks 0D75
consume (`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`, the pullback along
the transition morphism of *ringed topoi*). This file identifies them.

Both are left adjoints, so the comparison is made on the right adjoints. There the direct image
of modules along the transition morphism of ringed topoi is
`Stacks.SheafOfModules.pushforwardCocontinuousModulesIso` for the structure map built here, and
the hypothesis that comparison asks for — that the two scalar maps agree on every leg of the
limit cone computing the Kan extension — is the arithmetic content; the case-(B) summand is
exhibited as a left adjoint of the same direct image, and uniqueness of left adjoints gives the
comparison.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.transitionFunctorB`: the transition functor
  `u_φ : C_m ⥤ C_n` of case (B), named so that its cocontinuity is an instance.
* `CategoryTheory.CocontinuousSimplicialSite.ringTransitionB`: the ring map `O(φ)` of
  Stacks 0D72 in case (B), read at `RingCat`: this is
  `Stacks.Sites.ComponentModuleSumFormula.ringTransition`, which is literal whiskering by
  `CategoryTheory.Grothendieck.ιNatTrans`.
* `CategoryTheory.CocontinuousSimplicialSite.fSharpB`: its direct-image form
  `O_n ⟶ {}_{su_φ} O_m`, the adjunct under the right-Kan-extension adjunction.
* `CategoryTheory.CocontinuousSimplicialSite.transitionPushforwardModulesIsoB`: the comparison of
  the two right adjoints, `{}_{su_φ} ≅ f_{φ*}`.
* `CategoryTheory.CocontinuousSimplicialSite.transitionRingedToposPushforwardModulesIsoB`: that
  comparison carried on to `AlgebraicGeometry.RingedToposHom.pushforwardModules` of the two-field
  transition morphism, across the two readings of it as the four-field datum of the modules
  development.
* `CategoryTheory.CocontinuousSimplicialSite.transitionModulePullbackAdjunctionB`: the case-(B)
  summand is left adjoint to that same direct image.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.hcompatB`: **the two scalar maps agree on every
  leg.** The composite of the unit `O_n ⟶ f_*f^{-1}O_n`, the leg of the limit cone and the
  inverse-image form of the structure map is the composite of `fSharpB` with the leg for `O_m`.
* `CategoryTheory.CocontinuousSimplicialSite.transitionPullbackModulesIsoB`: **the summand
  comparison.** The pullback of sheaves of modules along the transition morphism of ringed topoi
  is the sheafified presheaf-level pullback along the transition functor.
* `CategoryTheory.CocontinuousSimplicialSite.homEquiv_transitionPullbackModulesIsoB_hom_app_comp`:
  **the summand comparison transposes away**, along the Stacks 03D7 adjunction of the two-field
  transition morphism, leaving the transposition along the case-(B) summand's own adjunction
  followed by the comparison of the two right adjoints.

## Implementation notes

The scalar identity is proved leg by leg and elementwise, which is what the comparison it feeds
needs; every step is an instance of a statement that is already available.

Naturality of the leg in the sheaf (`Stacks.SheafOfModules.ranπ_map_functor_apply`) moves the
inverse-image form of the structure map from after the leg to before it, and there the structure
map composed with the unit is the direct-image form, by `CategoryTheory.Adjunction.homEquiv_unit`
for the topos adjunction of the transition. The inverse-image form is the inverse-image transition
of Stacks 09WF (`…ringSheafMap_ringFsharpInverseImage_transition`), whose mate is the direct-image
transition (`…fiberTransition_adj`); and in case (B) that transition *is* the adjunct of the
whiskering by `CategoryTheory.Grothendieck.ιNatTrans` — its definition, read through
`CategoryTheory.SimplicialSiteSituation.restrictTransition`, is literally that adjunct. So both
sides are, on the leg at `(U, ψ)`, restriction along `ψ` followed by restriction along the
cross-fibre arrow `(φ, 𝟙)`, and the final step is `rfl`.

Two places need their implicit arguments supplied by name. The source and target of the
whiskering are passed to `…homEquiv_app_comp_ranπ_apply_type`, because recovering them from the
composite would be a higher-order unification problem that does not terminate inside the
heartbeat budget; and the step through the unit is stated with the direct image of the morphism of
topoi rather than with the right Kan extension it unfolds to, for the same reason.

*Why the comparison of right adjoints is stated with the cocontinuous direct image first.* Its
two sides live over two spellings of the same two topologies: the morphism of ringed topoi spells
them `(componentRingedTopos P k).J` and the morphism of sites spells them `componentTopology k`,
the friction recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ComponentPullbackRestriction.lean`.
The implicit site arguments of `Stacks.SheafOfModules.pushforwardCocontinuous` are read off
`fSharpB`, hence at the second spelling, only if it is elaborated before the expected type has
fixed them; written on the right of the `≅` it inherits the first spelling instead, and the
cocontinuity instance is then sought at a spelling instance search does not match — it cannot
unfold a projection of `componentRingedTopos` to get there.

*Why the summand's adjunction is not
`Stacks.SheafOfModules.RestrictRan.cocontinuousSheafAdjunction`.* That statement presents `O_m`
as the sheafification of the restricted presheaf of rings, so it needs `ringTransitionB` to be
locally bijective for the degree-`m` component topology. It is not:
it is a restriction map of the total structure sheaf along the cross-fibre arrows `(φ, 𝟙)`, an
arbitrary map of sheaves of rings, and already over a one-object component with the trivial
topology local bijectivity would force it to be bijective. So
`CategoryTheory.PresheafOfModules.sheafification` is used at the *identity* structure map, which
is the sheafification the summand is built with anyway, and the change of rings is carried out
before it by extension of scalars along `ringTransitionB`. On the right adjoint that leaves a
restriction of scalars in front of the direct image of presheaves of modules over the unit
structure map, and `Stacks.SheafOfModules.RestrictRan.ranPushforwardRestrictScalarsIso` is what
moves it past the Kan extension, turning it into the direct image over `fSharpB`.

## References

* [Stacks Project, Tag 00XO](https://stacks.math.columbia.edu/tag/00XO)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sites.ComponentModuleSumFormula
open Stacks.SheafOfModules

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

variable (C : CocontinuousSimplicialSite.{u}) {n m : SimplexCategory}
  (P : Sheaf (situation C).totalTopology CommRingCat.{u})

/-- The transition functor `u_φ : C_m ⥤ C_n` of case (B). -/
def transitionFunctorB (φ : n ⟶ m) :
    (situation C).component m ⥤ (situation C).component n :=
  (C.underlying.map φ.op).toFunctor

/-- The transition functor `u_φ` of case (B) is cocontinuous for the component topologies. -/
instance isCocontinuous_transitionFunctorB (φ : n ⟶ m) :
    (transitionFunctorB C φ).IsCocontinuous
      ((situation C).componentTopology m) ((situation C).componentTopology n) :=
  C.isCocontinuous φ.op

/-- The sheaf of rings on the degree-`k` component: the restriction of the total structure sheaf,
read as a sheaf of not necessarily commutative rings. -/
abbrev ringSheafB (k : SimplexCategory) : Sheaf ((situation C).componentTopology k) RingCat.{u} :=
  (situation C).componentRingSheaf
    ((Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)) k

/-- **The ring map `O(φ) : u_φ^{-1}O_n ⟶ O_m` of Stacks 0D72 in case (B)**, read at `RingCat`:
restriction of the total sheaf of rings along the cross-fibre arrows `(φ, 𝟙)`. In case (B) the
inverse image of the transition is restriction along `u_φ`, so this is literal whiskering by
`CategoryTheory.Grothendieck.ιNatTrans`. -/
def ringTransitionB (φ : n ⟶ m) :
    (transitionFunctorB C φ).op ⋙ (ringSheafB C P n).obj ⟶ (ringSheafB C P m).obj :=
  Functor.whiskerRight (ringTransition C P.obj φ) (forget₂ CommRingCat.{u} RingCat.{u})

/-- **The direct-image form `O_n ⟶ {}_{su_φ} O_m` of the structure map of case (B)**: the adjunct
of `ringTransitionB` under the right-Kan-extension adjunction. This is the structure map over
which `Stacks.SheafOfModules.pushforwardCocontinuous` reproduces the direct image of modules
along the transition morphism of ringed topoi. -/
def fSharpB (φ : n ⟶ m) :
    ringSheafB C P n ⟶
      ((transitionFunctorB C φ).sheafPushforwardCocontinuous RingCat.{u}
        ((situation C).componentTopology m) ((situation C).componentTopology n)).obj
        (ringSheafB C P m) :=
  Stacks.SheafOfModules.RestrictRan.sheafRanFsharp (transitionFunctorB C φ)
    ((situation C).componentTopology m) ((situation C).componentTopology n)
    (ringSheafB C P n) (ringSheafB C P m) (ringTransitionB C P φ)

/-- On the leg at `(U, ψ)`, the direct-image form of the structure map acts through the
restriction map of `O_n` along `ψ` followed by the ring map `O(φ)`: the defining property of the
adjunct. -/
theorem fSharpB_leg (φ : n ⟶ m) (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (r : (ringSheafB C P n).obj.obj V) :
    (ranπ (transitionFunctorB C φ).op (ringSheafB C P m).obj V j).hom
        (((fSharpB C P φ).hom.app V).hom r) =
      ((ringTransitionB C P φ).app j.right).hom
        (((ringSheafB C P n).obj.map j.hom).hom r) :=
  Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ_apply_ring
    (transitionFunctorB C φ).op (ringTransitionB C P φ) V j r

/-- That composite, read on underlying sets, is restriction along `ψ` followed by restriction
along the cross-fibre arrow `(φ, 𝟙)`. Both sides are whiskerings by
`CategoryTheory.Grothendieck.ιNatTrans`, at `CommRingCat` and at `Type`, so this holds by
definition. -/
theorem ringTransitionB_app_apply (φ : n ⟶ m)
    (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (r : (ringSheafB C P n).obj.obj V) :
    ((ringTransitionB C P φ).app j.right).hom
        (((ringSheafB C P n).obj.map j.hom).hom r) =
      (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            ((sheafCompose (situation C).totalTopology (forget CommRingCat.{u})).obj P).obj).app
          j.right
        ((((situation C).restrict n).obj
            ((sheafCompose (situation C).totalTopology
              (forget CommRingCat.{u})).obj P)).obj.map j.hom r) := rfl

/-- The total structure sheaf read as a sheaf of sets: the coefficients in which both transitions
of Stacks 09WF are stated. -/
abbrev forgetP : Sheaf (situation C).totalTopology (Type u) :=
  (sheafCompose (situation C).totalTopology (forget CommRingCat.{u})).obj P

/-- On a section of the degree-`n` restriction of the total structure sheaf of sets, the unit of
the topos adjunction of the transition followed by the direct image of the inverse-image transition
is the direct-image transition. -/
theorem ranMap_fiberTransition_unit (φ : n ⟶ m) (V : ((situation C).component n)ᵒᵖ)
    (r : (((situation C).restrict n).obj (forgetP C P)).obj.obj V) :
    ((((situation C).transitionMorphism φ).pushforward.map
          (((situation C).fiberTransition φ).app (forgetP C P))).hom.app V)
        ((((situation C).transitionMorphism φ).adj.unit.app
          (((situation C).restrict n).obj (forgetP C P))).hom.app V r) =
      ((((situation C).restrictTransition φ).app (forgetP C P)).hom.app V) r :=
  congrArg (fun t => t.hom.app V r)
    ((Adjunction.homEquiv_unit (adj := ((situation C).transitionMorphism φ).adj)
      (f := ((situation C).fiberTransition φ).app (forgetP C P))).symm.trans
      ((situation C).fiberTransition_adj φ (forgetP C P)))

/-- **The leg of the direct-image transition of Stacks 09WF.** On the leg at `(U, ψ)` over `V`,
the direct-image transition of a sheaf of sets on the total site is restriction along `ψ` followed
by restriction along the cross-fibre arrow `(φ, 𝟙)`: the defining property of the adjunct, the
transition being the adjunct of that whiskering.

It is stated at an arbitrary sheaf of sets on the total site rather than at the structure sheaf,
because the right-hand leg of the case-(B) leg equation needs it at the underlying sheaf of sets
of a sheaf of modules; `hcompatB` below is the instance at the structure sheaf. -/
theorem ranπ_restrictTransition (φ : n ⟶ m)
    (G : Sheaf (situation C).totalTopology (Type u)) (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (r : (((situation C).restrict n).obj G).obj.obj V) :
    ranπ (transitionFunctorB C φ).op
        (((situation C).restrict m).obj G).obj V j
        ((((situation C).restrictTransition φ).app G).hom.app V r) =
      (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
            G.obj).app j.right
        ((((situation C).restrict n).obj G).obj.map j.hom r) :=
  Stacks.SheafOfModules.RestrictRan.homEquiv_app_comp_ranπ_apply_type
    (transitionFunctorB C φ).op
    (G := (Grothendieck.ι C.underlying (op n)).op ⋙ G.obj)
    (F := (Grothendieck.ι C.underlying (op m)).op ⋙ G.obj)
    (Functor.whiskerRight (NatTrans.op (Grothendieck.ιNatTrans (F := C.underlying) φ.op))
      G.obj) V j r

/-- The inverse-image form of the structure map of the transition, on a section, is the
inverse-image transition of Stacks 09WF. This is
`CategoryTheory.SimplicialSiteSituation.ringSheafMap_ringFsharpInverseImage_transition` read on
a section; the source and target are spelled as the transition's own so that the statement
elaborates without universe metavariables. -/
theorem ringFsharpInverseImage_app_apply (φ : n ⟶ m) (U : ((situation C).component m)ᵒᵖ)
    (x : ((((situation C).restrict n ⋙ ((situation C).transitionMorphism φ).inverseImage).obj
      (forgetP C P)).obj.obj U)) :
    ((((situation C).transitionRingedToposHom P φ).toModulesHom.fSharpInverseImage).hom.app U).hom
        x =
      ((((situation C).fiberTransition φ).app (forgetP C P)).hom.app U) x :=
  (congrArg (fun d => (d.hom.app U).hom x)
      (AlgebraicGeometry.RingedToposHom.forgetCommRingSheaf_map_fSharpInverseImage
        ((situation C).transitionRingedToposHom P φ)).symm).trans
    (congrArg
      (fun t : (((situation C).restrict n ⋙
            ((situation C).transitionMorphism φ).inverseImage).obj (forgetP C P)) ⟶
          (((situation C).restrict m).obj (forgetP C P)) => t.hom.app U x)
      ((situation C).ringSheafMap_ringFsharpInverseImage_transition P φ))

/-- **The two scalar maps of the summand comparison agree on every leg.** On the leg at `(U, ψ)`
over `V`, the unit `O_n ⟶ f_*f^{-1}O_n`, followed by the leg and by the inverse-image form of the
structure map of the transition, is the direct-image form `fSharpB` followed by the leg for
`O_m`.

This is the hypothesis of `Stacks.SheafOfModules.pushforwardCocontinuousModulesIso`, and it is
what identifies the direct image of sheaves of modules along the transition morphism of ringed
topoi with the direct image along the cocontinuous transition functor over `fSharpB`. -/
theorem hcompatB (φ : n ⟶ m) (V : ((situation C).component n)ᵒᵖ)
    (j : StructuredArrow V (transitionFunctorB C φ).op)
    (r : (ringSheafB C P n).obj.obj V) :
    ((((situation C).transitionRingedToposHom P φ).toModulesHom.fSharpInverseImage).hom.app
          j.right).hom
        (ranπ (transitionFunctorB C φ).op
          ((((situation C).restrict n ⋙
            ((situation C).transitionMorphism φ).inverseImage).obj (forgetP C P))).obj V j
          (((ringUnit ((situation C).transitionMorphism φ)
            (ringSheafB C P n)).hom.app V).hom r)) =
      (ranπ (transitionFunctorB C φ).op (ringSheafB C P m).obj V j).hom
        (((fSharpB C P φ).hom.app V).hom r) :=
  (ringFsharpInverseImage_app_apply C P φ j.right _).trans
    (((ranπ_map_functor_apply (transitionFunctorB C φ)
        (((situation C).fiberTransition φ).app (forgetP C P)).hom V j _).symm).trans
      ((congrArg (ranπ (transitionFunctorB C φ).op
            (((situation C).restrict m).obj (forgetP C P)).obj V j)
          (ranMap_fiberTransition_unit C P φ V r)).trans
        ((ranπ_restrictTransition C φ (forgetP C P) V j r).trans
          ((ringTransitionB_app_apply C P φ V j r).symm.trans
            (fSharpB_leg C P φ V j r).symm))))

/-- **The direct image of sheaves of modules along the transition morphism of ringed topoi is
the direct image along the cocontinuous transition functor.** In case (B) the direct image of
sheaves of sets of the transition is `CategoryTheory.Functor.sheafPushforwardCocontinuous` for
`u_φ` — it is the defining field of the morphism of topoi of Stacks 00XO — so the generic
comparison applies, with the inverse-image form of the structure map for its restriction of
scalars on the source, the unit `O_n ⟶ f_*f^{-1}O_n` for the one on the target, and `fSharpB` for
the structure map over which the Kan extension carries its module structure. -/
def transitionPushforwardModulesIsoB (φ : n ⟶ m) :
    pushforwardCocontinuous.{u} (transitionFunctorB C φ) (fSharpB C P φ) ≅
      pushforwardModules (X := (situation C).componentRingedTopos P m)
        (Y := (situation C).componentRingedTopos P n)
        ((situation C).transitionRingedToposHom P φ).toModulesHom :=
  (pushforwardCocontinuousModulesIso.{u} (transitionFunctorB C φ)
    ((situation C).componentTopology m) ((situation C).componentTopology n) _ _
    ((situation C).transitionRingedToposHom P φ).toModulesHom.fSharpInverseImage _
    (ringUnit ((situation C).transitionMorphism φ) (ringSheafB C P n))
    (fSharpB C P φ) (hcompatB C P φ)).symm

/-- **The case-(B) summand is left adjoint to the direct image of modules along the cocontinuous
transition functor.** Restriction of presheaves of modules along `u_φ` is left adjoint to the
direct image of presheaves of modules over the unit structure map; extension of scalars along the
ring map `O(φ)` is left adjoint to restriction of scalars; sheafification at the identity
structure map is left adjoint to taking the underlying presheaf of modules. Composing the three
and restricting along the fully faithful forgetful functor of sheaves of modules on the degree-`n`
component gives the summand, and on the right adjoint the restriction of scalars is moved past the
Kan extension, where it becomes the direct image over `fSharpB`. -/
def transitionModulePullbackAdjunctionB (φ : n ⟶ m) :
    transitionModulePullbackB C P n m φ ⊣
      pushforwardCocontinuous.{u} (transitionFunctorB C φ) (fSharpB C P φ) :=
  Adjunction.restrictFullyFaithful
    ((RestrictRan.adjunction (transitionFunctorB C φ) (ringSheafB C P n).obj).comp
      ((Stacks.PullbackModel.extendScalarsAdjunction (ringTransition C P.obj φ)).comp
        (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheafB C P m).obj))))
    (_root_.SheafOfModules.fullyFaithfulForget.{u} (ringSheafB C P n))
    (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.isoWhiskerLeft (_root_.SheafOfModules.forget.{u} (ringSheafB C P m))
      (RestrictRan.ranPushforwardRestrictScalarsIso (transitionFunctorB C φ)
        (ringTransitionB C P φ)))

/-- **The comparison of the two direct images along a transition of Stacks 09WF in case (B).**
The direct image of sheaves of modules along the cocontinuous transition functor over `fSharpB`,
which is the right adjoint of the case-(B) summand, is the direct image along the transition
morphism of ringed topoi, which is the right adjoint of the summand
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModules` that Stacks 0D74 consumes.

Two comparisons separate them and this assembles both: the comparison
`CategoryTheory.CocontinuousSimplicialSite.transitionPushforwardModulesIsoB` of the right
adjoints, and the comparison
`AlgebraicGeometry.RingedToposHom.toModulesPushforwardIso` of the modules development's direct
image with `AlgebraicGeometry.RingedToposHom.pushforwardModules`. The transport across the two
readings `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` and
`AlgebraicGeometry.RingedToposHom.toModulesHom` of a morphism of ringed topoi used to sit between
them, and is gone: `…transitionPushforwardModulesIsoB` is built at the second reading, which is
the one `AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules` is defined at. The
measurements that forced that change are in the docstring of
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA`.

It is the case-(B) counterpart of
`CategoryTheory.SimplicialSite.transitionRingedToposPushforwardModulesIsoA`, and it exists for
the same reason: the transport across the two readings is placed here, on the *right* adjoints,
so that the summand comparison below can be taken against the Stacks 03D7 adjunction of the
two-field morphism and carry no transport on the left. -/
def transitionRingedToposPushforwardModulesIsoB (φ : n ⟶ m) :
    pushforwardCocontinuous.{u} (transitionFunctorB C φ) (fSharpB C P φ) ≅
      ((situation C).transitionRingedToposHom P φ).pushforwardModules :=
  transitionPushforwardModulesIsoB C P φ ≪≫
    ((situation C).transitionRingedToposHom P φ).toModulesPushforwardIso

/-- **The summand comparison of Stacks 0D72 in case (B).** The pullback of sheaves of modules
along the transition morphism of ringed topoi of a simplex map `φ : [n] ⟶ [m]` is the
sheafification of the presheaf-level pullback along the transition functor `u_φ`.

Both are left adjoints — the first by Stacks 03D7 for the two-field morphism of ringed topoi,
the second by `transitionModulePullbackAdjunctionB` — and their right adjoints are identified by
`transitionRingedToposPushforwardModulesIsoB`, so uniqueness of left adjoints gives the
comparison. This is what turns the direct-sum formula
`CategoryTheory.CocontinuousSimplicialSite.componentModuleSumFormulaB` into the formula that
Stacks 0D74 and Stacks 0D75 consume.

The Stacks 03D7 adjunction taken here is the one of the *two-field* morphism of ringed topoi,
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, whose left adjoint already *is*
the summand `CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`, so the comparison
is a bare `CategoryTheory.Adjunction.leftAdjointUniq` carrying no transport.

It used to be taken against the adjunction of the modules development at
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` — the other reading of the morphism —
which left a `CategoryTheory.eqToIso` in front of the comparison, carrying
`AlgebraicGeometry.RingedToposHom.pullbackModules_toRingedToposModulesHom`. That transport could
not be cancelled downstream at any price: the two readings agree only propositionally, so every
definitional comparison which reaches them is unbounded. The transport is now carried on the
*right* adjoints instead, inside
`transitionRingedToposPushforwardModulesIsoB`, where it is crossed once and never has to be
cancelled. -/
def transitionPullbackModulesIsoB (φ : n ⟶ m) :
    (situation C).transitionPullbackModules' P φ ≅ transitionModulePullbackB C P n m φ :=
  Adjunction.leftAdjointUniq
    (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.ofNatIsoRight
      (transitionRingedToposPushforwardModulesIsoB C P φ).symm)
    (transitionModulePullbackAdjunctionB C P φ)

/-- `CategoryTheory.CocontinuousSimplicialSite.transitionPullbackModulesIsoB` is, by definition,
the comparison of the two left adjoints of the two adjunctions it is built from.

This records the definition as a *propositional* equality, so that a consumer never has to unfold
it inside a larger type; it is the case-(B) counterpart of
`CategoryTheory.SimplicialSite.transitionPullbackModulesIsoA_eq`. -/
theorem transitionPullbackModulesIsoB_eq (φ : n ⟶ m) :
    transitionPullbackModulesIsoB C P φ =
      Adjunction.leftAdjointUniq
        (((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.ofNatIsoRight
          (transitionRingedToposPushforwardModulesIsoB C P φ).symm)
        (transitionModulePullbackAdjunctionB C P φ) :=
  rfl

/-- **The summand comparison of case (B) transposes away: Stacks 0D72 (6), the step that moves a
transposition between the two readings of the summand.** Transposing the summand comparison
`CategoryTheory.CocontinuousSimplicialSite.transitionPullbackModulesIsoB`, followed by a morphism
out of the case-(B) summand, along the Stacks 03D7 adjunction of the transition morphism of
ringed topoi is transposing that morphism along the case-(B) summand's own adjunction
`…transitionModulePullbackAdjunctionB` and applying the comparison
`…transitionRingedToposPushforwardModulesIsoB` of the two right adjoints afterwards.

This is the case-(B) counterpart of
`CategoryTheory.SimplicialSite.homEquiv_transitionPullbackModulesIsoA_hom_app_comp`, and it
supersedes `…homEquiv_leftAdjointUniq_transitionModulePullbackAdjunctionB`: that statement
transposes the same comparison along the Stacks 03D7 adjunction of the *modules development*, at
the four-field reading of the transition morphism, which is the side of the
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom_eq_toModulesHom` equality that the
canonical leg cannot be reached from. -/
theorem homEquiv_transitionPullbackModulesIsoB_hom_app_comp (φ : n ⟶ m)
    (X : _root_.SheafOfModules.{u} (ringSheafB C P n))
    (T : _root_.SheafOfModules.{u} (ringSheafB C P m))
    (k : (transitionModulePullbackB C P n m φ).obj X ⟶ T) :
    ((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules.homEquiv X T
        ((transitionPullbackModulesIsoB C P φ).hom.app X ≫ k) =
      (transitionModulePullbackAdjunctionB C P φ).homEquiv X T k ≫
        (transitionRingedToposPushforwardModulesIsoB C P φ).hom.app T :=
  Adjunction.homEquiv_eq_of_eq_leftAdjointUniq_ofNatIsoRight_symm
    ((situation C).transitionRingedToposHom P φ).pullbackAdjPushforwardModules
    (transitionModulePullbackAdjunctionB C P φ)
    (transitionRingedToposPushforwardModulesIsoB C P φ)
    (transitionPullbackModulesIsoB C P φ) (transitionPullbackModulesIsoB_eq C P φ) k

end CategoryTheory.CocontinuousSimplicialSite

end
