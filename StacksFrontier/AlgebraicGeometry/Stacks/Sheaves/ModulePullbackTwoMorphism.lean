module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.ProjectionTwoArrow
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Equivalence

/-!
# Two-morphisms and the inverse image of sheaves of modules

Stacks 06TM attaches to a 2-morphism `t : f ⟶ g` of 1-morphisms of categories fibred in
groupoids a canonical isomorphism `t^p : g^p ⟶ f^p` of the restriction functors on presheaves,
and a canonical isomorphism `{}_pt : {}_pf ⟶ {}_pg` of their right adjoints, compatible with
the adjunctions and with vertical and horizontal composition.  That tag is proved for presheaves
in `StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/Presheaves.lean`.

This file proves the **module-level analogue of the first half**: the same 2-morphism induces a
canonical isomorphism of the inverse-image functors `AlgebraicGeometry.Stack.modulePullback` of
Stacks 06WE on sheaves of modules over the structure sheaves of the two associated sites of
Stacks 06TP.  The contravariance is the source's: `t : f ⟶ g` gives `g^* ≅ f^*`.

The point is that the comparison is a morphism of *modules* and not merely of abelian sheaves.
`AlgebraicGeometry.Stack.modulePullback` carries a module `M` on `𝒴` to the objectwise
restriction `f.op ⋙ M`, whose scalars are transported along
`AlgebraicGeometry.Stack.ringStructureSheafCore_obj_eq`.  The comparison acts at an object `x`
of `𝒳` by `M.map (t.app x).op`, and that is `𝒪`-linear exactly because every component of a
2-morphism lies over an identity of the base site: the structure sheaf is restricted along the
structure functor, so the ring map it induces is the identity.  That is
`AlgebraicGeometry.Stack.whiskerRight_op_ringStructureSheafCore`, and it is the whole content
of the construction.

## Main definitions

* `AlgebraicGeometry.Stack.modulePullbackTwoMorphismIso`: the module-level analogue of `t^p`,
  the isomorphism `g^* ≅ f^*` of inverse-image functors on sheaves of modules.
* `AlgebraicGeometry.Stack.quotientStackTwoArrowModulePullbackIso`: that isomorphism at the
  canonical 2-morphism of Stacks 044S for the quotient stack of a groupoid in algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.whiskerRight_op_ringStructureSheafCore`: a 2-morphism acts on the
  restricted structure presheaf by the canonical `eqToHom`, which is the linearity of the
  comparison.
* `AlgebraicGeometry.Stack.modulePullbackTwoMorphismIso_hom_app_val_app`: the pointwise
  description — on a module and an object the comparison is restriction along the component of
  the 2-morphism.
* `AlgebraicGeometry.Stack.modulePullbackTwoMorphismIso_trans`: compatibility with vertical
  composition of 2-morphisms, in the contravariant order.

## Implementation notes

**This is not the tag.** Stacks 06TM is a statement about the presheaf functors `f^p` and
`{}_pf`, and it has four clauses: the two isomorphisms, their compatibility with the two
adjunctions, and their compatibility with vertical and horizontal composition.  What is proved
here is the analogue of one of those isomorphisms for a different pair of functors — the
inverse image of *sheaves of modules* of Stacks 06WE — so no declaration in this file carries
`@[stacks 06TM]`.  The direct-image half is not stated: unlike the inverse image, the direct
image of sheaves of modules exists in this library only at a module universe large enough for
the two sites (`AlgebraicGeometry.Stack.ModuleSheafFunctoriality`), so there is no adjoint pair
to take a mate in at the universes below.  Horizontal composition is not stated either; the
pointwise description makes it a computation for whoever needs it.

**Universes.** The module universe `m` is arbitrary and independent of every other universe
here, and that is deliberate rather than incidental: `AlgebraicGeometry.Stack.modulePullback`
is objectwise restriction, no limit is taken, so neither it nor this comparison needs a bound
on `m`.  Module universes have been the real obstruction elsewhere in this area —
`AlgebraicGeometry.Stack.isQuasicoherentOnSite_modulePullback` (Stacks 06WH) preserves
quasi-coherence only at `SheafOfModules.{max u v w m}`, and the groupoid side of Stacks 0441
forces module universe `u` — so a comparison available at *every* `m` is what makes this usable
on both sides of that divide.

The two categories carry independent object and morphism universes, which is also forced by the
intended application: the quotient stack of a groupoid in algebraic spaces has objects and
morphisms in `Type (u + 1)`, while the fibration of the arrow space has objects in
`Type (u + 1)` and morphisms in `Type u`.  So `quotientStackTwoArrowModulePullbackIso` is at
`.{u, u + 1, u, m, u + 1, u + 1}`, matching
`AlgebraicGeometry.Stack.quotientStackModulePullback`.

The 2-morphism is taken as a bare natural transformation together with the hypothesis that each
of its components lies over an identity, rather than as a `CategoryTheory.BasedNatTrans` or a
2-morphism of `CategoryTheory.CatFiberedInGroupoids`.  That is the shape
`AlgebraicGeometry.Stack.modulePullback` itself is stated in, it keeps the two categories'
universes independent, and a `BasedNatTrans` supplies it directly through `toNatTrans` and
`isHomLift'` — which is how the quotient-stack corollary below is obtained from
`AlgebraicGeometry.Stack.quotientStackTwoArrow`.

## References

* [Stacks Project, Tag 06TM](https://stacks.math.columbia.edu/tag/06TM)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 044S](https://stacks.math.columbia.edu/tag/044S)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w m v' w'

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  {f g : 𝒳 ⥤ 𝒴} (hf : f ⋙ q = p) (hg : g ⋙ q = p)
  (t : f ⟶ g) (ht : ∀ x, q.IsHomLift (𝟙 (p.obj x)) (t.app x))
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

include hp hq hf hg ht

/-- **The linearity of the module-level comparison of Stacks 06TM.** A 2-morphism `t : f ⟶ g`
acts on the structure presheaf of rings restricted along `g` by exactly the canonical `eqToHom`
between the two restrictions along `f` and along `g`.

The structure presheaf of `𝒴` is the structure presheaf of the base site restricted along the
structure functor `q`, so the ring map induced by a component `t.app x` is the one induced by
`q.map (t.app x)`; and that is an `eqToHom`, because `t.app x` lies over an identity of the
base.  This is why restriction along the components of `t` is a morphism of modules and not
only of abelian sheaves, and it is what the construction below feeds to
`SheafOfModules.pushforwardCongr₂`. -/
theorem whiskerRight_op_ringStructureSheafCore :
    Functor.whiskerRight (NatTrans.op t) (ringStructureSheafCore B S hS q hq τ hτ).obj =
      eqToHom ((ringStructureSheafCore_obj_eq B S hS p q hp hq g hg τ hτ).symm.trans
        (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ)) := by
  refine NatTrans.ext (funext fun x => ?_)
  have := ht x.unop
  have hqmap : q.map (t.app x.unop) =
      eqToHom ((Functor.congr_obj hf x.unop).trans (Functor.congr_obj hg x.unop).symm) := by
    simpa using CategoryTheory.IsHomLift.fac' q (𝟙 (p.obj x.unop)) (t.app x.unop)
  change (BigFppfOver.structureSheaf B S hS).obj.map (q.map (t.app x.unop)).op = _
  rw [hqmap, eqToHom_op, eqToHom_map, eqToHom_app]
  rfl

/-- The scalar identification of `AlgebraicGeometry.Stack.modulePullback` for `g`, followed by
the action of a 2-morphism `t : f ⟶ g`, is the scalar identification for `f`.

This is the hypothesis `SheafOfModules.pushforwardCongr₂` asks for, read on underlying
presheaves of rings; stating it away from `CategoryTheory.Functor.sheafPushforwardContinuous`
keeps it type-correct at `implicit` transparency, so that `rw` and `simp` apply to it. -/
theorem eqToHom_ringStructureSheafCore_obj_eq_comp :
    eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq g hg τ hτ) ≫
        Functor.whiskerRight (NatTrans.op t) (ringStructureSheafCore B S hS q hq τ hτ).obj =
      eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ) := by
  rw [whiskerRight_op_ringStructureSheafCore B S hS p q hp hq hf hg t ht τ hτ, eqToHom_trans]

/-- **The module-level analogue of the restriction comparison of Stacks 06TM.** A 2-morphism
`t : f ⟶ g` of 1-morphisms of categories fibred in groupoids over the big fppf category of `S`
induces a canonical isomorphism `g^* ≅ f^*` of the inverse-image functors of Stacks 06WE on
sheaves of modules, contravariantly in the 2-morphism.

Every component of `t` is invertible, because it lies over an identity of the base and the
fibres are groupoids
(`CategoryTheory.Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id`), so `t` is a natural
isomorphism of the underlying functors; the comparison is the induced isomorphism of
restriction functors, with the scalars matched by
`AlgebraicGeometry.Stack.eqToHom_ringStructureSheafCore_obj_eq_comp`.

The module universe is arbitrary; see the module documentation. -/
noncomputable def modulePullbackTwoMorphismIso :
    modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq g hg τ hτ ≅
      modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ := by
  letI : p.IsFibered := hp.isFibered
  letI : q.IsFibered := hq.isFibered
  letI := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  letI := ((hq.isFibredOneMorphism hg).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  letI : ∀ x, IsIso (t.app x) := fun x => hq.isIso_of_isHomLift_id (t.app x) (ht x)
  letI := NatIso.isIso_of_isIso_app t
  exact SheafOfModules.pushforwardCongr₂ (F := f) (G := g)
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq g hg τ hτ)⟩
    (ψ := ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ)⟩) (asIso t)
    (Sheaf.hom_ext
      (eqToHom_ringStructureSheafCore_obj_eq_comp B S hS p q hp hq hf hg t ht τ hτ))

/-- On a sheaf of modules and an object, the module-level comparison of Stacks 06TM is
restriction along the component of the 2-morphism there. This is the module-level form of
`CategoryTheory.CatFiberedInGroupoids.pullbackIso_hom_app`. -/
theorem modulePullbackTwoMorphismIso_hom_app_val_app
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ)) (x y) :
    ((modulePullbackTwoMorphismIso.{u, v, w, m, v', w'} B S hS p q hp hq hf hg t ht
        τ hτ).hom.app M).val.app x y = M.val.map (t.app x.unop).op y := rfl

/-- **Compatibility with vertical composition.** The module-level comparison of Stacks 06TM
turns vertical composition of 2-morphisms into composition of the induced isomorphisms, in the
reverse order. This is the module-level form of
`CategoryTheory.CatFiberedInGroupoids.pullbackIso_trans`. -/
theorem modulePullbackTwoMorphismIso_trans {h : 𝒳 ⥤ 𝒴} (hh : h ⋙ q = p) (s : g ⟶ h)
    (hs : ∀ x, q.IsHomLift (𝟙 (p.obj x)) (s.app x)) :
    modulePullbackTwoMorphismIso.{u, v, w, m, v', w'} B S hS p q hp hq hf hh (t ≫ s)
        (fun x ↦ haveI := ht x; haveI := hs x
          CategoryTheory.IsHomLift.comp_of_lift_id q (p.obj x) (t.app x) (s.app x)) τ hτ =
      modulePullbackTwoMorphismIso.{u, v, w, m, v', w'} B S hS p q hp hq hg hh s hs τ hτ ≪≫
        modulePullbackTwoMorphismIso.{u, v, w, m, v', w'} B S hS p q hp hq hf hg t ht τ hτ := by
  apply Iso.ext
  ext M x y
  suffices h' : M.val.presheaf.map ((t ≫ s).app x.unop).op =
      M.val.presheaf.map (s.app x.unop).op ≫ M.val.presheaf.map (t.app x.unop).op from
    congr($h' y)
  rw [NatTrans.comp_app, op_comp, Functor.map_comp]

end General

section QuotientStack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {A : AlgebraicSpaces C S hS}

/-- **The module-level comparison of Stacks 06TM at the canonical 2-morphism of Stacks 044S.**
For a groupoid `G = (U, R, s, t, c)` in algebraic spaces, the square of Stacks 044R commutes
only up to the 2-morphism `AlgebraicGeometry.Stack.quotientStackTwoArrow`; this is the induced
isomorphism of the two inverse-image functors it compares, on sheaves of modules over the
structure sheaves of the associated sites.

On a module `ℱ` on the quotient stack this is an isomorphism
`(π ∘ t)^* ℱ ≅ (π ∘ s)^* ℱ` on the fibration of the arrow space, which is the big-site avatar of
the transition morphism `α` of Stacks 0441: with the two legs written through
`AlgebraicGeometry.Stack.quotientStackModulePullback` it compares `t^*(x^* ℱ)` with
`s^*(x^* ℱ)`.  Its pointwise description is
`AlgebraicGeometry.Stack.modulePullbackTwoMorphismIso_hom_app_val_app` together with
`AlgebraicGeometry.Stack.quotientStackTwoArrow_app`, and its compatibility with the cocycle
identity of Stacks 044T comes from
`AlgebraicGeometry.Stack.modulePullbackTwoMorphismIso_trans` and
`AlgebraicGeometry.Stack.quotientStackTwoArrow_cocycle`.  What still separates it from `α`
itself is Stacks 0GQD, which carries a module on the big fppf site of the presentation of an
algebraic space to one on its small étale site; that is a different missing input, recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuotientStackQuasicoherentMissingInputs.lean`.

The module universe is arbitrary, so this is available both at `u + 1`, where
`AlgebraicGeometry.Stack.quotientStackModulePullback` lives, and at `u`, where the groupoid side
of Stacks 0441 lives. -/
noncomputable def quotientStackTwoArrowModulePullbackIso
    (G : GroupoidInAlgebraicSpaces C S hS A)
    (τ : GrothendieckTopology C.Schemes) (hτ : τ ≤ C.topology) :
    modulePullback.{u, u + 1, u, m, u + 1, u + 1} C S hS
        (fibredCategory C S hS G.arrows.obj).val.p (quotientStack G).p
        (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_quotientStack G)
        (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
          (quotientStackProjection G)).toFunctor
        (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
          (quotientStackProjection G)).w τ hτ ≅
      modulePullback.{u, u + 1, u, m, u + 1, u + 1} C S hS
        (fibredCategory C S hS G.arrows.obj).val.p (quotientStack G).p
        (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_quotientStack G)
        (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
          (quotientStackProjection G)).toFunctor
        (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
          (quotientStackProjection G)).w τ hτ :=
  modulePullbackTwoMorphismIso.{u, u + 1, u, m, u + 1, u + 1} C S hS
    (fibredCategory C S hS G.arrows.obj).val.p (quotientStack G).p
    (fibredCategory C S hS G.arrows.obj).property (isFiberedInGroupoids_quotientStack G)
    (BasedFunctor.comp (associatedMap C S hS G.source.hom).1.hom
      (quotientStackProjection G)).w
    (BasedFunctor.comp (associatedMap C S hS G.target.hom).1.hom
      (quotientStackProjection G)).w
    (quotientStackTwoArrow G).toNatTrans (quotientStackTwoArrow G).isHomLift' τ hτ

end QuotientStack

end AlgebraicGeometry.Stack

end
