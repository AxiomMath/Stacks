module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor

/-!
# Pullback of sheaves of modules along a square of ringed sites

Pullback of sheaves of modules is compatible with composition of morphisms of ringed sites, so
two morphisms of ringed sites with the same source and target induce isomorphic pullbacks as
soon as the two routes agree.  This file states that compatibility for a *square*, and applies
it to the associated-module construction of the big fppf site of a scheme.

Let `f : X ⟶ Y` be a morphism of schemes, both contained in a big fppf site, and let
`f_big : ((Sch/X)_fppf, 𝒪) ⟶ ((Sch/Y)_fppf, 𝒪)` be a morphism of ringed sites between their big
fppf sites: a continuous functor `Ff` in the direction `(Sch/Y)_fppf ⥤ (Sch/X)_fppf` together
with a comparison `ψ` of the two structure sheaves.  Then the associated-module construction
commutes with pullback,
`(f^*𝓕)^a ≅ f_big^*(𝓕^a)`.

Two hypotheses are offered for the square, and the difference between them is the point.  The
general statement asks for an isomorphism of the two composite *continuous functors* together
with an equation between the two composite structure-sheaf comparisons — elementary data, of
which the geometric half here is the identification of `X ×_Y V` with `f⁻¹(V)` for `V` an open of
`Y`.  The statement at the associated-module functors asks instead for an isomorphism of the two
composite *pushforwards*; that is weaker, in fact equivalent to the conclusion, since a left
adjoint and its right adjoint determine each other.  It is nonetheless the useful form, because
pushforward along a continuous functor is restriction and so has sections over an object given by
a formula, whereas the pullbacks are left adjoints and have none.

## Main results

* `SheafOfModules.pushforwardSquareIso`: the pushforwards along the two routes round a commuting
  square of ringed sites are isomorphic, and
  `SheafOfModules.pushforwardSquareIso_hom_app_val_app` is the formula for that isomorphism on
  sections: over an object it is restriction along the component of the geometric half of the
  square.
* `SheafOfModules.pullbackSquareIso`: the pullbacks along the two routes round a commuting square
  of ringed sites are isomorphic.
* `SheafOfModules.unit_comp_pullbackSquareIso_hom_app`: **the adjunct square.**  The isomorphism
  of the two composite pullbacks is the unique one compatible with the units of the two composite
  adjunctions, the comparison between the two right adjoints being
  `SheafOfModules.pushforwardSquareIso`.  This is the only description a composite of left
  adjoints admits, and it is what gives the isomorphism a reading on sections.
* `AlgebraicGeometry.BigFppfOver.associatedModulePullbackIsoOfSquare`: the associated-module
  functor of the big fppf site of `X`, precomposed with pullback of modules along `f`, is
  isomorphic to the associated-module functor of the big fppf site of `Y` followed by pullback
  along `f_big`, given the square of sites.
* `AlgebraicGeometry.BigFppfOver.associatedModulePullbackIso`: the same conclusion from the
  weaker hypothesis that the two composite pushforwards agree.
* `AlgebraicGeometry.BigFppfOver.associatedModuleObjPullbackIso`: the identification read at a
  single module, which is the form `(f^*𝓕)^a = f_big^*𝓕^a` in which the Stacks project states it.

## Implementation notes

`SheafOfModules.comparisonComp` is the comparison of sheaves of rings of a composite of two
morphisms of ringed sites, named only so that it carries the type pushforward along the composite
continuous functor expects; the two spellings of that type agree by unfolding, which no rewrite
reaches.

The adjunct square is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` and nothing more,
the isomorphism being `CategoryTheory.Adjunction.leftAdjointUniq` of the two composite
adjunctions with the second transported along `SheafOfModules.pushforwardSquareIso`.  What makes
it a usable statement is that the comparison of the two composite pushforwards has a formula on
sections: `SheafOfModules.pushforwardComp` is the identity isomorphism and
`SheafOfModules.pushforwardCongr` is the identity on sections, so the whole comparison is the
single restriction map induced by the geometric half of the square.

The morphism of ringed sites `f_big` is taken as hypothesis data — the continuous functor `Ff`,
the structure-sheaf comparison `ψ`, and the existence of the left adjoint of its pushforward.
That data is supplied, for the big fppf sites of two schemes contained in one big fppf site, by
`AlgebraicGeometry.BigFppfOver.baseChange` and
`AlgebraicGeometry.BigFppfOver.structureComparison` of
`StacksFrontier.AlgebraicGeometry.Descent.BigFppfRingedMorphism`, and the hypothesis `e` below is
discharged in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigFppf`, where the conclusion is
restated with no hypothesis as
`AlgebraicGeometry.BigFppfOver.associatedModuleBigPullbackIso`.  Both halves of the square on
the small-site side are available unconditionally:
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and
`AlgebraicGeometry.BigFppfOver.associatedModuleAdjunction`.

Nothing here identifies `𝓕^a` with the sheaf of sections `(f : T → S) ↦ Γ(T, f^*𝓕)`; that is a
separate statement about one base and is not used, which is why this file does not depend on it.

## References

* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
-/

@[expose] public section

open CategoryTheory

universe v u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace SheafOfModules

section Comparison

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E} [F.IsContinuous J K] [G.IsContinuous K L] [(F ⋙ G).IsContinuous J L]
  {R : Sheaf J RingCat.{u}} {R' : Sheaf K RingCat.{u}} {R'' : Sheaf L RingCat.{u}}

/-- The comparison of sheaves of rings carried by the composite of two morphisms of ringed
sites, stated at the type that pushforward along the composite continuous functor expects.
This is the composite that appears in `SheafOfModules.pushforwardComp`, named so that it can be
composed further: the two spellings of its target agree only up to unfolding
`CategoryTheory.Functor.sheafPushforwardContinuous`. -/
public abbrev comparisonComp (φ : R ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R')
    (ψ : R' ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj R'') :
    R ⟶ ((F ⋙ G).sheafPushforwardContinuous RingCat.{u} J L).obj R'' :=
  φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ

end Comparison

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  {D : Type u₃} [Category.{v₃} D] {D' : Type u₄} [Category.{v₄} D']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}
  {K : GrothendieckTopology D} {K' : GrothendieckTopology D'}
  {a : C ⥤ C'} {b : C' ⥤ D'} {c : C ⥤ D} {d : D ⥤ D'}
  [a.IsContinuous J J'] [b.IsContinuous J' K'] [c.IsContinuous J K] [d.IsContinuous K K']
  [(a ⋙ b).IsContinuous J K'] [(c ⋙ d).IsContinuous J K']
  {RC : Sheaf J RingCat.{u}} {RC' : Sheaf J' RingCat.{u}}
  {RD : Sheaf K RingCat.{u}} {RD' : Sheaf K' RingCat.{u}}
  (φa : RC ⟶ (a.sheafPushforwardContinuous RingCat.{u} J J').obj RC')
  (φb : RC' ⟶ (b.sheafPushforwardContinuous RingCat.{u} J' K').obj RD')
  (φc : RC ⟶ (c.sheafPushforwardContinuous RingCat.{u} J K).obj RD)
  (φd : RD ⟶ (d.sheafPushforwardContinuous RingCat.{u} K K').obj RD')
  [(pushforward.{v} φa).IsRightAdjoint] [(pushforward.{v} φb).IsRightAdjoint]
  [(pushforward.{v} φc).IsRightAdjoint] [(pushforward.{v} φd).IsRightAdjoint]

/-- **The comparison of the two composite pushforwards round the square.**  Pushforward is
compatible with composition, so each route round the square pushes forward as the pushforward
along the corresponding composite comparison of sheaves of rings; the hypothesis `he` says the
two composites agree after transporting along `e`.

Unlike the pullbacks, this comparison has a formula on sections: over an object of `C` it is
restriction along the component of `e`, which is
`SheafOfModules.pushforwardSquareIso_hom_app_val_app`. -/
public noncomputable def pushforwardSquareIso (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb) :
    pushforward.{v} φd ⋙ pushforward.{v} φc ≅ pushforward.{v} φb ⋙ pushforward.{v} φa :=
  pushforwardComp.{v} φc φd ≪≫ pushforwardCongr₂.{v} _ e he ≪≫
    (pushforwardComp.{v} φa φb).symm

omit [(pushforward.{v} φa).IsRightAdjoint] [(pushforward.{v} φb).IsRightAdjoint]
  [(pushforward.{v} φc).IsRightAdjoint] [(pushforward.{v} φd).IsRightAdjoint] in
/-- **The comparison of the two composite pushforwards is restriction along `e`.**  Both
composites are the identity on underlying presheaves — pushforward along a continuous functor is
restriction, and `SheafOfModules.pushforwardComp` is the identity isomorphism — so the whole
comparison is the single restriction map that `e` induces. -/
public theorem pushforwardSquareIso_hom_app_val_app (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb) (N : SheafOfModules.{v} RD') (U : Cᵒᵖ)
    (x : ((pushforward.{v} φd ⋙ pushforward.{v} φc).obj N).val.obj U) :
    ((pushforwardSquareIso.{v} φa φb φc φd e he).hom.app N).val.app U x =
      N.val.map (e.hom.app U.unop).op x :=
  rfl

/-- **Stacks 03D8 for a square.**  Let the two routes `a` then `b`, and `c` then `d`, round a
square of morphisms of ringed sites have the same source and target.  If the two composite
continuous functors are isomorphic by `e`, compatibly with the two composite comparisons of
sheaves of rings, then the two composite pullbacks of sheaves of modules are isomorphic.

The proof is that each composite pullback is left adjoint to the corresponding composite
pushforward, that those two pushforwards are isomorphic by
`SheafOfModules.pushforwardSquareIso`, and that a left adjoint is determined by its right
adjoint. -/
public noncomputable def pullbackSquareIso (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb) :
    pullback.{v} φa ⋙ pullback.{v} φb ≅ pullback.{v} φc ⋙ pullback.{v} φd :=
  Adjunction.leftAdjointUniq
    ((pullbackPushforwardAdjunction.{v} φa).comp (pullbackPushforwardAdjunction.{v} φb))
    (((pullbackPushforwardAdjunction.{v} φc).comp
        (pullbackPushforwardAdjunction.{v} φd)).ofNatIsoRight
      (pushforwardSquareIso.{v} φa φb φc φd e he))

/-- **The adjunct square of `SheafOfModules.pullbackSquareIso`.**  The isomorphism of the two
composite pullbacks is the unique one compatible with the units of the two composite
adjunctions: the unit round `a` then `b`, followed by the isomorphism, is the unit round `c`
then `d`, followed by the comparison `SheafOfModules.pushforwardSquareIso` of the two composite
pushforwards.

This is the only description a composite of left adjoints admits, and it is what gives the
isomorphism a reading on sections: the right-hand side is a composite of two units with a
restriction map, each of which has a formula over an object. -/
public theorem unit_comp_pullbackSquareIso_hom_app (e : a ⋙ b ≅ c ⋙ d)
    (he : comparisonComp φc φd ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K').app RD' =
      comparisonComp φa φb) (M : SheafOfModules.{v} RC) :
    ((pullbackPushforwardAdjunction.{v} φa).comp
          (pullbackPushforwardAdjunction.{v} φb)).unit.app M ≫
        (pushforward.{v} φb ⋙ pushforward.{v} φa).map
          ((pullbackSquareIso.{v} φa φb φc φd e he).hom.app M) =
      ((pullbackPushforwardAdjunction.{v} φc).comp
            (pullbackPushforwardAdjunction.{v} φd)).unit.app M ≫
        (pushforwardSquareIso.{v} φa φb φc φd e he).hom.app
          ((pullback.{v} φc ⋙ pullback.{v} φd).obj M) :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

end SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (hX : B.Contains X) (hY : B.Contains Y)
  (f : X ⟶ Y) (Ff : BigFppfOver B Y hY ⥤ BigFppfOver B X hX)
  [Ff.IsContinuous (topology B Y hY) (topology B X hX)]
  (ψ : structureSheaf B Y hY ⟶
    (Ff.sheafPushforwardContinuous RingCat.{u} (topology B Y hY) (topology B X hX)).obj
      (structureSheaf B X hX))
  [(SheafOfModules.pushforward.{u} ψ).IsRightAdjoint]

/-- **Stacks 03FH (2), over a morphism of ringed sites between the two big fppf sites.**  The
associated module of a pullback is the pullback of the associated module.  The hypothesis is the
identification of the two restriction functors `SheafOfModules 𝒪_{(Sch/X)} ⥤ Y.Modules` obtained
by traversing the square of ringed sites the other way; the conclusion follows because each side
of it is the right adjoint of the corresponding side of the conclusion. -/
public noncomputable def associatedModulePullbackIso
    (e : restrictModule B X hX ⋙ Scheme.Modules.pushforward f ≅
      SheafOfModules.pushforward.{u} ψ ⋙ restrictModule B Y hY) :
    Scheme.Modules.pullback f ⋙ associatedModule B X hX ≅
      associatedModule B Y hY ⋙ SheafOfModules.pullback.{u} ψ :=
  Adjunction.leftAdjointUniq
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp (associatedModuleAdjunction B X hX))
    (((associatedModuleAdjunction B Y hY).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u} ψ)).ofNatIsoRight e.symm)

/-- **Stacks 03FH (2), over the square of sites.**  The same conclusion as
`AlgebraicGeometry.BigFppfOver.associatedModulePullbackIso` from strictly more elementary data:
an isomorphism `e` between the two routes `V ↦ f⁻¹(V)` then into the big fppf site of `X`, and
into the big fppf site of `Y` then along `f_big`, compatible with the two composite comparisons
of structure sheaves.  The geometric content of `e` is that `X ×_Y V` is `f⁻¹(V)`. -/
public noncomputable def associatedModulePullbackIsoOfSquare
    [(TopologicalSpace.Opens.map f.base ⋙ opensToBig B X hX).IsContinuous
      (Opens.grothendieckTopology ↥Y) (topology B X hX)]
    [(opensToBig B Y hY ⋙ Ff).IsContinuous (Opens.grothendieckTopology ↥Y) (topology B X hX)]
    (e : TopologicalSpace.Opens.map f.base ⋙ opensToBig B X hX ≅ opensToBig B Y hY ⋙ Ff)
    (he : SheafOfModules.comparisonComp (structureMap B Y hY) ψ ≫
        (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u}
          (Opens.grothendieckTopology ↥Y) (topology B X hX)).app (structureSheaf B X hX) =
      SheafOfModules.comparisonComp f.toRingCatSheafHom (structureMap B X hX)) :
    Scheme.Modules.pullback f ⋙ associatedModule B X hX ≅
      associatedModule B Y hY ⋙ SheafOfModules.pullback.{u} ψ :=
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  SheafOfModules.pullbackSquareIso.{u} f.toRingCatSheafHom (structureMap B X hX)
    (structureMap B Y hY) ψ e he

/-- **Stacks 03FH (2), at one module.**  `(f^*𝓕)^a ≅ f_big^*(𝓕^a)`, read off from
`AlgebraicGeometry.BigFppfOver.associatedModulePullbackIso`. -/
public noncomputable def associatedModuleObjPullbackIso
    (e : restrictModule B X hX ⋙ Scheme.Modules.pushforward f ≅
      SheafOfModules.pushforward.{u} ψ ⋙ restrictModule B Y hY)
    (𝓕 : Y.Modules) :
    (associatedModule B X hX).obj ((Scheme.Modules.pullback f).obj 𝓕) ≅
      (SheafOfModules.pullback.{u} ψ).obj ((associatedModule B Y hY).obj 𝓕) :=
  (associatedModulePullbackIso B hX hY f Ff ψ e).app 𝓕

end AlgebraicGeometry.BigFppfOver

end
