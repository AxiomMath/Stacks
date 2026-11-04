module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeIsomGroupSection
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatPresentation

/-!
# A gerbe with a section is the quotient stack of its self-intersection (Stacks 06QG, part (1))

Let `π : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of `S`
which makes `𝒳` a gerbe over `𝒴` in the sense of Stacks 06P2, let `x : 𝒴 ⟶ 𝒳` be a *section* of
`π`, that is a 1-morphism together with a 2-isomorphism `x ≫ π ≅ 𝟙 𝒴`, and let `𝒳` be an
algebraic stack whose source `𝒴` is representable by an algebraic space `U`, so that the
self-intersection `ℛ = 𝒰 ×_{x, 𝒳, x} 𝒰` is representable by an algebraic space `R` (Stacks
04T4 (1)). Stacks 04T4 (4) and (5) build from these data a groupoid in algebraic spaces `R ⇉ U`
and a canonical 1-morphism `x_can : [U/R] ⟶ 𝒳` out of its quotient stack. **Part (1) of
Stacks 06QG is that `x_can` is an equivalence, and that the groupoid is the one of a group
algebraic space acting trivially on `U`.** This file proves that `x_can` is an equivalence and
that the groupoid's source equals its target; the group packaging, and with it the whole of
Stacks 06QG, is assembled in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack`.

## Main results

All names are in the namespace `AlgebraicGeometry.Stack`.

* `locallyEssSurjOnFibers_of_section_of_isGerbeOver`: a section of a gerbe is locally essentially
  surjective on fibres — the fibre-level form of Stacks 06P1 (2) for a section, and the input
  Stacks 046N consumes.
* `SelfIntersection.locallyEssSurjOnFibers_canonicalMap_of_locallyEssSurjOnFibers`:
  local essential surjectivity on fibres transports from a 1-morphism `x` to the canonical
  1-morphism of the presentation datum of Stacks 04T4 (4) and (5).
* `SelfIntersection.relationSourceMap_eq_relationTargetMap` and
  `.source_eq_target_selfIntersectionPresentation`: **Stacks 06QG, part (1)**, the triviality of
  the action — the source and the target of the self-intersection groupoid of a section of a
  gerbe are one and the same morphism `R ⟶ U`.
* `SelfIntersection.nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver`:
  **Stacks 06QG, part (1)**, the canonical 1-morphism `x_can : [U/R] ⟶ 𝒳` is an equivalence
  over the big fppf site of `S`.

## Implementation notes

**The equivalence.** The route is the source's. Full faithfulness of `x_can` is Stacks 04T4 (6),
`AlgebraicGeometry.Stack.SelfIntersection.nonempty_fullyFaithful_canonicalMap`, and needs no
hypothesis beyond the presentation data; what the gerbe hypothesis buys is essential
surjectivity, through Stacks 046N. The source gets it from Stacks 06P1 (2)(a); the argument runs
on (2)(b) instead, exactly as in the surjectivity clause
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_of_section_of_isGerbeOver`: given an object `ξ` of
`𝒳` over `T`, the section provides a vertical comparison `b : π (x (π ξ)) ⟶ π ξ` of the two
objects `x (π ξ)` and `ξ`, namely the component of the 2-isomorphism at `π ξ`, and Stacks
06P1 (2)(b) then produces a covering sieve of `T` along each member `g : V ⟶ T` of which `ξ` is,
after restriction, isomorphic to the `x`-image of an object of `𝒴` over `V`. Since every morphism
of a category fibred in groupoids is strongly cartesian, that comparison and the chosen pullback
of `ξ` along `g` are two cartesian lifts of one morphism, so they are isomorphic in the fibre over
`V`, which is what `CategoryTheory.Functor.LocallyEssSurjOnFibers` asks for.

The transport of that statement along the presentation is the same calculation as in
`AlgebraicGeometry.Stack.SelfIntersection.locallyEssSurjOnFibers_canonicalMap`, and simpler: that
one takes a *single* covering morphism and has to base change the lift along the factorisation of
a member of the sieve it generates, whereas here a lift is given over each member of the covering
sieve already, so only the vertical comparison of the presentation datum with `x` is needed. The
two are not interchangeable — the gerbe condition supplies a covering sieve, not a single
covering morphism — which is why both exist.

**The trivial action.** The source argues that `R → U × U` factors through the diagonal because it
factors through `U ×_U U = U`. Here that is read on sections: a section of `R` over `W` is named by
an object `r` of the self-intersection over `W`, a triple `(r.x, r.y, r.iso)` with
`r.iso : x (r.x) ≅ x (r.y)` vertical, and the source and target morphisms send it to the sections
named by `r.y` and by `r.x` (`relationSourceMap_sectionOfObj` and
`relationTargetMap_sectionOfObj`). Applying `π` to `r.iso` and conjugating by the 2-isomorphism of
the section gives a vertical morphism `r.y ⟶ r.x` of `𝒴`, and the fibres of the category of
elements of a presheaf of sets are discrete, so the two sections named are equal
(`CategoryTheory.PresheafOfCategories.sectionOfObj_eq_of_hom`). This is the reason `R = G` with `G`
a *group* algebraic space over `U` rather than merely a groupoid.

**How part (1) reaches the source's formulation.** The source states the equivalence at the
quotient stack `[U/G]` of the trivial action of `G = Isom_𝒳(x, x)` on `U`, with `G` a group
algebraic space over `U`. The equivalence is stated here at the quotient stack of the
self-intersection groupoid of Stacks 04T4 (4), whose arrow space is the representing space of
`𝒰 ×_{x, 𝒳, x} 𝒰` — the same object, before the group packaging — together with the statement
that its source and target coincide.

The packaging is supplied in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack`. The group law is the one
**Stacks 0447** puts on the stabilizer of a groupoid in algebraic spaces,
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer`, which for a groupoid with equal source
and target is all of the arrow space
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizerArrowIso`), and whose multiplication is
groupoid composition — composition of automorphisms of `x`, by Stacks 04T4 (4) — by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.stabilizer_mul_comp_arrow`. The groupoid of the
trivial action of that group on `U` is the self-intersection groupoid itself
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso`), and a quotient stack only
depends on a groupoid through its underlying groupoid in presheaves, so the equivalence proved
here transports.

The identification of the arrow object with `Isom_𝒳(x, x)` is
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_relation_isomSpaceOverSpace`
(`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomSelfIntersection`), which makes
`𝒰 ×_{x, 𝒳, x} 𝒰` equivalent over the big fppf site of `S` to the category of elements of the
presheaf `AlgebraicGeometry.Stack.isomSpaceOverSpace`, which is `Isom_𝒳(x, x)` written out on
sections; its object-level input is the same triviality as
`relationSourceMap_eq_relationTargetMap` below. Over the object space it is the explicit
comparison `AlgebraicGeometry.Stack.isomSpaceToRelationSpace` of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomProjection`, and that presheaf is an
algebraic space by
`AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicSpace_isomSpaceOverSpace_of_section`.

The group law of **Stacks 04YP**, `AlgebraicGeometry.Stack.isomSpaceOverGrpObj`, is over a base
*in the site* and plays no part in any of this.

## References

* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 046N](https://stacks.math.columbia.edu/tag/046N)
* [Stacks Project, Tag 04YP](https://stacks.math.columbia.edu/tag/04YP)
* [Stacks Project, Tag 06P1](https://stacks.math.columbia.edu/tag/06P1)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **A section of a gerbe is locally essentially surjective on fibres.** Let `π : 𝒳 ⟶ 𝒴` make
`𝒳` a gerbe over `𝒴` and let `x : 𝒴 ⟶ 𝒳` be a section of `π`. Then every object of a fibre of
`𝒳` is, locally on the base, isomorphic in that fibre to the `x`-image of an object of a fibre
of `𝒴`.

This is the fibre-level form of the surjectivity clause of Stacks 06QG part (3), and it is the
hypothesis Stacks 046N consumes on the way to the equivalence of part (1). -/
theorem locallyEssSurjOnFibers_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ 𝒴) (x : 𝒴 ⟶ 𝒳) (hx : x ≫ π ≅ 𝟙 𝒴)
    (hπ : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor π)) :
    Functor.LocallyEssSurjOnFibers 𝒳.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p x) (BigFppfOver.topology B S hS) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro V y
  obtain ⟨ξ, hξ⟩ := y
  have hTy : 𝒴.val.p.obj (π.hom.toFunctor.obj ξ) = V := (BasedFunctor.w_obj π.hom ξ).trans hξ
  subst hTy
  -- The section compares `x (π ξ)` with `ξ` over the base.
  have hb := hx.hom.hom.isHomLift' (π.hom.toFunctor.obj ξ)
  obtain ⟨R, hR, hcov⟩ := hπ.locally_full _ hb
  refine ⟨R, hR, ?_⟩
  intro V' g hg
  obtain ⟨a₁, a₁', e₁, e₁', a, h₁, h₂, h₃, -⟩ := hcov g hg
  have he₁ : 𝒳.val.p.IsHomLift g e₁ := by
    rw [← CatFiberedInGroupoids.homFunctor_comp_p π]; exact h₁
  have he₁' : 𝒳.val.p.IsHomLift g e₁' := by
    rw [← CatFiberedInGroupoids.homFunctor_comp_p π]; exact h₂
  have ha : 𝒳.val.p.IsHomLift (𝟙 V') a := by
    rw [← CatFiberedInGroupoids.homFunctor_comp_p π]; exact h₃
  -- A cartesian lift of `g` in `𝒴`, carried into `𝒳` by the section.
  obtain ⟨u, φ, hφ⟩ := 𝒴.isFiberedInGroupoids.exists_lift g (π.hom.toFunctor.obj ξ) rfl
  have hxφ : 𝒳.val.p.IsHomLift g (x.hom.toFunctor.map φ) := inferInstance
  have hcart : 𝒳.val.p.IsStronglyCartesian g e₁ :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift g e₁
  set θ := Functor.IsStronglyCartesian.map 𝒳.val.p g e₁ (Category.id_comp g).symm
      (x.hom.toFunctor.map φ) ≫ a ≫ e₁' with hθdef
  have hθ : 𝒳.val.p.IsHomLift g θ := inferInstance
  have hθcart : 𝒳.val.p.IsStronglyCartesian g θ :=
    𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift g θ
  refine ⟨⟨u, IsHomLift.domain_eq 𝒴.val.p g φ⟩, ⟨?_⟩⟩
  exact (Functor.fiberIsoOfCartesian g (IsPreFibered.pullbackMap hξ g) θ
    (IsPreFibered.pullbackMap.IsCartesian hξ g)
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian 𝒳.val.p g θ)).symm

namespace SelfIntersection

variable {x : 𝒴 ⟶ 𝒳}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒴.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒴 𝒳 x.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- **The canonical 1-morphism of the presentation datum of Stacks 04T4 (4) and (5) is locally
essentially surjective on fibres** as soon as `x` is.

The lift is transported along the presentation: an object of a fibre of `𝒴` over a member of the
covering sieve is read through the chosen equivalence of `𝒴` with the fibred category of the
object space, then through the canonical projection of Stacks 044R to the quotient stack, where
the comparison of the composite with `x` supplied by the presentation datum — which is vertical
over the site — identifies its image under the canonical 1-morphism with the object `x` produces.

This is the sieve-indexed companion of
`AlgebraicGeometry.Stack.SelfIntersection.locallyEssSurjOnFibers_canonicalMap`, which asks
instead for a single covering morphism; neither implies the other, and a gerbe supplies a
covering sieve. -/
theorem locallyEssSurjOnFibers_canonicalMap_of_locallyEssSurjOnFibers
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hloc : Functor.LocallyEssSurjOnFibers 𝒳.isFiberedInGroupoids.isFibered
      (CatFiberedInGroupoids.homFunctor_comp_p x) (BigFppfOver.topology B S hS)) :
    Functor.LocallyEssSurjOnFibers 𝒳.isFiberedInGroupoids.isFibered
      (selfIntersectionPresentation eU eR h𝒳).canonicalMap.w
      (BigFppfOver.topology B S hS) := by
  classical
  let P := selfIntersectionPresentation eU eR h𝒳
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hFmor := 𝒳.isFiberedInGroupoids.isFibredOneMorphism P.canonicalMap.w
  let pU := 𝒴.val.p
  let pX := 𝒳.val.p
  let pQ := (Stack.quotientStack P.groupoid).p
  let pObj := (Stack.fibredCategory B S hS P.groupoid.objects.obj).val.p
  let proj := Stack.quotientStackProjection P.groupoid
  let hSP := P.sourcePresentation.hom.w
  let hProj := proj.w
  intro V y
  obtain ⟨Rs, hRs, hmem⟩ := hloc V y
  refine ⟨Rs, hRs, ?_⟩
  intro V' g hg
  obtain ⟨z, ⟨eX⟩⟩ := hmem g hg
  let hSPobj := congrArg (fun G => G.obj z.1) hSP
  let zObj : pObj.Fiber V' := Fiber.mk (hSPobj.trans z.2)
  let hProjobj := congrArg (fun G => G.obj zObj.1) hProj
  let zQ : pQ.Fiber V' := Fiber.mk (hProjobj.trans zObj.2)
  let zH := (Fiber.mapOfComp pQ pX P.canonicalMap.toFunctor hFmor.comp_eq V').obj zQ
  let zF := (Functor.fiberFunctorOfCompEq (CatFiberedInGroupoids.homFunctor_comp_p x) V').obj z
  let α := P.extends_f.1.app z.1
  have hα : pX.IsHomLift (𝟙 V') α.hom := by
    have h := P.extends_f.2 z.1
    rwa [z.2] at h
  let eExt : zH ≅ zF := Fiber.isoMk (p := pX) α hα
  refine ⟨zQ, ⟨?_⟩⟩
  simpa [zQ, zObj, zH, zF] using (eExt ≪≫ eX)

/-- **Stacks 06QG, part (1): the action is trivial.** The source and the target morphism
`R ⟶ U` of the self-intersection groupoid of a section of a gerbe are the same morphism, which
is the content of the source's remark that `R → U × U` factors through the diagonal of `U`.
It is what makes that groupoid the groupoid of a group algebraic space acting trivially.

Only the section is used: the gerbe hypothesis plays no part. -/
theorem relationSourceMap_eq_relationTargetMap (π : 𝒳 ⟶ 𝒴) (hx : x ≫ π ≅ 𝟙 𝒴) :
    relationSourceMap eU eR = relationTargetMap eU eR := by
  refine natTrans_eq_of_forall_sectionOfObj B S hS _ _ _ eR _ _ ?_
  intro r W h
  rw [relationSourceMap_sectionOfObj eU eR r h, relationTargetMap_sectionOfObj eU eR r h]
  have hyW : 𝒴.val.p.obj r.y = W := relation_obj_y h
  have hxW : 𝒴.val.p.obj r.x = W := relation_obj_x h
  have hbW : r.base = W := h
  have hv := r.vertical
  have h1 : 𝒴.val.p.IsHomLift (𝟙 W) (hx.inv.hom.toNatTrans.app r.y) := by
    have hi := CatFiberedInGroupoids.isHomLift_app hx.inv r.y
    rw [hyW] at hi; exact hi
  have h3 : 𝒴.val.p.IsHomLift (𝟙 W) (hx.hom.hom.toNatTrans.app r.x) := by
    have hi := CatFiberedInGroupoids.isHomLift_app hx.hom r.x
    rw [hxW] at hi; exact hi
  have h2' : 𝒳.val.p.IsHomLift (𝟙 W) r.iso.inv := by
    rw [← hbW]; infer_instance
  have h2 : 𝒴.val.p.IsHomLift (𝟙 W) (π.hom.toFunctor.map r.iso.inv) :=
    (Functor.isHomLift_comp_iff (CatFiberedInGroupoids.homFunctor π) 𝒴.val.p (𝟙 W)
      r.iso.inv).1 (by rw [CatFiberedInGroupoids.homFunctor_comp_p π]; exact h2')
  have hπy : 𝒴.val.p.obj (π.hom.toFunctor.obj (x.hom.toFunctor.obj r.y)) = W :=
    (BasedFunctor.w_obj π.hom _).trans ((BasedFunctor.w_obj x.hom r.y).trans hyW)
  have hπx : 𝒴.val.p.obj (π.hom.toFunctor.obj (x.hom.toFunctor.obj r.x)) = W :=
    (BasedFunctor.w_obj π.hom _).trans ((BasedFunctor.w_obj x.hom r.x).trans hxW)
  -- The three vertical morphisms, composed in the fibre of `𝒴` over `W`.
  let m1 : (Functor.Fiber.mk hyW : 𝒴.val.p.Fiber W) ⟶ Functor.Fiber.mk hπy :=
    ⟨hx.inv.hom.toNatTrans.app r.y, h1⟩
  let m2 : (Functor.Fiber.mk hπy : 𝒴.val.p.Fiber W) ⟶ Functor.Fiber.mk hπx :=
    ⟨π.hom.toFunctor.map r.iso.inv, h2⟩
  let m3 : (Functor.Fiber.mk hπx : 𝒴.val.p.Fiber W) ⟶ Functor.Fiber.mk hxW :=
    ⟨hx.hom.hom.toNatTrans.app r.x, h3⟩
  exact PresheafOfCategories.sectionOfObj_eq_of_hom eU hyW hxW
    (m1 ≫ m2 ≫ m3).1 (m1 ≫ m2 ≫ m3).2

/-- **Stacks 06QG, part (1): the action is trivial**, read on the presentation datum of
Stacks 04T4 (4) and (5): the groupoid in algebraic spaces it builds from a section of a gerbe has
one and the same source and target, so it is the groupoid of a group algebraic space acting
trivially on the object space. -/
@[stacks 06QG "part (1): the self-intersection groupoid of a section of a gerbe has equal source \
and target, so the group algebraic space of part (1) acts trivially"]
theorem source_eq_target_selfIntersectionPresentation
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (π : 𝒳 ⟶ 𝒴) (hx : x ≫ π ≅ 𝟙 𝒴) :
    (selfIntersectionPresentation eU eR h𝒳).groupoid.source =
      (selfIntersectionPresentation eU eR h𝒳).groupoid.target := by
  show (ObjectProperty.homMk (relationSourceMap eU eR) : R ⟶ U) =
    ObjectProperty.homMk (relationTargetMap eU eR)
  rw [relationSourceMap_eq_relationTargetMap eU eR π hx]

/-- **Stacks 06QG, part (1): the canonical equivalence.** Let `𝒳` be an algebraic stack over `S`,
let `π : 𝒳 ⟶ 𝒴` make `𝒳` a gerbe over `𝒴`, let `x : 𝒴 ⟶ 𝒳` be a section of `π`, let `𝒴` be
represented by an algebraic space `U` and let the self-intersection `𝒴 ×_{x, 𝒳, x} 𝒴` be
represented by an algebraic space `R` — which it is, by Stacks 04T4 (1). Then the canonical
1-morphism `x_can : [U/R] ⟶ 𝒳` of the presentation datum of Stacks 04T4 (4) and (5) is an
equivalence over the big fppf site of `S`.

Full faithfulness is Stacks 04T4 (6) and needs no hypothesis beyond the presentation data;
essential surjectivity on each fibre is the local essential surjectivity of the section, glued by
effective descent in the quotient stack against the `Mor`-sheaf condition on `𝒳`, and a
1-morphism of fibred categories which is fully faithful and essentially surjective on every fibre
is an equivalence over the site.

The source states the equivalence at the quotient stack of the trivial action of
`G = Isom_𝒳(x, x)`. That is this equivalence: the self-intersection groupoid has equal source and
target (`source_eq_target_selfIntersectionPresentation`), hence is the groupoid of the trivial
action of its stabilizer group of **Stacks 0447** on the object space, and that stabilizer is
`Isom_𝒳(x, x)` over the object space. The passage is
`exists_grpObj_nonempty_equivalenceOver_quotientStackOfAction_of_section_of_isGerbeOver`, in the
namespace `AlgebraicGeometry.Stack.AlgebraicStacks` of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack`, where the whole of Stacks 06QG
is assembled. -/
@[stacks 06QG "part (1): the canonical 1-morphism out of the quotient stack of the \
self-intersection groupoid is an equivalence"]
theorem nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) (π : 𝒳 ⟶ 𝒴) (hx : x ≫ π ≅ 𝟙 𝒴)
    (hπ : CategoryTheory.IsGerbeOver (BigFppfOver.topology B S hS) 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor π)) :
    Nonempty (Functor.IsEquivalenceOver
      (Stack.quotientStack (selfIntersectionPresentation eU eR h𝒳).groupoid).p
      𝒳.val.p
      (selfIntersectionPresentation eU eR h𝒳).canonicalMap.toFunctor) := by
  classical
  let P := selfIntersectionPresentation eU eR h𝒳
  have hFF : P.canonicalMap.toFunctor.FullyFaithful :=
    Classical.choice (nonempty_fullyFaithful_canonicalMap eU eR h𝒳)
  have h𝒳' := h𝒳
  rcases h𝒳' with ⟨h𝒳fiber, h𝒳stack, -, -⟩
  have : 𝒳.val.p.IsFibered := h𝒳fiber.isFibered
  have hFbase : P.canonicalMap.toFunctor ⋙ 𝒳.val.p =
      (Stack.quotientStack P.groupoid).p := P.canonicalMap.w
  have hFmor : (Stack.quotientStack P.groupoid).p.IsFibredOneMorphism
      𝒳.val.p P.canonicalMap.toFunctor := h𝒳fiber.isFibredOneMorphism hFbase
  have : P.canonicalMap.toFunctor.Full := ⟨fun g => ⟨hFF.preimage g, hFF.map_preimage g⟩⟩
  have : P.canonicalMap.toFunctor.Faithful := ⟨by
    intro X Y g g' h
    calc
      g = hFF.preimage (P.canonicalMap.toFunctor.map g) := (hFF.preimage_map g).symm
      _ = hFF.preimage (P.canonicalMap.toFunctor.map g') := congrArg hFF.preimage h
      _ = g' := hFF.preimage_map g'⟩
  have hLoc := locallyEssSurjOnFibers_canonicalMap_of_locallyEssSurjOnFibers eU eR h𝒳
    (locallyEssSurjOnFibers_of_section_of_isGerbeOver π x hx hπ)
  have hess : ∀ V : BigFppfOver B S hS,
      (Fiber.mapOfComp (Stack.quotientStack P.groupoid).p 𝒳.val.p
        P.canonicalMap.toFunctor hFmor.comp_eq V).EssSurj := by
    intro V
    refine ⟨fun y => ?_⟩
    obtain ⟨RS, hRS, hRSess⟩ := hLoc V y
    exact Functor.exists_iso_of_locally_essImage hFmor
      (Stack.isStack_quotientStack P.groupoid).hasEffectiveDescent
      (h𝒳stack.1.isMorSheaf V) y hRS hRSess
  exact ⟨Functor.isEquivalenceOver_of_exists_vertical_iso hFbase
    (Functor.exists_vertical_iso_of_fiber_essSurj hFbase hess)⟩

end SelfIntersection

end AlgebraicGeometry.Stack

end
