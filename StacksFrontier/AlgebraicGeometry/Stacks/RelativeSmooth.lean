module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertySpaceBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityComp

/-!
# Smooth representable 1-morphisms of stacks

Following Stacks 04XB, a 1-morphism `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big
fppf site of `S` which is representable by algebraic spaces *is smooth* when every algebraic
space representing the base change of `f` along a scheme-valued point of `𝒴` has smooth
structural morphism — that is, when `f` has the relative property of **Stacks 03YK** at
`AlgebraicGeometry.Space.smoothMorphismProperty`.

`AlgebraicGeometry.Stack.HasRelativeProperty` is stated for a
`CategoryTheory.MorphismProperty` on the category of algebraic spaces over `S` carrying two
instance hypotheses: stability under base change and locality at the target for the fppf
precoverage of Stacks 03YH. For smoothness **both are discharged by results in the library** —
`AlgebraicGeometry.Space.instIsStableUnderBaseChangeSmoothMorphismProperty` (Stacks 03ZE) and
`AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf` (Stacks 0429 at the fppf precoverage, got
from its fpqc form through `AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`) — so
the predicate below needs no hypothesis on the property and no written-out substitute, unlike
`AlgebraicGeometry.Stack.IsImmersion` and the predicates of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism`, whose properties still lack the
locality instance.

That is also what makes the four lemmas below available. Each is one of the general
relative-property results — Stacks 045B, 045C, 045D, 04XC — read at the smooth property, and
each needs its fppf-locality instance, which would otherwise have to be supplied by hand.

## Main definitions

* `AlgebraicGeometry.Stack.IsRelativelySmooth`: smoothness of a 1-morphism representable by
  algebraic spaces, in the sense of Stacks 04XB.

## Main results

* `AlgebraicGeometry.Stack.isRelativelySmooth_comp`: Stacks 045B at the smooth property.
* `AlgebraicGeometry.Stack.isRelativelySmooth_baseChange`: Stacks 045C at the smooth property.
* `AlgebraicGeometry.Stack.isRelativelySmooth_of_baseChange`: Stacks 045D at the smooth
  property.
* `AlgebraicGeometry.Stack.isRelativelySmooth_iff_forall_space_baseChange`: Stacks 04XC at the
  smooth property.

## Implementation notes

No declaration here carries a `@[stacks]` attribute, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMorphism`: Stacks 04XB introduces its notion for
*every* property of morphisms of algebraic spaces which is stable under base change and local at
the target, that general notion is already tagged as
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**), and the five declarations below
are its instance, and the instances of four already-tagged lemmas, at one specific property.
Tagging them would claim tags their general forms already cover.

The representability witness is bundled into the predicate as an existential, as the statement
of Stacks 06FM does: the witness argument of
`AlgebraicGeometry.Stack.HasRelativeProperty` is inert — `HasRelativeProperty B S hS P f h₁` and
`HasRelativeProperty B S hS P f h₂` are the same proposition by `rfl` — so bundling loses
nothing and lets a consumer apply the predicate without carrying the witness separately.

The universes follow the lemma being instantiated, and they differ: Stacks 045B and 04XC hold at
unconstrained universes, while Stacks 045C and 045D need the saturation
`CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}` of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` (Stacks 0302), which is
what produces the representability witness of the projection. Stacks 045D additionally needs the
locality instance at index universe `u`; that is the weakest member of the family, and it is
available here because `AlgebraicGeometry.Space.smooth_isLocalAtTarget_fppf` is universe
polymorphic in the index universe.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XC](https://stacks.math.columbia.edu/tag/04XC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` *is smooth*
when it is representable by algebraic spaces and every algebraic space representing its base
change along a scheme-valued point of the target has smooth structural morphism, read as a
morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB at
`AlgebraicGeometry.Space.smoothMorphismProperty`, i.e. the relative property of Stacks 03YK
there; both instance hypotheses of that definition are discharged for smoothness, so this
carries no hypothesis on the property. -/
abbrev IsRelativelySmooth
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ hf : IsRepresentableByAlgebraicSpaces B S hS f.hom,
    HasRelativeProperty.{u, v, w, u} B S hS (Space.smoothMorphismProperty B S hS) f hf

/-- **Stacks 045B** at the smooth property: the composite of two smooth 1-morphisms of
categories fibred in groupoids over the big fppf site of `S` is smooth. Representability of the
composite is Stacks 0301 and stability of smoothness under composition is Stacks 03ZD. -/
theorem isRelativelySmooth_comp
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒴 ⟶ 𝒵)
    (hf : IsRelativelySmooth B S hS f) (hg : IsRelativelySmooth B S hS g) :
    IsRelativelySmooth B S hS (f ≫ g) := by
  obtain ⟨hfr, hPf⟩ := hf
  obtain ⟨hgr, hPg⟩ := hg
  exact ⟨isRepresentableByAlgebraicSpaces_comp B S hS f g hfr hgr,
    hasRelativeProperty_comp.{u, v, w, u} B S hS (Space.smoothMorphismProperty B S hS)
      f g hfr hgr hPf hPg⟩

/-- **Stacks 045C** at the smooth property: in a 2-fibre product square over a cospan
`g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴`, the projection to `𝒵` is smooth as soon as `f` is. -/
theorem isRelativelySmooth_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f) (hR : Bicategory.IsTwoFibreProduct R)
    (hf : IsRelativelySmooth B S hS f) :
    IsRelativelySmooth B S hS R.fst := by
  obtain ⟨hfr, hPf⟩ := hf
  exact ⟨isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR hfr,
    hasRelativeProperty_baseChange.{u, v, w, u} B S hS
      (Space.smoothMorphismProperty B S hS) 𝒳 𝒴 𝒵 f g R hR hfr hPf⟩

/-- **Stacks 045D** at the smooth property: a 1-morphism representable by algebraic spaces is
smooth as soon as one of its base changes is, along a 1-morphism `g : 𝒵 ⟶ 𝒴` for which every
object of a fibre of `𝒴` becomes, after restriction to a covering sieve, isomorphic to the image
of an object of `𝒵`. -/
theorem isRelativelySmooth_of_baseChange
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (D : Bicategory.TwoCommSq g f) (hD : Bicategory.IsTwoFibreProduct D)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom)
    (hg : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒵.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor g).obj z ⟶ y.1,
            𝒴.val.p.IsHomLift k φ)
    (hP : IsRelativelySmooth B S hS D.fst) :
    IsRelativelySmooth B S hS f := by
  obtain ⟨_, hPfst⟩ := hP
  exact ⟨hf, hasRelativeProperty_of_baseChange.{u, v, w, u} B S hS 𝒳 𝒴 𝒵
    (Space.smoothMorphismProperty B S hS) f g D hD hf hg hPfst⟩

/-- **Stacks 04XC** at the smooth property: a 1-morphism representable by algebraic spaces is
smooth exactly when, for every 2-fibre product square over a 1-morphism out of a stack
representable by an algebraic space, the morphism of representing presheaves induced by the
first projection is a smooth morphism of algebraic spaces over `S`. -/
theorem isRelativelySmooth_iff_forall_space_baseChange
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    IsRelativelySmooth B S hS f ↔
      ∀ (𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
        (_h𝒵 : IsRepresentableByAlgebraicSpace B S hS 𝒵)
        (g : 𝒵 ⟶ 𝒴) (Q : Bicategory.TwoCommSq g f)
        (_hQ : Bicategory.IsTwoFibreProduct Q)
        (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
        (eF : StacksRepresentableCFG.EquivalenceOver
          Q.pt.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
        (eG : StacksRepresentableCFG.EquivalenceOver
          𝒵.val.p (presheafOfCategories (G ⋙ typeToCat)).p),
        Space.smoothMorphismProperty B S hS
          (ObjectProperty.homMk (representingMap B S hS Q.pt 𝒵 F G eF eG Q.fst) :
            (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ (⟨G, hG⟩ : AlgebraicSpaces B S hS)) := by
  have e := hasRelativeProperty_iff_forall_space_baseChange.{u, u} B S hS
    (Space.smoothMorphismProperty B S hS) f hf
  exact ⟨fun ⟨_, hP⟩ ↦ e.1 hP, fun h ↦ ⟨hf, e.2 h⟩⟩

end AlgebraicGeometry.Stack

end
