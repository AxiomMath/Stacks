module

public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.MorphismSpaceSections
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoid

/-!
# The automorphism sheaf is the arrow space of the self-intersection, over `Z`

Let `𝒳` be an algebraic stack over `S`, let `Z` be an algebraic space over `S`, write `𝒰 = 𝒮_Z`
for the algebraic stack of `Z` and let `x : 𝒰 ⟶ 𝒳` be an algebraic-space-valued point of `𝒳`. Let
`R` be a chosen algebraic space representing the self-intersection `ℛ = 𝒰 ×_{x, 𝒳, x} 𝒰` — one
exists by Stacks 04T4 (1) — through an equivalence `eR` over the big fppf site of `S`.

`AlgebraicGeometry.Stack.nonempty_equivalenceOver_relation_isomSpaceOverSpace` identifies `ℛ`
with the category of elements of the presheaf `Isom_𝒳(x, x)` of Stacks 06PP, written out on
sections as `AlgebraicGeometry.Stack.isomSpaceOverSpace`. **This file reads that identification
on the chosen representing space**: it builds the comparison

```text
Isom_𝒳(x, x) ⟶ R
```

of presheaves on the big fppf site of `S`, shows that it is an isomorphism, and — this is the
point — shows that it is a comparison **over `Z`**: composed with the source morphism `s : R ⟶ Z`
of the self-intersection groupoid of Stacks 04T4 (4) it is the structure morphism
`Isom_𝒳(x, x) ⟶ Z` of Stacks 06PP, which forgets the automorphism and keeps the point.

That last statement is what makes `R ⇉ Z` the groupoid of the automorphism sheaf of `x` *over
`Z`*, and it is the step in the proof of Stacks 06QG which identifies the arrow space of the
presentation groupoid with the object `G = Isom_𝒳(x, x)` of Stacks 06PP sitting over the object
space.

## Main definitions

* `AlgebraicGeometry.Stack.algebraicSpaceStackTautologicalPresentation`: the tautological
  presentation of the algebraic stack of `Z` by `Z` itself, that is the identity equivalence
  exhibited by Stacks 04SV
  (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory`), named so that it can
  be handed to the structure morphisms of the self-intersection groupoid.
* `AlgebraicGeometry.Stack.isomSpaceToRelationSpace`: **the comparison on sections.** An
  automorphism `φ` of `x(z)` over `W` names the arrow `(z, z, φ)` of the self-intersection
  (`AlgebraicGeometry.Stack.isomToRelation`), hence a section of `R` over `W`. It is the morphism
  of representing presheaves that the comparison 1-morphism induces through the bijection of
  Stacks 04SW, so it is a morphism of presheaves by construction.

## Main results

* `AlgebraicGeometry.Stack.isomSpaceToRelationSpace_app`: the value of the comparison on a
  section, which is the only computation rule the results below use.
* `AlgebraicGeometry.Stack.isomSection_eq_of_isomSpaceToRelationSpace_app_eq`: the comparison is
  injective on the sections over every object of the site. **No hypothesis on `x` is used**: two
  sections with the same image name two arrows of `ℛ` lying in one fibre and naming one section
  of `R`, hence isomorphic in that fibre
  (`CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq`), and fullness of the
  comparison 1-morphism turns that isomorphism into a *vertical* morphism of the category of
  elements of `Isom_𝒳(x, x)`, whose fibre component is an equality of the two sections.
* `AlgebraicGeometry.Stack.exists_isomSection_isomSpaceToRelationSpace_app_eq` and
  `AlgebraicGeometry.Stack.isIso_isomSpaceToRelationSpace`: for a *section* `x` of a 1-morphism
  `π : 𝒳 ⟶ 𝒰` the comparison is surjective on sections as well, hence an isomorphism of
  presheaves. Surjectivity is where the section enters: every section of `R` is named by an arrow
  of `ℛ` (`CategoryTheory.PresheafOfCategories.exists_sectionOfObj`), and for a section every
  arrow of `ℛ` *is* an automorphism of `x` at a point of `Z`
  (`AlgebraicGeometry.Stack.exists_eq_isomToRelation_obj`).
* `AlgebraicGeometry.Stack.isomSpaceToRelationSpace_comp_relationSourceMap`: **the comparison is
  over the object space.** Composed with the source morphism of the self-intersection groupoid of
  Stacks 04T4 (4), taken at the tautological presentation of `𝒰` by `Z`, it is the canonical
  projection `Isom_𝒳(x, x) ⟶ Z`. **No hypothesis on `x` is used here either.**

## Implementation notes

The comparison is *defined* through the bijection of Stacks 04SW
(`AlgebraicGeometry.Stack.morphismSpaceEquiv`) applied to the 1-morphism
`AlgebraicGeometry.Stack.isomToRelation`, with the tautological equivalence on the source and the
given `eR` on the target, rather than written out as a natural transformation. That is what makes
naturality free: the only thing left to say about it is its value on a named section, and
`AlgebraicGeometry.Stack.morphismSpaceEquiv_app_sectionOfObj` supplies that in one step. Every
result below follows from that single computation rule together with the properties of naming a
section collected in `StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection`.

The triangle is stated with `AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap` at the
*tautological* presentation of `𝒰 = 𝒮_Z` by `Z`, which is what makes its right-hand side the
honest projection `AlgebraicGeometry.Stack.isomSpaceOverSpaceProj` rather than that projection
transported along some other presentation of `Z`. Once a section is available the source morphism
agrees with the target morphism, by
`AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap_eq_relationTargetMap`, so the same
triangle then holds for the target morphism too; the form proved here needs no section.

**What this still does not give.** This is an identification of presheaves over `Z`, not of group
algebraic spaces: the group law that Stacks 06PP puts on `Isom_𝒳(x, x)` over an algebraic space
base is absent from the library, as recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/AutomorphismSpaceOverAlgebraicSpace.lean` and of
`StacksFrontier/AlgebraicGeometry/Stacks/GerbeSectionQuotientPresentation.lean`. What the comparison
built here adds to those notes is the missing link on the arrow object: `R`, the representing
space whose two structure morphisms Stacks 04T4 (4) uses, is identified with `Isom_𝒳(x, x)`
compatibly with the maps to `Z`, so the composition law
`AlgebraicGeometry.Stack.SelfIntersection.compositionLaw` can be transported to a group law on
`Isom_𝒳(x, x)` over `Z` when that is wanted. Nothing here claims that `Isom_𝒳(x, x)` is itself an
algebraic space; what is used is that the *representing space* `R` of `ℛ` is one, which is a
hypothesis in the shape of `eR`.

No Stacks tag is registered: this is a step inside the proof of Stacks 06QG, not the statement of
a tag.

## References

* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The tautological presentation of the algebraic stack of an algebraic space `Z` by `Z`
itself.** The category of elements of `Z` *is* the category of elements of `Z`, so the comparison
is the identity equivalence over the big fppf site of `S`. This is the equivalence that
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fibredCategory` exhibits, named so that
it can be handed to the structure morphisms of the self-intersection groupoid of
Stacks 04T4 (4). -/
def algebraicSpaceStackTautologicalPresentation :
    StacksRepresentableCFG.EquivalenceOver
      (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.p
      (presheafOfCategories ((⟨Z, hZ⟩ : AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p :=
  StacksRepresentableCFG.EquivalenceOver.refl _

variable (x : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) {R : AlgebraicSpaces B S hS}
variable (eR : StacksRepresentableCFG.EquivalenceOver
  (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
    𝒳.val x.hom.hom).val.p
  (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- **The comparison on sections**: an automorphism `φ` of `x(z)` over `W` names the arrow
`(z, z, φ)` of the self-intersection `ℛ = 𝒰 ×_{x, 𝒳, x} 𝒰`, hence a section over `W` of the
algebraic space `R` representing `ℛ`.

It is the morphism of representing presheaves that the comparison 1-morphism
`AlgebraicGeometry.Stack.isomToRelation` induces through the bijection of Stacks 04SW, taken at
the tautological presentation of the category of elements of `Isom_𝒳(x, x)` by `Isom_𝒳(x, x)` and
at the given presentation `eR` of `ℛ` by `R`. -/
noncomputable def isomSpaceToRelationSpace : isomSpaceOverSpace B S hS Z hZ x x ⟶ R.obj :=
  morphismSpaceEquiv B S hS
      (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x))
      (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom)
      (isomSpaceOverSpace B S hS Z hZ x x) R.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _) eR
    (Quotient.mk _ ⟨(isomToRelation B S hS Z hZ x).toFunctor,
      (isomToRelation B S hS Z hZ x).w⟩)

/-- **The value of the comparison on a section**: the section of `R` named by the arrow of the
self-intersection that the comparison 1-morphism attaches to it. This is the only computation rule
about `AlgebraicGeometry.Stack.isomSpaceToRelationSpace` that the results below use. -/
theorem isomSpaceToRelationSpace_app (W : BigFppfOver B S hS)
    (s : isomSection B S hS Z hZ x x (op W)) :
    (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W) s =
      PresheafOfCategories.sectionOfObj eR
        ((isomToRelation B S hS Z hZ x).toFunctor.obj ⟨W, Discrete.mk s⟩) rfl :=
  morphismSpaceEquiv_app_sectionOfObj B S hS
    (fibredCategory B S hS (isomSpaceOverSpace B S hS Z hZ x x))
    (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
      𝒳.val x.hom.hom)
    (isomSpaceOverSpace B S hS Z hZ x x) R.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _) eR
    ⟨(isomToRelation B S hS Z hZ x).toFunctor, (isomToRelation B S hS Z hZ x).w⟩
    ⟨W, Discrete.mk s⟩ rfl

/-- **The comparison is injective on sections.** Two automorphisms of `x` over `W` with the same
image name two arrows of the self-intersection which lie in the fibre over `W` and name the same
section of `R`, hence are isomorphic in that fibre
(`CategoryTheory.PresheafOfCategories.fiberIsoOfSectionOfObj_eq`). Fullness of the comparison
1-morphism turns that isomorphism into a morphism of the category of elements of `Isom_𝒳(x, x)`
lying over the identity of `W`, and the fibre component of such a morphism is exactly an equality
of the two sections.

No hypothesis on `x` is used: fullness of `AlgebraicGeometry.Stack.isomToRelation` needs none. -/
theorem isomSection_eq_of_isomSpaceToRelationSpace_app_eq (W : BigFppfOver B S hS)
    (s s' : isomSection B S hS Z hZ x x (op W))
    (h : (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W) s =
      (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W) s') : s = s' := by
  rw [isomSpaceToRelationSpace_app, isomSpaceToRelationSpace_app] at h
  have i := PresheafOfCategories.fiberIsoOfSectionOfObj_eq eR
    (z := (isomToRelation B S hS Z hZ x).toFunctor.obj ⟨W, Discrete.mk s⟩)
    (z' := (isomToRelation B S hS Z hZ x).toFunctor.obj ⟨W, Discrete.mk s'⟩)
    (W := W) rfl rfl h
  obtain ⟨g, hg⟩ := (isomToRelation B S hS Z hZ x).toFunctor.map_surjective
    (Functor.Fiber.fiberInclusion.map i.hom)
  have hhb : (𝟙 W : W ⟶ W) = ((isomToRelation B S hS Z hZ x).toFunctor.map g).hbase := by
    rw [hg]
    exact @IsHomLift.eq_of_isHomLift _ _ _ _
      (SelfIntersection.relation B S hS (algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p
      ((isomToRelation B S hS Z hZ x).toFunctor.obj ⟨W, Discrete.mk s⟩)
      ((isomToRelation B S hS Z hZ x).toFunctor.obj ⟨W, Discrete.mk s'⟩)
      (𝟙 W) (Functor.Fiber.fiberInclusion.map i.hom) i.hom.2
  have hgb : g.base = 𝟙 W :=
    (isomToRelation_map_hbase B S hS Z hZ x g).symm.trans hhb.symm
  have hsec : s = (isomSpaceOverSpace B S hS Z hZ x x).map (𝟙 W).op s' := by
    rw [← hgb]
    exact isomObjSection_map B S hS Z hZ x g
  refine hsec.trans ?_
  rw [CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **The comparison is surjective on sections**, for a section `x : 𝒰 ⟶ 𝒳` of a 1-morphism
`π : 𝒳 ⟶ 𝒰`. Every section of `R` over `W` is named by an arrow of the self-intersection lying
over `W` (`CategoryTheory.PresheafOfCategories.exists_sectionOfObj`), and for a section every
arrow of the self-intersection *is* an automorphism of `x` at a point of `Z`
(`AlgebraicGeometry.Stack.exists_eq_isomToRelation_obj`). -/
theorem exists_isomSection_isomSpaceToRelationSpace_app_eq
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ))
    (W : BigFppfOver B S hS) (t : R.obj.obj (op W)) :
    ∃ s, (isomSpaceToRelationSpace B S hS Z hZ x eR).app (op W) s = t := by
  obtain ⟨r, hr, hrs⟩ := PresheafOfCategories.exists_sectionOfObj eR (W := W) t
  obtain ⟨Q, hQ⟩ := exists_eq_isomToRelation_obj B S hS Z hZ x π hx r
  subst hQ
  have hb : Q.base = W := hr
  subst hb
  exact ⟨isomObjSection B S hS Z hZ x Q,
    (isomSpaceToRelationSpace_app B S hS Z hZ x eR _ _).trans hrs⟩

/-- **`Isom_𝒳(x, x) = R` for a section `x`.** The comparison is an isomorphism of presheaves on
the big fppf site of `S`: a morphism of presheaves of sets is an isomorphism as soon as each of
its components is bijective, and the components are injective with no hypothesis and surjective
because the two ends of an arrow of the self-intersection of a section agree. -/
theorem isIso_isomSpaceToRelationSpace
    (π : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    IsIso (isomSpaceToRelationSpace B S hS Z hZ x eR) := by
  have (V : (BigFppfOver B S hS)ᵒᵖ) :
      IsIso ((isomSpaceToRelationSpace B S hS Z hZ x eR).app V) :=
    (isIso_iff_bijective _).2
      ⟨fun s s' => isomSection_eq_of_isomSpaceToRelationSpace_app_eq B S hS Z hZ x eR V.unop s s',
        exists_isomSection_isomSpaceToRelationSpace_app_eq B S hS Z hZ x eR π hx V.unop⟩
  exact NatIso.isIso_of_isIso_app _

/-- **The comparison is over the object space.** Composing it with the source morphism `s : R ⟶ Z`
of the self-intersection groupoid of Stacks 04T4 (4), taken at the tautological presentation of
`𝒰 = 𝒮_Z` by `Z`, gives the canonical projection `Isom_𝒳(x, x) ⟶ Z` of Stacks 06PP, which forgets
the automorphism and keeps the point.

Both sides send an automorphism `φ` of `x(z)` to `z`: the source morphism carries the section
named by an arrow of the self-intersection to the section named by the *source* of that arrow
(`AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap_sectionOfObj`), the source of the
arrow `(z, z, φ)` is the point `z`, and naming a section through the tautological presentation is
reading off the element (`CategoryTheory.PresheafOfCategories.sectionOfObj_refl`).

No hypothesis on `x` is used; in particular no section of a 1-morphism `𝒳 ⟶ 𝒰` is needed. With
one available the source morphism agrees with the target morphism by
`AlgebraicGeometry.Stack.SelfIntersection.relationSourceMap_eq_relationTargetMap`, so the same
triangle then holds for the target morphism as well. -/
theorem isomSpaceToRelationSpace_comp_relationSourceMap :
    isomSpaceToRelationSpace B S hS Z hZ x eR ≫
        SelfIntersection.relationSourceMap
          (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR =
      isomSpaceOverSpaceProj B S hS Z hZ x x := by
  refine Functor.presheafHom_ext fun V s => ?_
  obtain ⟨V⟩ := V
  show (SelfIntersection.relationSourceMap
        (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR).app (op V)
      ((isomSpaceToRelationSpace B S hS Z hZ x eR).app (op V) s) =
    (isomSpaceOverSpaceProj B S hS Z hZ x x).app (op V) s
  rw [isomSpaceToRelationSpace_app B S hS Z hZ x eR V s]
  exact (SelfIntersection.relationSourceMap_sectionOfObj
    (algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
    ((isomToRelation B S hS Z hZ x).toFunctor.obj ⟨V, Discrete.mk s⟩) rfl).trans
      (PresheafOfCategories.sectionOfObj_refl _)

end AlgebraicGeometry.Stack

end
