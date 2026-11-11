module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.UnitActionGroupIso
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionAutomorphismGroup
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack

/-!
# The canonical equivalence of Stacks 06QG

Let `π : 𝒳 ⟶ 𝒰` be a 1-morphism from an algebraic stack `𝒳` over `S` to the algebraic stack `𝒰`
of an algebraic space `Z` over `S`, let `x : 𝒰 ⟶ 𝒳` be a section of `π` — a 1-morphism together
with a 2-isomorphism `x ≫ π ≅ 𝟙 𝒰` — and let `π` make `𝒳` a gerbe over `𝒰`. Let
`G = Isom_𝒳(x, x)` be the group algebraic space over `Z` of **Stacks 06PP**, with composition of
automorphisms as group law. **Stacks 06QG** asserts that

1. there is a canonical equivalence of stacks in groupoids `x_can : [Z/G] ⟶ 𝒳`, where `[Z/G]` is
   the quotient stack of the *trivial* action of `G` on `Z`;
2. `G ⟶ Z` is flat and locally of finite presentation;
3. `x` is surjective, flat and locally of finite presentation.

This file defines `x_can` and proves all three.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.gerbeSectionClassifyingFunctor`: the canonical
  1-morphism `x_can : [Z/G] ⟶ 𝒳`.

## Main results

* `AlgebraicStacks.exists_equivalenceOver_gerbeSectionClassifyingFunctor_of_isGerbeOver`:
  **Stacks 06QG**.

## Implementation notes

`G` is `AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace` at `π`, the group
algebraic space `Isom_{𝒳/𝒰}(x, x)` of Stacks 06PP part (1) with its group law, composition of
automorphisms. Because `𝒰` is an algebraic space every automorphism of a point of `𝒳` is killed by
`π`, so this is `Isom_𝒳(x, x)`, the notation the last paragraph of Stacks 06PP uses when the base
is an algebraic space; the comparison with the presheaf `AlgebraicGeometry.Stack.isomSpaceOverSpace`
of all automorphisms is `AlgebraicGeometry.Stack.isIso_relativeAutomorphismToIsomSpace`.

`x_can` follows the source's proof. The source identifies the self-intersection groupoid
`R = 𝒰 ×_{x, 𝒳, x} 𝒰 ⇉ Z` of **Stacks 04T4** (4) with `G`, notes that its composition law
"agrees with the group law on `G` (proof omitted)", and takes for `x_can` the canonical 1-morphism
of Stacks 04T4 (5). Here `x_can` is the composite of three 1-morphisms:

* the 1-morphism of quotient stacks (**Stacks 046Q**) induced by the isomorphism of trivial-action
  groupoids `AlgebraicGeometry.Space.unitActionGroupoidIso` of the isomorphism of group algebraic
  spaces `AlgebraicGeometry.Stack.sectionAutomorphismStabilizerIso : G ≅ G/U` onto the stabilizer
  of `R ⇉ Z` with the group law of **Stacks 0447** — this is the omitted proof, carried out in
  `StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionAutomorphismGroup`;
* the 1-morphism of quotient stacks induced by
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso`, the identification of `R ⇉ Z`,
  whose source and target agree for a section, with the groupoid of the trivial action of its
  stabilizer;
* the canonical 1-morphism of Stacks 04T4 (5) out of the quotient stack of `R ⇉ Z`.

The algebraic space representing `𝒰 ×_{x, 𝒳, x} 𝒰` is a choice
(`AlgebraicGeometry.Stack.AlgebraicStacks.sectionRelationPresentation`), as it is in the source.

## References

* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

attribute [local instance] Space.isFlat_isLocalAtTarget_fppf
  Space.isFlat_isStableUnderBaseChange
  Space.isLocallyOfFinitePresentation_isStableUnderBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hZ : IsAlgebraicSpace B S hS Z}

/-- The algebraic space representing the self-intersection `𝒰 ×_{x, 𝒳, x} 𝒰` of a point
`x : 𝒰 ⟶ 𝒳` of an algebraic stack, which exists by **Stacks 04T4** part (1); a choice of it. -/
noncomputable def sectionRelationSpace
    (x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) : AlgebraicSpaces B S hS :=
  ⟨(SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val x.hom.hom 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)).choose,
    (SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val x.hom.hom 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)).choose_spec.1⟩

/-- The presentation of the self-intersection `𝒰 ×_{x, 𝒳, x} 𝒰` by the algebraic space
`AlgebraicGeometry.Stack.AlgebraicStacks.sectionRelationSpace`. -/
noncomputable def sectionRelationPresentation
    (x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p
      (presheafOfCategories ((sectionRelationSpace B S hS x).obj ⋙ typeToCat)).p :=
  Classical.choice
    (SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val x.hom.hom 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)).choose_spec.2

/-- The isomorphism of trivial-action groupoids over `Z` induced by the isomorphism of group
algebraic spaces `Isom_𝒳(x, x) ≅ G/U` of `AlgebraicGeometry.Stack.sectionAutomorphismStabilizerIso`,
for `Isom_𝒳(x, x)` with the group law of Stacks 06PP and the stabilizer `G/U` of the
self-intersection groupoid with the group law of Stacks 0447. -/
noncomputable def gerbeSectionUnitActionIso
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) :=
  letI : ModObj (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X
      (𝟙_ (Over Z)) := ModObj.trivialAction _ _
  letI : ModObj (Stack.sectionStabilizer B S hS Z hZ x (sectionRelationPresentation B S hS x))
      (𝟙_ (Over Z)) := ModObj.trivialAction _ _
  haveI := Stack.isMonHom_sectionAutomorphismStabilizerIso B S hS Z hZ π x
    (sectionRelationPresentation B S hS x) hx
  Space.unitActionGroupoidIso (B := ⟨Z, hZ⟩)
    (G₁ := (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X)
    (G₂ := Stack.sectionStabilizer B S hS Z hZ x (sectionRelationPresentation B S hS x))
    (hG₁ := (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).property)
    (hG₂ := Stack.isAlgebraicSpace_sectionStabilizer B S hS Z hZ x
      (sectionRelationPresentation B S hS x))
    (Stack.sectionAutomorphismStabilizerIso B S hS Z hZ π x
      (sectionRelationPresentation B S hS x) hx)

/-- The identification of the self-intersection groupoid of a section, read over its object space
`Z`, with the groupoid of the trivial action of its stabilizer
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso`, Stacks 0447). -/
noncomputable def gerbeSectionTrivialActionIso
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) :=
  letI : ModObj (Stack.sectionStabilizer B S hS Z hZ x (sectionRelationPresentation B S hS x))
      (𝟙_ (Over Z)) := ModObj.trivialAction _ _
  GroupoidInAlgebraicSpaces.trivialActionIso
    (Stack.sectionSelfIntersectionGroupoid B S hS Z hZ x (sectionRelationPresentation B S hS x))
    (Stack.sectionSelfIntersectionGroupoid_source_eq_target B S hS Z hZ π x
      (sectionRelationPresentation B S hS x) hx)
    (Space.groupoidOfAction ⟨Z, hZ⟩
      (Stack.sectionStabilizer B S hS Z hZ x (sectionRelationPresentation B S hS x))
      (𝟙_ (Over Z))
      (Stack.isAlgebraicSpace_sectionStabilizer B S hS Z hZ x
        (sectionRelationPresentation B S hS x)) hZ)

/-- **The canonical 1-morphism `x_can : [Z/G] ⟶ 𝒳` of Stacks 06QG**, for a section `x` of
`π : 𝒳 ⟶ 𝒰` and `G = Isom_𝒳(x, x)` with the group law of **Stacks 06PP**
(`AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace`), acting trivially on `Z`.
It is the source's construction: the canonical 1-morphism of **Stacks 04T4** (5) out of the
quotient stack of the self-intersection groupoid `R ⇉ Z`, precomposed with the 1-morphisms of
quotient stacks (**Stacks 046Q**) induced by the identification of `R ⇉ Z` with the groupoid of the
trivial action of its stabilizer (`gerbeSectionTrivialActionIso`, Stacks 0447) and by the
isomorphism of group algebraic spaces `G ≅ G/U` (`gerbeSectionUnitActionIso`), under which the
composition law of `R` is the group law of `G`. -/
noncomputable def gerbeSectionClassifyingFunctor
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    letI : ModObj (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X
      (𝟙_ (Over Z)) := ModObj.trivialAction _ _
    (Stack.quotientStackOfAction (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)
      (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X (𝟙_ _)
      (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).property hZ).obj ⥤
      𝒳.val.val.obj :=
  (Stack.quotientStackMap (gerbeSectionUnitActionIso B S hS π x hx).hom).toFunctor ⋙
    (Stack.quotientStackMap (gerbeSectionTrivialActionIso B S hS π x hx).hom).toFunctor ⋙
    (SelfIntersection.selfIntersectionPresentation
      (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ)
      (sectionRelationPresentation B S hS x) 𝒳.property).canonicalMap.toFunctor

/-- **Stacks 06QG.** Let `π : 𝒳 ⟶ 𝒰` be a 1-morphism from an algebraic stack `𝒳` over `S` to the
algebraic stack `𝒰` of an algebraic space `Z` over `S`, let `x : 𝒰 ⟶ 𝒳` be a section of `π` — a
1-morphism together with a 2-isomorphism `x ≫ π ≅ 𝟙 𝒰` — and let `π` make `𝒳` a gerbe over `𝒰`.
Let `G = Isom_𝒳(x, x)` be the group algebraic space over `Z` of **Stacks 06PP**, whose group law
is composition of automorphisms (`AlgebraicGeometry.Stack.relativeAutomorphismGroupAlgebraicSpace`
at `π`; since `𝒰` is an algebraic space, its sections are all the automorphisms of `x`, by
`AlgebraicGeometry.Stack.isIso_relativeAutomorphismToIsomSpace`). Then

1. the canonical 1-morphism `x_can : [Z/G] ⟶ 𝒳`
   (`AlgebraicGeometry.Stack.AlgebraicStacks.gerbeSectionClassifyingFunctor`) out of the
   quotient stack of the *trivial* action of `G` on `Z` is an equivalence of stacks in groupoids
   over the big fppf site of `S`;
2. `G ⟶ Z` is flat and locally of finite presentation;
3. `x` is surjective, flat and locally of finite presentation. -/
@[stacks 06QG]
theorem exists_equivalenceOver_gerbeSectionClassifyingFunctor_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    letI : ModObj (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X
      (𝟙_ (Over Z)) := ModObj.trivialAction _ _
    (∃ e : StacksRepresentableCFG.EquivalenceOver
        (Stack.quotientStackOfAction (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)
          (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X (𝟙_ _)
          (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).property hZ).p
        𝒳.val.val.p,
        e.hom.functor = gerbeSectionClassifyingFunctor B S hS π x hx) ∧
      Space.IsFlat B S hS
        (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X.hom ∧
      Space.IsLocallyOfFinitePresentation B S hS
        (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).obj.X.hom ∧
      Stack.IsSurjective B S hS x ∧ IsFlat B S hS x ∧
        IsLocallyOfFinitePresentation B S hS x := by
  classical
  obtain ⟨hxflat, hxlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver
    B S hS π x hx hπ (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  have hiso := Stack.isIso_relativeAutomorphismToIsomSpace B S hS Z hZ π x
  have hflat : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom) :=
    (Space.isFlat_isStableUnderBaseChange B S hS).respectsIso
  have hlfp : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) :=
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).respectsIso
  refine ⟨⟨(StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (Stack.quotientStackMap (gerbeSectionUnitActionIso B S hS π x hx).hom).w
      (Classical.choice (Stack.nonempty_isEquivalenceOver_quotientStackMap_of_iso
        (gerbeSectionUnitActionIso B S hS π x hx)))).trans
    ((StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (Stack.quotientStackMap (gerbeSectionTrivialActionIso B S hS π x hx).hom).w
      (Classical.choice (Stack.nonempty_isEquivalenceOver_quotientStackMap_of_iso
        (gerbeSectionTrivialActionIso B S hS π x hx)))).trans
    (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
      (SelfIntersection.selfIntersectionPresentation
        (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ)
        (sectionRelationPresentation B S hS x) 𝒳.property).canonicalMap.w
      (Classical.choice
        (SelfIntersection.nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver
          (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ)
          (sectionRelationPresentation B S hS x) 𝒳.property π.hom
          (Bicategory.InducedBicategory.isoHom (f := x ≫ π)
            (g := 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) hx) hπ)))), rfl⟩, ?_, ?_,
    Stack.isSurjective_of_section_of_isGerbeOver B S hS π x hx hπ, hxflat, hxlfp⟩
  · exact property_comp_of_iso B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom)
      (F := ⟨_, (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).property⟩)
      (G := ⟨_, isAlgebraicSpace_isomSpaceOverSpace_of_section B S hS π hx⟩) (H := ⟨Z, hZ⟩)
      (@asIso _ _ _ _ (Stack.relativeAutomorphismToIsomSpace B S hS Z hZ π x) hiso)
      (ObjectProperty.homMk (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x))
      (isFlat_isomSpaceOverSpaceProj_of_section_of_isGerbeOver B S hS π hx hπ)
  · exact property_comp_of_iso B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom)
      (F := ⟨_, (Stack.relativeAutomorphismGroupAlgebraicSpace B S hS Z hZ π x).property⟩)
      (G := ⟨_, isAlgebraicSpace_isomSpaceOverSpace_of_section B S hS π hx⟩) (H := ⟨Z, hZ⟩)
      (@asIso _ _ _ _ (Stack.relativeAutomorphismToIsomSpace B S hS Z hZ π x) hiso)
      (ObjectProperty.homMk (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x))
      (isLocallyOfFinitePresentation_isomSpaceOverSpaceProj_of_section_of_isGerbeOver
        B S hS π hx hπ)


end AlgebraicGeometry.Stack.AlgebraicStacks

end
