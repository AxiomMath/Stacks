module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackOfAction
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.GroupStructure
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.TrivialActionComparison
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomProjection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomSelfIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionFlatProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRelative
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence

/-!
# A gerbe with a section is a classifying stack (Stacks 06QG)

Let `π : 𝒳 ⟶ 𝒰` be a 1-morphism from an algebraic stack `𝒳` over `S` to the algebraic stack `𝒰`
of an algebraic space `Z` over `S`, let `x : 𝒰 ⟶ 𝒳` be a *section* of `π` — a 1-morphism together
with a 2-isomorphism `x ≫ π ≅ 𝟙 𝒰` — and let `π` make `𝒳` a gerbe over `𝒰`. Write
`G = Isom_𝒳(x, x)` for the automorphism sheaf of the section. **Stacks 06QG** asserts three
things:

1. `G` is a group algebraic space over `Z` and there is a canonical equivalence of stacks in
   groupoids `[Z/G] ⟶ 𝒳`, where `[Z/G]` is the quotient stack of the *trivial* action of `G`
   on `Z`;
2. `G ⟶ Z` is flat and locally of finite presentation;
3. `x` is surjective, flat and locally of finite presentation.

This file proves parts (2) and (3) and an existential form of part (1). The statement of
Stacks 06QG, with `G` carrying the group law of Stacks 06PP and with the canonical 1-morphism
`x_can : [Z/G] ⟶ 𝒳`, is
`AlgebraicStacks.exists_equivalenceOver_gerbeSectionClassifyingFunctor_of_isGerbeOver` of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionCanonicalEquivalence`.

## Main results

* `exists_grpObj_nonempty_equivalenceOver_quotientStackOfAction_of_section_of_isGerbeOver`:
  the existential form of Stacks 06QG: some group structure on an algebraic space isomorphic to
  `Isom_𝒳(x, x)` over `Z` has a trivial-action quotient stack equivalent to `𝒳`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasRelativeProperty_isFlat_of_isFlat` and
  `…hasRelativeProperty_isLocallyOfFinitePresentation_of_isLocallyOfFinitePresentation`:
  **Stacks 06FM** for a representable 1-morphism, read at flatness of **Stacks 06PW** and at
  local finite presentation of **Stacks 06Q2** — the bridge from those two notions to the
  relative property of **Stacks 03YK** that **Stacks 04WY** consumes.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAlgebraicSpace_isomSpaceOverSpace_of_section`:
  **`Isom_𝒳(x, x)` is an algebraic space** for a section. This is the first paragraph of the
  source's proof, `R = G`, read as a representability statement.
* `Stack.AlgebraicStacks.isFlat_source_selfIntersectionPresentation_of_section_of_isGerbeOver`
  and its local-finite-presentation sibling: the source morphism `R ⟶ Z` of the self-intersection
  groupoid of Stacks 04T4 (4) is flat and locally of finite presentation.

## Implementation notes

Part (3) is `AlgebraicGeometry.Stack.isSurjective_of_section_of_isGerbeOver` together with
`Stack.AlgebraicStacks.isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver`
of `StacksFrontier.AlgebraicGeometry.Stacks.GerbeFlatLocalSection`, both at the source's generality.

Part (2) is **Stacks 04WY** at the section: the source morphism of the self-intersection groupoid
is a base change of `x`, so it inherits flatness and local finite presentation from part (3).
Stacks 04WY asks for those properties in the shape of the relative property of Stacks 03YK, while
part (3) delivers them in the shape of Stacks 06PW and Stacks 06Q2; the two bridges above convert
between them, by **Stacks 06FM** for a representable 1-morphism — and `x` is representable by
algebraic spaces because its source is representable by an algebraic space and `𝒳` is algebraic
(**Stacks 045G**).

Part (1) is the equivalence
`Stack.SelfIntersection.nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver`
between the quotient stack of the self-intersection groupoid and `𝒳`, composed with the
identification of that groupoid with the groupoid of the trivial action of its stabilizer group
(**Stacks 0447**) on the object space — which is available because the source and the target of
the self-intersection groupoid of a section agree
(`AlgebraicGeometry.Stack.SelfIntersection.source_eq_target_selfIntersectionPresentation`).
The identification of that stabilizer with `Isom_𝒳(x, x)` *as a group*, and the canonical
1-morphism, are in `StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionCanonicalEquivalence`.

That `Isom_𝒳(x, x)` is an algebraic space closes the gap recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionIsomSelfIntersection` and of
`StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismSpaceOverAlgebraicSpace`: the
self-intersection is representable by an algebraic space by **Stacks 04T4** part (1) and is
equivalent over the site to the category of elements of the presheaf
`AlgebraicGeometry.Stack.isomSpaceOverSpace`, and the category of elements of a presheaf of sets
determines the presheaf
(`CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`).

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04WY](https://stacks.math.columbia.edu/tag/04WY)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
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

/-- **Flatness of a 1-morphism of algebraic stacks representable by algebraic spaces is the
relative property of Stacks 03YK at flatness of morphisms of algebraic spaces.** Flatness of
Stacks 06PW is the existential smooth-diagram criterion of Stacks 06FM, and for a representable
1-morphism that criterion is the relative property. -/
theorem hasRelativeProperty_isFlat_of_isFlat
    {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hflat : IsFlat B S hS f) :
    Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom)
      f.hom hf :=
  (Stack.hasPropertyOnSomeSmoothDiagram_iff_relative.{u, w, u} B S hS
    (fun _ _ h => Space.IsFlat B S hS h) (Space.isSmoothLocalOnSourceAndTarget_flat B S hS)
    𝒰.property 𝒳.property f.hom hf).1 hflat

/-- **Local finite presentation of a 1-morphism of algebraic stacks representable by algebraic
spaces is the relative property of Stacks 03YK at local finite presentation of morphisms of
algebraic spaces.** -/
theorem hasRelativeProperty_isLocallyOfFinitePresentation_of_isLocallyOfFinitePresentation
    {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (hf : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f) :
    Stack.HasRelativeProperty.{u, u, u + 1, u} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom)
      f.hom hf :=
  (Stack.hasPropertyOnEverySmoothDiagram_iff_relative.{u, u, w} B S hS
    (fun _ _ h => Space.IsLocallyOfFinitePresentation B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
    𝒰.property 𝒳.property f.hom hf).1 hlfp

/-- An isomorphism of presheaves between two algebraic spaces over `S` is an isomorphism in the
category of algebraic spaces over `S`. -/
theorem isIso_homMk_of_iso {F G : AlgebraicSpaces B S hS} (α : F.obj ≅ G.obj) :
    IsIso (ObjectProperty.homMk α.hom : F ⟶ G) :=
  ⟨ObjectProperty.homMk α.inv, ObjectProperty.hom_ext _ α.hom_inv_id,
    ObjectProperty.hom_ext _ α.inv_hom_id⟩

/-- A property of morphisms of algebraic spaces over `S` which respects isomorphisms is
unchanged by precomposition with an isomorphism of the underlying presheaves. -/
theorem property_comp_of_iso (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.RespectsIso] {F G H : AlgebraicSpaces B S hS} (α : F.obj ≅ G.obj) (g : G ⟶ H)
    (hg : P g) : P (ObjectProperty.homMk (α.hom ≫ g.hom) : F ⟶ H) := by
  have := isIso_homMk_of_iso B S hS α
  exact (MorphismProperty.cancel_left_of_respectsIso P
    (ObjectProperty.homMk α.hom : F ⟶ G) g).2 hg

section Section

variable {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
variable {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hZ : IsAlgebraicSpace B S hS Z}
variable {x : Stack.algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳}

/-- The isomorphism of presheaves of sets attached to a pointwise family of bijections of
presheaves with values in one universe. -/
def presheafIsoOfPointwiseEquiv {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (pe : CategoryTheory.PresheafOfCategories.PointwiseEquiv F G) : F ≅ G :=
  NatIso.ofComponents (fun T => Equiv.toIso (pe.equiv T))
    (fun {T T'} f => by ext s; exact pe.naturality f s)

/-- **`Isom_𝒳(x, x)` is an algebraic space over `S`, for a section `x` of a 1-morphism
`π : 𝒳 ⟶ 𝒰` with `𝒰` the algebraic stack of an algebraic space `Z`.** This is the first step of
the proof of **Stacks 06QG**, `R = G`, read as a representability statement: the
self-intersection `𝒰 ×_{x, 𝒳, x} 𝒰` is representable by an algebraic space by **Stacks 04T4**
part (1), and it is equivalent over the big fppf site of `S` to the category of elements of the
presheaf `AlgebraicGeometry.Stack.isomSpaceOverSpace` by
`AlgebraicGeometry.Stack.nonempty_equivalenceOver_relation_isomSpaceOverSpace`; the category of
elements of a presheaf of sets determines the presheaf
(`CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver`), so that presheaf is
isomorphic to the representing algebraic space. -/
theorem isAlgebraicSpace_isomSpaceOverSpace_of_section
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) :
    IsAlgebraicSpace B S hS (Stack.isomSpaceOverSpace B S hS Z hZ x x) := by
  obtain ⟨e₀⟩ := Stack.nonempty_equivalenceOver_relation_isomSpaceOverSpace B S hS Z hZ x π hx
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val x.hom.hom 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  exact isAlgebraicSpace_of_iso B S hS
    (presheafIsoOfPointwiseEquiv B S hS
      (CategoryTheory.PresheafOfCategories.pointwiseEquivOfEquivalenceOver (e₀.symm.trans eF)))
    hF

variable {R : AlgebraicSpaces B S hS}
variable
  (eR : StacksRepresentableCFG.EquivalenceOver
    (SelfIntersection.relation B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val
      𝒳.val x.hom.hom).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-- **The quotient stack of the self-intersection groupoid of a section of a gerbe is equivalent
to the gerbe, over the big fppf site of `S`.** This is
`Stack.SelfIntersection.nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver`
read as an equivalence over the site rather than as a 1-morphism which is one. -/
theorem nonempty_equivalenceOver_quotientStack_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (Stack.quotientStack (SelfIntersection.selfIntersectionPresentation
        (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
          𝒳.property).groupoid).p
      𝒳.val.val.p) := by
  obtain ⟨he⟩ :=
    SelfIntersection.nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver
      (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR 𝒳.property π.hom
      (Bicategory.InducedBicategory.isoHom (f := x ≫ π)
        (g := 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) hx) hπ
  exact ⟨StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
    (SelfIntersection.selfIntersectionPresentation
      (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
        𝒳.property).canonicalMap.w he⟩

/-- The source morphism `R ⟶ U` of the self-intersection groupoid of a section of a gerbe over an
algebraic space is **flat**: the section is flat by Stacks 06QG part (3), and the source morphism
is a base change of it by Stacks 04WY. -/
theorem isFlat_source_selfIntersectionPresentation_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    Space.IsFlat B S hS (SelfIntersection.selfIntersectionPresentation
      (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
        𝒳.property).groupoid.source.hom := by
  have hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS x.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ) x.hom
  exact SelfIntersection.isFlat_selfIntersectionPresentation_source _ eR hrep
    (hasRelativeProperty_isFlat_of_isFlat B S hS x hrep
      (isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver B S hS π x hx hπ
        (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)).1) 𝒳.property

/-- The source morphism `R ⟶ U` of the self-intersection groupoid of a section of a gerbe over an
algebraic space is **locally of finite presentation**, by the same route. -/
theorem isLocallyOfFinitePresentation_source_selfIntersectionPresentation_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    Space.IsLocallyOfFinitePresentation B S hS
      (SelfIntersection.selfIntersectionPresentation
        (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR
          𝒳.property).groupoid.source.hom := by
  have hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS x.hom.hom :=
    Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ) x.hom
  exact SelfIntersection.isLocallyOfFinitePresentation_selfIntersectionPresentation_source _ eR
    hrep (hasRelativeProperty_isLocallyOfFinitePresentation_of_isLocallyOfFinitePresentation
      B S hS x hrep
      (isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver B S hS π x hx hπ
        (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)).2) 𝒳.property

/-- A property of morphisms of algebraic spaces which respects isomorphisms holds for
`Isom_𝒳(x, x) ⟶ Z` as soon as it holds for the source morphism of every self-intersection
groupoid of a section. -/
private theorem property_isomSpaceOverSpaceProj_of_section
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.RespectsIso]
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (h : ∀ {R : AlgebraicSpaces B S hS}
      (eR : StacksRepresentableCFG.EquivalenceOver
        (SelfIntersection.relation B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val
          𝒳.val x.hom.hom).val.p
        (presheafOfCategories (R.obj ⋙ typeToCat)).p),
      P (ObjectProperty.homMk (SelfIntersection.relationSourceMap
        (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR) :
          R ⟶ ⟨Z, hZ⟩)) :
    P (ObjectProperty.homMk (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x) :
      (⟨_, isAlgebraicSpace_isomSpaceOverSpace_of_section B S hS π hx⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩) := by
  obtain ⟨F, hF, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val x.hom.hom 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  have eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p
      (presheafOfCategories
        ((⟨F, hF⟩ : AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p := eR₀
  have := Stack.isIso_isomSpaceToRelationSpace B S hS Z hZ x eR π hx
  rw [← Stack.isomSpaceToRelationSpace_comp_relationSourceMap B S hS Z hZ x eR]
  exact property_comp_of_iso B S hS P
    (F := ⟨_, isAlgebraicSpace_isomSpaceOverSpace_of_section B S hS π hx⟩) (G := ⟨F, hF⟩)
    (asIso (Stack.isomSpaceToRelationSpace B S hS Z hZ x eR))
    (ObjectProperty.homMk (SelfIntersection.relationSourceMap
      (Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ) eR))
    (h (R := ⟨F, hF⟩) eR)

/-- `Isom_𝒳(x, x) ⟶ Z` is **flat** for a section `x` of a gerbe over an algebraic space: it is
the source morphism of the self-intersection groupoid up to isomorphism. -/
theorem isFlat_isomSpaceOverSpaceProj_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    Space.IsFlat B S hS (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x) := by
  have : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom) :=
    (Space.isFlat_isStableUnderBaseChange B S hS).respectsIso
  exact property_isomSpaceOverSpaceProj_of_section B S hS
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom) π hx
    fun eR => isFlat_source_selfIntersectionPresentation_of_section_of_isGerbeOver
      B S hS eR π hx hπ

/-- `Isom_𝒳(x, x) ⟶ Z` is **locally of finite presentation** for a section `x` of a gerbe over an
algebraic space, by the same route. -/
theorem isLocallyOfFinitePresentation_isomSpaceOverSpaceProj_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    Space.IsLocallyOfFinitePresentation B S hS (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x) := by
  have : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom) :=
    (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).respectsIso
  exact property_isomSpaceOverSpaceProj_of_section B S hS
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
      Space.IsLocallyOfFinitePresentation B S hS g.hom) π hx
    fun eR =>
      isLocallyOfFinitePresentation_source_selfIntersectionPresentation_of_section_of_isGerbeOver
        B S hS eR π hx hπ

/-! ### An existential form of Stacks 06QG -/

/-- **An existential form of Stacks 06QG**, for a section `x` of a 1-morphism `π : 𝒳 ⟶ 𝒰` making
the algebraic stack `𝒳` a gerbe over the algebraic stack `𝒰` of an algebraic space `Z`. Write
`G = Isom_𝒳(x, x)` for the automorphism sheaf of the section, an algebraic space over `Z` through
`AlgebraicGeometry.Stack.isomSpaceOverSpaceProj`. Then some group algebraic space `G'` over `Z`,
isomorphic to `G` as an object over `Z`, has a trivial-action quotient stack `[Z/G']` equivalent
to `𝒳` over the big fppf site of `S`; `G ⟶ Z` is flat and locally of finite presentation; and `x`
is surjective, flat and locally of finite presentation.

This does not pin down the group law of `G'` against the one of `G`, nor the equivalence. The
statement of Stacks 06QG, with `G` carrying the composition law of Stacks 06PP and with the
canonical 1-morphism `x_can : [Z/G] ⟶ 𝒳`, is
`AlgebraicStacks.exists_equivalenceOver_gerbeSectionClassifyingFunctor_of_isGerbeOver`.
Here `G'` is the stabilizer of the self-intersection groupoid of **Stacks 04T4** (4), with the
group law of **Stacks 0447**, which is all of the arrow space of that groupoid because for a
section its source and target agree; the equivalence is the canonical 1-morphism of Stacks 04T4
(5), carried across the identification of the self-intersection groupoid with the trivial-action
groupoid of its stabilizer. -/
theorem exists_grpObj_nonempty_equivalenceOver_quotientStackOfAction_of_section_of_isGerbeOver
    (π : 𝒳 ⟶ Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)
    (hx : x ≫ π ≅ 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ))
    (hπ : IsGerbeOver B S hS π) :
    (∃ (G : Over (⟨Z, hZ⟩ : AlgebraicSpaces B S hS).obj) (hGrp : GrpObj G)
        (hG : IsAlgebraicSpace B S hS G.left)
        (_ι : G ≅ Over.mk (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x)),
        letI : GrpObj G := hGrp
        letI : ModObj G (𝟙_ (Over (⟨Z, hZ⟩ : AlgebraicSpaces B S hS).obj)) :=
          ModObj.trivialAction G _
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (Stack.quotientStackOfAction (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) G (𝟙_ _) hG hZ).p
          𝒳.val.val.p)) ∧
      Space.IsFlat B S hS (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x) ∧
      Space.IsLocallyOfFinitePresentation B S hS
        (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x) ∧
      Stack.IsSurjective B S hS x ∧ IsFlat B S hS x ∧
        IsLocallyOfFinitePresentation B S hS x := by
  classical
  -- the self-intersection is representable by an algebraic space (Stacks 04T4 (1))
  obtain ⟨F, hF, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val 𝒳.val x.hom.hom 𝒳.property
      (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  have eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ).val
        𝒳.val x.hom.hom).val.p
      (presheafOfCategories
        ((⟨F, hF⟩ : AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p := eR₀
  set eU := Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS Z hZ
  set 𝒢 := (SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property).groupoid
  -- the source and the target of the self-intersection groupoid of a section agree
  have hst : 𝒢.source = 𝒢.target :=
    SelfIntersection.source_eq_target_selfIntersectionPresentation eU eR 𝒳.property π.hom
      (Bicategory.InducedBicategory.isoHom (f := x ≫ π)
        (g := 𝟙 (Stack.algebraicSpaceStack.{u, w} B S hS Z hZ)) hx)
  -- the comparison of the arrow space with `Isom_𝒳(x, x)`, over the object space
  have := Stack.isIso_isomSpaceToRelationSpace B S hS Z hZ x eR π hx
  set β := asIso (Stack.isomSpaceToRelationSpace B S hS Z hZ x eR)
  have hβproj : β.hom ≫ SelfIntersection.relationSourceMap eU eR =
      Stack.isomSpaceOverSpaceProj B S hS Z hZ x x :=
    Stack.isomSpaceToRelationSpace_comp_relationSourceMap B S hS Z hZ x eR
  -- the stabilizer of the self-intersection groupoid, a group algebraic space over `Z`
  let hGrp : GrpObj (GroupoidInAlgebraicSpaces.stabilizer 𝒢) :=
    (GroupoidInAlgebraicSpaces.stabilizerGroupStructure 𝒢).1
  let : ModObj (GroupoidInAlgebraicSpaces.stabilizer 𝒢) (𝟙_ (Over 𝒢.objects.obj)) :=
    ModObj.trivialAction _ _
  have hpart1 := Stack.nonempty_equivalenceOver_quotientStack_of_iso
    (GroupoidInAlgebraicSpaces.trivialActionIso 𝒢 hst
      (Space.groupoidOfAction 𝒢.objects (GroupoidInAlgebraicSpaces.stabilizer 𝒢)
        (𝟙_ (Over 𝒢.objects.obj))
        (GroupoidInAlgebraicSpaces.isAlgebraicSpace_stabilizer 𝒢) 𝒢.objects.property))
  obtain ⟨hxflat, hxlfp⟩ := isFlat_and_isLocallyOfFinitePresentation_section_of_isGerbeOver
    B S hS π x hx hπ (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  refine ⟨⟨GroupoidInAlgebraicSpaces.stabilizer 𝒢, hGrp,
    GroupoidInAlgebraicSpaces.isAlgebraicSpace_stabilizer 𝒢, ?_, ?_⟩,
    isFlat_isomSpaceOverSpaceProj_of_section_of_isGerbeOver B S hS π hx hπ,
    isLocallyOfFinitePresentation_isomSpaceOverSpaceProj_of_section_of_isGerbeOver B S hS π hx hπ,
    Stack.isSurjective_of_section_of_isGerbeOver B S hS π x hx hπ, hxflat, hxlfp⟩
  -- the identification of the stabilizer with `Isom_𝒳(x, x)` over the object space
  · refine Over.isoMk (GroupoidInAlgebraicSpaces.stabilizerArrowIso 𝒢 hst ≪≫ β.symm) ?_
    have hinv : β.inv ≫ Stack.isomSpaceOverSpaceProj B S hS Z hZ x x =
        SelfIntersection.relationSourceMap eU eR := by
      simp [← hβproj]
    exact (Category.assoc (GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢) β.inv
        (Stack.isomSpaceOverSpaceProj B S hS Z hZ x x)).trans
      ((congrArg (fun k => GroupoidInAlgebraicSpaces.stabilizerArrow 𝒢 ≫ k) hinv).trans
        (GroupoidInAlgebraicSpaces.stabilizerArrow_source 𝒢))
  -- part (1)
  · exact hpart1.elim fun e =>
      (nonempty_equivalenceOver_quotientStack_of_section_of_isGerbeOver B S hS eR π hx hπ).elim
        fun f => ⟨e.trans f⟩

end Section

end AlgebraicGeometry.Stack.AlgebraicStacks

end
