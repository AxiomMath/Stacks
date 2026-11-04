module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeAtlasSection
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeClassifyingCoverReduction
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverFiberedInSets

/-!
# A gerbe is fppf-locally a classifying stack (Stacks 06QH)

**Stacks 06QH** says that a 1-morphism `π : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` makes `𝒳` a
gerbe over `𝒴` exactly when there are an algebraic space `U`, a group algebraic space `G` flat
and locally of finite presentation over `U`, and a surjective, flat, locally finitely presented
1-morphism `U ⟶ 𝒴` with `𝒳 ×_𝒴 U ≅ [U/G]` **over `U`**, the quotient being taken for the trivial
action of `G` on `U`.

This file proves the implication (1) `⟹` (2) and assembles the equivalence with the implication
(2) `⟹` (1) of `StacksFrontier.AlgebraicGeometry.Stacks.GerbeCharacterization`.

## Main results

All three results live in the namespace `AlgebraicGeometry.Stack.AlgebraicStacks`.

* `exists_grpObj_nonempty_equivalenceOver_quotientStackToBase_of_section_of_isGerbeOver`:
  **Stacks 06QG parts (1) and (2), with the equivalence read over the base.** For a gerbe over
  the algebraic stack of an algebraic space `U` admitting a section, the automorphism group
  algebraic space `G` of that section is flat and locally of finite presentation over `U`, and
  the classifying stack `[U/G]` of its trivial action is equivalent to the gerbe *over `U`*.
* `hasClassifyingFppfCover_of_isGerbeOver`: **Stacks 06QH, the implication (1) `⟹` (2).**
* `isGerbeOver_iff_hasClassifyingFppfCover`: **Stacks 06QH.**

## Implementation notes

The one thing the library's form of Stacks 06QG
(`exists_grpObj_nonempty_equivalenceOver_quotientStackOfAction_of_section_of_isGerbeOver`)
does not say is that its canonical equivalence `[U/G] ⟶ 𝒳` is an equivalence **over `U`**, which
is what clause (2) of Stacks 06QH asks for; it exhibits the equivalence only over the big fppf
site of `S`. The first result above adds exactly that, by identifying the two 1-morphisms
`[U/G] ⟶ U` on the nose:

* the structure arrow of **Stacks 044R** restricts along the projection `U ⟶ [U/G]` to the
  structure morphism of the object space
  (`AlgebraicGeometry.Stack.quotientStackProjection_comp_toBase`);
* the composite of the canonical equivalence with `π` restricts along that projection to the
  composite of the section with `π`, which the section's own 2-isomorphism identifies with the
  identity — and a 2-isomorphism between 1-morphisms into a category fibred in sets is an
  identity (**Stacks 02Y2**), so this is an equality of 1-morphisms and not merely a
  2-isomorphism;
* a 1-morphism `[U/R] ⟶ Y` into an algebraic space is determined by its restriction along the
  projection (**Stacks 0DUH**, `AlgebraicGeometry.Stack.restriction_injective`).

The comparison of the self-intersection groupoid of the section with the action groupoid of the
trivial action of its stabilizer is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso`
and the induced equivalence of quotient stacks is **Stacks 046T** at an isomorphism of groupoids;
its compatibility with the projections is
`AlgebraicGeometry.Stack.quotientStackProjection_comp_quotientStackMap`. That comparison is
stated for the action of the stabilizer through `CategoryTheory.ModObj.trivialAction`, while
clause (2) of Stacks 06QH names the action through
`AlgebraicGeometry.Space.modObjTensorUnit`; the two modules structures on the monoidal unit are
equal, because their action maps are two morphisms into a terminal object, and
`AlgebraicGeometry.Space.modObj_tensorUnit_eq` records that so that the comparison can be read
for either.

Flatness and local finite presentation of `G ⟶ U` are those of the source morphism of the
self-intersection groupoid — the content of Stacks 06QG part (2), proved in
`StacksFrontier.AlgebraicGeometry.Stacks.GerbeSectionClassifyingStack` — carried across the
identification of the stabilizer with the arrow space of that groupoid, which is available
because the source and the target of the self-intersection groupoid of a section agree.

## References

* [Stacks Project, Tag 02Y2](https://stacks.math.columbia.edu/tag/02Y2)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046T](https://stacks.math.columbia.edu/tag/046T)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06QE](https://stacks.math.columbia.edu/tag/06QE)
* [Stacks Project, Tag 06QF](https://stacks.math.columbia.edu/tag/06QF)
* [Stacks Project, Tag 06QG](https://stacks.math.columbia.edu/tag/06QG)
* [Stacks Project, Tag 06QH](https://stacks.math.columbia.edu/tag/06QH)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory

namespace AlgebraicGeometry.Space

universe u

/-- **A module structure on the monoidal unit of a cartesian monoidal category is unique.** Its
action map is a morphism into a terminal object, and there is only one of those. -/
theorem modObj_tensorUnit_eq {D : Type*} [Category D] [CartesianMonoidalCategory D] {M : D}
    [MonObj M] (m₁ m₂ : ModObj M (𝟙_ D)) : m₁ = m₂ := by
  obtain ⟨s₁, -, -⟩ := m₁
  obtain ⟨s₂, -, -⟩ := m₂
  obtain rfl : s₁ = s₂ := toUnit_unique s₁ s₂
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

/-- **A groupoid in algebraic spaces whose source and target agree is the action groupoid of the
trivial action of its stabilizer, read over its object space**, with the map on object spaces of
the comparison the structure morphism of the action groupoid's object space.

This is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.trivialActionIso` together with
`…trivialActionHom_mapObjects` and `…trivialActionObjectsToBase_hom`, stated for an arbitrary
module structure on the monoidal unit rather than for
`CategoryTheory.ModObj.trivialAction`: the two are equal by
`AlgebraicGeometry.Space.modObj_tensorUnit_eq`, and the one clause (2) of Stacks 06QH names is
`AlgebraicGeometry.Space.modObjTensorUnit`. -/
theorem exists_iso_overObjects_of_source_eq_target
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} {Bs : AlgebraicSpaces C S hS}
    (𝒢 : GroupoidInAlgebraicSpaces C S hS Bs) (hst : 𝒢.source = 𝒢.target)
    (i : ModObj (GroupoidInAlgebraicSpaces.stabilizer 𝒢) (𝟙_ (Over 𝒢.objects.obj)))
    (A : @Space.ActionGroupoidConstruction C S hS 𝒢.objects
      (GroupoidInAlgebraicSpaces.stabilizer 𝒢) (𝟙_ (Over 𝒢.objects.obj)) inferInstance i
      (GroupoidInAlgebraicSpaces.isAlgebraicSpace_stabilizer 𝒢) 𝒢.objects.property) :
    ∃ ι : GroupoidInAlgebraicSpaces.Iso A.groupoid
        (GroupoidInAlgebraicSpaces.overObjects 𝒢 hst),
      ι.hom.toGroupoidHom.mapObjects = A.groupoid.objectsToBase.hom := by
  obtain rfl : i = ModObj.trivialAction (GroupoidInAlgebraicSpaces.stabilizer 𝒢) _ :=
    Space.modObj_tensorUnit_eq i _
  refine ⟨GroupoidInAlgebraicSpaces.trivialActionIso 𝒢 hst A, ?_⟩
  exact (GroupoidInAlgebraicSpaces.trivialActionHom_mapObjects 𝒢 hst A).trans
    (GroupoidInAlgebraicSpaces.trivialActionObjectsToBase_hom 𝒢 A).symm

/-- **Stacks 06QG parts (1) and (2), with the equivalence of part (1) read over the base.** Let
`π : 𝒳 ⟶ 𝒰` be a 1-morphism from an algebraic stack `𝒳` over `S` to the algebraic stack of an
algebraic space `U` over `S`, let `x` be a section of `π` and let `π` make `𝒳` a gerbe over `𝒰`.
Then there is a group algebraic space `G` over `U`, flat and locally of finite presentation over
`U`, whose classifying stack `[U/G]` — the quotient stack of the trivial action of `G` on `U` —
is equivalent to `𝒳` **over `U`**, that is, in the 2-category of categories over the total
category of `𝒰`.

This is what clause (2) of **Stacks 06QH** consumes. The library's form of Stacks 06QG,
`exists_grpObj_nonempty_equivalenceOver_quotientStackOfAction_of_section_of_isGerbeOver`, states
the equivalence over the big fppf site of `S` only. -/
theorem exists_grpObj_nonempty_equivalenceOver_quotientStackToBase_of_section_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (U : AlgebraicSpaces B S hS)
    (π : 𝒳 ⟶ ofAlgebraicSpace.{u, w} B S hS U)
    (x : ofAlgebraicSpace.{u, w} B S hS U ⟶ 𝒳)
    (hx : x ≫ π ≅ 𝟙 (ofAlgebraicSpace.{u, w} B S hS U))
    (hπ : IsGerbeOver B S hS π) :
    ∃ (G : Over U.obj) (_ : GrpObj G) (hG : IsAlgebraicSpace B S hS G.left),
      Space.IsFlat B S hS G.hom ∧ Space.IsLocallyOfFinitePresentation B S hS G.hom ∧
        ∃ A : Space.ActionGroupoidConstruction U G (𝟙_ (Over U.obj)) hG U.property,
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (CatFiberedInGroupoids.homFunctor π.hom)
            (Stack.quotientStackToBase A.groupoid).toFunctor) := by
  classical
  -- the self-intersection of the section is representable by an algebraic space (Stacks 04T4 (1))
  obtain ⟨F, hF, ⟨eR₀⟩⟩ :=
    SelfIntersection.isRepresentableByAlgebraicSpace_relation_of_isAlgebraicStack.{u, w}
      B S hS (Stack.algebraicSpaceStack.{u, w} B S hS U.obj U.property).val 𝒳.val x.hom.hom
      𝒳.property (Stack.isRepresentableByAlgebraicSpace_fibredCategory B S hS U.obj U.property)
  have eR : StacksRepresentableCFG.EquivalenceOver
      (SelfIntersection.relation B S hS
          (Stack.algebraicSpaceStack.{u, w} B S hS U.obj U.property).val 𝒳.val x.hom.hom).val.p
      (presheafOfCategories
        ((⟨F, hF⟩ : AlgebraicSpaces B S hS).obj ⋙ typeToCat)).p := eR₀
  set eU := Stack.algebraicSpaceStackTautologicalPresentation.{u, w} B S hS U.obj U.property
    with heU
  have hxi := Bicategory.InducedBicategory.isoHom (f := x ≫ π)
    (g := 𝟙 (ofAlgebraicSpace.{u, w} B S hS U)) hx
  set 𝒢P := SelfIntersection.selfIntersectionPresentation eU eR 𝒳.property with h𝒢P
  set 𝒢 := 𝒢P.groupoid with h𝒢
  -- the source and the target of the self-intersection groupoid of a section agree
  have hst : 𝒢.source = 𝒢.target :=
    SelfIntersection.source_eq_target_selfIntersectionPresentation eU eR 𝒳.property π.hom hxi
  have hstab := GroupoidInAlgebraicSpaces.isAlgebraicSpace_stabilizer 𝒢
  have hfs : (Stack.fibredCategory B S hS U.obj).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection U.obj).IsFiberedInSets
  -- the action groupoid of the trivial action of the stabilizer, and the comparison with `𝒢`
  set A := Space.groupoidOfAction 𝒢.objects (GroupoidInAlgebraicSpaces.stabilizer 𝒢)
    (𝟙_ (Over 𝒢.objects.obj)) hstab 𝒢.objects.property with hA
  obtain ⟨ι, hιobj⟩ := exists_iso_overObjects_of_source_eq_target 𝒢 hst _ A
  -- the two equivalences over the big fppf site, with their forward 1-morphisms named
  have hcan : Functor.IsEquivalenceOver (Stack.quotientStack 𝒢).p 𝒳.val.val.p
      𝒢P.canonicalMap.toFunctor :=
    Classical.choice
      (SelfIntersection.nonempty_isEquivalenceOver_canonicalMap_of_section_of_isGerbeOver
        eU eR 𝒳.property π.hom hxi hπ)
  have hqm := Classical.choice (Stack.nonempty_isEquivalenceOver_quotientStackMap_of_iso ι)
  -- `U ⟶ [U/G] ⟶ 𝒳 ⟶ 𝒰` is the identity: the presentation compares it with `x ≫ π`
  have hprojL : BasedFunctor.comp
      (Stack.quotientStackProjection (GroupoidInAlgebraicSpaces.overObjects 𝒢 hst))
      (BasedFunctor.comp 𝒢P.canonicalMap π.hom.hom) =
      BasedFunctor.id (Stack.fibredCategory B S hS U.obj).val := by
    refine BasedCategory.BasedFunctor.ext' ?_
    refine Functor.IsFiberedInSets.eq_of_obj_eq
      (Stack.fibredCategory B S hS U.obj).val.p (Stack.fibredCategory B S hS U.obj).val.p _ _
      (BasedFunctor.comp
        (Stack.quotientStackProjection (GroupoidInAlgebraicSpaces.overObjects 𝒢 hst))
        (BasedFunctor.comp 𝒢P.canonicalMap π.hom.hom)).w
      (BasedFunctor.id (Stack.fibredCategory B S hS U.obj).val).w (fun y => ?_)
    have ha : 𝒳.val.val.p.IsHomLift
        (𝟙 ((Stack.fibredCategory B S hS U.obj).val.p.obj y))
        (𝒢P.extends_f.1.hom.app y) := 𝒢P.extends_f.2 y
    have hb : (Stack.fibredCategory B S hS U.obj).val.p.IsHomLift
        (𝟙 ((Stack.fibredCategory B S hS U.obj).val.p.obj y))
        ((CatFiberedInGroupoids.homFunctor π.hom).map (𝒢P.extends_f.1.hom.app y)) :=
      Functor.isHomLift_map_of_comp_eq (CatFiberedInGroupoids.homFunctor_comp_p π.hom) _
        (𝒢P.extends_f.1.hom.app y)
    have hc := CatFiberedInGroupoids.isHomLift_app hxi.hom y
    have hd : (Stack.fibredCategory B S hS U.obj).val.p.IsHomLift
        (𝟙 ((Stack.fibredCategory B S hS U.obj).val.p.obj y))
        ((CatFiberedInGroupoids.homFunctor π.hom).map (𝒢P.extends_f.1.hom.app y) ≫
          hxi.hom.hom.toNatTrans.app y) :=
      @IsHomLift.comp_of_lift_id _ _ _ _ (Stack.fibredCategory B S hS U.obj).val.p
        ((Stack.fibredCategory B S hS U.obj).val.p.obj y) _ _ _ _ _ hb hc
    exact (@Functor.IsFiberedInSets.eq_of_isHomLift _ _ _ _
      (Stack.fibredCategory B S hS U.obj).val.p _ _ _
      (𝟙 ((Stack.fibredCategory B S hS U.obj).val.p.obj y)) _ _ _
      ((CatFiberedInGroupoids.homFunctor π.hom).map (𝒢P.extends_f.1.hom.app y) ≫
        hxi.hom.hom.toNatTrans.app y)
      (𝟙 y) hd (IsHomLift.id rfl)).choose
  -- the two 1-morphisms `[U/G] ⟶ U` agree, so the equivalence is one over `U`
  have hbased : BasedFunctor.comp (Stack.quotientStackMap ι.hom)
      (BasedFunctor.comp 𝒢P.canonicalMap π.hom.hom) =
      Stack.quotientStackToBase A.groupoid := by
    refine Stack.restriction_injective A.groupoid _ _ ?_
    refine (Stack.quotientStackProjection_comp_quotientStackMap ι.hom
      (BasedFunctor.comp 𝒢P.canonicalMap π.hom.hom)).trans ?_
    refine Eq.trans ?_ (Stack.quotientStackProjection_comp_toBase A.groupoid).symm
    exact (congrArg
      (BasedFunctor.comp
        (Stack.associatedMap B S hS ι.hom.toGroupoidHom.mapObjects).1.hom) hprojL).trans
      (congrArg (fun k => (Stack.associatedMap B S hS k).1.hom) hιobj)
  -- part (2): the stabilizer is flat and locally of finite presentation over the object space
  have hsrcflat :=
    isFlat_source_selfIntersectionPresentation_of_section_of_isGerbeOver B S hS eR π hx hπ
  have hsrclfp :=
    isLocallyOfFinitePresentation_source_selfIntersectionPresentation_of_section_of_isGerbeOver
      B S hS eR π hx hπ
  have hG : ∀ P : MorphismProperty (AlgebraicSpaces B S hS), P.RespectsIso → P 𝒢.source →
      P (ObjectProperty.homMk (GroupoidInAlgebraicSpaces.stabilizer 𝒢).hom :
        (⟨_, hstab⟩ : AlgebraicSpaces B S hS) ⟶ 𝒢.objects) := fun P _ h => by
    rw [← GroupoidInAlgebraicSpaces.stabilizerArrow_source 𝒢]
    exact property_comp_of_iso B S hS P (F := ⟨_, hstab⟩) (G := 𝒢.arrows)
      (GroupoidInAlgebraicSpaces.stabilizerArrowIso 𝒢 hst) 𝒢.source h
  have hGflat : Space.IsFlat B S hS (GroupoidInAlgebraicSpaces.stabilizer 𝒢).hom :=
    hG (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) => Space.IsFlat B S hS g.hom)
      (Space.isFlat_isStableUnderBaseChange B S hS).respectsIso hsrcflat
  have hGlfp : Space.IsLocallyOfFinitePresentation B S hS
      (GroupoidInAlgebraicSpaces.stabilizer 𝒢).hom :=
    hG (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (g : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS g.hom)
      (Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).respectsIso hsrclfp
  refine ⟨GroupoidInAlgebraicSpaces.stabilizer 𝒢,
    (GroupoidInAlgebraicSpaces.stabilizerGroupStructure 𝒢).1, hstab, hGflat, hGlfp, A,
    ⟨StacksRepresentableCFG.EquivalenceOver.symm
      (StacksRepresentableCFG.EquivalenceOver.ofIsFiberedInSetsBase
        (Stack.fibredCategory B S hS U.obj).val.p
        (Stack.quotientStackToBase A.groupoid).w
        (CatFiberedInGroupoids.homFunctor_comp_p π.hom)
        ((StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
            (Stack.quotientStackMap ι.hom).w hqm).trans
          (StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver
            𝒢P.canonicalMap.w hcan))
        (congrArg BasedFunctor.toFunctor hbased))⟩⟩

/-- **Stacks 06QH, the implication (1) `⟹` (2).** A 1-morphism of algebraic stacks over `S`
which makes its source a gerbe over its target is, fppf-locally on its target, the classifying
stack of a flat, locally finitely presented group algebraic space.

The covering 1-morphism out of an algebraic space after which the gerbe acquires a section is
`exists_space_section_snd_of_isGerbeOver`; the base change along it is again a gerbe by
**Stacks 06QE**; and the section turns it into a classifying stack over that algebraic space by
`exists_grpObj_nonempty_equivalenceOver_quotientStackToBase_of_section_of_isGerbeOver`, which is
**Stacks 06QG** parts (1) and (2) with the equivalence read over the base. -/
theorem hasClassifyingFppfCover_of_isGerbeOver
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (hf : IsGerbeOver B S hS f) :
    HasClassifyingFppfCover.{u, w} B S hS f := by
  obtain ⟨U, g, hgsurj, hgflat, hglfp, hsec⟩ :=
    exists_space_section_snd_of_isGerbeOver.{u, w} B S hS f hf
  have hP := Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f g
  obtain ⟨σ, ⟨hσ⟩⟩ := hsec (Stack.twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f g) hP
  have hPgerbe : IsGerbeOver B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f g).snd :=
    isGerbeOver_of_isTwoFibreProduct B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f g) hP hf
  obtain ⟨G, instG, hG, hGflat, hGlfp, A, e⟩ :=
    exists_grpObj_nonempty_equivalenceOver_quotientStackToBase_of_section_of_isGerbeOver.{u, w}
      B S hS U (Stack.twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f g).snd σ hσ hPgerbe
  exact ⟨U, g, hgsurj, hgflat, hglfp, G, instG, hG, hGflat, hGlfp, A,
    Stack.twoFibreProductSquareAlgebraicStacks.{u, w} B S hS f g, hP, e⟩

/-- **Stacks 06QH.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following are
equivalent:

1. `f` makes `𝒳` a gerbe over `𝒴`;
2. there are an algebraic space `U` over `S`, a group algebraic space `G` over `U` which is flat
   and locally of finite presentation over `U`, and a surjective, flat, locally finitely
   presented 1-morphism `U ⟶ 𝒴` such that the base change `𝒳 ×_𝒴 U` is isomorphic over `U` to
   the quotient stack `[U/G]` of the trivial action of `G` on `U`.

Clause (2) is `AlgebraicGeometry.Stack.AlgebraicStacks.HasClassifyingFppfCover`. -/
@[stacks 06QH]
theorem isGerbeOver_iff_hasClassifyingFppfCover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsGerbeOver B S hS f ↔ HasClassifyingFppfCover.{u, w} B S hS f :=
  ⟨hasClassifyingFppfCover_of_isGerbeOver.{u, w} B S hS f,
    isGerbeOver_of_hasClassifyingFppfCover.{u, w} B S hS f⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
