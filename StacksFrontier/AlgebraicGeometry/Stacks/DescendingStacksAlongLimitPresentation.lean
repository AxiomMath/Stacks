module

public import StacksFrontier.AlgebraicGeometry.Stacks.DescendingStacksAlongLimit
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBigSiteStackEssentialImage
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionSmoothProjections
public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoidRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.MorphismsToAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.GroupoidBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.GraphMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartSlicingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryRelative
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyComp
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint

/-!
# The groupoid presentation of a stack of finite presentation over an algebraic space

Let `Y` be a quasi-compact, quasi-separated algebraic space over a scheme `S` of a big fppf site,
and let `f : 𝒳 ⟶ Y` be a 1-morphism of finite presentation from an algebraic stack, with an affine
smooth surjective chart `U ⟶ 𝒳`. The first paragraph of the proof of Stacks 0CN4 turns that chart
into a smooth groupoid `(U, R, s, t, c)` in algebraic spaces *over `Y`*, with `U` and `R` of
finite presentation over `Y`, together with an identification `𝒳 ≅ [U/R]` over `Y`. This file
carries that paragraph out.

## Main results

* `AlgebraicGeometry.Stack.exists_smoothGroupoid_overBase_of_affineSmoothChart`: for a
  quasi-separated `f` with an affine smooth chart, the smooth groupoid over `Y` presenting `𝒳`,
  with object and arrow spaces quasi-compact and quasi-separated over `Y`, and locally of finite
  presentation (resp. locally of finite type) over `Y` when `f` is. The finite-type case is the
  first paragraph of the proof of Stacks 0CQ1.
* `AlgebraicGeometry.Stack.groupoidPresentationOfAffineSmoothChart`: the statement
  `AlgebraicGeometry.Stack.GroupoidPresentationOfAffineSmoothChart`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_of_comp_of_graph`: a relative property of
  `a : 𝒰 ⟶ 𝒳` is read off the composite `a ≫ f` and the graph of `a` over the target of `f`.
* `AlgebraicGeometry.Stack.hasRelativeProperty_quasiCompact_of_comp` and
  `AlgebraicGeometry.Stack.hasRelativeProperty_quasiSeparated_of_comp`: its two instances at
  quasi-compactness and quasi-separatedness, against a quasi-separated `f`.

## Implementation notes

The groupoid is the self-intersection groupoid of Stacks 04T4 (4), which lives over the final
algebraic space, and Stacks 04T5 identifies its quotient stack with `𝒳`. It is moved over `Y`
along the morphism `u : U ⟶ Y` that the composite `[U/R] ⟶ 𝒳 ⟶ Y` restricts to (Stacks 0DUH);
`u` is invariant for that reason, so the groupoid over the invariant target
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.overInvariantTarget`) has the same quotient stack,
and its structure arrow to `Y` is that composite on the nose, by the injectivity half of Stacks
0DUH. So the identification over `Y` is the counit of the equivalence of Stacks 04T5 whiskered by
`f`.

Finite presentation is the bookkeeping of the source's proof. `U ⟶ Y` is locally of finite
presentation because it is induced by the chart followed by `f` (Stacks 06FM, read on algebraic
spaces), quasi-compact because `U` is affine and `Y` quasi-separated (Stacks 073B), and
quasi-separated because `U` is (Stacks 04ZI). For `R ⟶ Y = s ≫ u`, the source map `s` is smooth
(Stacks 04T5 (1)), and quasi-compact and quasi-separated because it is a base change of the chart
(Stacks 04T4), which is quasi-compact and quasi-separated: the chart is the graph of itself over
`Y` followed by a base change of `U ⟶ Y`, and the graph is quasi-compact and quasi-separated
because `f` is quasi-separated (Stacks 050I).

## References

* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 04T5](https://stacks.math.columbia.edu/tag/04T5)
* [Stacks Project, Tag 050I](https://stacks.math.columbia.edu/tag/050I)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A relative property of a 1-morphism read off its composite through the graph.** Let
`a : 𝒰 ⟶ 𝒳` and `f : 𝒳 ⟶ 𝒴` be 1-morphisms of algebraic stacks over `S` with `a` and `a ≫ f`
representable by algebraic spaces, and let `P` be a property of morphisms of algebraic spaces
stable under base change and composition and local on the target. If the graph
`Γ_a : 𝒰 ⟶ 𝒰 ×_𝒴 𝒳` of `a` over `𝒴` and the composite `a ≫ f` have `P` in the relative sense of
Stacks 03YK, then so does `a`.

The 1-morphism `a` is 2-isomorphic to `Γ_a` followed by the second projection of `𝒰 ×_𝒴 𝒳`, which
is a base change of `a ≫ f` (Stacks 045C); Stacks 045B composes the two, and Stacks 0457 carries
the result along the 2-isomorphism. -/
theorem hasRelativeProperty_of_comp_of_graph
    (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)]
    [P.IsStableUnderComposition]
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (a : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (haf : IsRepresentableByAlgebraicSpaces B S hS (a ≫ f).hom.hom)
    (hPΓ : HasRelativeProperty.{u, u, u + 1, u} B S hS P
      (graph B S hS a (a ≫ f) f (Iso.refl _)).hom
      (isRepresentableByAlgebraicSpaces_graph B S hS a (a ≫ f) f (Iso.refl _)))
    (hPaf : HasRelativeProperty.{u, u, u + 1, u} B S hS P (a ≫ f).hom haf) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS P a.hom ha := by
  have : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso
  let T := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (a ≫ f).hom f.hom
  have hT : Bicategory.IsTwoFibreProduct T.swap := Bicategory.isTwoFibreProduct_swap
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (a ≫ f).hom f.hom)
  have hrep₂ := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS 𝒰.val 𝒴.val 𝒳.val
    (a ≫ f).hom f.hom T.swap hT haf
  have hP₂ := relativeProperty_baseChange.{u, u, u + 1} B S hS P 𝒰.val 𝒴.val 𝒳.val
    (a ≫ f).hom f.hom T.swap hT hPaf
  have hcomp := prop_comp_of_atlasDescent B S hS P
    (fun {_X _Y} k {_T} {_a} hsurj hetale h =>
      (Space.prop_iff_pullbackSnd_atlas.{u, u} B S hS P k hsurj hetale).2 h)
    (graph B S hS a (a ≫ f) f (Iso.refl _)).hom T.swap.fst
    (isRepresentableByAlgebraicSpaces_graph B S hS a (a ≫ f) f (Iso.refl _)) hrep₂ hPΓ hP₂
  have : Functor.IsEquivalence (BasedFunctor.id 𝒰.val.val).toFunctor :=
    Functor.isEquivalence_refl
  have : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    Functor.isEquivalence_refl
  exact relativeProperty_of_equivalences B S hS P a.hom.hom
    ((graph B S hS a (a ≫ f) f (Iso.refl _)).hom ≫ T.swap.fst).hom
    (BasedFunctor.id 𝒰.val.val) (BasedFunctor.id 𝒳.val.val)
    (Bicategory.InducedBicategory.isoHom (Bicategory.InducedBicategory.isoHom
      (graph_snd_iso B S hS a (a ≫ f) f (Iso.refl _)))).symm hcomp

/-- **Quasi-compactness of a 1-morphism from that of its composite with a quasi-separated
1-morphism**, in the relative sense of Stacks 03YK: the graph is quasi-compact by Stacks 050I
part (5). -/
theorem hasRelativeProperty_quasiCompact_of_comp
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (a : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (haf : IsRepresentableByAlgebraicSpaces B S hS (a ≫ f).hom.hom)
    (hPaf : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiCompactProperty B S hS)
      (a ≫ f).hom haf) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiCompactProperty B S hS) a.hom ha :=
  hasRelativeProperty_of_comp_of_graph B S hS _ a f ha haf
    (isQuasiCompact_graph B S hS a (a ≫ f) f (Iso.refl _) hf) hPaf

/-- **Quasi-separatedness of a 1-morphism from that of its composite with a quasi-separated
1-morphism**, in the relative sense of Stacks 03YK: the graph is quasi-separated by Stacks 050I
part (5). -/
theorem hasRelativeProperty_quasiSeparated_of_comp
    {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (a : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom.hom)
    (haf : IsRepresentableByAlgebraicSpaces B S hS (a ≫ f).hom.hom)
    (hPaf : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiSeparatedProperty B S hS)
      (a ≫ f).hom haf) :
    HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiSeparatedProperty B S hS) a.hom ha :=
  hasRelativeProperty_of_comp_of_graph B S hS _ a f ha haf
    (isQuasiSeparated_graph B S hS a (a ≫ f) f (Iso.refl _) hf) hPaf

/-- **The smooth groupoid presentation over the base, from an affine smooth chart.** Let `Y` be a
quasi-separated algebraic space over `S` and `f : 𝒳 ⟶ Y` a quasi-separated 1-morphism from an
algebraic stack with an affine smooth surjective chart. Then `𝒳` is, over `Y`, the quotient stack
of a smooth groupoid `(U, R, s, t, c)` in algebraic spaces over `Y` whose object and arrow spaces
are quasi-compact and quasi-separated over `Y`, and are locally of finite presentation (resp.
locally of finite type) over `Y` as soon as `f` is.

This is the first paragraph of the proof of Stacks 0CN4 and of Stacks 0CQ1 with the chart of
Stacks 04YC given; see the module documentation for the argument. -/
theorem exists_smoothGroupoid_overBase_of_affineSmoothChart (Y : AlgebraicSpaces B S hS)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ Y.obj) (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y.obj Y.property)
    (hfqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hchart : HasAffineSmoothPresentation.{u, w} B S hS 𝒳) :
    ∃ G : GroupoidInAlgebraicSpaces B S hS Y, GroupoidInAlgebraicSpaces.IsSmooth B S hS G ∧
      Space.IsQuasiCompact B S hS G.objectsToBase.hom ∧
      Space.IsQuasiSeparated B S hS G.objectsToBase.hom ∧
      Space.IsQuasiCompact B S hS G.arrowsToBase.hom ∧
      Space.IsQuasiSeparated B S hS G.arrowsToBase.hom ∧
      (AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
        Space.IsLocallyOfFinitePresentation B S hS G.objectsToBase.hom ∧
          Space.IsLocallyOfFinitePresentation B S hS G.arrowsToBase.hom) ∧
      (AlgebraicStacks.IsLocallyOfFiniteType B S hS f →
        Space.IsLocallyOfFiniteType B S hS G.objectsToBase.hom ∧
          Space.IsLocallyOfFiniteType B S hS G.arrowsToBase.hom) ∧
      Nonempty (BasedCategory.EquivalenceOver f.hom.hom (quotientStackToBase G)) := by
  classical
  obtain ⟨V, hVaff, a, hasurj, hrep, hsmRel⟩ := hchart
  have h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val.val := 𝒳.property
  have h₃ : IsRepresentableFromSchemes B S hS 𝒳.val := by
    obtain ⟨_, _, hdiag, -⟩ := h𝒳
    exact (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳.val).mp
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳.val).mp hdiag)
  obtain ⟨RF, hRF, ⟨eR⟩⟩ :=
    (isRepresentableFromSchemes_iff_hasAlgebraicSpaceSchemePointProducts B S hS 𝒳.val).mp h₃
      V V a.hom.hom a.hom.hom
  let Uspace : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let Rspace : AlgebraicSpaces B S hS := ⟨RF, hRF⟩
  let eU := PresheafOfCategories.sliceElementsEquivalenceOver V
  have hsurjRel : HasRelativeProperty.{u, u, u + 1, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) a.hom hrep :=
    (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS a.hom hrep).1
      (isSurjectiveOnObjects_of_pointsMap_surjective B S hS a hasurj)
  let P := SelfIntersection.selfIntersectionPresentation (f := a.hom.hom) (U := Uspace)
    (R := Rspace) eU eR h𝒳
  obtain ⟨e, he⟩ := SelfIntersection.exists_equivalenceOver_canonicalMap_of_isSmooth
    (f := a.hom) (U := Uspace) (R := Rspace) eU eR h𝒳 hsmRel hsurjRel
  let G₀ := P.groupoid
  let Eb := e.toBasedEquivalence
  have hc : Eb.functor = P.canonicalMap := BasedCategory.BasedFunctor.ext' he
  let L : quotientStack G₀ ⥤ᵇ (fibredCategory B S hS Y.obj).val :=
    BasedFunctor.comp P.canonicalMap f.hom.hom
  let u : G₀.objects ⟶ Y := restrictedMorphism G₀ L
  have hu : Space.IsInvariant (Space.groupoidPreRelation G₀) u.hom :=
    restrictedMorphism_isInvariant G₀ L
  let XtoB : Y ⟶ P.base := (Space.terminalSpace_isTerminal B S hS).from Y
  have huB : u ≫ XtoB = G₀.objectsToBase := (Space.terminalSpace_isTerminal B S hS).hom_ext _ _
  let G := (GroupoidInAlgebraicSpaces.overInvariantTarget G₀ XtoB u huB hu).val
  have hL : quotientStackToBase G = L :=
    restriction_injective G₀ _ _
      ((quotientStackProjection_comp_quotientStackOfInvariant G₀ u
        ((isInvariant_iff G₀ u).1 hu)).trans (restrictedMorphism_spec G₀ L).symm)
  -- the chart read on the object space: `a' = π ≫ c` with `π` the projection of Stacks 044R
  let eUb : (schemeFibredCategory B S hS V).val ⥤ᵇ
      (fibredCategory B S hS G₀.objects.obj).val :=
    ⟨P.sourcePresentation.hom.functor, P.sourcePresentation.hom.w⟩
  have : Functor.IsEquivalence eUb.toFunctor :=
    P.sourcePresentation.toEquivalence.isEquivalence_functor
  have hid𝒳 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    Functor.isEquivalence_refl
  let c' : (fibredCategory B S hS G₀.objects.obj).val ⥤ᵇ 𝒳.val.val :=
    BasedFunctor.comp (quotientStackProjection G₀) P.canonicalMap
  have α₀ : BasedFunctor.comp eUb c' ≅ BasedFunctor.comp a.hom.hom (BasedFunctor.id 𝒳.val.val) :=
    BasedNatIso.mkNatIso P.extends_f.1 P.extends_f.2
  let a'c : fibredCategory B S hS G₀.objects.obj ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom c'
  let a' : algebraicSpaceStack.{u, w} B S hS G₀.objects.obj G₀.objects.property ⟶
      𝒳 := Bicategory.InducedBicategory.mkHom a'c
  have hrep' : IsRepresentableByAlgebraicSpaces B S hS c' :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS a.hom.hom c' eUb
      (BasedFunctor.id 𝒳.val.val) α₀).2 hrep
  have hsm' := relativeProperty_of_equivalences_symm B S hS (Space.smoothMorphismProperty B S hS)
    a.hom.hom c' eUb (BasedFunctor.id 𝒳.val.val) α₀ hsmRel
  have hUalg : IsAlgebraicSpace B S hS G₀.objects.obj := G₀.objects.property
  -- local finite presentation of `u`
  have hlfp' : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS a' := by
    exact hasPropertyOnEverySmoothDiagram_of_hasRelativeProperty.{u, u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFinitePresentation B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS G₀.objects.obj hUalg) h𝒳 a'c hrep'
      (fun T y hy F hF hE => Space.isLocallyOfFinitePresentation_of_isSmooth B S hS
        (hsm' T y hy F hF hE))
  have hspec : algebraicSpaceStackMap.{u, w} B S hS hUalg Y.property u.hom = a' ≫ f :=
    Bicategory.InducedBicategory.hom_ext (Bicategory.InducedBicategory.hom_ext
      (restrictedMorphism_spec G₀ L).symm)
  have hulfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f →
      Space.IsLocallyOfFinitePresentation B S hS u.hom := fun hf =>
    (isLocallyOfFinitePresentation_algebraicSpaceStackMap_iff.{u, w} B S hS hUalg Y.property
      u.hom).1 (hspec ▸ AlgebraicStacks.isLocallyOfFinitePresentation_comp B S hS a' f hlfp' hf)
  have hulft : AlgebraicStacks.IsLocallyOfFiniteType B S hS f →
      Space.IsLocallyOfFiniteType B S hS u.hom := fun hf =>
    (isLocallyOfFiniteType_algebraicSpaceStackMap_iff.{u, w} B S hS hUalg Y.property
      u.hom).1 (hspec ▸ AlgebraicStacks.isLocallyOfFiniteType_comp B S hS a' f
        (AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hlfp') hf)
  have hobj : G₀.objects = Uspace := P.objects_eq
  have hUqc : Space.IsQuasiCompactSpace B S hS G₀.objects.obj := by
    rw [hobj]
    exact Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS V hVaff
  have hUqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ G₀.objects.obj := by
    rw [hobj]
    apply Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS _ hZ
    refine ⟨V, ?_, ⟨Functor.representableByEquiv.symm (Iso.refl _)⟩⟩
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj V) := hVaff
    infer_instance
  have huqc : Space.IsQuasiCompact B S hS u.hom :=
    Space.isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.property hYqs hUqc u.hom
  have huqs : Space.IsQuasiSeparated B S hS u.hom :=
    Space.isQuasiSeparated_of_isQuasiSeparatedOver B S hS
      (Space.isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated B S hS hZ hUalg hUqs) u.hom
  -- quasi-compactness and quasi-separatedness of the chart, read off its graph over `Y`
  have hrepu : IsRepresentableByAlgebraicSpaces B S hS (associatedMap B S hS u.hom).1.hom :=
    isRepresentableByAlgebraicSpaces_associatedMap (X := G₀.objects) (Y := Y) u.hom
  have α₁ : BasedFunctor.comp eUb (associatedMap B S hS u.hom).1.hom ≅
      BasedFunctor.comp (a ≫ f).hom.hom (BasedFunctor.id (fibredCategory B S hS Y.obj).val) :=
    eqToIso (congrArg (BasedFunctor.comp eUb) (restrictedMorphism_spec G₀ L).symm) ≪≫
      BasedCategory.isoWhiskerRight α₀ f.hom.hom
  have : Functor.IsEquivalence
      (BasedFunctor.id (fibredCategory B S hS Y.obj).val).toFunctor :=
    Functor.isEquivalence_refl
  have hrepaf : IsRepresentableByAlgebraicSpaces B S hS (a ≫ f).hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (a ≫ f).hom.hom
      (associatedMap B S hS u.hom).1.hom eUb (BasedFunctor.id _) α₁).1 hrepu
  have hPaf : ∀ (Q : MorphismProperty (AlgebraicSpaces B S hS)) [Q.IsStableUnderBaseChange]
      [Q.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      Q u → HasRelativeProperty.{u, u, u + 1, u} B S hS Q (a ≫ f).hom hrepaf := by
    intro Q _ _ hQ
    refine relativeProperty_of_equivalences B S hS Q (a ≫ f).hom.hom
      (associatedMap B S hS u.hom).1.hom eUb (BasedFunctor.id _) α₁ ?_
    refine (hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS Q
      (associatedMap B S hS u.hom).1 hrepu G₀.objects.obj Y.obj hUalg Y.property
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).2 ?_
    rw [representingMap_associatedMap]
    exact hQ
  have hPaqc : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiCompactProperty B S hS)
      a.hom hrep :=
    hasRelativeProperty_quasiCompact_of_comp B S hS a f hfqs hrep hrepaf
      (hPaf (Space.quasiCompactProperty B S hS) huqc)
  have hPaqs : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.quasiSeparatedProperty B S hS)
      a.hom hrep :=
    hasRelativeProperty_quasiSeparated_of_comp B S hS a f hfqs hrep hrepaf
      (hPaf (Space.quasiSeparatedProperty B S hS) huqs)
  have hsqc := SelfIntersection.prop_relationSource B S hS (schemeFibredCategory B S hS V) 𝒳.val
    a.hom Uspace Rspace eU eR
      (Space.quasiCompactProperty B S hS) hrep hPaqc
  have hsqs := SelfIntersection.prop_relationSource B S hS (schemeFibredCategory B S hS V) 𝒳.val
    a.hom Uspace Rspace eU eR
      (Space.quasiSeparatedProperty B S hS) hrep hPaqs
  have hssm : Space.IsSmooth B S hS G₀.source.hom :=
    SelfIntersection.isSmooth_selfIntersectionPresentation_source
      (F := a.hom) (U := Uspace) (R := Rspace) eU eR hrep hsmRel h𝒳
  have hsqc' : Space.IsQuasiCompact B S hS G₀.source.hom := hsqc
  have hsqs' : Space.IsQuasiSeparated B S hS G₀.source.hom := hsqs
  refine ⟨G, ⟨hssm, ?_⟩, huqc, huqs,
    Space.isQuasiCompact_comp B S hS hUalg Y.property G₀.source.hom u.hom hsqc' huqc,
    Space.isQuasiSeparated_comp B S hS G₀.arrows.property hUalg G₀.source.hom u.hom hsqs' huqs,
    fun hf => ⟨hulfp hf, ?_⟩, fun hf => ⟨hulft hf, ?_⟩, ⟨{ equiv := Eb.symm, compIso := ?_ }⟩⟩
  · exact SelfIntersection.isSmooth_selfIntersectionPresentation_target
      (F := a.hom) (U := Uspace) (R := Rspace) eU eR hrep hsmRel h𝒳
  · exact Space.isLocallyOfFinitePresentation_comp B S hS G₀.arrows.property hUalg Y.property
      G₀.source.hom u.hom (Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hssm) (hulfp hf)
  · exact Space.isLocallyOfFiniteType_comp B S hS G₀.arrows.property hUalg Y.property
      G₀.source.hom u.hom (Space.isLocallyOfFiniteType_of_isSmooth B S hS hssm) (hulft hf)
  · change Eb.inverse.comp (quotientStackToBase G) ≅ f.hom.hom
    rw [hL, show L = BasedFunctor.comp Eb.functor f.hom.hom from
      congrArg (fun F => BasedFunctor.comp F f.hom.hom) hc.symm]
    exact BasedCategory.isoWhiskerRight Eb.counitIso f.hom.hom

/-- **The groupoid presentation over the base, from an affine smooth chart.** An algebraic stack
`𝒳` of finite presentation over a quasi-compact, quasi-separated algebraic space `Y` over `S`
which has an affine smooth surjective chart is, over `Y`, the quotient stack of a smooth groupoid
in algebraic spaces over `Y` whose object and arrow spaces are of finite presentation over `Y`.

This is the first paragraph of the proof of Stacks 0CN4 with the chart of Stacks 04YC given:
`AlgebraicGeometry.Stack.exists_smoothGroupoid_overBase_of_affineSmoothChart`. -/
theorem groupoidPresentationOfAffineSmoothChart :
    GroupoidPresentationOfAffineSmoothChart.{u, w} B S hS hZ := by
  intro Y _ hYqs 𝒳 f hf hchart
  obtain ⟨G, hG, huqc, huqs, hrqc, hrqs, hlfp, -, ⟨e⟩⟩ :=
    exists_smoothGroupoid_overBase_of_affineSmoothChart.{u, w} B S hS hZ Y hYqs 𝒳 f hf.2.2 hchart
  exact ⟨{ groupoid := G, isSmooth := hG
           objects_finitePresentation := ⟨(hlfp hf.1).1, huqc, huqs⟩
           arrows_finitePresentation := ⟨(hlfp hf.1).2, hrqc, hrqs⟩
           equivOver := e }⟩

end AlgebraicGeometry.Stack

end
