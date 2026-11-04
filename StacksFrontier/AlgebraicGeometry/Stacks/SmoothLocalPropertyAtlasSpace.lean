module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveProperties

/-!
# The two algebraic-space criteria of Stacks 04YF, and the represented cases

Let `P` be a property of schemes local in the smooth topology (**Stacks 0348**). Two of the four
conditions of **Stacks 04YF** are about algebraic-space charts: that *some* smooth surjective
1-morphism from the algebraic stack of an algebraic space over `S` has source with the étale-local
property `P` of **Stacks 03E6**, and that *every* smooth one does. This module proves those two
equivalent to the scheme criteria of
`StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme`, and identifies them with
the étale-local property when the stack is the one of an algebraic space.

The source's argument is that the implications (2) ⇒ (1), (1) ⇒ (3) and (4) ⇒ (2) are immediate
once a scheme is read as an algebraic space and an étale scheme atlas of an algebraic space is
read as a smooth scheme chart of its stack. Both readings are instances of one statement: a
1-morphism of algebraic stacks whose source and target are representable by algebraic spaces *is*
a morphism of the representing presheaves (**Stacks 04SW**), with smoothness and surjectivity
transported in both directions.

## Main results

* `AlgebraicGeometry.Stack.exists_scheme_atlas_iff_exists_space_atlas`: the existential scheme and
  algebraic-space criteria agree.
* `AlgebraicGeometry.Stack.exists_space_atlas_iff_forall_space`: the two algebraic-space criteria
  agree.
* `AlgebraicGeometry.Stack.exists_space_atlas_iff_space`: on the algebraic stack of an algebraic
  space they are the étale-local property of that algebraic space.
* `AlgebraicGeometry.Stack.isSmooth_comp_of_isRepresentableByAlgebraicSpace`: smooth 1-morphisms
  of algebraic stacks compose when the first two objects are representable by algebraic spaces.

## Implementation notes

The smooth locality the comparisons need, **Stacks 06FC** in the smooth case, is
`AlgebraicGeometry.Space.isSmoothLocalOnSourceAndTarget_smooth`.
`scheme_atlas_iff_etaleLocalProperty` is the implication (3) ⇒ (4) of Stacks 04YF in the single
case where the chart is the atlas itself.

Unlike the scheme criteria, the comparison with the algebraic-space criteria does need a
composition law for smooth 1-morphisms of algebraic stacks: a scheme chart of an algebraic-space
chart of `𝒳` is a scheme chart of `𝒳`, and the target `𝒳` is arbitrary.
`isSmooth_comp_of_isRepresentableByAlgebraicSpace` supplies it in the only generality needed, the
first two objects being representable by algebraic spaces, and **its 2-cell is not built by
product calculus**. Both halves of the required square are 1-morphisms between objects
representable by algebraic spaces, so the uniqueness clause of Stacks 04SW
(`AlgebraicGeometry.Stack.nonempty_unique_twoIso_of_representingMap_eq`) produces the comparison
2-isomorphisms from an *equality of morphisms of representing presheaves* — and that equality is
the defining square of a fibre product of algebraic spaces. The rest of the 2-cell is five
associators and two whiskerings.

The diagram the composite is tested on is the source's: for a diagram `(U₂, V₂, a₂, b₂, h₂)` of
the second 1-morphism, base change the representing morphism `U₂ ⟶ G` of `a₂` along the
representing morphism `F ⟶ G` of the first 1-morphism; the apex is the new source corner, its
projection to `F` composed with the representing equivalence is the new left vertical
1-morphism — smooth and surjective on objects because the projection is a base change of a smooth
surjection — and the new top morphism is the other projection followed by `h₂`.

`exists_oneMorphism_representingMap_eq` is stated as an existential rather than as a definition
with a computation rule: nothing downstream needs the 1-morphism itself, only that one exists
inducing the given morphism of representing presheaves, and the 2-isomorphism class the
Stacks 04SW bijection returns has no canonical representative.

## References

* [Stacks Project, Tag 0348](https://stacks.math.columbia.edu/tag/0348)
* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XI](https://stacks.math.columbia.edu/tag/04XI)
* [Stacks Project, Tag 04XX](https://stacks.math.columbia.edu/tag/04XX)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 04ZT](https://stacks.math.columbia.edu/tag/04ZT)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A morphism of representing presheaves is a 1-morphism -/

/-- **The surjectivity clause of Stacks 04SW.** Every morphism of the presheaves representing two
algebraic stacks over `S` is induced by a 1-morphism between them.

Only existence is asserted: the Stacks 04SW bijection returns a 2-isomorphism class, which has no
canonical representative. -/
theorem exists_oneMorphism_representingMap_eq
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (h : F ⟶ G) :
    ∃ f : 𝒳 ⟶ 𝒴, representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom = h := by
  obtain ⟨q, hq⟩ :=
    Quotient.exists_rep ((morphismSpaceEquiv B S hS 𝒳.val 𝒴.val F G eF eG).symm h)
  refine ⟨Bicategory.InducedBicategory.mkHom
    ((CatFiberedInGroupoids.homEquivBasedFunctor 𝒳.val 𝒴.val).symm ⟨q.1, q.2⟩), ?_⟩
  have hsub : (⟨CatFiberedInGroupoids.homFunctor
        ((CatFiberedInGroupoids.homEquivBasedFunctor 𝒳.val 𝒴.val).symm ⟨q.1, q.2⟩),
      CatFiberedInGroupoids.homFunctor_comp_p
        ((CatFiberedInGroupoids.homEquivBasedFunctor 𝒳.val 𝒴.val).symm ⟨q.1, q.2⟩)⟩ :
      {H : 𝒳.val.val.obj ⥤ 𝒴.val.val.obj // H ⋙ 𝒴.val.val.p = 𝒳.val.val.p}) = q :=
    Subtype.ext rfl
  rw [show representingMap B S hS 𝒳.val 𝒴.val F G eF eG
        ((CatFiberedInGroupoids.homEquivBasedFunctor 𝒳.val 𝒴.val).symm ⟨q.1, q.2⟩)
      = morphismSpaceEquiv B S hS 𝒳.val 𝒴.val F G eF eG (Quotient.mk _ q) from
    congrArg (morphismSpaceEquiv B S hS 𝒳.val 𝒴.val F G eF eG)
      (congrArg (Quotient.mk _) hsub), hq]
  exact (morphismSpaceEquiv B S hS 𝒳.val 𝒴.val F G eF eG).apply_symm_apply h

/-- **The converse half of Stacks 06FM for representable source and target.** A 1-morphism of
algebraic stacks over `S` between two objects representable by algebraic spaces is smooth as soon
as the induced morphism of representing presheaves is. No smooth-locality hypothesis is needed in
this direction. -/
theorem isSmooth_of_isSmooth_representingMap
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴)
    (hf : Space.IsSmooth B S hS (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom)) :
    AlgebraicStacks.IsSmooth B S hS f :=
  hasPropertyOnSomeSmoothDiagram_of_prop_representingMap B S hS _ F G hF hG eF eG f.hom hf

/-- **The converse of `AlgebraicGeometry.Stack.isSurjective_representingMap_of_isSurjective`.** A
1-morphism of algebraic stacks over `S` between two objects representable by algebraic spaces is
surjective (**Stacks 04ZS**) as soon as the induced morphism of representing presheaves is
(**Stacks 03ME**): the 1-morphism is representable by algebraic spaces, so Stacks 04XI reduces
surjectivity on points to the relative surjectivity of Stacks 03YK, which the bridge of
Stacks 04XB reads on the induced morphism. -/
theorem isSurjective_of_isSurjective_representingMap
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒴)
    (hf : Space.IsSurjective B S hS (representingMap B S hS 𝒳.val 𝒴.val F G eF eG f.hom)) :
    IsSurjective B S hS f := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS f.hom
      ⟨F, hF, ⟨eF⟩⟩ ⟨G, hG, ⟨eG⟩⟩
  exact (pointsMap_surjective_iff_isRelativelySurjective.{u, w, u} B S hS f hrep).mpr
    ((hasRelativeProperty_iff_prop_representingMap.{u, u} B S hS
      (Space.surjectiveMorphismProperty B S hS) f.hom hrep F G hF hG eF eG).2 hf)

/-! ### Composition of smooth 1-morphisms out of representable objects -/

/-- **Smooth 1-morphisms of algebraic stacks over `S` compose, when the first two objects are
representable by algebraic spaces.**

The diagram the composite is tested on is the source's. Given a diagram `(U₂, V₂, a₂, b₂, h₂)`
for `g`, base change the morphism `U₂ ⟶ G` of representing presheaves induced by `a₂` along the
morphism `F ⟶ G` induced by `f`; both are smooth, and the first is surjective because `a₂` is
surjective on objects. The apex `T` of the base change is the new source corner, its projection
to `F` followed by the representing equivalence of `𝒰` is the new left vertical 1-morphism, and
`T ⟶ U₂ ⟶ V₂` is the new top morphism of algebraic spaces.

The 2-cell is assembled from the filler of the given diagram, the functoriality
`AlgebraicGeometry.Stack.associatedMap_comp` of the associated 1-morphism (Stacks 0458), and the
*uniqueness* clause of Stacks 04SW: the remaining square is a square of 1-morphisms between
objects representable by algebraic spaces, so it is enough that its two sides induce the same
morphism of representing presheaves, which is the defining square of the fibre product. -/
theorem isSmooth_comp_of_isRepresentableByAlgebraicSpace
    (hsm : Space.IsSmoothLocalOnSourceAndTarget B S hS
      (fun _ _ k => Space.IsSmooth B S hS k))
    {𝒰 𝒱 𝒵 : AlgebraicStacks.{u, w} B S hS}
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒱.val.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (f : 𝒰 ⟶ 𝒱) (g : 𝒱 ⟶ 𝒵)
    (hf : AlgebraicStacks.IsSmooth B S hS f) (hg : AlgebraicStacks.IsSmooth B S hS g) :
    AlgebraicStacks.IsSmooth B S hS (f ≫ g) := by
  obtain ⟨U₂, V₂, hU₂, hV₂, a₂, b₂, h₂, ⟨η₂⟩, ha₂, hsurj₂, hb₂, hP₂⟩ := hg
  obtain ⟨φ, hφEq, hφ⟩ : ∃ φ : F ⟶ G,
      representingMap B S hS 𝒰.val 𝒱.val F G eF eG f.hom = φ ∧
        Space.IsSmooth B S hS φ :=
    ⟨_, rfl, isSmooth_representingMap_of_isSmooth B S hS hsm F G hF hG eF eG f hf⟩
  obtain ⟨u₂, hu₂Eq, hu₂, hu₂Surj⟩ : ∃ u₂ : U₂ ⟶ G,
      representingMap B S hS (fibredCategory B S hS U₂) 𝒱.val U₂ G
          (StacksRepresentableCFG.EquivalenceOver.refl _) eG a₂ = u₂ ∧
        Space.IsSmooth B S hS u₂ ∧ Space.IsSurjective B S hS u₂ :=
    ⟨_, rfl,
      (isRelativelySmooth_iff_isSmooth_representingMap B S hS a₂ ha₂.1 U₂ G hU₂ hG
        (StacksRepresentableCFG.EquivalenceOver.refl _) eG).1 ha₂,
      isSurjective_representingMap_of_isSurjectiveOnObjects B S hS a₂ U₂ G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eG hsurj₂⟩
  obtain ⟨T, hT, t₁, t₂, ht₁, ht₁Surj, ht₂, hcond⟩ :=
    Space.exists_smoothPullback B S hS hF hG hU₂ φ u₂ hφ hu₂ hu₂Surj
  have hψ : Unique ((associatedMap B S hS t₂).1 ≫ a₂ ≅
      (associatedMap B S hS t₁).1 ≫ (equivalenceOverInvMap B S hS F eF ≫ f.hom)) := by
    refine (nonempty_unique_twoIso_of_representingMap_eq B S hS
      (fibredCategory B S hS T) 𝒱.val T G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eG ?_).some
    have hL := representingMap_comp B S hS T U₂ G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) eG
      (associatedMap B S hS t₂).1 a₂
    rw [representingMap_associatedMap, hu₂Eq] at hL
    have hR2 := representingMap_comp B S hS F F G
      (StacksRepresentableCFG.EquivalenceOver.refl _) eF eG
      (equivalenceOverInvMap B S hS F eF) f.hom
    rw [representingMap_equivalenceOverInvMap, hφEq, Category.id_comp] at hR2
    have hR := representingMap_comp B S hS T F G
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) eG
      (associatedMap B S hS t₁).1 (equivalenceOverInvMap B S hS F eF ≫ f.hom)
    rw [representingMap_associatedMap, hR2] at hR
    rw [hL, hR, hcond]
  refine ⟨T, V₂, hT, hV₂,
    (associatedMap B S hS t₁).1 ≫ equivalenceOverInvMap B S hS F eF, b₂, t₂ ≫ h₂,
    ⟨?_⟩, ?_, ?_, hb₂, ?_⟩
  · exact Bicategory.whiskerRightIso (eqToIso (associatedMap_comp B S hS t₂ h₂)) b₂ ≪≫
      α_ _ _ _ ≪≫ Bicategory.whiskerLeftIso _ η₂ ≪≫ (α_ _ _ _).symm ≪≫
      Bicategory.whiskerRightIso hψ.default g.hom ≪≫ α_ _ _ _ ≪≫
      Bicategory.whiskerLeftIso _ (α_ _ _ _) ≪≫ (α_ _ _ _).symm
  · exact isRelativelySmooth_comp B S hS _ _
      (isRelativelySmooth_associatedMap B S hS hT hF t₁ ht₁)
      (isRelativelySmooth_equivalenceOverInvMap B S hS F hF eF)
  · exact isSurjectiveOnObjects_comp B S hS _ _ _ _ _
      (CatFiberedInGroupoids.homFunctor_comp_p (equivalenceOverInvMap B S hS F eF))
      (isSurjectiveOnObjects_associatedMap B S hS hT hF t₁ ht₁Surj)
      (isSurjectiveOnObjects_equivalenceOverInvMap B S hS F eF)
  · exact Space.isSmooth_comp B S hS hT hU₂ hV₂ t₂ h₂ ht₂ hP₂

/-! ### Scheme charts of the stack of an algebraic space -/

/-- **An étale scheme atlas of an algebraic space is a smooth scheme chart of its algebraic
stack**, and a surjective one is a surjective chart. The 1-morphism is the one Stacks 04SW
attaches to the atlas; smoothness is Stacks 04XX followed by the converse half of Stacks 06FM,
and surjectivity is Stacks 03H5 followed by Stacks 04XI. -/
theorem exists_schemeStack_hom_of_etaleChart
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ F)
    (haEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a) :
    ∃ c : schemeStack.{u, w} B S hS U ⟶ algebraicSpaceStack.{u, w} B S hS F hF,
      AlgebraicStacks.IsSmooth B S hS c ∧
        ((MorphismProperty.inverseImage
            (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS)).presheaf a →
          IsSurjective B S hS c) := by
  obtain ⟨c, hc⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := schemeStack.{u, w} B S hS U) (𝒴 := algebraicSpaceStack.{u, w} B S hS F hF)
    (yoneda.obj U) F (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) a
  refine ⟨c, ?_, fun haSurj => ?_⟩
  · refine isSmooth_of_isSmooth_representingMap B S hS (yoneda.obj U) F
      (isAlgebraicSpace_yoneda B S hS U) hF
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) c ?_
    rw [hc]
    exact Space.isSmooth_of_isEtale B S hS hF
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS a).2 haEtale)
  · refine isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj U) F
      (isAlgebraicSpace_yoneda B S hS U) hF
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (StacksRepresentableCFG.EquivalenceOver.refl _) c ?_
    rw [hc]
    exact (Space.surjective_iff_surjective_pointsMap B S hS F hF U a).1 haSurj

/-- **The algebraic stack of the algebraic space represented by a scheme over `S` maps to the
algebraic stack of that scheme by a smooth surjective 1-morphism.** Both are representable by the
same presheaf, so the 1-morphism Stacks 04SW attaches to its identity does it. -/
theorem exists_smooth_surjective_algebraicSpaceStack_hom (U : BigFppfOver B S hS) :
    ∃ e : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶
        schemeStack.{u, w} B S hS U,
      AlgebraicStacks.IsSmooth B S hS e ∧ IsSurjective B S hS e := by
  obtain ⟨e, he⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
    (𝒴 := schemeStack.{u, w} B S hS U)
    (yoneda.obj U) (yoneda.obj U) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) (𝟙 (yoneda.obj U))
  refine ⟨e, ?_, ?_⟩
  · refine isSmooth_of_isSmooth_representingMap B S hS (yoneda.obj U) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS U)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) e ?_
    rw [he]
    exact Space.isSmooth_id B S hS (isAlgebraicSpace_yoneda B S hS U)
  · refine isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj U) (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U) (isAlgebraicSpace_yoneda B S hS U)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (PresheafOfCategories.sliceElementsEquivalenceOver U) e ?_
    rw [he]
    exact Space.isSurjective_id B S hS (yoneda.obj U)

/-! ### The comparisons -/

/-- Smooth 1-morphisms compose from the algebraic stack of the algebraic space of a scheme `U`
over `S` to the algebraic stack of `U` and on to any algebraic stack. -/
private theorem isSmooth_comp_algebraicSpaceStack_schemeStack {U : BigFppfOver B S hS}
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {e : algebraicSpaceStack.{u, w} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U) ⟶
      schemeStack.{u, w} B S hS U}
    {a : schemeStack.{u, w} B S hS U ⟶ 𝒳}
    (he : AlgebraicStacks.IsSmooth B S hS e) (ha : AlgebraicStacks.IsSmooth B S hS a) :
    AlgebraicStacks.IsSmooth B S hS (e ≫ a) :=
  isSmooth_comp_of_isRepresentableByAlgebraicSpace B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (yoneda.obj U) (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
    (isAlgebraicSpace_yoneda B S hS U) (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) e a he ha

/-- Smooth 1-morphisms compose from the algebraic stack of a scheme `U` over `S` to the algebraic
stack of an algebraic space `F` and on to any algebraic stack. -/
private theorem isSmooth_comp_schemeStack_algebraicSpaceStack {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {b : schemeStack.{u, w} B S hS U ⟶ algebraicSpaceStack.{u, w} B S hS F hF}
    {a : algebraicSpaceStack.{u, w} B S hS F hF ⟶ 𝒳}
    (hb : AlgebraicStacks.IsSmooth B S hS b) (ha : AlgebraicStacks.IsSmooth B S hS a) :
    AlgebraicStacks.IsSmooth B S hS (b ≫ a) :=
  isSmooth_comp_of_isRepresentableByAlgebraicSpace B S hS
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (yoneda.obj U) F (isAlgebraicSpace_yoneda B S hS U) hF
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (StacksRepresentableCFG.EquivalenceOver.refl _) b a hb ha

variable (P : ObjectProperty Scheme.{u})
  [P.IsLocal (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]

/-- **The scheme criterion of Stacks 04YF on the algebraic stack of an algebraic space is the
étale-local property of Stacks 03E6.** This is the content of the implication (3) ⇒ (4) of
Stacks 04YF in the case where the chart is the atlas itself.

Forward: an étale scheme atlas of the algebraic space is a smooth scheme chart of its stack, so
the universal scheme criterion applies to it. Backward: the same chart, with the property of its
source given. -/
theorem scheme_atlas_iff_etaleLocalProperty
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasPropertyOnSomeSchemeAtlas B S hS P (algebraicSpaceStack.{u, w} B S hS F hF) ↔
      Space.HasEtaleLocalProperty B S hS F P := by
  constructor
  · intro h
    obtain ⟨U, a, haSurj, haEtale⟩ := hF.exists_atlas
    obtain ⟨c, hcSmooth, -⟩ := exists_schemeStack_hom_of_etaleChart.{u, w} B S hS hF a haEtale
    exact ⟨U, a, haSurj, haEtale,
      (exists_scheme_atlas_iff_forall_scheme B S hS P _).mp h U c hcSmooth⟩
  · rintro ⟨U, a, haSurj, haEtale, hU⟩
    obtain ⟨c, hcSmooth, hcSurj⟩ :=
      exists_schemeStack_hom_of_etaleChart.{u, w} B S hS hF a haEtale
    exact ⟨U, c, hcSurj haSurj, hcSmooth, hU⟩

/-- An algebraic stack over `S` admits a smooth surjective 1-morphism from the algebraic stack of
a scheme over `S` with `P` exactly when it admits one from the algebraic stack of an algebraic
space over `S` with the étale-local property `P` of Stacks 03E6. -/
@[stacks 04YF "scheme and space atlases"]
theorem exists_scheme_atlas_iff_exists_space_atlas
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasPropertyOnSomeSchemeAtlas B S hS P 𝒳 ↔
      HasPropertyOnSomeSpaceAtlas B S hS P 𝒳 := by
  constructor
  · rintro ⟨U, a, haSurj, haSmooth, hU⟩
    obtain ⟨e, heSmooth, heSurj⟩ :=
      exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
    exact ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, e ≫ a,
      isSurjective_comp B S hS e a heSurj haSurj,
      isSmooth_comp_algebraicSpaceStack_schemeStack B S hS heSmooth haSmooth,
      (Space.exists_atlas_iff_of_representable B S hS (yoneda.obj U) P U (Iso.refl _)).mpr hU⟩
  · rintro ⟨F, hF, a, haSurj, haSmooth, hP⟩
    obtain ⟨U, b, hbSurj, hbSmooth, hU⟩ :=
      (scheme_atlas_iff_etaleLocalProperty.{u, w} B S hS P F hF).mpr hP
    exact ⟨U, b ≫ a, isSurjective_comp B S hS b a hbSurj haSurj,
      isSmooth_comp_schemeStack_algebraicSpaceStack B S hS hbSmooth haSmooth, hU⟩

/-- An algebraic stack over `S` admits a smooth surjective 1-morphism from the algebraic stack of
an algebraic space over `S` with the étale-local property `P` exactly when every smooth
1-morphism from the algebraic stack of an algebraic space over `S` has source with that
property. -/
@[stacks 04YF "space criteria"]
theorem exists_space_atlas_iff_forall_space
    (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    HasPropertyOnSomeSpaceAtlas B S hS P 𝒳 ↔
      HasPropertyOnEverySpaceChart B S hS P 𝒳 := by
  constructor
  · intro h F hF a ha
    have hschemes := (exists_scheme_atlas_iff_forall_scheme B S hS P 𝒳).mp
      ((exists_scheme_atlas_iff_exists_space_atlas B S hS P 𝒳).mpr h)
    obtain ⟨U, b, hbSurj, hbEtale⟩ := hF.exists_atlas
    obtain ⟨c, hcSmooth, -⟩ := exists_schemeStack_hom_of_etaleChart.{u, w} B S hS hF b hbEtale
    exact ⟨U, b, hbSurj, hbEtale, hschemes U (c ≫ a)
      (isSmooth_comp_schemeStack_algebraicSpaceStack B S hS hcSmooth ha)⟩
  · intro h
    obtain ⟨U, a, haSmooth, haSurj⟩ := exists_smooth_surjective_schemeStack B S hS 𝒳
    obtain ⟨e, heSmooth, heSurj⟩ :=
      exists_smooth_surjective_algebraicSpaceStack_hom.{u, w} B S hS U
    have hcomp := isSmooth_comp_algebraicSpaceStack_schemeStack B S hS heSmooth haSmooth
    exact ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U, e ≫ a,
      isSurjective_comp B S hS e a heSurj haSurj, hcomp,
      h _ (isAlgebraicSpace_yoneda B S hS U) (e ≫ a) hcomp⟩

/-- On the algebraic stack of an algebraic space over `S`, the existential algebraic-space
criterion for a smooth-local property `P` is the étale-local property `P` of Stacks 03E6 of that
algebraic space. -/
@[stacks 04YF "algebraic-space case"]
theorem exists_space_atlas_iff_space
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasPropertyOnSomeSpaceAtlas B S hS P (algebraicSpaceStack.{u, w} B S hS F hF) ↔
      Space.HasEtaleLocalProperty B S hS F P :=
  (exists_scheme_atlas_iff_exists_space_atlas B S hS P _).symm.trans
    (scheme_atlas_iff_etaleLocalProperty.{u, w} B S hS P F hF)

end AlgebraicGeometry.Stack

end
