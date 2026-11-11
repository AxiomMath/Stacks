module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyOpenSubmersiveBaseChange
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelFstTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.Topology.Maps.OpenSurjectiveDescent

/-!
# Open morphisms of algebraic stacks (Stacks 06U1, 04XB)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` which is representable by algebraic
spaces. **Stacks 06U1** says that the following two conditions on `f` are equivalent:

1. `f` is *universally open* in the sense of Properties of Stacks, Section **04XB** — the relative
   property of Stacks 03YK tested at universal openness of morphisms of algebraic spaces; and
2. for every 1-morphism `𝒵 ⟶ 𝒴` of algebraic stacks over `S`, the map of topological spaces
   `|𝒵 ×_𝒴 𝒳| → |𝒵|` is open.

The second condition is already in the library: it is
`AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyOpen` (**Stacks 06U2**, part (2)), whose
quantifier over a test stack `𝒵` and a 1-morphism `g : 𝒵 ⟶ 𝒴` asks exactly that the first
projection of the canonical 2-fibre product square of Stacks 04T2 be an open map for the topology
of Stacks 04XL. The first condition is *not*: the Stacks 04XB notion at universal openness is
introduced here, as `AlgebraicGeometry.Stack.UniversallyOpen`, alongside its closed sibling
`AlgebraicGeometry.Stack.UniversallyClosed` and the two other instances of the same pattern,
`...IsSeparated` and `...IsProper`. So the theorem below is a statement about two genuinely
different predicates and not a reformulation of either.

This is the open mirror of **Stacks 0512**
(`AlgebraicGeometry.Stack.representable_universallyClosed_iff_closedMap_baseChange`) and it is
assembled the same way, from the same three transfers, with only the second of them re-proved
here: the point-set congruence for the choice of 2-fibre product is already available on the open
side as `AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr` (the open half of Stacks 06U3),
and the topological descent step is already available as
`isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective`.

For the forward direction, take a chart of `𝒵` by the slice of the site over a scheme `U` which is
open and surjective on points. Universal openness of `f`, read on the lower-shriek extension at
the scheme-valued point of `𝒴` that the chart names, says the structural morphism of the presheaf
representing the base change is an open morphism of algebraic spaces; the second transfer turns
that into openness on points of the first projection of the canonical square over that point;
Stacks 02XD's first-factor cancellation and
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr` move it to `U ×_𝒵 (𝒵 ×_𝒴 𝒳)`; and the open
surjection `|U| → |𝒵|` descends it to `𝒵 ×_𝒴 𝒳`, the surjectivity of the comparison map to the
topological fibre product being Stacks 04XH.

For the converse, a morphism `k : Z ⟶ h_U` of algebraic spaces is the morphism of representing
presheaves induced by a 1-morphism out of the category of elements of `Z` (Stacks 04SW, onto); the
hypothesis at that algebraic stack, pushed through two first-factor cancellations, is openness on
points of the first projection of `Z ×_U (U ×_𝒴 𝒳)`; the second transfer reads that on the
representing presheaves; and Stacks 04SD identifies the representing presheaf of that apex with
`Z ×_{h_U} Λ_U T`, which is the base change `AlgebraicGeometry.Space.UniversallyOpen` is asking
about.

## Main definitions

* `AlgebraicGeometry.Stack.UniversallyOpen`: the Stacks 04XB notion at universal openness of
  morphisms of algebraic spaces.

## Main results

* `AlgebraicGeometry.Stack.universallyOpen_iff_forall_relocalize`: that notion read on the
  lower-shriek extension of Stacks 03I5.
* `AlgebraicGeometry.Stack.isOpenMap_pointsMap_iff_isOpenMorphism_representingMap`: openness on
  points of a 1-morphism of represented categories fibred in groupoids is openness of the induced
  morphism of representing presheaves.
* `AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_of_universallyOpen` and
  `...universallyOpen_of_isOpenMap_pointsMap_fst`: the two implications.
* `AlgebraicGeometry.Stack.representable_universallyOpen_iff_openMap_baseChange`: **Stacks 06U1**.

## Implementation notes

`AlgebraicGeometry.Stack.UniversallyOpen` writes the quantifier of Stacks 04XB out longhand
instead of instantiating `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**), for the
reason recorded in the file of `AlgebraicGeometry.Stack.UniversallyClosed`: the general notion
carries the instance arguments `IsStableUnderBaseChange` and locality at the target for the fppf
precoverage, the latter for universal openness being Stacks 041P
(`AlgebraicGeometry.Space.universallyOpen_isLocalAtTarget_fpqc`, moved to the fppf precoverage
along Stacks 0DFQ). Writing the quantifier out gives the same proposition with no hypothesis on
the property. The route below reaches `AlgebraicGeometry.Stack.prop_algebraicSpaceMap_iff`, which
needs only `RespectsIso`, so no locality is used for Stacks 06U1; the `RespectsIso` witness is
`AlgebraicGeometry.Stack.universallyOpenMorphismProperty_respectsIso`, which reads universal
openness as `CategoryTheory.MorphismProperty.universally` of being an open morphism.

That definition is the section's relative property at the single entry *universally open*,
which is the notion Stacks 06U1 part (1) refers to; it carries no `@[stacks]` attribute. The
general relative property is `AlgebraicGeometry.Stack.HasRelativeProperty` (Stacks 03YK), and the
assertions of Section 04XB about it, for every property the section lists, are
`AlgebraicGeometry.Stack.representableMorphismProperties`, which is the Stacks 04XB registration.

The `@[stacks 06U1]` attribute sits on the equivalence alone, which is that tag's whole covering
set: both directions are proved, and neither side of it is definitionally the other.

The topology of Stacks 04XL is a `def` and not an instance, so every point-set statement here
names it explicitly through `@IsOpenMap`.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 06U1](https://stacks.math.columbia.edu/tag/06U1)
* [Stacks Project, Tag 06U2](https://stacks.math.columbia.edu/tag/06U2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The Stacks 04XB notion at universal openness -/

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is universally open* when every algebraic space representing
its base change along a scheme-valued point of the target has universally open structural
morphism, read as a morphism of algebraic spaces over `S`. This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.UniversallyOpen`, and it is the condition Stacks 06U1 part (1) names.

It is *not* `AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyOpen`, which is Stacks 06U2
part (2) and tests openness of base changes on the topological spaces of points; the equivalence
of the two is Stacks 06U1. -/
abbrev UniversallyOpen {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.UniversallyOpen B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- Universal openness of morphisms of algebraic spaces over `S`, as a property of morphisms in
the category of algebraic spaces over `S`, respects isomorphisms: it is
`CategoryTheory.MorphismProperty.universally` of being an open morphism, by
`AlgebraicGeometry.Space.universallyOpen_iff_universally_isOpenMorphism`, and that construction
respects isomorphisms for every property. -/
theorem universallyOpenMorphismProperty_respectsIso :
    (Space.universallyOpenMorphismProperty B S hS).RespectsIso := by
  have heq : Space.universallyOpenMorphismProperty B S hS =
      (Space.isOpenMorphismProperty B S hS).universally := by
    funext X T g
    exact propext (Space.universallyOpen_iff_universally_isOpenMorphism B S hS g)
  rw [heq]
  infer_instance

/-- **Universal openness of a representable 1-morphism, read on the lower-shriek extension.**
`AlgebraicGeometry.Stack.UniversallyOpen` tests the structural morphism of Stacks 04SG of each
algebraic space representing a base change along a scheme-valued point of the target; this reads
that test on `CategoryTheory.OverShriek.relocalizeToYoneda`, which is the explicit form of that
structural morphism. Only `RespectsIso` is used, so this needs no locality of universal openness
for the fppf topology. -/
theorem universallyOpen_iff_forall_relocalize
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    UniversallyOpen B S hS f ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (_hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (T ⋙ typeToCat)).p) →
        Space.UniversallyOpen B S hS (OverShriek.relocalizeToYoneda U.hom T) := by
  have := universallyOpenMorphismProperty_respectsIso B S hS
  constructor <;> intro H U y hy T hT he
  · exact (prop_algebraicSpaceMap_iff B S hS (Space.universallyOpenMorphismProperty B S hS)
      U T hT).mp (H U y hy T hT he)
  · exact (prop_algebraicSpaceMap_iff B S hS (Space.universallyOpenMorphismProperty B S hS)
      U T hT).mpr (H U y hy T hT he)

/-! ### Openness on points against openness of the representing morphism -/

/-- Openness of a map transfers across a commutative square whose two horizontal maps are
homeomorphisms. -/
private theorem isOpenMap_iff_of_isHomeomorph {A C A' C' : Type*} [TopologicalSpace A]
    [TopologicalSpace C] [TopologicalSpace A'] [TopologicalSpace C']
    {p : A → C} {q : A' → C'} {σ : A → A'} {τ : C → C'}
    (hσ : IsHomeomorph σ) (hτ : IsHomeomorph τ) (hcomm : ∀ x, τ (p x) = q (σ x)) :
    IsOpenMap p ↔ IsOpenMap q := by
  have himg : ∀ V : Set A, τ '' (p '' V) = q '' (σ '' V) := by
    intro V
    rw [← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr' hcomm
  constructor
  · intro hp T hT
    rw [← Set.image_preimage_eq T hσ.bijective.surjective, ← himg]
    exact hτ.isOpenMap _ (hp _ (hT.preimage hσ.continuous))
  · intro hq V hV
    rw [← Set.preimage_image_eq (p '' V) hτ.bijective.injective, himg]
    exact (hq _ (hσ.isOpenMap _ hV)).preimage hτ.continuous

/-- **Openness on points of a 1-morphism of represented stacks is openness of the induced
morphism of representing presheaves.** Both ends of the 1-morphism are represented by algebraic
spaces, so the canonical maps on points of the two representing charts are homeomorphisms by
`AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_representing`, and they identify the two maps
by `AlgebraicGeometry.Stack.spacePointMap_representing_naturality`. -/
theorem isOpenMap_pointsMap_iff_isOpenMorphism_representingMap
    (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ 𝒞) :
    @IsOpenMap _ _ (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
        (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property a.hom) ↔
      Space.IsOpenMorphism B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) :=
  (@isOpenMap_iff_of_isHomeomorph
      (Space.points B S hS F) (Space.points B S hS G)
      (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
      (Space.pointTopology B S hS F) (Space.pointTopology B S hS G)
      (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
      (Space.pointsMap B S hS F (representingMap B S hS 𝒜 𝒞 F G eF eG a))
      (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property a.hom)
      (spacePointMap B S hS F 𝒜 (representingEquivalence B S hS F 𝒜 eF).functor)
      (spacePointMap B S hS G 𝒞 (representingEquivalence B S hS G 𝒞 eG).functor)
      (isHomeomorph_spacePointMap_representing B S hS F hF 𝒜 eF)
      (isHomeomorph_spacePointMap_representing B S hS G hG 𝒞 eG)
      (spacePointMap_representing_naturality B S hS F G 𝒜 𝒞 eF eG a)).symm

/-! ### The two implications of Stacks 06U1 -/

/-- Universal openness of a 1-morphism `f`, at a scheme-valued point `y` of its target, makes the
first projection of the canonical 2-fibre product square of `f` and `y` open on points. -/
private theorem isOpenMap_pointsMap_fst_schemeSliceMap_of_universallyOpen
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (H : UniversallyOpen B S hS f) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj) (hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    @IsOpenMap _ _
      (pointTopology B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (schemeSliceMap B S hS U y hy) f).pt)
      (pointTopology B S hS (schemeSlice B S hS U))
      (pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).pt.val
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).pt.property
        (schemeSlice B S hS U).property
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (schemeSliceMap B S hS U y hy) f).fst.hom) := by
  refine (isOpenMap_pointsMap_iff_isOpenMorphism_representingMap B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f).pt
    (schemeSlice B S hS U) ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
    (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
    (isAlgebraicSpace_yoneda B S hS U) (relocalizeFibreEquivalence B S hS U f y T eT)
    (schemeSliceEquivalenceOver B S hS U)
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f).fst).mpr ?_
  rw [representingMap_relocalizeFibre B S hS U f y T eT hy]
  exact MorphismProperty.universally_le (Space.isOpenMorphismProperty B S hS) _
    ((Space.universallyOpen_iff_universally_isOpenMorphism B S hS
      (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS))).mp
      ((universallyOpen_iff_forall_relocalize B S hS f).mp H U y hy T hT ⟨eT⟩))

/-- Openness on points of the first projection of the canonical 2-fibre product square of `G` and
`f` gives it for the first-factor cancellation square of `g`, `f`, `c`, read through the exchange
of the two factors. -/
private theorem isOpenMap_pointsMap_fst_cancelFstSquare_swap
    {𝒵 𝒳 𝒴 𝒰 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒵) (G : 𝒰 ⟶ 𝒴) (θ : c ≫ g ≅ G)
    (h : @IsOpenMap _ _
      (pointTopology B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        G f).pt)
      (pointTopology B S hS 𝒰)
      (pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          G f).pt.val
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} G f).pt.property
        𝒰.property (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          G f).fst.hom)) :
    @IsOpenMap _ _
      (pointTopology B S hS (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
        g f c G θ).swap.pt)
      (pointTopology B S hS 𝒰)
      (pointsMap B S hS (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
          g f c G θ).swap.pt.val
        (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} g f c G θ).swap.pt.property
        𝒰.property (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
          g f c G θ).swap.fst.hom) :=
  isOpenMap_pointsMap_fst_congr B S hS _ _
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} G f)
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1} g f c G θ)) h

/-- **Stacks 06U1, (1) implies (2).** A universally open representable 1-morphism in the sense of
Stacks 04XB has first projection open on points after every base change by an algebraic stack.

Take a chart of `𝒵` by the slice of the site over a scheme `U`, open and surjective on points by
`AlgebraicGeometry.Stack.exists_sliceChart_isOpenMap_surjective`. Universal openness, read on the
lower-shriek extension at the scheme-valued point of `𝒴` the chart names, says the structural
morphism of the presheaf representing the base change is an open morphism of algebraic spaces;
that is openness on points of the first projection of the canonical square over the point, by
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_iff_isOpenMorphism_representingMap` and
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`; the first-factor cancellation of
Stacks 02XD and `AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr` move it to
`U ×_𝒵 (𝒵 ×_𝒴 𝒳)`; and the open surjection descends it, the hypothesis on the canonical map to
the topological fibre product being Stacks 04XH. -/
theorem isOpenMap_pointsMap_fst_of_universallyOpen
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (H : UniversallyOpen B S hS f.hom)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴) :
    @IsOpenMap _ _
      (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
      (pointTopology B S hS 𝒵.val)
      (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
        (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom) := by
  classical
  obtain ⟨U, c, hcsurj, hcopen⟩ := exists_sliceChart_isOpenMap_surjective B S hS 𝒵
  let cMor : schemeSlice B S hS U ⟶ 𝒵.val := Bicategory.InducedBicategory.mkHom c
  let y := CatFiberedInGroupoids.homFunctor (cMor ≫ g.hom)
  have hy : y ⋙ 𝒴.val.val.p = Over.map U.hom :=
    CatFiberedInGroupoids.homFunctor_comp_p (cMor ≫ g.hom)
  let Pb := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom
  let V := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Pb.fst cMor
  obtain ⟨T, hT, ⟨eT⟩⟩ := hf U y hy
  have hRopen := isOpenMap_pointsMap_fst_cancelFstSquare_swap B S hS g.hom f.hom cMor
    (schemeSliceMap B S hS U y hy) (Iso.refl _)
    (isOpenMap_pointsMap_fst_schemeSliceMap_of_universallyOpen B S hS f.hom H U y hy T hT eT)
  refine @isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective
    (points B S hS V.pt.val _)
    (points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property)
    (points B S hS Pb.pt.val _) (points B S hS 𝒵.val.val 𝒵.val.property)
    (pointTopology B S hS V.pt) (pointTopology B S hS (schemeSlice B S hS U))
    (pointTopology B S hS Pb.pt) (pointTopology B S hS 𝒵.val)
    (pointsMap B S hS V.pt.val _ (schemeSlice B S hS U).property V.snd.hom)
    (pointsMap B S hS V.pt.val _ _ V.fst.hom)
    (pointsMap B S hS Pb.pt.val _ 𝒵.val.property Pb.fst.hom)
    (pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
      𝒵.val.property c)
    (fun x => ?_) hcopen hcsurj (continuous_pointsMap B S hS V.pt Pb.pt V.fst.hom)
    (fun v cc h => ?_) hRopen
  · exact ((pointsMap_comp B S hS _ _ (schemeSlice B S hS U).property 𝒵.val.property
        V.snd.hom cMor.hom x).trans
      (congrFun (pointsMap_eq_of_basedNatTrans B S hS _ _ 𝒵.val.property V.iso.inv.hom) x)).trans
      (pointsMap_comp B S hS _ _ _ 𝒵.val.property V.fst.hom Pb.fst.hom x).symm
  · exact (exists_point_of_isTwoFibreProduct B S hS V
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Pb.fst cMor) cc v h.symm).imp fun _ => And.symm

/-- **Stacks 04SD, read on openness.** For represented categories fibred in groupoids, the first
projection of the fibre product of the representing presheaves of `f` and `g` is an open morphism
if and only if the morphism of representing presheaves induced by the first projection of the
canonical 2-fibre product square of `f` and `g` is. -/
private theorem isOpenMorphism_pullback_fst_iff_representingMap_fst
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G H T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H) (hT : IsAlgebraicSpace B S hS T)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒳.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒴.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒵.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) [(twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered]
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g)
      (presheafOfCategories (T ⋙ typeToCat)).p) :
    Space.IsOpenMorphism B S hS (pullback.fst (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g)) ↔
      Space.IsOpenMorphism B S hS (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst) := by
  have hiso : Arrow.mk (ObjectProperty.homMk (pullback.fst
        (representingMap B S hS 𝒳 𝒵 F H eF eH f) (representingMap B S hS 𝒴 𝒵 G H eG eH g)) :
      (⟨pullback (representingMap B S hS 𝒳 𝒵 F H eF eH f)
          (representingMap B S hS 𝒴 𝒵 G H eG eH g),
        isAlgebraicSpace_pullback B S hS _ _ hF hG hH⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨F, hF⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk (representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst) :
        (⟨T, hT⟩ : AlgebraicSpaces B S hS) ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)) := by
    refine Arrow.isoMk (ObjectProperty.isoMk _ ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
      fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT)) (Iso.refl _) ?_
    apply ObjectProperty.hom_ext
    change ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g T eT).hom ≫
        representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt 𝒳 T F eT eF
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).fst =
      pullback.fst (representingMap B S hS 𝒳 𝒵 F H eF eH f)
        (representingMap B S hS 𝒴 𝒵 G H eG eH g) ≫ 𝟙 _
    rw [Category.comp_id, Iso.trans_hom, Category.assoc,
      fibreProductIsoRepresenting_hom_comp_representingMap_fst, Iso.symm_hom]
    exact (Presheaf.isPullback_fibreProduct _ _).isoPullback_inv_fst
  exact (Space.isOpenMorphismProperty B S hS).arrow_mk_iso_iff hiso

/-- **Stacks 06U1, (2) implies (1).** A representable 1-morphism whose first projection is open on
points after every base change by an algebraic stack is universally open in the sense of
Stacks 04XB.

It is enough to see that the structural morphism `Λ_U T ⟶ h_U` of the lower-shriek extension of a
presheaf representing a base change along a scheme-valued point is universally open, that is, that
`|Z ×_{h_U} Λ_U T| → |Z|` is open for every algebraic space `Z` over `h_U`. The morphism
`k : Z ⟶ h_U` comes from a 1-morphism out of the category of elements of `Z` (Stacks 04SW, onto);
the hypothesis at that algebraic stack, moved by two first-factor cancellations of Stacks 02XD and
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_fst_congr`, is openness on points of the first
projection of `Z ×_U (U ×_𝒴 𝒳)`;
`AlgebraicGeometry.Stack.isOpenMap_pointsMap_iff_isOpenMorphism_representingMap` reads that on the
representing presheaves; and Stacks 04SD identifies that representing presheaf with the fibre
product `Z ×_{h_U} Λ_U T`. -/
theorem universallyOpen_of_isOpenMap_pointsMap_fst
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (Hpts : ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
      @IsOpenMap _ _
        (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
        (pointTopology B S hS 𝒵.val)
        (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
          (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom)) :
    UniversallyOpen B S hS f.hom := by
  classical
  rw [universallyOpen_iff_forall_relocalize]
  rintro U y hy T hT ⟨eT⟩ Z hZ k
  -- the two represented algebraic stacks and the 1-morphism inducing `k`
  let Ualg : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeSlice B S hS U, isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS
      (schemeSlice B S hS U) (isRepresentableByAlgebraicSpace_schemeSlice B S hS U)⟩
  let Zalg : AlgebraicStacks.{u, w} B S hS :=
    ⟨fibredCategory B S hS Z, isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ⟩
  obtain ⟨hZU, hk⟩ := exists_oneMorphism_representingMap_eq B S hS (𝒳 := Zalg) (𝒴 := Ualg)
    Z (yoneda.obj U) (spaceEquivalenceOver B S hS Z) (schemeSliceEquivalenceOver B S hS U) k
  let Q := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  let gZ := hZU ≫ Bicategory.InducedBicategory.mkHom (schemeSliceMap B S hS U y hy)
  let R := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} hZU.hom Q.fst
  -- the canonical square over the scheme-valued point, and its representing data
  have hQrep := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒳.val 𝒴.val
    (schemeSlice B S hS U) f.hom (schemeSliceMap B S hS U y hy) Q
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f.hom) hf
  -- the hypothesis at the represented stack `Z`
  -- cancel the middle factor, twice, to read it on `Z ×_U (U ×_𝒴 𝒳)`
  have h1 := isOpenMap_pointsMap_fst_cancelFstSquare_swap B S hS (schemeSliceMap B S hS U y hy)
    f.hom hZU.hom gZ.hom (Iso.refl _) (Hpts Zalg gZ)
  have h2 := isOpenMap_pointsMap_fst_congr B S hS
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.fst hZU.hom).swap R
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Q.fst hZU.hom))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} hZU.hom
      Q.fst) h1
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS
    Q.pt (schemeSlice B S hS U) (fibredCategory B S hS Z) Q.fst hZU.hom R
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      hZU.hom Q.fst) hQrep (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  rw [← hk, ← representingMap_relocalizeFibre B S hS U f.hom y T eT hy]
  let _inst : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS Z) Q.pt
      (schemeSlice B S hS U) hZU.hom Q.fst).IsFibered := R.pt.property.isFibered
  exact (isOpenMorphism_pullback_fst_iff_representingMap_fst B S hS (fibredCategory B S hS Z)
    Q.pt (schemeSlice B S hS U) Z ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
    (yoneda.obj U) W hZ (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
    (isAlgebraicSpace_yoneda B S hS U) hW (spaceEquivalenceOver B S hS Z)
    (relocalizeFibreEquivalence B S hS U f.hom y T eT) (schemeSliceEquivalenceOver B S hS U)
    hZU.hom Q.fst eW).mpr
    ((isOpenMap_pointsMap_iff_isOpenMorphism_representingMap B S hS R.pt
      (fibredCategory B S hS Z) W Z hW hZ eW (spaceEquivalenceOver B S hS Z) R.fst).mp h2)

/-- **Stacks 06U1.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is
representable by algebraic spaces, the two conditions

1. `f` is universally open in the sense of Properties of Stacks, Section 04XB, that is
   `AlgebraicGeometry.Stack.UniversallyOpen`; and
2. for every 1-morphism `g : 𝒵 ⟶ 𝒴` of algebraic stacks over `S` the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` on the
   points of Stacks 04XG for the topology of Stacks 04XL is open, that is
   `AlgebraicGeometry.Stack.AlgebraicStacks.UniversallyOpen`

are equivalent. -/
@[stacks 06U1]
theorem representable_universallyOpen_iff_openMap_baseChange
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    UniversallyOpen B S hS f.hom ↔ AlgebraicStacks.UniversallyOpen B S hS f :=
  ⟨fun H 𝒵 g => isOpenMap_pointsMap_fst_of_universallyOpen B S hS f hf H 𝒵 g,
    universallyOpen_of_isOpenMap_pointsMap_fst B S hS f hf⟩

end AlgebraicGeometry.Stack

end
