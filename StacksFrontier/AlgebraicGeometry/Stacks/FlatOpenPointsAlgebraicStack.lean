module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEvery
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse

/-!
# A flat 1-morphism locally of finite presentation is open on points (Stacks 06R7)

A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is flat (**Stacks 06PW**) and
locally of finite presentation (**Stacks 06Q2**, part (1)) induces an open map on the topological
spaces of points of **Stacks 04XG** and **Stacks 04XL**.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenMap_pointsMap`: **Stacks 06R7**.

## Implementation notes

The source chooses a smooth surjective chart `V ⟶ 𝒴` by an algebraic space, then a smooth
surjective chart `U ⟶ V ×_𝒴 𝒳`, observes that `U ⟶ V` is a flat morphism of algebraic spaces
locally of finite presentation, and concludes by elementary topology from openness of `|V| ⟶ |𝒴|`
and surjectivity of `|U| ⟶ |𝒳|`. Each of those steps is a statement of the library.

* `AlgebraicGeometry.Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation` gives
  the chart of the target, and
  `AlgebraicGeometry.Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram` builds the
  rest of the diagram *over that prescribed chart* — its construction is the source's own, with
  `U` presenting `𝒳 ×_𝒴 V`.
* That lemma consumes the **universal** smooth-diagram criterion of **Stacks 06FM**, so the two
  hypotheses have to be read at the same criterion before they can be read on one and the same
  `U ⟶ V`: **Stacks 06Q2** part (1) is already the universal form, while **Stacks 06PW** is the
  existential one, and
  `AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram`
  converts it. The conjunction of two universal criteria is then the pointwise conjunction, since
  the criterion is a universally quantified implication whose conclusion is the property itself.
* `AlgebraicGeometry.Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation` is the
  statement for morphisms of algebraic spaces, that is, the consequence of Morphisms, Lemma 01UA
  which the source cites.
* `AlgebraicGeometry.Stack.isOpenMap_spacePointMap` is the openness half of the characterizing
  property of the topology of **Stacks 04XL**, which is what "by construction of the topology on
  `|𝒴|` the map `|V| ⟶ |𝒴|` is open" means; its hypothesis is discharged from smoothness of the
  chart by `AlgebraicGeometry.Space.isFlat_of_isSmooth` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isSmooth`.
* `AlgebraicGeometry.Stack.pointsMap_surjective_of_isSurjectiveOnObjects` gives surjectivity of
  `|U| ⟶ |𝒳|` from surjectivity on objects of the chart, with no representability hypothesis.

Two bookkeeping steps are local. The canonical map on points out of an algebraic space factors as
the tautological bijection followed by the map on points of the chart
(`AlgebraicGeometry.Stack.spacePointMap_comp` at the identity), which is both how surjectivity is
transported and how invariance under the 2-cell of the diagram is obtained from
`AlgebraicGeometry.Stack.pointsMap_eq_of_basedNatTrans`. And the identification of the canonical
map of the 1-morphism attached to a morphism of algebraic spaces with that morphism's own map on
points exists already as a `private` helper of
`StacksFrontier.AlgebraicGeometry.Stacks.SmoothPresentationQuasiCompact`, and is re-derived here.

Eleven of the thirteen imports are removable *individually* — each is supplied transitively by
the others — but removing all eleven *jointly* fails, so they are load-bearing as a set and are
retained, each because this module names a declaration of it by hand.

The 2-cell is used only through `pointsMap_eq_of_basedNatTrans`, which is applied in term mode
with its type ascribed: a `rw` with it fails against a goal that prints the pattern, because the
composite of two 1-morphisms of the induced bicategory is only *definitionally* the composite of
the underlying based functors.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06PW](https://stacks.math.columbia.edu/tag/06PW)
* [Stacks Project, Tag 06Q2](https://stacks.math.columbia.edu/tag/06Q2)
* [Stacks Project, Tag 06R7](https://stacks.math.columbia.edu/tag/06R7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06R7.** A flat 1-morphism of algebraic stacks over `S` which is locally of finite
presentation induces an open map on the topological spaces of points of Stacks 04XG and
Stacks 04XL. -/
@[stacks 06R7]
theorem isOpenMap_pointsMap {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hflat : IsFlat B S hS f) (hlfp : IsLocallyOfFinitePresentation B S hS f) :
    @IsOpenMap _ _ (Stack.pointTopology B S hS 𝒳.val) (Stack.pointTopology B S hS 𝒴.val)
      (Stack.pointsMap B S hS 𝒳.val.val 𝒳.val.property 𝒴.val.property f.hom.hom) := by
  classical
  let _ := Stack.pointTopology B S hS 𝒳.val
  let _ := Stack.pointTopology B S hS 𝒴.val
  obtain ⟨V, hV, b, hbsm, hbsu⟩ :=
    Stack.exists_isAlgebraicSpace_smooth_surjectiveOnObjects_presentation.{u, w} B S hS 𝒴.property
  have hflatE : Stack.HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ h => Space.IsFlat B S hS h) f.hom :=
    Stack.hasPropertyOnEverySmoothDiagram_of_hasPropertyOnSomeSmoothDiagram B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_flat B S hS) f.hom
      ((Stack.AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS f).1 hflat)
  have hevery : Stack.HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ h => Space.IsFlat B S hS h ∧ Space.IsLocallyOfFinitePresentation B S hS h)
      f.hom := fun U' V' hU' hV' a' b' h' η' ha' hb' hk' =>
    ⟨hflatE U' V' hU' hV' a' b' h' η' ha' hb' hk',
      hlfp U' V' hU' hV' a' b' h' η' ha' hb' hk'⟩
  obtain ⟨U, hU, a, h, ⟨η⟩, hasm, hasu, hflath, hlfph⟩ :=
    Stack.exists_smoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
      𝒳.property 𝒴.property f.hom V hV b hbsm hbsu hevery
  let _ := Space.pointTopology B S hS U
  let _ := Space.pointTopology B S hS V
  -- the private helper of SmoothPresentationQuasiCompact.lean, re-derived here (it is not
  -- exported from that module)
  have hassoc : ∀ (𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (c : (Stack.fibredCategory B S hS V).val ⥤ᵇ 𝒞.val),
      Stack.spacePointMap B S hS U 𝒞 (((Stack.associatedMap B S hS h).1.hom).comp c) =
        Stack.spacePointMap B S hS V 𝒞 c ∘ Space.pointsMap B S hS U h := by
    intro 𝒞 c
    funext x
    induction x using Quot.inductionOn with
    | h p =>
      let assoc := Stack.associatedMap B S hS h
      let src := Stack.spaceFieldValuedPoint B S hS U p
      let mid := Stack.spaceFieldValuedPoint B S hS V (Space.FieldValuedPoint.map B S hS U h p)
      have hbase : ((CatFiberedInGroupoids.homFunctor assoc.1).obj src.obj).base = mid.obj.base :=
        BasedFunctor.w_obj assoc.1.hom src.obj
      have hobj : (CatFiberedInGroupoids.homFunctor assoc.1).obj src.obj = mid.obj :=
        Pseudofunctor.CoGrothendieck.ext hbase (assoc.2 src.obj)
      have hobj' : (Stack.fieldValuedPointMap B S hS (Stack.fibredCategory B S hS U).val
            ((assoc.1.hom).comp c) src).obj =
          (Stack.fieldValuedPointMap B S hS (Stack.fibredCategory B S hS V).val c mid).obj :=
        congrArg c.toFunctor.obj hobj
      calc
        Stack.spacePointMap B S hS U 𝒞 ((assoc.1.hom).comp c) (p.class B S hS U) =
            Stack.pointClass B S hS 𝒞.val 𝒞.property
              (Stack.fieldValuedPointMap B S hS (Stack.fibredCategory B S hS U).val
                ((assoc.1.hom).comp c) src) :=
          Stack.spacePointMap_class B S hS U 𝒞 ((assoc.1.hom).comp c) p
        _ = Stack.pointClass B S hS 𝒞.val 𝒞.property
              (Stack.fieldValuedPointMap B S hS (Stack.fibredCategory B S hS V).val c mid) :=
          (Stack.class_eq_class_iff_hasCommonExtension B S hS 𝒞.val 𝒞.property _ _).2
            ⟨Stack.fieldValuedPointMap B S hS (Stack.fibredCategory B S hS U).val
              ((assoc.1.hom).comp c) src, ⟨𝟙 _⟩, ⟨eqToHom hobj'⟩⟩
        _ = Stack.spacePointMap B S hS V 𝒞 c
              ((Space.FieldValuedPoint.map B S hS U h p).class B S hS V) :=
          (Stack.spacePointMap_class B S hS V 𝒞 c (Space.FieldValuedPoint.map B S hS U h p)).symm
        _ = (Stack.spacePointMap B S hS V 𝒞 c ∘ Space.pointsMap B S hS U h) (p.class B S hS U) :=
          congrArg (Stack.spacePointMap B S hS V 𝒞 c) (Space.pointsMap_class B S hS U h p).symm
  have hsplit : ∀ (𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
      (k : (Stack.fibredCategory B S hS U).val ⥤ᵇ 𝒞.val),
      Stack.spacePointMap B S hS U 𝒞 k =
        Stack.pointsMap B S hS (Stack.fibredCategory B S hS U).val
            (Stack.fibredCategory B S hS U).property 𝒞.property k ∘
          Stack.spacePointMap B S hS U (Stack.fibredCategory B S hS U)
            (BasedFunctor.id (Stack.fibredCategory B S hS U).val) :=
    fun 𝒞 k => Stack.spacePointMap_comp B S hS U (Stack.fibredCategory B S hS U) 𝒞
      (BasedFunctor.id (Stack.fibredCategory B S hS U).val) k
  -- the chart of the source is surjective on points
  have hUalg : Stack.IsAlgebraicStack.{u, w} B S hS (Stack.fibredCategory B S hS U).val :=
    Stack.isAlgebraicStack_fibredCategory B S hS U hU
  have hsurjpt : Function.Surjective
      (Stack.pointsMap B S hS (Stack.fibredCategory B S hS U).val
        (Stack.fibredCategory B S hS U).property 𝒳.val.property a.hom) :=
    Stack.pointsMap_surjective_of_isSurjectiveOnObjects B S hS
      (𝒳 := (⟨Stack.fibredCategory B S hS U, hUalg⟩ : Stack.AlgebraicStacks.{u, w} B S hS)) (𝒴 := 𝒳)
      (Bicategory.InducedBicategory.mkHom a) hasu
  have hsU : Function.Surjective (Stack.spacePointMap B S hS U 𝒳.val a.hom) := by
    rw [hsplit 𝒳.val a.hom]
    exact hsurjpt.comp (Stack.spacePointMap_id_bijective B S hS U).surjective
  -- the chart of the source is continuous
  have hcU : @Continuous _ _ (Space.pointTopology B S hS U) (Stack.pointTopology B S hS 𝒳.val)
      (Stack.spacePointMap B S hS U 𝒳.val a.hom) :=
    Stack.continuous_spacePointMap B S hS U hU 𝒳.val a.hom
  -- the chart of the target is open on points
  obtain ⟨hbrep, hbpr⟩ := hbsm
  have hVYopen : @IsOpenMap _ _ (Space.pointTopology B S hS V) (Stack.pointTopology B S hS 𝒴.val)
      (Stack.spacePointMap B S hS V 𝒴.val b.hom) := by
    refine Stack.isOpenMap_spacePointMap B S hS V hV 𝒴.val 𝒴.property b.hom ?_
    intro W y hy G hG hE
    have hsm := hbpr W y hy G hG hE
    exact ⟨Space.isFlat_of_isSmooth B S hS _ hsm,
      Space.isLocallyOfFinitePresentation_of_isSmooth B S hS hsm⟩
  -- the composite chart of the target is open on points
  have hUYopen : @IsOpenMap _ _ (Space.pointTopology B S hS U) (Stack.pointTopology B S hS 𝒴.val)
      (Stack.spacePointMap B S hS U 𝒴.val (a.hom.comp f.hom.hom)) := by
    have hiso : Stack.spacePointMap B S hS U 𝒴.val (a.hom.comp f.hom.hom) =
        Stack.spacePointMap B S hS U 𝒴.val (((Stack.associatedMap B S hS h).1.hom).comp b.hom) := by
      rw [hsplit 𝒴.val (a.hom.comp f.hom.hom),
        hsplit 𝒴.val (((Stack.associatedMap B S hS h).1.hom).comp b.hom)]
      exact congrArg (· ∘ _)
        (Stack.pointsMap_eq_of_basedNatTrans B S hS (Stack.fibredCategory B S hS U).val
          (Stack.fibredCategory B S hS U).property 𝒴.val.property η.inv.hom)
    rw [hiso, hassoc 𝒴.val b.hom]
    exact hVYopen.comp
      (Space.isOpenMap_pointsMap_of_isFlat_of_isLocallyOfFinitePresentation B S hS hU hV h
        hflath hlfph)
  -- elementary topology
  intro W hW
  have hWpre : @IsOpen _ (Space.pointTopology B S hS U)
      (Stack.spacePointMap B S hS U 𝒳.val a.hom ⁻¹' W) := hcU.isOpen_preimage W hW
  have := hUYopen _ hWpre
  rwa [Stack.spacePointMap_comp B S hS U 𝒳.val 𝒴.val a.hom f.hom.hom, Set.image_comp,
    Set.image_preimage_eq W hsU] at this

end AlgebraicGeometry.Stack.AlgebraicStacks

end
