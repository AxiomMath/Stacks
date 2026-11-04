module

public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSliceProduct

/-!
# Quasi-compactness of the structure morphism of a represented algebraic stack

Let `S` be a scheme in a big fppf site `B` and let `T` be an object of the big fppf site of `S`.
The structure morphism of the algebraic stack `(Sch/T)_fppf` is a quasi-compact 1-morphism —
that is, every 2-fibre product of that stack with a quasi-compact algebraic stack over the final
stack of `S` is quasi-compact — as soon as the product of `T` with every affine object of the
site has compact underlying space, and in particular whenever the underlying space of `T` is a
subsingleton, which is the case for the base of a field-valued point.

The 2-fibre product of two represented algebraic stacks over the final stack is identified with
the algebraic stack represented by their product in the site.

## Main definitions

* `AlgebraicGeometry.Stack.schemeStackProdFunctor`: the comparison functor from the slice of the
  site over the product `V ⨯ T` to the 2-fibre product of the two represented stacks over the
  final stack.
* `AlgebraicGeometry.Stack.schemeStackProdHom`: that functor as a 1-morphism of algebraic stacks
  over `S`.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_schemeStackProdFunctor`: the comparison functor is an
  equivalence.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_twoFibreProduct_structureMorphism`: the 2-fibre
  product of two represented algebraic stacks over the final stack is quasi-compact as soon as
  the site-level product of the two objects has compact underlying space.
* `AlgebraicGeometry.Stack.isSurjective_id`: the identity 1-morphism of an algebraic stack is
  surjective.
* `AlgebraicGeometry.Stack.isQuasiCompactStack_schemeStack_of_compactSpace`: the algebraic stack
  of an object of the site with compact underlying space is quasi-compact.
* `AlgebraicGeometry.quasiCompact_of_subsingleton`: a morphism of schemes whose source has
  subsingleton underlying space is quasi-compact.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_structureMorphism_schemeStack`: the structure
  morphism of a represented algebraic stack is quasi-compact when the product of its object with
  every affine object of the site has compact underlying space.
* `AlgebraicGeometry.Stack.isQuasiCompactMorphism_structureMorphism_schemeStack_of_subsingleton`
  and `AlgebraicGeometry.Stack.isQuasiCompactMorphism_structureMorphism_fieldValuedPointBase`:
  the cases of an object with subsingleton underlying space and of the base of a field-valued
  point.

## References

* [Stacks Project, Tag 03EH](https://stacks.math.columbia.edu/tag/03EH)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 04SV](https://stacks.math.columbia.edu/tag/04SV)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04YC](https://stacks.math.columbia.edu/tag/04YC)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
* [Stacks Project, Tag 0GW2](https://stacks.math.columbia.edu/tag/0GW2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u w

/-- A morphism of schemes whose source has subsingleton underlying space is quasi-compact. -/
theorem quasiCompact_of_subsingleton {X Y : Scheme.{u}} [Subsingleton X] (f : X ⟶ Y) :
    QuasiCompact f :=
  ⟨fun _ _ _ ↦ Set.Subsingleton.isCompact Set.subsingleton_of_subsingleton⟩

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Two facts about represented algebraic stacks -/

/-- The identity 1-morphism of an algebraic stack over `S` is surjective. -/
theorem isSurjective_id (𝒰 : AlgebraicStacks.{u, w} B S hS) :
    IsSurjective B S hS (𝟙 𝒰) :=
  have : ((𝟙 𝒰 : 𝒰 ⟶ 𝒰)).hom.hom.toFunctor.EssSurj :=
    inferInstanceAs (Functor.EssSurj (𝟭 _))
  pointsMap_surjective_of_essSurj B S hS _ _ ((𝟙 𝒰 : 𝒰 ⟶ 𝒰)).hom.hom

/-- The algebraic stack of an object of the big fppf site of `S` with compact underlying space is
quasi-compact. -/
theorem isQuasiCompactStack_schemeStack_of_compactSpace (P : BigFppfOver B S hS)
    (hP : CompactSpace ((BigFppfOver.toScheme B S hS).obj P)) :
    IsQuasiCompactStack.{u, w} B S hS (schemeStack.{u, w} B S hS P).val
      (schemeStack.{u, w} B S hS P).property :=
  (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS _).2
    ((hasAffineSmoothPresentation_iff_hasQuasiCompactSchemeSmoothPresentation.{u, w}
        B S hS _).2
      ⟨P, hP, 𝟙 _, isSurjective_id.{u, w} B S hS _,
        isRelativelySmooth_id B S hS
          (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS P)⟩)

/-! ### The 2-fibre product of two represented stacks over the final stack -/

variable (V T : BigFppfOver B S hS)

/-- Postcomposing both legs of the product over the site of two slices with the inverse of the
iterated-slice equivalence: the functor from the 2-fibre product taken over the identity functor
of the site to the one taken over the final object of the site. -/
noncomputable def schemeStackProdRetarget :
    TwoFibreProductOver (Over.forget V) (Over.forget T) (𝟭 (BigFppfOver B S hS))
        (Over.forget V) (Over.forget T) ⥤
      TwoFibreProductOver (Over.forget V) (Over.forget T)
        (Over.forget (Over.mk (𝟙 (B.obj hS))))
        (Over.forget V ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))))
        (Over.forget T ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS)))) :=
  TwoFibreProductOver.mapBase (pT := Over.forget V) (p𝒜 := Over.forget T)
    (Over.forget V) (Over.forget T)
    (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))))
    (Over.iteratedSliceBackward_mk_id_comp_forget (B.obj hS))

/-- The comparison functor from the slice of the site over `V ⨯ T` to the 2-fibre product of the
two represented algebraic stacks over the final stack:
`CategoryTheory.TwoFibreProductOver.sliceProd` followed by
`AlgebraicGeometry.Stack.schemeStackProdRetarget`. -/
noncomputable def schemeStackProdFunctor :
    Over (V ⨯ T) ⥤ (twoFibreProductAlgebraicStack.{u, w} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS V))
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T))).val.val.obj :=
  TwoFibreProductOver.sliceProd V T ⋙ schemeStackProdRetarget B S hS V T

/-- The comparison functor `AlgebraicGeometry.Stack.schemeStackProdFunctor` is an equivalence. -/
theorem isEquivalence_schemeStackProdFunctor :
    (schemeStackProdFunctor.{u, w} B S hS V T).IsEquivalence :=
  have _hb : (Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS)))).IsEquivalence :=
    (Over.iteratedSliceEquiv (Over.mk (𝟙 (B.obj hS)))).isEquivalence_inverse
  have _hr : (schemeStackProdRetarget B S hS V T).IsEquivalence :=
    TwoFibreProductOver.isEquivalence_mapBase
      (pT := Over.forget V) (p𝒜 := Over.forget T)
      (G := Over.forget V) (F := Over.forget T)
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 (B.obj hS))))
      (Over.iteratedSliceBackward_mk_id_comp_forget (B.obj hS))
  Functor.isEquivalence_trans (TwoFibreProductOver.sliceProd V T)
    (schemeStackProdRetarget B S hS V T)

/-- The comparison functor `AlgebraicGeometry.Stack.schemeStackProdFunctor` as a 1-morphism of
algebraic stacks over `S`. -/
noncomputable def schemeStackProdHom :
    schemeStack.{u, w} B S hS (V ⨯ T) ⟶ twoFibreProductAlgebraicStack.{u, w} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS V))
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)) :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := schemeStackProdFunctor.{u, w} B S hS V T
      w := rfl })

/-- The 2-fibre product over the final stack of two represented algebraic stacks is quasi-compact
as soon as the product of the two objects in the site has compact underlying space. -/
theorem isQuasiCompactStack_twoFibreProduct_structureMorphism
    (h : CompactSpace ((BigFppfOver.toScheme B S hS).obj (V ⨯ T))) :
    IsQuasiCompactStack.{u, w} B S hS
      (twoFibreProductAlgebraicStack.{u, w} B S hS
        (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS V))
        (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T))).val
      (twoFibreProductAlgebraicStack.{u, w} B S hS
        (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS V))
        (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T))).property :=
  have : (schemeStackProdHom.{u, w} B S hS V T).hom.hom.toFunctor.EssSurj :=
    (isEquivalence_schemeStackProdFunctor.{u, w} B S hS V T).essSurj
  isQuasiCompactStack_of_essSurj B S hS (schemeStackProdHom.{u, w} B S hS V T)
    (isQuasiCompactStack_schemeStack_of_compactSpace.{u, w} B S hS (V ⨯ T) h)

/-! ### Quasi-compactness of the structure morphism -/

/-- The underlying scheme of the product in the site of an object with compact underlying space
and an object with subsingleton underlying space is compact. -/
theorem compactSpace_prod_of_subsingleton
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj V)]
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj T)] :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (V ⨯ T)) := by
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hPB : IsPullback (Limits.prod.fst : V ⨯ T ⟶ V) Limits.prod.snd
      (terminal.from V) (terminal.from T) := IsPullback.of_hasBinaryProduct' V T
  have hqcfst : QuasiCompact ((BigFppfOver.toScheme B S hS).map
      (Limits.prod.fst : V ⨯ T ⟶ V)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (hPB.flip.map (BigFppfOver.toScheme B S hS))
      (quasiCompact_of_subsingleton ((BigFppfOver.toScheme B S hS).map (terminal.from T)))
  exact QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).map (Limits.prod.fst : V ⨯ T ⟶ V))

/-- The structure morphism of a represented algebraic stack over `S` is a quasi-compact
1-morphism as soon as the product of its object with every affine object of the site has compact
underlying space. -/
theorem isQuasiCompactMorphism_structureMorphism_schemeStack
    (hT : ∀ V : BigFppfOver B S hS, IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      CompactSpace ((BigFppfOver.toScheme B S hS).obj (V ⨯ T))) :
    IsQuasiCompactMorphism.{u, w} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)) := by
  intro 𝒵 g h𝒵
  obtain ⟨V, hV, a, hasurj, -⟩ :=
    (isQuasiCompactStack_iff_hasAffineSmoothPresentation.{u, w} B S hS 𝒵).1 h𝒵
  obtain rfl := eq_structureMorphism.{u, w} B S hS 𝒵 g
  refine isQuasiCompactStack_twoFibreProduct_of_isSurjective_of_isSurjective.{u, w} B S hS
    (structureMorphism.{u, w} B S hS 𝒵)
    (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)) a (𝟙 _) hasurj
    (isSurjective_id.{u, w} B S hS _) ?_
  rw [comp_structureMorphism.{u, w} B S hS a]
  exact isQuasiCompactStack_twoFibreProduct_structureMorphism.{u, w} B S hS V T (hT V hV)

/-- The structure morphism of the algebraic stack of an object of the site whose underlying space
is a subsingleton is a quasi-compact 1-morphism. -/
theorem isQuasiCompactMorphism_structureMorphism_schemeStack_of_subsingleton
    (hT : Subsingleton ((BigFppfOver.toScheme B S hS).obj T)) :
    IsQuasiCompactMorphism.{u, w} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS T)) :=
  isQuasiCompactMorphism_structureMorphism_schemeStack.{u, w} B S hS T fun V _ ↦
    compactSpace_prod_of_subsingleton B S hS V T

/-- The structure morphism of the algebraic stack of the base of a field-valued point is a
quasi-compact 1-morphism. -/
theorem isQuasiCompactMorphism_structureMorphism_fieldValuedPointBase
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (p : FieldValuedPoint B S hS 𝒳.val) :
    IsQuasiCompactMorphism.{u, w} B S hS
      (structureMorphism.{u, w} B S hS (schemeStack.{u, w} B S hS p.base)) :=
  isQuasiCompactMorphism_structureMorphism_schemeStack_of_subsingleton.{u, w} B S hS p.base
    (Scheme.homeoOfIso p.isSpec).symm.surjective.subsingleton

end Stack

end AlgebraicGeometry

end
