module

public import StacksFrontier.AlgebraicGeometry.Stacks.FirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCategory
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSchemeStack
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalenceClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback

/-!
# Thickenings of algebraic spaces read as algebraic stacks

Let `i : X ⟶ Y` be a morphism of algebraic spaces over `S`. The stack of `i`
(`AlgebraicGeometry.Stack.algebraicSpaceStackFunctor`) may be a thickening, or a first-order
thickening, of algebraic stacks in the sense of Stacks 0BPP and Stacks 0BPQ, which are tested on
scheme-valued points of the target. This file reads those conditions back on `i` itself: `i` is
then a thickening of algebraic spaces (`AlgebraicGeometry.Space.IsThickeningHom`), and its image
is a first-order thickening of `Y` in the sense of Stacks 05ZK, part (2) — its defining ideal has
square zero on every object of the small étale site of `Y`.

This is the bridge that turns the hypothesis "`𝒳 ⊂ 𝒳'` is a first-order thickening of algebraic
stacks" of Stacks 0CKG into the first-order thickening `U ⊂ U'` of algebraic spaces that the
deformation theory of algebraic spaces (Stacks 061C, 0CK6, 0CK7) consumes.

## Main results

* `AlgebraicGeometry.Stack.isThickeningHom_of_isThickening_algebraicSpaceStackFunctor_map`: a
  morphism of algebraic spaces whose stack is a thickening is a thickening of algebraic spaces.
* `isFirstOrderThickening_range_of_isFirstOrderThickening_algebraicSpaceStackFunctor_map`
  (in `AlgebraicGeometry.Stack`): a morphism of algebraic spaces whose stack is a first-order
  thickening has image a first-order thickening of algebraic spaces.
* `CategoryTheory.Subfunctor.range_pullback_fst`: the range of the first projection of a pullback
  of presheaves of sets is the inverse image of the range of the second morphism.

## Implementation notes

The square-zero clause is checked one étale chart `V ⟶ Y` at a time. The condition of Stacks 0BPQ
at the scheme-valued point `V` is about the image of the representing space of `V ×_Y X` in `V`;
`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback` identifies that representing space with
the fibre product of presheaves over the identity of `V`, so the two images agree, and the image of
the first projection of a fibre product is an inverse image. The defining ideal of the inverse
image at the identity chart of `V` is the defining ideal of the image of `i` at `V`
(`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`). The scheme-valued
point is introduced through an existential so that it is never unfolded: its definition goes
through a quotient representative, and `whnf` on it does not terminate in reasonable time.

## References

* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
* [Stacks Project, Tag 0BPQ](https://stacks.math.columbia.edu/tag/0BPQ)
* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Subfunctor

universe v₀ u₀

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞]

/-- The range of a morphism of presheaves of sets precomposed with an isomorphism is its
range. -/
theorem range_isoHom_comp {F F' G : 𝒞ᵒᵖ ⥤ Type v₀} (e : F' ≅ F) (g : F ⟶ G) :
    range (e.hom ≫ g) = range g := by
  ext V x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e.hom.app V y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨e.inv.app V y, ?_⟩
    change (e.inv ≫ e.hom ≫ g).app V y = g.app V y
    rw [Iso.inv_hom_id_assoc]

/-- **The range of the first projection of a pullback of presheaves of sets** is the inverse
image, along the other leg of the cospan, of the range of the second morphism. -/
theorem range_pullback_fst {F G H : 𝒞ᵒᵖ ⥤ Type v₀} (b : F ⟶ H) (m : G ⟶ H) :
    range (pullback.fst b m) = (range m).preimage b := by
  ext V x
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨(pullback.snd b m).app V z, ?_⟩
    change ((pullback.snd b m) ≫ m).app V z = ((pullback.fst b m) ≫ b).app V z
    rw [pullback.condition]
  · rintro ⟨w, hw⟩
    let z₀ : pullback (b.app V) (m.app V) :=
      (Types.pullbackIsoPullback (b.app V) (m.app V)).inv ⟨(x, w), hw.symm⟩
    refine ⟨(pullbackObjIso b m V).inv z₀, ?_⟩
    exact (congrArg (fun φ => φ z₀) (pullbackObjIso_inv_comp_fst b m V)).trans
      (Types.pullbackIsoPullback_inv_fst_apply (b.app V) (m.app V) ⟨(x, w), hw.symm⟩)

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Postcomposing the identity chart of an étale chart `V ⟶ Y` with `V ⟶ Y` gives back `V`. -/
theorem smallEtalePostcomp_obj_idChart {Y : AlgebraicSpaces B S hS} (V : SmallEtale B S hS Y.obj) :
    (smallEtalePostcomp B S hS (chartToSpace B S hS Y V) (isEtale_chartToSpace B S hS Y V)).obj
      (idChart B S hS V.obj.left) = V := by
  apply ObjectProperty.FullSubcategory.ext
  refine Eq.trans ?_ (CostructuredArrow.eq_mk V.obj).symm
  change CostructuredArrow.mk (𝟙 (yoneda.obj V.obj.left) ≫ V.obj.hom) =
    CostructuredArrow.mk V.obj.hom
  rw [Category.id_comp]

/-- If the inverse image of a closed subspace `Z ⊆ Y` along an étale chart `V ⟶ Y` is a
first-order thickening of `V`, then the defining ideal of `Z` at `V` has square zero. -/
theorem definingIdealAt_sq_eq_bot_of_isFirstOrderThickening_preimage
    {Y : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS Y.1) (V : SmallEtale B S hS Y.obj)
    (h : IsFirstOrderThickening B S hS
      ⟨yoneda.obj V.obj.left, isAlgebraicSpace_yoneda B S hS V.obj.left⟩
      (Z.1.preimage V.obj.hom)) :
    definingIdealAt B S hS Y Z (op V) ^ (1 + 1) = ⊥ := by
  obtain ⟨_, hsq⟩ := h
  have key := definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS
    (chartToSpace B S hS Y V) (isEtale_chartToSpace B S hS Y V) Z (idChart B S hS V.obj.left)
  have h₄ : definingIdealAt B S hS Y Z
      (op ((smallEtalePostcomp B S hS (chartToSpace B S hS Y V)
        (isEtale_chartToSpace B S hS Y V)).obj (idChart B S hS V.obj.left))) ^ (1 + 1) = ⊥ := by
    rw [← key]
    exact hsq (idChart B S hS V.obj.left)
  rwa [smallEtalePostcomp_obj_idChart V] at h₄

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structural morphism of the lower-shriek extension of an algebraic space `T` over `U` and
the structural morphism of Stacks 04SG have the same image. -/
theorem range_relocalizeToYoneda_eq_range_algebraicSpaceMap (U : BigFppfOver B S hS)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T) :
    Subfunctor.range (OverShriek.relocalizeToYoneda U.hom T) =
      Subfunctor.range (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩)).hom := by
  let ι := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app ⟨T, hT⟩
  have h : OverShriek.relocalizeToYoneda U.hom T =
      ι.inv ≫ (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩)).hom := by
    ext W s
    exact (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS
      U.hom ⟨T, hT⟩ W s).symm
  rw [h]
  exact Subfunctor.range_isoHom_comp ι.symm _

/-- **A morphism of algebraic spaces whose stack is a thickening of algebraic stacks is a
thickening of algebraic spaces.** -/
theorem isThickeningHom_of_isThickening_algebraicSpaceStackFunctor_map
    {X Y : AlgebraicSpaces B S hS} (i : X ⟶ Y)
    (hi : IsThickening ((algebraicSpaceStackFunctor.{u, w} B S hS).map i)) :
    Space.IsThickeningHom B S hS i := by
  obtain ⟨X, hX⟩ := X
  obtain ⟨Y, hY⟩ := Y
  have h := isThickeningHom_representingMap_of_isThickening B S hS
    ((algebraicSpaceStackFunctor.{u, w} B S hS).map i) hi hX hY
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
  have e : (ObjectProperty.homMk (representingMap B S hS _ _ X Y
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map i).hom) :
        (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) = i :=
    ObjectProperty.hom_ext _ (representingMap_associatedMap B S hS X Y i.hom)
  exact e ▸ h

/-- **The inverse image of the image of a morphism of algebraic spaces whose stack is a
first-order thickening, along a scheme-valued point `b : U ⟶ Y`, is a first-order thickening of
`U`.** The point `b` is given through a morphism `pt` of stacks representing it. -/
theorem isFirstOrderThickening_preimage_range_of_representingMap_eq
    {X Y : AlgebraicSpaces B S hS} (i : X ⟶ Y)
    (hi₁ : AlgebraicStacks.IsFirstOrderThickening B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map i))
    {U : BigFppfOver B S hS} (b : yoneda.obj U ⟶ Y.obj)
    (pt : schemeSlice B S hS U ⟶ ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val)
    (hpt : representingMap B S hS (schemeSlice B S hS U)
        ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val (yoneda.obj U) Y.obj
        (schemeSliceEquivalenceOver B S hS U) (StacksRepresentableCFG.EquivalenceOver.refl _) pt =
      b) :
    Space.IsFirstOrderThickening B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
      ((Subfunctor.range i.hom).preimage b) := by
  have hrep : IsRepresentableByAlgebraicSpaces B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map i).hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isRepresentableByAlgebraicSpace B S hS _
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS X.obj X.property)
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS Y.obj Y.property)
  obtain ⟨T, hT, ⟨eT⟩⟩ := hrep U (CatFiberedInGroupoids.homFunctor pt)
    (CatFiberedInGroupoids.homFunctor_comp_p pt)
  -- the representing space of the base change is the fibre product
  let a := arrowIsoRelocalizeFibrePullback B S hS U
    ((algebraicSpaceStackFunctor.{u, w} B S hS).map i).hom (CatFiberedInGroupoids.homFunctor pt)
    (CatFiberedInGroupoids.homFunctor_comp_p pt) X.obj Y.obj
    (StacksRepresentableCFG.EquivalenceOver.refl _) (StacksRepresentableCFG.EquivalenceOver.refl _)
    X.property Y.property T eT hT
  have e₂ : Subfunctor.range (pullback.fst
        (representingMap B S hS (schemeSlice B S hS U)
          ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val (yoneda.obj U) Y.obj
          (schemeSliceEquivalenceOver B S hS U) (StacksRepresentableCFG.EquivalenceOver.refl _)
          (schemeSliceMap B S hS U (CatFiberedInGroupoids.homFunctor pt)
            (CatFiberedInGroupoids.homFunctor_comp_p pt)))
        (representingMap B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).obj X).val
          ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val X.obj Y.obj
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          ((algebraicSpaceStackFunctor.{u, w} B S hS).map i).hom)) =
      Subfunctor.range (OverShriek.relocalizeToYoneda U.hom T) := by
    have hw : a.hom.left ≫ (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
        (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
            isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
          AlgebraicSpaces B S hS) ⟶
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS)) =
        ObjectProperty.homMk _ := (Arrow.w a.hom).trans (Category.comp_id _)
    exact (congrArg (fun φ => Subfunctor.range φ.hom) hw).symm.trans
      (Subfunctor.range_isoHom_comp ((ObjectProperty.ι _).mapIso (Arrow.leftFunc.mapIso a)) _)
  have hb : representingMap B S hS (schemeSlice B S hS U)
          ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val (yoneda.obj U) Y.obj
      (schemeSliceEquivalenceOver B S hS U) (StacksRepresentableCFG.EquivalenceOver.refl _)
      (schemeSliceMap B S hS U (CatFiberedInGroupoids.homFunctor pt)
        (CatFiberedInGroupoids.homFunctor_comp_p pt)) = b :=
    hpt
  have hm : representingMap B S hS ((algebraicSpaceStackFunctor.{u, w} B S hS).obj X).val
      ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val X.obj Y.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map i).hom = i.hom :=
    representingMap_associatedMap B S hS X.obj Y.obj i.hom
  rw [hb, hm, Subfunctor.range_pullback_fst] at e₂
  rw [e₂, range_relocalizeToYoneda_eq_range_algebraicSpaceMap U T hT]
  exact hi₁.2 U (CatFiberedInGroupoids.homFunctor pt) (CatFiberedInGroupoids.homFunctor_comp_p pt)
    T hT ⟨eT⟩

/-- **A morphism of algebraic spaces whose stack is a first-order thickening of algebraic stacks
has image a first-order thickening of algebraic spaces.** The thickening clause is
`AlgebraicGeometry.Stack.isThickeningHom_of_isThickening_algebraicSpaceStackFunctor_map`. For the
square-zero clause at an étale chart `V ⟶ Y`, the condition of Stacks 0BPQ at the scheme-valued
point `V` says that the representing space of `V ×_Y X` has image a first-order thickening of `V`;
that image is the inverse image of the image of `i`
(`AlgebraicGeometry.Stack.arrowIsoRelocalizeFibrePullback`,
`CategoryTheory.Subfunctor.range_pullback_fst`), and the defining ideal of an inverse image along
an étale morphism is the defining ideal at the composite chart
(`AlgebraicGeometry.Space.definingIdealAt_preimage_eq_definingIdealAt_postcomp`). -/
theorem isFirstOrderThickening_range_of_isFirstOrderThickening_algebraicSpaceStackFunctor_map
    {X Y : AlgebraicSpaces B S hS} (i : X ⟶ Y)
    (hi : IsThickening ((algebraicSpaceStackFunctor.{u, w} B S hS).map i))
    (hi₁ : AlgebraicStacks.IsFirstOrderThickening B S hS
      ((algebraicSpaceStackFunctor.{u, w} B S hS).map i)) :
    Space.IsFirstOrderThickening B S hS Y (Subfunctor.range i.hom) := by
  have hth := isThickeningHom_of_isThickening_algebraicSpaceStackFunctor_map.{u, w} i hi
  refine ⟨hth.2, fun V =>
    Space.definingIdealAt_sq_eq_bot_of_isFirstOrderThickening_preimage ⟨_, hth.2.1⟩ V ?_⟩
  let U : BigFppfOver B S hS := V.obj.left
  let b : yoneda.obj U ⟶ Y.obj := V.obj.hom
  obtain ⟨pt, hpt⟩ : ∃ pt : schemeSlice B S hS U ⟶
        ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val,
      representingMap B S hS (schemeSlice B S hS U)
        ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val (yoneda.obj U) Y.obj
        (schemeSliceEquivalenceOver B S hS U) (StacksRepresentableCFG.EquivalenceOver.refl _)
        pt = b :=
    ⟨_, representingMap_schemePointMap B S hS U
      (𝒵 := ((algebraicSpaceStackFunctor.{u, w} B S hS).obj Y).val) Y.obj
      (StacksRepresentableCFG.EquivalenceOver.refl _) b⟩
  exact isFirstOrderThickening_preimage_range_of_representingMap_eq.{u, w} i hi₁ b pt hpt

end AlgebraicGeometry.Stack

end
