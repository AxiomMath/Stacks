module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRelocalizeRestrict
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapToRepresentingSpace
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrictYoneda
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageThreeLocallyBijective
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRestrict

/-!
# The relative map of Stacks 06CK under a morphism of the base object

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of categories fibred in groupoids over the big fppf site of a
scheme `S`, let `y` be a scheme-valued point of `𝒴` over an object `U` of the site and let `X_y`
be an algebraic space over `U` representing the 2-fibre product
`(Sch/U)_{fppf} ×_{y, 𝒴, F} 𝒳`. For `ι : U' ⟶ U` a morphism of the site, restriction along
`CategoryTheory.Over.map ι` carries the point to a point `ι^{-1}y = Over.map ι ⋙ y` over `U'` and
the representing presheaf to `ι^{-1}X_y`, and
`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_relocalizeRestrict` says the latter
represents the base change along the former.

This file gives that representing equivalence explicitly, for an arbitrary `ι`: the first
projections of the two 2-fibre products are related by
`CategoryTheory.TwoFibreProductOver.precomposeFst`, and this comparison followed by the given
representing equivalence descends to a 1-morphism into the category of elements of `ι^{-1}X_y`
over the big fppf site of `U'`, which is an equivalence. The section of Stacks 06CK named by an
object of the restricted 2-fibre product is the section named by its image in the original one.

This is the base-change remark preceding the definition of the locus in the section of
Stacks 06CJ — that the relative map attached to a comparison of quintuples over `g : U' ⟶ U` is
read off the original one along `g` — in the form in which it holds for every `g`, not only for
an isomorphism.

## Main definitions

* `AlgebraicGeometry.Stack.relativeFibreProductRestrict`: the comparison of the two 2-fibre
  products, over `CategoryTheory.Over.map ι`.
* `AlgebraicGeometry.Stack.relativeSpaceRestrictFunctor`: its descent into the category of
  elements of `ι^{-1}X_y`.
* `AlgebraicGeometry.Stack.relativeSpaceRestrictEquivalence`: that descent as an equivalence over
  the big fppf site of `U'`, exhibiting `ι^{-1}X_y` as representing the restricted base change.

## Main results

* `AlgebraicGeometry.Stack.faithful_fst_of_representing`: the first projection of a represented
  2-fibre product is faithful.
* `AlgebraicGeometry.Stack.isEquivalence_relativeSpaceRestrictFunctor`: the descent is an
  equivalence of categories.
* `AlgebraicGeometry.Stack.relativeSection_relocalizeRestrict`: **the section of Stacks 06CK
  named by the restricted data is the section named by the original data at the image object.**
* `AlgebraicGeometry.Stack.relativeSection_relocalizeRestrict_map`: the same statement composed
  with the compatibility of the relative map with restriction, which is the form a comparison of
  two quintuples takes.

## Implementation notes

The equivalence `AlgebraicGeometry.Stack.relativeSpaceRestrictEquivalence` is a choice, but its
forward 1-morphism is `AlgebraicGeometry.Stack.relativeSpaceRestrictFunctor`
(`AlgebraicGeometry.Stack.relativeSpaceRestrictEquivalence_hom_functor`); since
`CategoryTheory.PresheafOfCategories.sectionOfObj` depends on an equivalence only through its
forward 1-morphism, the section is computed from it.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.PresheafOfCategories

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : BasedCategory.{v₁, w₁} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, w₂} (BigFppfOver B S hS)}
  (F : 𝒳 ⥤ᵇ 𝒴) {U U' : BigFppfOver B S hS}
  (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.obj)
  {Xy : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u}
  (e : StacksRepresentableCFG.EquivalenceOver
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor)
    (discreteProjection Xy))
  (ι : U'.left ⟶ U.left)

/-- The slice functor of `U'` is the slice functor of `ι` followed by that of `U`, for `ι` a
morphism over `S`. -/
theorem overMap_comp_eq_of_comp_hom (hι : ι ≫ U.hom = U'.hom) :
    Over.map ι ⋙ Over.map U.hom = Over.map U'.hom := by
  rw [← hι, Over.mapComp_eq]

/-- **The comparison of the two 2-fibre products.** The base change of `F` along the restricted
point `ι^{-1}y` maps to the base change along `y`, over `CategoryTheory.Over.map ι`: an object
`(V, x, α)` is sent to `(j V, x, α)`, the comparison isomorphism being unchanged because
`(ι^{-1}y)(V)` is `y(j V)`. -/
noncomputable def relativeFibreProductRestrict (hι : ι ≫ U.hom = U'.hom) :
    TwoFibreProductOver (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor ⥤
      TwoFibreProductOver (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor :=
  TwoFibreProductOver.precomposeFst (Over.map U'.hom) (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor
    (Over.map ι) (overMap_comp_eq_of_comp_hom ι hι)

/-- The comparison commutes with the two first projections through `CategoryTheory.Over.map ι`. -/
theorem relativeFibreProductRestrict_comp_fst (hι : ι ≫ U.hom = U'.hom) :
    relativeFibreProductRestrict F y ι hι ⋙
        TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor =
      TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor ⋙
        Over.map ι := rfl

/-- The comparison followed by the given representing equivalence is a 1-morphism into the
category of elements of `X_y` over `CategoryTheory.Over.map ι` composed with the first projection
of the restricted 2-fibre product. -/
theorem relativeFibreProductRestrict_comp_discreteProjection (hι : ι ≫ U.hom = U'.hom) :
    (relativeFibreProductRestrict F y ι hι ⋙ e.hom.functor) ⋙ discreteProjection Xy =
      TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor ⋙
        Over.map ι := by
  rw [Functor.assoc, e.hom.w]
  rfl

/-- **The descent of the comparison into the category of elements of `ι^{-1}X_y`.** A section of
`X_y` over `j V` *is* a section of `ι^{-1}X_y` over `V`, so the comparison, which lies over
`CategoryTheory.Over.map ι`, descends to a 1-morphism over the big fppf site of `U'`. -/
noncomputable def relativeSpaceRestrictFunctor (hι : ι ≫ U.hom = U'.hom) :
    TwoFibreProductOver (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor ⥤
      (presheafOfCategories
        (((OverShriek.relocalizeRestrict ι).obj Xy) ⋙ typeToCat)).obj :=
  descendRestrictElements ι Xy
    (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor)
    (relativeFibreProductRestrict F y ι hι ⋙ e.hom.functor)
    (relativeFibreProductRestrict_comp_discreteProjection F y e ι hι)

/-- The descent is strictly a 1-morphism over the first projection of the restricted 2-fibre
product. -/
theorem relativeSpaceRestrictFunctor_comp (hι : ι ≫ U.hom = U'.hom) :
    relativeSpaceRestrictFunctor F y e ι hι ⋙
        discreteProjection ((OverShriek.relocalizeRestrict ι).obj Xy) =
      TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor :=
  descendRestrictElements_comp ι Xy _ _
    (relativeFibreProductRestrict_comp_discreteProjection F y e ι hι)

/-! ### The descent is an equivalence -/

include e in
/-- **The first projection of a represented 2-fibre product is faithful.** -/
theorem faithful_fst_of_representing :
    (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor).Faithful := by
  have _ : e.hom.functor.IsEquivalence := Equivalence.isEquivalence_functor e.toEquivalence
  have _ := faithful_discreteProjection (F := Xy)
  have h : (e.hom.functor ⋙ discreteProjection Xy).Faithful := inferInstance
  rwa [e.hom.w] at h

include e in
/-- **The first projection of the restricted 2-fibre product is faithful**, given a representing
equivalence for the original 2-fibre product. -/
theorem faithful_fst_relativeFibreProductRestrict (hι : ι ≫ U.hom = U'.hom) :
    (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y)
      F.toFunctor).Faithful := by
  have _ := faithful_fst_of_representing F y e
  refine ⟨fun {z z'} u v h => ?_⟩
  have ha : u.a = v.a := h
  have himg := (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor).map_injective
    (a₁ := (relativeFibreProductRestrict F y ι hι).map u)
    (a₂ := (relativeFibreProductRestrict F y ι hι).map v) (congrArg (Over.map ι).map ha)
  have hbcomp : ((relativeFibreProductRestrict F y ι hι).map u).b =
    ((relativeFibreProductRestrict F y ι hι).map v).b := congrArg TwoFibreProductOver.Hom.b himg
  exact TwoFibreProductOver.Hom.ext' ha hbcomp

/-- **The descent is faithful.** -/
theorem faithful_relativeSpaceRestrictFunctor (hι : ι ≫ U.hom = U'.hom) :
    (relativeSpaceRestrictFunctor F y e ι hι).Faithful := by
  have : (relativeSpaceRestrictFunctor F y e ι hι ⋙
      discreteProjection ((OverShriek.relocalizeRestrict ι).obj Xy)).Faithful := by
    rw [relativeSpaceRestrictFunctor_comp F y e ι hι]
    exact faithful_fst_relativeFibreProductRestrict F y e ι hι
  exact Functor.Faithful.of_comp _ (discreteProjection ((OverShriek.relocalizeRestrict ι).obj Xy))

/-- **The descent is full.** -/
theorem full_relativeSpaceRestrictFunctor (hι : ι ≫ U.hom = U'.hom) :
    (relativeSpaceRestrictFunctor F y e ι hι).Full := by
  refine ⟨fun {z z'} m => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b : z.x ⟶ z'.x,
      b = (discreteProjection ((OverShriek.relocalizeRestrict ι).obj Xy)).map m := ⟨_, rfl⟩
  have hs : sectionOfObj e ((relativeFibreProductRestrict F y ι hι).obj z) rfl =
      Xy.map ((Over.map ι).map b).op
        (sectionOfObj e ((relativeFibreProductRestrict F y ι hι).obj z') rfl) := by
    rw [hb]
    exact Discrete.eq_of_hom m.fiber
  obtain ⟨φ, hφ⟩ := exists_hom_of_sectionOfObj_map e
    (z := (relativeFibreProductRestrict F y ι hι).obj z')
    (z' := (relativeFibreProductRestrict F y ι hι).obj z) rfl rfl ((Over.map ι).map b) hs
  have hφ' : (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor).IsHomLift
      ((Over.map ι).map b) φ := hφ
  have hφa : φ.a = (Over.map ι).map b := by
    have h : φ.a = 𝟙 ((Over.map ι).obj z.x) ≫ (Over.map ι).map b ≫
        𝟙 ((Over.map ι).obj z'.x) :=
      IsHomLift.fac' (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.p 𝒴.p y F.toFunctor)
        ((Over.map ι).map b) φ
    simpa using h
  have haa : (Over.map U.hom).IsHomLift φ.hbase ((Over.map ι).map b) := by
    rw [← hφa]
    exact φ.ha
  have ha : (Over.map U'.hom).IsHomLift φ.hbase b :=
    Functor.isHomLift_of_isHomLift_map_of_comp_eq (overMap_comp_eq_of_comp_hom ι hι) φ.hbase b haa
  have hw : (Over.map ι ⋙ y).map b ≫ z'.iso.hom = z.iso.hom ≫ F.toFunctor.map φ.b := by
    have h := φ.w
    rwa [hφa] at h
  exact ⟨{ hbase := φ.hbase
           a := b
           b := φ.b
           ha := ha
           hb := φ.hb
           w := hw }, elements_hom_ext' _ _ hb⟩

/-- **The descent is essentially surjective.** -/
theorem essSurj_relativeSpaceRestrictFunctor (hι : ι ≫ U.hom = U'.hom) :
    (relativeSpaceRestrictFunctor F y e ι hι).EssSurj := by
  refine ⟨fun W => ?_⟩
  obtain ⟨w, hw, hws⟩ :=
    exists_sectionOfObj e (W := (Over.map ι).obj W.base) W.fiber.as
  obtain ⟨base, wx, wy, whx, why, wiso, wvert⟩ := w
  change wx = (Over.map ι).obj W.base at hw
  subst hw
  change (Over.map U.hom).obj ((Over.map ι).obj W.base) = base at whx
  subst whx
  refine ⟨{ base := (Over.map U.hom).obj ((Over.map ι).obj W.base)
            x := W.base
            y := wy
            hx := (Functor.congr_obj (overMap_comp_eq_of_comp_hom ι hι) W.base).symm
            hy := why
            iso := wiso
            vertical := wvert }, ⟨?_⟩⟩
  refine elementsIsoOfBaseIso (Iso.refl W.base) ?_
  have hid : ((OverShriek.relocalizeRestrict ι).obj Xy).map (Iso.refl W.base).hom.op
      W.fiber.as = W.fiber.as := by simp
  exact hws.trans hid.symm

/-- **The descent is an equivalence of categories.** -/
theorem isEquivalence_relativeSpaceRestrictFunctor (hι : ι ≫ U.hom = U'.hom) :
    (relativeSpaceRestrictFunctor F y e ι hι).IsEquivalence := by
  have _ := faithful_relativeSpaceRestrictFunctor F y e ι hι
  have _ := full_relativeSpaceRestrictFunctor F y e ι hι
  have _ := essSurj_relativeSpaceRestrictFunctor F y e ι hι
  exact Functor.IsEquivalence.mk

/-- **The restriction of a representing presheaf represents the restricted base change**, by an
equivalence whose forward 1-morphism is `AlgebraicGeometry.Stack.relativeSpaceRestrictFunctor`. -/
theorem exists_equivalenceOver_relativeSpaceRestrict (hι : ι ≫ U.hom = U'.hom)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) :
    ∃ E : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor)
      (discreteProjection ((OverShriek.relocalizeRestrict ι).obj Xy)),
      E.hom.functor = relativeSpaceRestrictFunctor F y e ι hι := by
  have h₁ : (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y)
      F.toFunctor).IsFiberedInGroupoids := by
    refine isFiberedInGroupoids_fst_overMap_of U'.hom h𝒳 h𝒴 ?_ F.w
    rw [Functor.assoc, hy]
    exact overMap_comp_eq_of_comp_hom ι hι
  exact ⟨StacksRepresentableCFG.equivalenceOverOfIsEquivalence h₁
      (isFiberedInSetoids_discreteProjection _).isFiberedInGroupoids _
      (relativeSpaceRestrictFunctor_comp F y e ι hι)
      (isEquivalence_relativeSpaceRestrictFunctor F y e ι hι),
    StacksRepresentableCFG.equivalenceOverOfIsEquivalence_hom _ _ _ _ _⟩

/-- **The restricted representing presheaf, as an equivalence over the big fppf site of `U'`**,
with forward 1-morphism `AlgebraicGeometry.Stack.relativeSpaceRestrictFunctor`. -/
noncomputable def relativeSpaceRestrictEquivalence (hι : ι ≫ U.hom = U'.hom)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U'.hom) 𝒳.p 𝒴.p (Over.map ι ⋙ y) F.toFunctor)
      (discreteProjection ((OverShriek.relocalizeRestrict ι).obj Xy)) :=
  (exists_equivalenceOver_relativeSpaceRestrict F y e ι hι h𝒳 h𝒴 hy).choose

/-- The forward 1-morphism of `AlgebraicGeometry.Stack.relativeSpaceRestrictEquivalence` is the
descent of the comparison. -/
theorem relativeSpaceRestrictEquivalence_hom_functor (hι : ι ≫ U.hom = U'.hom)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (hy : y ⋙ 𝒴.p = Over.map U.hom) :
    (relativeSpaceRestrictEquivalence F y e ι hι h𝒳 h𝒴 hy).hom.functor =
      relativeSpaceRestrictFunctor F y e ι hι :=
  (exists_equivalenceOver_relativeSpaceRestrict F y e ι hι h𝒳 h𝒴 hy).choose_spec

/-- **The section of Stacks 06CK named by the restricted data is the section named by the original
data at the image object.** Both sides are sections of `X_y` over `j Z`, since a section of
`ι^{-1}X_y` over `Z` *is* one of `X_y` over `j Z`. -/
theorem relativeSection_relocalizeRestrict (hι : ι ≫ U.hom = U'.hom)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (hy : y ⋙ 𝒴.p = Over.map U.hom)
    (Z : BigFppfOver B U'.left.1 U'.left.2) (x : 𝒳.obj)
    (hx : 𝒳.p.obj x = (Over.map U'.hom).obj Z)
    (hx' : 𝒳.p.obj x = (Over.map U.hom).obj ((Over.map ι).obj Z))
    (α : y.obj ((Over.map ι).obj Z) ≅ F.toFunctor.obj x)
    (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U'.hom).obj Z)) α.hom)
    (hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj ((Over.map ι).obj Z))) α.hom) :
    relativeSection F (Over.map ι ⋙ y)
        (relativeSpaceRestrictEquivalence F y e ι hι h𝒳 h𝒴 hy) Z x hx α hα =
      relativeSection F y e ((Over.map ι).obj Z) x hx' α hα' := by
  have hstep : relativeSection F (Over.map ι ⋙ y)
        (relativeSpaceRestrictEquivalence F y e ι hι h𝒳 h𝒴 hy) Z x hx α hα =
      elementsFiberEquiv ((OverShriek.relocalizeRestrict ι).obj Xy) Z
        ⟨(relativeSpaceRestrictFunctor F y e ι hι).obj
          (relativeObj F (Over.map ι ⋙ y) Z x hx α hα), rfl⟩ :=
    sectionOfObj_of_hom_functor_eq _ _
      (relativeSpaceRestrictEquivalence_hom_functor F y e ι hι h𝒳 h𝒴 hy) _ rfl rfl
  refine hstep.trans ?_
  change sectionOfObj e ((relativeFibreProductRestrict F y ι hι).obj
      (relativeObj F (Over.map ι ⋙ y) Z x hx α hα)) rfl =
    sectionOfObj e (relativeObj F y ((Over.map ι).obj Z) x hx' α hα') rfl
  refine sectionOfObj_eq_of_hom e
    (z := (relativeFibreProductRestrict F y ι hι).obj
      (relativeObj F (Over.map ι ⋙ y) Z x hx α hα))
    (z' := relativeObj F y ((Over.map ι).obj Z) x hx' α hα') rfl rfl
    (TwoFibreProductOver.isoMkVertical
      (U := (Over.map U.hom).obj ((Over.map ι).obj Z))
      (Iso.refl ((Over.map ι).obj Z)) (Iso.refl x) (IsHomLift.id rfl) (IsHomLift.id hx') ?_).hom ?_
  · change y.map (𝟙 ((Over.map ι).obj Z)) ≫ α.hom = α.hom ≫ F.toFunctor.map (𝟙 x)
    simp
  · refine CategoryTheory.IsHomLift.of_fac' _ (𝟙 ((Over.map ι).obj Z)) _ rfl rfl ?_
    change 𝟙 ((Over.map ι).obj Z) =
      eqToHom rfl ≫ 𝟙 ((Over.map ι).obj Z) ≫ eqToHom rfl
    simp

/-- **The section of Stacks 06CK named by the restricted data is a restriction of the section
named by the original data**, along a morphism `κ : j Z ⟶ W` of the big fppf site of `U` and a
morphism `a` of `𝒳` over it compatible with the two comparison isomorphisms. -/
theorem relativeSection_relocalizeRestrict_map (hι : ι ≫ U.hom = U'.hom)
    (h𝒳 : 𝒳.p.IsFiberedInGroupoids) (h𝒴 : 𝒴.p.IsFiberedInGroupoids)
    (hy : y ⋙ 𝒴.p = Over.map U.hom)
    (Z : BigFppfOver B U'.left.1 U'.left.2) (W : BigFppfOver B U.left.1 U.left.2)
    (κ : (Over.map ι).obj Z ⟶ W) {x x' : 𝒳.obj} (a : x ⟶ x')
    (hx : 𝒳.p.obj x = (Over.map U'.hom).obj Z)
    (hxi : 𝒳.p.obj x = (Over.map U.hom).obj ((Over.map ι).obj Z))
    (hx' : 𝒳.p.obj x' = (Over.map U.hom).obj W)
    (α : y.obj ((Over.map ι).obj Z) ≅ F.toFunctor.obj x)
    (hα : 𝒴.p.IsHomLift (𝟙 ((Over.map U'.hom).obj Z)) α.hom)
    (hαi : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj ((Over.map ι).obj Z))) α.hom)
    (α' : y.obj W ≅ F.toFunctor.obj x')
    (hα' : 𝒴.p.IsHomLift (𝟙 ((Over.map U.hom).obj W)) α'.hom)
    (ha : 𝒳.p.IsHomLift ((Over.map U.hom).map κ) a)
    (w : y.map κ ≫ α'.hom = α.hom ≫ F.toFunctor.map a) :
    relativeSection F (Over.map ι ⋙ y)
        (relativeSpaceRestrictEquivalence F y e ι hι h𝒳 h𝒴 hy) Z x hx α hα =
      Xy.map κ.op (relativeSection F y e W x' hx' α' hα') :=
  (relativeSection_relocalizeRestrict F y e ι hι h𝒳 h𝒴 hy Z x hx hxi α hα hαi).trans
    (relativeSection_map (e := e) (Z := W) (Z' := (Over.map ι).obj Z) (x := x') (x' := x)
      (hx := hx') (hx' := hxi) (α := α') (α' := α) (hα := hα') (hα' := hαi) κ a ha w)

end AlgebraicGeometry.Stack

end
