module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubstackOfFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoidsSupplement
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize
import all StacksFrontier.AlgebraicGeometry.Quot.CurvesNodal

/-!
# Open substacks of the stack of curves from an open locus in the base (Stacks 0E0E)

Section 109.6 of the source describes a general method for cutting an open substack out of the
stack of curves: for a property `P` of families of curves one has only to check that for every
family of curves `X → S` there is a largest open `S' ⊆ S` over which the restricted family has
`P`, and that forming `S'` commutes with arbitrary base change. The proofs of Stacks 0DSY,
0DZZ, 0E0I, 0E1F and their companions all end by invoking that method.

This module carries out the method once and for all. The input is packaged as `hlocus` below:
for every family of curves `G` an open subspace `W` of its base through which the morphism of
base schemes of a family `F ⟶ G` factors exactly when `F` has `P`. That single condition is
equivalent to the source's pair "largest open subscheme, formation commuting with base change",
because a family mapping to `G` is a base change of `G`.

## Main definitions

* `AlgebraicGeometry.curvesOpenSubstackOfBaseLocus`: **Stacks 0E0E** — the open substack cut
  out by a property of families of curves which has such a locus, together with the
  characterisation of its objects.
* `AlgebraicGeometry.curvesFullSubcategoryFibered` and
  `AlgebraicGeometry.curvesFullSubcategoryInclusion`: the same subcategory and its inclusion
  over the genuine category of families of curves, formed with no hypothesis at all.

## Main results

* `AlgebraicGeometry.classifying_factors_curvesOpenSubstackOfBaseLocus_iff`: the classifying
  object of a family of curves lifts through the inclusion of that open substack exactly when
  the family has the property.
* `AlgebraicGeometry.isClosedUnderIsomorphisms_of_curveFamily_hom`,
  `AlgebraicGeometry.isRepresentableByAlgebraicSpaces_curvesFullSubcategoryInclusion`,
  `AlgebraicGeometry.isOpenImmersion_curvesFullSubcategoryInclusion` and
  `AlgebraicGeometry.lifts_curvesFullSubcategory_iff`: the method of Section 109.6 over the
  genuine category of families of curves, with no hypothesis — the subcategory is strictly
  full, its inclusion is representable by algebraic spaces and is an open immersion in the
  sense of **Stacks 04XB**, and a family lifts through it exactly when it has the property.
* `AlgebraicGeometry.lifts_curvesFullSubcategoryInclusion_iff`: the same factorization
  criterion read through the inclusion 1-morphism
  `AlgebraicGeometry.curvesFullSubcategoryInclusion` itself.

## Implementation notes

The algebraic stack of curves is not constructed in this library (Stacks 0D5A is not proved
here), so the substack is formed inside an arbitrary algebraic stack `𝒳` presented as being
equivalent, over the big fppf site of the integers, to the category of families of curves; the
equivalence `E` and the compatibility `hE` of `E` with the two projections to the site are
hypotheses. Membership of the substack is the condition on the family which the inverse
equivalence attaches to an object, which is invariant under isomorphism because it is inherited
along morphisms of families, so the subcategory is strictly full.

The locus construction, the representability of the inclusion by algebraic spaces and its being
an open immersion do not use `𝒳`, `E` or `hE`, so those three are also stated over the genuine
category of families of curves, in the shape of **Stacks 0D5B**: they are the first and third
clauses of the definition of an open substack (**Stacks 04YM**, part (1)).

## References

* [Stacks Project, Tag 0E0E](https://stacks.math.columbia.edu/tag/0E0E)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0D5B](https://stacks.math.columbia.edu/tag/0D5B)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0D5A](https://stacks.math.columbia.edu/tag/0D5A)
-/

@[expose] public noncomputable section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### Strictly full subcategories of a fibred category -/

/-- Two presentations of a fibred category in groupoids as the category of elements of a presheaf
of sets identify the two presheaves: both are the presheaf of isomorphism classes of objects of
the fibres. -/
private def presheafIsoOfEquivalenceOver_ofBaseLocus
    {C : Type (u + 1)} [Category.{u} C] {D : Type t} [Category.{v} D] {p : D ⥤ C}
    (hp : p.IsFiberedInGroupoids) (F G : Cᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (G ⋙ typeToCat)).p) : F ≅ G := by
  letI : p.IsFibered := hp.isFibered
  refine NatIso.ofComponents (fun T =>
    ((PresheafOfCategories.elementsIsoClassEquiv F eF T.unop).symm.trans
      (PresheafOfCategories.elementsIsoClassEquiv G eG T.unop)).toIso) ?_
  intro T T' f
  ext a
  let qF := PresheafOfCategories.elementsIsoClassEquiv F eF T.unop
  let qF' := PresheafOfCategories.elementsIsoClassEquiv F eF T'.unop
  let qG := PresheafOfCategories.elementsIsoClassEquiv G eG T.unop
  let qG' := PresheafOfCategories.elementsIsoClassEquiv G eG T'.unop
  let c := qF.symm a
  have hc : qF'.symm (F.map f a) = p.isoClassPresheaf.map f c := by
    apply qF'.injective
    rw [qF'.apply_symm_apply]
    simpa only [c, qF, qF', Quiver.Hom.op_unop, Equiv.apply_symm_apply] using
      (PresheafOfCategories.elementsIsoClassEquiv_naturality hp F eF f.unop c).symm
  change qG' (qF'.symm (F.map f a)) = G.map f (qG (qF.symm a))
  rw [hc]
  exact PresheafOfCategories.elementsIsoClassEquiv_naturality hp G eG f.unop c

/-! ### The locus over a scheme-valued point of the stack -/

/-- The base scheme of the family of curves attached to an object of the stack, identified with
the object of the site the structure functor sends it to. -/
private def curveFamilyBaseIso_ofBaseLocus
    (𝒟 : BasedCategory.{v, t} (BigFppfOver B integerBase hZ))
    (E : CurveFamily B hZ ≌ 𝒟.obj)
    (hE : E.functor ⋙ 𝒟.p = curvesProjectionOver B hZ)
    (x : 𝒟.obj) :
    (E.inverse.obj x).base ≅ 𝒟.p.obj x :=
  have h : 𝒟.p.obj (E.functor.obj (E.inverse.obj x)) = (E.inverse.obj x).base :=
    congrArg (fun F => F.obj (E.inverse.obj x)) hE
  eqToIso h.symm ≪≫ 𝒟.p.mapIso (E.counitIso.app x)

/-- Pushing the identity object of the over category of `U.left` forward along `U.hom` gives `U`. -/
private theorem over_map_obj_mk_id_ofBaseLocus (U : BigFppfOver B integerBase hZ) :
    (Over.map U.hom).obj (Over.mk (𝟙 U.left)) = U := by
  cases U
  congr 1

/-- The identification of `AlgebraicGeometry.curveFamilyBaseIso_ofBaseLocus` at the identity
point of a scheme-valued point of the stack. -/
private def curveFamilyBaseIsoAt_ofBaseLocus
    (𝒟 : BasedCategory.{v, t} (BigFppfOver B integerBase hZ))
    (E : CurveFamily B hZ ≌ 𝒟.obj)
    (hE : E.functor ⋙ 𝒟.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj)
    (hy : y ⋙ 𝒟.p = Over.map U.hom) :
    (E.inverse.obj (y.obj (Over.mk (𝟙 U.left)))).base ≅ U :=
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  have h₁ : 𝒟.p.obj (y.obj T₀) = (Over.map U.hom).obj T₀ :=
    congrArg (fun F => F.obj T₀) hy
  curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE (y.obj T₀) ≪≫ eqToIso h₁ ≪≫
    eqToIso (over_map_obj_mk_id_ofBaseLocus B hZ U)

/-- `AlgebraicGeometry.curveFamilyBaseIso_ofBaseLocus` is natural. -/
private theorem curveFamilyBaseIso_naturality_ofBaseLocus
    (𝒟 : BasedCategory.{v, t} (BigFppfOver B integerBase hZ))
    (E : CurveFamily B hZ ≌ 𝒟.obj)
    (hE : E.functor ⋙ 𝒟.p = curvesProjectionOver B hZ)
    {x z : 𝒟.obj} (φ : x ⟶ z) :
    (E.inverse.map φ).baseMap ≫ (curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE z).hom =
      (curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE x).hom ≫ 𝒟.p.map φ := by
  simp only [curveFamilyBaseIso_ofBaseLocus, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
    Category.assoc]
  have hm := CategoryTheory.Functor.congr_hom hE.symm (E.inverse.map φ)
  have hc := E.counitIso.hom.naturality φ
  simp only [Functor.comp_map, curvesProjectionOver] at hm
  simp only [Functor.comp_map, Functor.id_map] at hc
  change E.functor.map (E.inverse.map φ) ≫ (E.counitIso.app z).hom =
    (E.counitIso.app x).hom ≫ φ at hc
  have hp := congrArg (fun ψ => 𝒟.p.map ψ) hc
  have hx : 𝒟.p.obj (E.functor.obj (E.inverse.obj x)) =
      (E.inverse.obj x).base := congrArg (fun F => F.obj (E.inverse.obj x)) hE
  have hz : 𝒟.p.obj (E.functor.obj (E.inverse.obj z)) =
      (E.inverse.obj z).base := congrArg (fun F => F.obj (E.inverse.obj z)) hE
  have hm' : (E.inverse.map φ).baseMap =
      eqToHom hx.symm ≫ 𝒟.p.map (E.functor.map (E.inverse.map φ)) ≫
        eqToHom hz := hm
  have hbase : (E.inverse.map φ).baseMap ≫ eqToHom hz.symm =
      eqToHom hx.symm ≫ 𝒟.p.map (E.functor.map (E.inverse.map φ)) := by
    rw [hm']
    simp [Category.assoc]
  change (E.inverse.map φ).baseMap ≫ eqToHom hz.symm ≫
      𝒟.p.map (E.counitIso.app z).hom =
    eqToHom hx.symm ≫ 𝒟.p.map (E.counitIso.app x).hom ≫ 𝒟.p.map φ
  rw [← Category.assoc, hbase, Category.assoc, ← Functor.map_comp, hp, Functor.map_comp]

/-- The morphism of base schemes attached to the structure morphism of an object of a
scheme-valued point of the stack is the structure morphism of the object of the site. -/
private theorem curveFamilyBaseMap_toTerminal_ofBaseLocus
    (𝒟 : BasedCategory.{v, t} (BigFppfOver B integerBase hZ))
    (E : CurveFamily B hZ ≌ 𝒟.obj)
    (hE : E.functor ⋙ 𝒟.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj)
    (hy : y ⋙ 𝒟.p = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
    let t : T ⟶ T₀ := Over.homMk T.hom rfl
    (E.inverse.map (y.map t)).baseMap ≫ (curveFamilyBaseIsoAt_ofBaseLocus B hZ 𝒟 E hE U y hy).hom =
    (curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE (y.obj T)).hom ≫
      eqToHom (congrArg (fun F => F.obj T) hy) ≫
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
  dsimp only
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let t : T ⟶ T₀ := Over.homMk T.hom rfl
  have hnat := curveFamilyBaseIso_naturality_ofBaseLocus B hZ 𝒟 E hE (y.map t)
  have hhy := Functor.congr_hom hy t
  have hT : 𝒟.p.obj (y.obj T) = (Over.map U.hom).obj T :=
    congrArg (fun F => F.obj T) hy
  have h₁ : 𝒟.p.obj (y.obj T₀) = (Over.map U.hom).obj T₀ :=
    congrArg (fun F => F.obj T₀) hy
  have h₂ := over_map_obj_mk_id_ofBaseLocus B hZ U
  have hhy' : 𝒟.p.map (y.map t) =
      eqToHom hT ≫ (Over.map U.hom).map t ≫ eqToHom h₁.symm := by
    simpa only [Functor.comp_map] using hhy
  have hcanon : (Over.map U.hom).map t ≫ eqToHom h₂ =
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    cases U
    rfl
  change (E.inverse.map (y.map t)).baseMap ≫
      (curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE (y.obj T₀)).hom ≫ eqToHom h₁ ≫ eqToHom h₂ =
    (curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE (y.obj T)).hom ≫
      eqToHom hT ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U)
  rw [← Category.assoc, ← Category.assoc, hnat, hhy']
  simp [Category.assoc, hcanon]

/-- The family of curves attached to an object of a scheme-valued point of the stack has the
property exactly when the object of the site maps to the open subobject representing the locus
in the base. -/
private theorem prop_y_iff_overFactor
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (𝒟 : BasedCategory.{v, t} (BigFppfOver B integerBase hZ))
    (E : CurveFamily B hZ ≌ 𝒟.obj)
    (hE : E.functor ⋙ 𝒟.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj)
    (hy : y ⋙ 𝒟.p = Over.map U.hom) :
    let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
    let G := E.inverse.obj (y.obj T₀)
    ∀ (W : Subfunctor (yoneda.obj G.base))
      (_hWchar : ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        Pfam F ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
      (V : BigFppfOver B integerBase hZ)
      (j : V ⟶ G.base) (eW : yoneda.obj V ≅ W.toFunctor)
      (_heW : eW.hom ≫ W.ι = yoneda.map j)
      (T : BigFppfOver B U.left.1 U.left.2),
      Pfam (E.inverse.obj (y.obj T)) ↔
        Nonempty (T ⟶
          (Over.mk (j ≫ (curveFamilyBaseIsoAt_ofBaseLocus B hZ 𝒟 E hE U y hy).hom).left :
            BigFppfOver B U.left.1 U.left.2)) := by
  dsimp only
  intro W hWchar V j e he T
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let t : T ⟶ T₀ := Over.homMk T.hom rfl
  let F := E.inverse.obj (y.obj T)
  let G := E.inverse.obj (y.obj T₀)
  let a : F ⟶ G := E.inverse.map (y.map t)
  let β := curveFamilyBaseIsoAt_ofBaseLocus B hZ 𝒟 E hE U y hy
  have hT : 𝒟.p.obj (y.obj T) = (Over.map U.hom).obj T :=
    congrArg (fun H => H.obj T) hy
  let α : F.base ≅ (Over.map U.hom).obj T :=
    curveFamilyBaseIso_ofBaseLocus B hZ 𝒟 E hE (y.obj T) ≪≫ eqToIso hT
  have hcomm : a.baseMap ≫ β.hom =
      α.hom ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    simpa only [α, Iso.trans_hom, eqToIso.hom, Category.assoc] using
      curveFamilyBaseMap_toTerminal_ofBaseLocus B hZ 𝒟 E hE U y hy T
  exact (hWchar F a).trans <|
    (factor_openSubspace_iff W j e he a.baseMap).trans <|
    (factorization_iff_of_iso a.baseMap
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) j α β hcomm).trans <|
    factor_to_over_iff B integerBase hZ U V (j ≫ β.hom) T

/-- **The locus over a scheme-valued point of the stack is represented by an open subobject.**
Over a scheme-valued point `y` of the stack there is an object of the site over the base scheme
whose structure morphism is an open immersion and which receives a morphism from an object of
the site exactly when the family of curves there has the property. -/
private theorem exists_prop_open_over
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
    (𝒟 : BasedCategory.{v, t} (BigFppfOver B integerBase hZ))
    (E : CurveFamily B hZ ≌ 𝒟.obj)
    (hE : E.functor ⋙ 𝒟.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj)
    (hy : y ⋙ 𝒟.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion (B.inclusion.map V.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Pfam (E.inverse.obj (y.obj T)) ↔ Nonempty (T ⟶ V) := by
  classical
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let G := E.inverse.obj (y.obj T₀)
  obtain ⟨W, hW, hWchar⟩ := hlocus G
  obtain ⟨V, j, hj, e, he⟩ := openSubspace_yoneda_representation B
    integerBase hZ G.base W hW
  let β := curveFamilyBaseIsoAt_ofBaseLocus B hZ 𝒟 E hE U y hy
  let j' : V ⟶ U := j ≫ β.hom
  let V' : BigFppfOver B U.left.1 U.left.2 := Over.mk j'.left
  have hj' : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j') := by
    change IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map (j ≫ β.hom))
    rw [Functor.map_comp]
    let : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) := hj
    infer_instance
  exact ⟨V', hj', prop_y_iff_overFactor B hZ Pfam 𝒟 E hE U y hy W hWchar V j e he⟩

/-! ### The method of Section 109.6 -/

/-- **The method of Section 109.6 (Stacks 0E0E).** Let `P` be a property of families of curves
which is inherited along morphisms of families — equivalently, stable under base change — and
suppose that for every family of curves `X → S` there is an open subspace of the base through
which the morphism of base schemes of a second family mapping to it factors exactly when that
second family has `P`. Then `P` cuts an open substack out of the stack of curves, and an object
of the stack belongs to it exactly when the family of curves it classifies has `P`.

The algebraic stack of curves is a hypothesis: `𝒳` is any algebraic stack over the big fppf
site of the integers whose objects are identified with families of curves by an equivalence `E`
over that site. -/
@[no_expose]
def curvesOpenSubstackOfBaseLocus
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    {U : Stack.OpenSubstack 𝒳 //
      ∀ F : CurveFamily B hZ, U.property (E.functor.obj F) ↔ Pfam F} := by
  classical
  let P : ObjectProperty 𝒳.val.val.obj := fun x => Pfam (E.inverse.obj x)
  have hpre : ∀ {x y : 𝒳.val.val.obj}, (x ⟶ y) → P y → P x := fun f => hPfam (E.inverse.map f)
  have hstrict : P.IsClosedUnderIsomorphisms := ⟨fun e hx => hpre e.inv hx⟩
  have hOpen :
      ∃ hP : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
          (Stack.fullSubcategoryBased 𝒳 P),
        Stack.AlgebraicStacks.IsOpenImmersion B integerBase hZ
          (Stack.fullSubcategoryInclusion 𝒳 P hP) := by
    have hlocal : ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        IsAlgebraicSpace B U.left.1 U.left.2
          (propertyPresheaf.{u} (fun T => P (y.obj T)) (fun f => hpre (y.map f))) := by
      intro U y hy
      obtain ⟨V, hV, hchar⟩ := exists_prop_open_over B hZ Pfam hlocus 𝒳.val.val E hE U y hy
      let e := propertyPresheafIsoYoneda.{u} (fun T => P (y.obj T))
        (fun f => hpre (y.map f)) V hchar
        (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
      exact isAlgebraicSpace_of_iso B U.left.1 U.left.2 e
        (isAlgebraicSpace_yoneda B U.left.1 U.left.2 V)
    let hP := fullSubcategory_isAlgebraicStack_of_local_representability
      B integerBase hZ 𝒳 P hpre hlocal
    refine ⟨hP, ?_⟩
    constructor
    · intro U
      dsimp only
      intro y hy
      exact ⟨propertyPresheaf.{u} (fun T => P (y.obj T)) (fun f => hpre (y.map f)),
        hlocal U y hy,
        ⟨fullSubcategoryBaseChangePresheafEquivalence
          𝒳.val.val.p (Over.map U.hom) y hy P hpre⟩⟩
    · intro U y hy F hF heF
      obtain ⟨V, hV, hchar⟩ := exists_prop_open_over B hZ Pfam hlocus 𝒳.val.val E hE U y hy
      let Q := propertyPresheaf.{u} (fun T => P (y.obj T)) (fun f => hpre (y.map f))
      let eQ := fullSubcategoryBaseChangePresheafEquivalence
        𝒳.val.val.p (Over.map U.hom) y hy P hpre
      have hp : (TwoFibreProductOver.fst (Over.map U.hom)
          (P.ι ⋙ 𝒳.val.val.p) 𝒳.val.val.p y P.ι).IsFiberedInGroupoids :=
        StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver eQ
          (elementsProjection_isFiberedInSetoids Q).isFiberedInGroupoids
      let e : F ≅ Q := presheafIsoOfEquivalenceOver_ofBaseLocus hp F Q (Classical.choice heF) eQ
      let eV := propertyPresheafIsoYoneda.{u} (fun T => P (y.obj T))
        (fun f => hpre (y.map f)) V hchar
        (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
      exact algebraicSpaceMap_open_of_yonedaIso B hZ U F hF V hV (e ≪≫ eV)
  exact ⟨⟨P, hstrict, hOpen.choose, hOpen.choose_spec⟩,
    fun F => ⟨hPfam (E.unitIso.app F).hom, hPfam (E.unitIso.app F).inv⟩⟩

/-- **The method of Section 109.6, as a factorization criterion.** The classifying object of a
family of curves lifts through the inclusion of the open substack cut out by `P` exactly when
the family has `P`.

As for `AlgebraicGeometry.curvesOpenSubstackOfBaseLocus`, the algebraic stack of curves and its
identification with families of curves are hypotheses, and nothing else is assumed. -/
theorem classifying_factors_curvesOpenSubstackOfBaseLocus_iff
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (F : CurveFamily B hZ) :
    (∃ Y : (curvesOpenSubstackOfBaseLocus B hZ Pfam hPfam hlocus 𝒳 E
        hE).1.property.FullSubcategory, Y.obj = E.functor.obj F) ↔ Pfam F := by
  have hchar := (curvesOpenSubstackOfBaseLocus B hZ Pfam hPfam hlocus 𝒳 E hE).2 F
  constructor
  · rintro ⟨Y, hY⟩
    exact hchar.mp (hY ▸ Y.property)
  · intro hN
    exact ⟨⟨E.functor.obj F, hchar.mpr hN⟩, rfl⟩

/-! ### The method of Section 109.6 over the category of curves, with no hypothesis -/

/-- A property of families of curves which is inherited along morphisms is invariant under
isomorphism, so the full subcategory it selects is *strictly* full. -/
theorem isClosedUnderIsomorphisms_of_curveFamily_hom
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F) :
    Pfam.IsClosedUnderIsomorphisms :=
  ⟨fun e hx => hPfam e.inv hx⟩

/-- The full subcategory of the category of families of curves selected by a property inherited
along morphisms, as an object of the 2-category of categories fibred in groupoids over the big
fppf site of `Spec(ℤ)`. -/
@[no_expose]
def curvesFullSubcategoryFibered
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F) :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (Pfam.ι ⋙ curvesProjectionOver B hZ))
    (fullSubcategory_isFiberedInGroupoids (curvesProjectionOver B hZ)
      (curvesFiberedCategory B hZ).isFiberedInGroupoids Pfam (fun a h => hPfam a h))

/-- The inclusion `Curves^P ⊂ Curves`, as a 1-morphism of categories fibred in groupoids over the
big fppf site of `Spec(ℤ)`. -/
@[no_expose]
def curvesFullSubcategoryInclusion
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F) :
    curvesFullSubcategoryFibered B hZ Pfam hPfam ⟶ curvesFiberedCategory B hZ :=
  Bicategory.InducedBicategory.mkHom ({ toFunctor := Pfam.ι, w := rfl })

/-- The inclusion `Curves^P ⊂ Curves` is full: its underlying functor is the inclusion of a full
subcategory of the category of families of curves. -/
theorem full_curvesFullSubcategoryInclusion
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F) :
    (curvesFullSubcategoryInclusion B hZ Pfam hPfam).hom.toFunctor.Full :=
  ObjectProperty.full_ι Pfam

/-- The inclusion `Curves^P ⊂ Curves` is faithful: its underlying functor is the inclusion of a
full subcategory of the category of families of curves. -/
theorem faithful_curvesFullSubcategoryInclusion
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F) :
    (curvesFullSubcategoryInclusion B hZ Pfam hPfam).hom.toFunctor.Faithful :=
  ObjectProperty.faithful_ι Pfam

/-- `AlgebraicGeometry.exists_prop_open_over` at the category of families of curves itself,
through the identity equivalence. -/
private theorem exists_prop_open_over_curves
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion (B.inclusion.map V.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2, Pfam (y.obj T) ↔ Nonempty (T ⟶ V) :=
  exists_prop_open_over B hZ Pfam hlocus (BasedCategory.ofFunctor (curvesProjectionOver B hZ))
    (CategoryTheory.Equivalence.refl) (Functor.id_comp _) U y hy

/-- The presheaf of proofs of the property over a scheme-valued point of the category of curves
is an algebraic space: it is represented by the open locus in the base. -/
private theorem isAlgebraicSpace_propertyPresheaf_curves
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ)
    (hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom) :
    IsAlgebraicSpace B U.left.1 U.left.2
      (propertyPresheaf.{u} (fun T => Pfam (y.obj T)) (fun f => hPfam (y.map f))) := by
  obtain ⟨V, hV, hchar⟩ := exists_prop_open_over_curves B hZ Pfam hlocus U y hy
  exact isAlgebraicSpace_of_iso B U.left.1 U.left.2
    (propertyPresheafIsoYoneda.{u} (fun T => Pfam (y.obj T)) (fun f => hPfam (y.map f)) V hchar
      (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV))
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 V)

/-- **The method of Section 109.6, representability clause, with no hypothesis.** The inclusion
`Curves^P ⊂ Curves` is representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpaces_curvesFullSubcategoryInclusion
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom) :
    Stack.IsRepresentableByAlgebraicSpaces B integerBase hZ
      (curvesFullSubcategoryInclusion B hZ Pfam hPfam).hom := by
  intro U
  dsimp only
  intro y₀ hy₀
  let y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ := y₀
  have hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom := hy₀
  exact ⟨_, isAlgebraicSpace_propertyPresheaf_curves B hZ Pfam hPfam hlocus U y hy,
    ⟨fullSubcategoryBaseChangePresheafEquivalence (curvesProjectionOver B hZ) (Over.map U.hom)
      y hy Pfam (fun a h => hPfam a h)⟩⟩

/-- **The method of Section 109.6, open-immersion clause, with no hypothesis.** The inclusion
`Curves^P ⊂ Curves` is an open immersion in the sense of Stacks 04XB: every algebraic space
representing one of its base changes along a scheme-valued point of `Curves` has open immersion
structural morphism. -/
theorem isOpenImmersion_curvesFullSubcategoryInclusion
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom) :
    Stack.IsOpenImmersion B integerBase hZ (curvesFullSubcategoryInclusion B hZ Pfam hPfam) := by
  intro U y₀ hy₀ F hF heF
  let y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ := y₀
  have hy : y ⋙ curvesProjectionOver B hZ = Over.map U.hom := hy₀
  obtain ⟨V, hV, hchar⟩ := exists_prop_open_over_curves B hZ Pfam hlocus U y hy
  let hpre : ∀ {x z : CurveFamily B hZ}, (x ⟶ z) → Pfam z → Pfam x := fun a h => hPfam a h
  let Q := propertyPresheaf.{u} (fun T => Pfam (y.obj T)) (fun f => hpre (y.map f))
  let eQ := fullSubcategoryBaseChangePresheafEquivalence (curvesProjectionOver B hZ)
    (Over.map U.hom) y hy Pfam hpre
  have hp := StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver eQ
    (elementsProjection_isFiberedInSetoids Q).isFiberedInGroupoids
  let e : F ≅ Q := presheafIsoOfEquivalenceOver_ofBaseLocus hp F Q (Classical.choice heF) eQ
  let eV := propertyPresheafIsoYoneda.{u} (fun T => Pfam (y.obj T))
    (fun f => hpre (y.map f)) V hchar
    (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
  exact algebraicSpaceMap_open_of_yonedaIso B hZ U F hF V hV (e ≪≫ eV)

/-- **The method of Section 109.6, as a factorization criterion, with no hypothesis.** A family
of curves lifts through the inclusion `Curves^P ⊂ Curves` exactly when it has `P`. -/
theorem lifts_curvesFullSubcategory_iff
    (Pfam : ObjectProperty (CurveFamily B hZ)) (F : CurveFamily B hZ) :
    (∃ Y : Pfam.FullSubcategory, Y.obj = F) ↔ Pfam F := by
  constructor
  · rintro ⟨Y, hY⟩
    exact hY ▸ Y.property
  · intro hF
    exact ⟨⟨F, hF⟩, rfl⟩

/-- **The method of Section 109.6, as a factorization criterion through the inclusion
1-morphism, with no hypothesis.** A family of curves is in the image on objects of the inclusion
`Curves^P ⟶ Curves` of categories fibred in groupoids over the big fppf site of `Spec(ℤ)`
exactly when it has `P`. -/
theorem lifts_curvesFullSubcategoryInclusion_iff
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (F : CurveFamily B hZ) :
    (∃ Y : (curvesFullSubcategoryFibered B hZ Pfam hPfam).based.obj,
        (CatFiberedInGroupoids.homFunctor
          (curvesFullSubcategoryInclusion B hZ Pfam hPfam)).obj Y = F) ↔
      Pfam F :=
  lifts_curvesFullSubcategory_iff B hZ Pfam F

/-- **The method of Section 109.6 (Stacks 0E0E), over the category of curves itself.** Let `P` be
a property of families of curves which is inherited along morphisms of families — equivalently,
stable under base change — and suppose that for every family of curves `X → S` there is an open
subspace of the base through which the morphism of base schemes of a second family mapping to it
factors exactly when that second family has `P`. Then `P` cuts an open substack
`Curves^P ⊂ Curves` out of the category fibred in groupoids of families of curves, in the sense
of `AlgebraicGeometry.Stack.FiberedOpenSubstack`, and its objects are the families with `P`
(`AlgebraicGeometry.curvesFiberedOpenSubstackOfBaseLocus_property`). -/
@[no_expose]
def curvesFiberedOpenSubstackOfBaseLocus
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom) :
    Stack.FiberedOpenSubstack (curvesFiberedCategory B hZ) where
  property := Pfam
  strictlyFull := isClosedUnderIsomorphisms_of_curveFamily_hom B hZ Pfam hPfam
  isFiberedInGroupoids := fullSubcategory_isFiberedInGroupoids (curvesProjectionOver B hZ)
    (curvesFiberedCategory B hZ).isFiberedInGroupoids Pfam (fun a h => hPfam a h)
  isRepresentable :=
    isRepresentableByAlgebraicSpaces_curvesFullSubcategoryInclusion B hZ Pfam hPfam hlocus
  isOpenImmersion := isOpenImmersion_curvesFullSubcategoryInclusion B hZ Pfam hPfam hlocus

/-- The objects of the open substack `Curves^P` of the method of Section 109.6 are the families
of curves with `P`. -/
@[simp]
theorem curvesFiberedOpenSubstackOfBaseLocus_property
    (Pfam : ObjectProperty (CurveFamily B hZ))
    (hPfam : ∀ {F G : CurveFamily B hZ}, (F ⟶ G) → Pfam G → Pfam F)
    (hlocus : ∀ G : CurveFamily B hZ,
      ∃ W : Subfunctor (schemeSpace G.base).obj,
        Space.IsOpenSubspace B integerBase hZ W ∧
        ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
          Pfam F ↔
            ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
              t ≫ W.ι = (schemeSpaceMap a.baseMap).hom) :
    (curvesFiberedOpenSubstackOfBaseLocus B hZ Pfam hPfam hlocus).property = Pfam := by
  unfold curvesFiberedOpenSubstackOfBaseLocus
  rfl

end AlgebraicGeometry

end
