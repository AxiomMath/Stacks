module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentedTwoFibreProductPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFunctorial
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterionSchemePoint
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CancelSndTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TripleProductRecognitionSnd
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative dimension at a point of a morphism from an algebraic space to an algebraic stack

Let `f : T ⟶ 𝒳` be a 1-morphism, locally of finite type, from an algebraic space to an
algebraic stack over `S`, and let `t ∈ |T|` have image `x ∈ |𝒳|`. Stacks 0DRG defines the
relative dimension `dim_t(T_x)` by choosing a field-valued point `Spec k ⟶ 𝒳` representing
`x` and a point `t'` of `T ×_𝒳 Spec k` above `t`, and setting
`dim_t(T_x) = dim_{t'}(T ×_𝒳 Spec k)`. The fibre `T ×_𝒳 Spec k` is an algebraic space
(Stacks 0300), so the right-hand side is the dimension of an algebraic space at a point
(Stacks 04N5).

## Main definitions

* `AlgebraicGeometry.Stack.representedDimensionAtPoint` is the dimension at a point of a
  category fibred in groupoids represented by an algebraic space.
* `AlgebraicGeometry.Stack.fieldFibreDimensionAt` is the right-hand side of the formula of
  Stacks 0DRG, for a given field-valued representative and a given point of the fibre.
* `AlgebraicGeometry.Stack.relativeDimensionAt` is **Stacks 0DRG**, the relative dimension of
  `f` at `t`, obtained by making the two choices the source prescribes.
* `AlgebraicGeometry.Stack.refinementBaseMap` and
  `AlgebraicGeometry.Stack.refinementMorphismIso`: the morphism of field spectra underlying an
  arrow between the objects of two field-valued points, and the 2-commutative triangle of
  1-morphisms it induces.
* `AlgebraicGeometry.Stack.refinedFieldFibreSquare`: the fibre over a refinement of a
  field-valued point, presented as a base change of the fibre over the point refined.
* `AlgebraicGeometry.Stack.algebraicSpaceStackMap` is the 1-morphism of algebraic stacks
  attached to a morphism of algebraic spaces over `S`.

## Main results

* `AlgebraicGeometry.Stack.exists_point_fieldFibreSquare`: Stacks 04XH supplies the point `t'`.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpace_fieldFibreSquare`: Stacks 0300
  makes `T ×_𝒳 Spec k` an algebraic space.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_of_representing`: two algebraic spaces
  representing the same category fibred in groupoids have the same dimension at points with
  the same image, so `representedDimensionAtPoint` does not depend on the representation.
* `AlgebraicGeometry.Stack.exists_eq_fieldFibreDimensionAt`: `relativeDimensionAt` is the
  value of the formula of Stacks 0DRG at choices satisfying the source's two conditions.
* `AlgebraicGeometry.Stack.fieldFibreDimensionAt_eq_dimensionAtPoint`: `fieldFibreDimensionAt`
  is computed by every algebraic space representing the fibre.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback`: in a
  cartesian square of algebraic spaces whose base change is taken along a morphism out of the
  field spectrum of a field-valued point, the dimension at a point upstairs is the relative
  dimension of the morphism base-changed at the image point. This is part (1) of Stacks 04NS,
  hence Morphisms Lemma 02FY, read over a field base through Stacks 0D4M.
* `AlgebraicGeometry.Stack.dimensionAtPoint_eq_of_isPullback_of_isPullback`: consequently two
  such base changes of one locally-of-finite-type morphism of algebraic spaces, along the field
  spectra of two different field-valued points, agree at any two points with the same image.
  This is the independence of both choices, at the level of algebraic spaces.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_refinedFieldFibreSquare`: Stacks 02XD identifies
  the fibre over a refinement with the base change of the fibre along the induced morphism of
  field spectra.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd`: the
  fibre `𝒯 ×_𝒳 Spec k ⟶ Spec k` is locally of finite type as a morphism of algebraic spaces.
* `AlgebraicGeometry.Stack.representedDimensionAtPoint_refinedFieldFibreSquare`: **the value of
  the formula of Stacks 0DRG is unchanged by refining the chosen field-valued point**, the
  chosen point of the fibre being transported along the base change. This is the independence
  of the field-valued representative asked for by Stacks 0DRH (1).
* `AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct`: Stacks 04SD at a
  2-fibre product square recognised by a theorem rather than constructed as the canonical apex.
* `AlgebraicGeometry.Stack.representedDimensionAtPoint_eq_fieldFibreDimensionAt`: the value of
  the formula of Stacks 0DRG is computed by *every* base change of the fibre to a field spectrum.
* `AlgebraicGeometry.Stack.fieldFibreDimensionAt_eq_fieldFibreDimensionAt_of_pointsMap_eq`: **the
  value of the formula of Stacks 0DRG depends on neither of the two choices** — two field-valued
  points and two points of the respective fibres with the same image in `|𝒯|` give one value.
* `AlgebraicGeometry.Stack.fieldFibreDimensionAt_eq_of_pointsMap_eq`: its case of one
  field-valued point, the independence of the chosen lift.
* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_fieldFibreDimensionAt`: **Stacks 0DRH (1)**,
  that `relativeDimensionAt` is the value of the formula of Stacks 0DRG at every admissible pair
  of choices, and so an invariant of `(f, t)`.
* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_algebraicSpaceStackMap_iff`: a morphism of
  algebraic spaces is locally of finite type exactly when the 1-morphism of algebraic stacks it
  induces is.
* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap`:
  when the target is represented by an algebraic space `G`, `relativeDimensionAt` is the relative
  dimension of Stacks 04NM of the induced morphism of algebraic spaces `T ⟶ G`.
* `AlgebraicGeometry.Stack.relativeDimensionAt_eq_iff_hasRelativeDimensionAt`: **Stacks
  0DRH (2)**, that for a morphism of algebraic spaces `relativeDimensionAt` agrees with the
  relative dimension at a point of Stacks 04NM.

## References

* [Stacks Project, Tag 0DRG](https://stacks.math.columbia.edu/tag/0DRG)
* [Stacks Project, Tag 0DRH](https://stacks.math.columbia.edu/tag/0DRH)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02XC](https://stacks.math.columbia.edu/tag/02XC)
* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 0300](https://stacks.math.columbia.edu/tag/0300)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
* [Stacks Project, Tag 04S7](https://stacks.math.columbia.edu/tag/04S7)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XF](https://stacks.math.columbia.edu/tag/04XF)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 06FC](https://stacks.math.columbia.edu/tag/06FC)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 0D4M](https://stacks.math.columbia.edu/tag/0D4M)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre over a field-valued point -/

section FieldFibre

variable {𝒯 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The field spectrum of a field-valued point `p` of `𝒳`, read as a field-valued point of the
category it represents: its object is the identity of the base of `p`. -/
def baseFieldValuedPoint (p : FieldValuedPoint B S hS 𝒳.val) :
    FieldValuedPoint B S hS (schemeFibredCategory B S hS p.base).val :=
  { carrier := p.carrier, base := p.base, isSpec := p.isSpec,
    obj := Over.mk (𝟙 p.base), «over» := rfl }

/-- The 1-morphism of a field-valued point carries the tautological point of its field
spectrum to the point of `|𝒳|` that it represents. -/
theorem pointsMap_baseFieldValuedPoint (p : FieldValuedPoint B S hS 𝒳.val) :
    pointsMap B S hS (schemeFibredCategory B S hS p.base).val
        (schemeFibredCategory B S hS p.base).property 𝒳.property
        (fieldValuedPointMorphism B S hS 𝒳 p).hom
        (pointClass B S hS (schemeFibredCategory B S hS p.base).val
          (schemeFibredCategory B S hS p.base).property (baseFieldValuedPoint B S hS p)) =
      pointClass B S hS 𝒳.val 𝒳.property p := by
  rw [pointsMap_class]
  apply (class_eq_class_iff_hasCommonExtension B S hS 𝒳.val 𝒳.property _ _).2
  refine ⟨_, ⟨𝟙 _⟩, ⟨?_⟩⟩
  exact (Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.property p.base
    (Functor.Fiber.mk p.over) (Over.mk (𝟙 p.base))).φ

/-- The fibre `𝒯 ×_𝒳 Spec k` of `f` over a field-valued point `p` of `𝒳`: the canonical
2-fibre product square of `f` with the 1-morphism `Spec k ⟶ 𝒳` of `p`. -/
noncomputable abbrev fieldFibreSquare (f : 𝒯 ⟶ 𝒳) (p : FieldValuedPoint B S hS 𝒳.val) :
    Bicategory.TwoCommSq f (fieldValuedPointMorphism B S hS 𝒳 p) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f
    (fieldValuedPointMorphism B S hS 𝒳 p)

/-- **Stacks 04XH at the fibre over a field-valued point.** If `p` represents the image of `t`,
some point of `𝒯 ×_𝒳 Spec k` maps to `t`; this is what the definition of Stacks 0DRG chooses. -/
theorem exists_point_fieldFibreSquare (f : 𝒯 ⟶ 𝒳) (t : points B S hS 𝒯.val 𝒯.property)
    (p : FieldValuedPoint B S hS 𝒳.val)
    (hp : pointClass B S hS 𝒳.val 𝒳.property p =
      pointsMap B S hS 𝒯.val 𝒯.property 𝒳.property f.hom t) :
    ∃ q : points B S hS (fieldFibreSquare B S hS f p).pt.val
        (fieldFibreSquare B S hS f p).pt.property,
      pointsMap B S hS (fieldFibreSquare B S hS f p).pt.val
        (fieldFibreSquare B S hS f p).pt.property 𝒯.property
        (fieldFibreSquare B S hS f p).fst.hom q = t := by
  obtain ⟨q, hq, -⟩ :=
    exists_point_of_isTwoFibreProduct B S hS (fieldFibreSquare B S hS f p)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f
        (fieldValuedPointMorphism B S hS 𝒳 p)) t
      (pointClass B S hS (schemeFibredCategory B S hS p.base).val
        (schemeFibredCategory B S hS p.base).property (baseFieldValuedPoint B S hS p))
      (by rw [pointsMap_baseFieldValuedPoint, hp])
  exact ⟨q, hq⟩

/-- **Stacks 0300 at the fibre over a field-valued point.** If `𝒯` is represented by an
algebraic space and `𝒳` is an algebraic stack, then `𝒯 ×_𝒳 Spec k` is represented by an
algebraic space, because the 1-morphism of a field-valued point of an algebraic stack is
representable by algebraic spaces. -/
theorem isRepresentableByAlgebraicSpace_fieldFibreSquare (f : 𝒯 ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯)
    (p : FieldValuedPoint B S hS 𝒳.val) :
    IsRepresentableByAlgebraicSpace B S hS (fieldFibreSquare B S hS f p).pt :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    (schemeFibredCategory B S hS p.base) 𝒳 𝒯 (fieldValuedPointMorphism B S hS 𝒳 p) f
    (fieldFibreSquare B S hS f p)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f
      (fieldValuedPointMorphism B S hS 𝒳 p))
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS h𝒳
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base) _) h𝒯

end FieldFibre

/-! ### Independence of the representing algebraic space -/

section Represented

variable {𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (e : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
    (presheafOfCategories (F ⋙ typeToCat)).p)
  (e' : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
    (presheafOfCategories (F' ⋙ typeToCat)).p)

/-- The comparison isomorphism between two algebraic spaces representing the same category
fibred in groupoids: the morphism of representing presheaves of Stacks 04SW attached to the
identity 1-morphism, taken in both directions. -/
noncomputable def representingIso : F ≅ F' where
  hom := representingMap B S hS 𝒲 𝒲 F F' e e' (𝟙 𝒲)
  inv := representingMap B S hS 𝒲 𝒲 F' F e' e (𝟙 𝒲)
  hom_inv_id := by
    rw [← representingMap_comp B S hS F F' F e e' e (𝟙 𝒲) (𝟙 𝒲), Category.comp_id,
      representingMap_id]
  inv_hom_id := by
    rw [← representingMap_comp B S hS F' F F' e' e e' (𝟙 𝒲) (𝟙 𝒲), Category.comp_id,
      representingMap_id]

/-- The comparison isomorphism of two representing algebraic spaces is compatible with their
canonical maps on points. -/
theorem spacePointMap_representingIso (x : Space.points B S hS F) :
    spacePointMap B S hS F' 𝒲 (representingEquivalence B S hS F' 𝒲 e').functor
        (Space.pointsMap B S hS F (representingIso B S hS F F' e e').hom x) =
      spacePointMap B S hS F 𝒲 (representingEquivalence B S hS F 𝒲 e).functor x := by
  rw [show (representingIso B S hS F F' e e').hom =
    representingMap B S hS 𝒲 𝒲 F F' e e' (𝟙 𝒲) from rfl,
    spacePointMap_representing_naturality B S hS F F' 𝒲 𝒲 e e' (𝟙 𝒲) x]
  exact pointsMap_basedFunctorId B S hS 𝒲.property _

/-- **The dimension of a category fibred in groupoids represented by an algebraic space does
not depend on the representation.** If two algebraic spaces represent `𝒲` and two of their
points have the same image in `|𝒲|`, the two spaces have the same dimension at those points. -/
theorem dimensionAtPoint_eq_of_representing
    (hF : IsAlgebraicSpace B S hS F) (hF' : IsAlgebraicSpace B S hS F')
    (x : Space.points B S hS F) (x' : Space.points B S hS F')
    (hx : spacePointMap B S hS F 𝒲 (representingEquivalence B S hS F 𝒲 e).functor x =
      spacePointMap B S hS F' 𝒲 (representingEquivalence B S hS F' 𝒲 e').functor x') :
    Space.dimensionAtPoint B S hS F hF x = Space.dimensionAtPoint B S hS F' hF' x' := by
  have hinj := (bijective_spacePointMap_representing B S hS F' 𝒲 e').injective
  have key : Space.pointsMap B S hS F (representingIso B S hS F F' e e').hom x = x' :=
    hinj (by rw [spacePointMap_representingIso, hx])
  rw [Space.dimensionAtPoint_eq_of_isEtale B S hS hF hF' _
    (Space.isEtale_of_iso B S hS (representingIso B S hS F F' e e')) x, key]

end Represented

/-! ### Dimension at a point of a represented category fibred in groupoids -/

section RepresentedDimension

variable (𝒲 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (h𝒲 : IsRepresentableByAlgebraicSpace B S hS 𝒲)

/-- The dimension at a point of a category fibred in groupoids represented by an algebraic
space: the dimension of a representing algebraic space at the point corresponding to it under
the bijection on points of Stacks 04XL. -/
noncomputable def representedDimensionAtPoint (q : points B S hS 𝒲.val 𝒲.property) :
    WithBot ℕ∞ :=
  Space.dimensionAtPoint B S hS h𝒲.choose h𝒲.choose_spec.1
    ((Equiv.ofBijective _ (bijective_spacePointMap_representing B S hS h𝒲.choose 𝒲
      (Classical.choice h𝒲.choose_spec.2))).symm q)

/-- `AlgebraicGeometry.Stack.representedDimensionAtPoint` is computed by every representing
algebraic space: its value at the image of a point `x` of `F` is the dimension of `F` at `x`. -/
theorem representedDimensionAtPoint_eq (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒲.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (x : Space.points B S hS F) :
    representedDimensionAtPoint B S hS 𝒲 h𝒲
        (spacePointMap B S hS F 𝒲 (representingEquivalence B S hS F 𝒲 e).functor x) =
      Space.dimensionAtPoint B S hS F hF x :=
  dimensionAtPoint_eq_of_representing B S hS h𝒲.choose F
    (Classical.choice h𝒲.choose_spec.2) e h𝒲.choose_spec.1 hF _ x
    (Equiv.ofBijective_apply_symm_apply _ _ _)

end RepresentedDimension

/-! ### The relative dimension of Stacks 0DRG -/

section RelativeDimension

/-- The right-hand side of the formula of Stacks 0DRG: the dimension of the algebraic space
`𝒯 ×_𝒳 Spec k` at a point `q`, for a field-valued point `p` of `𝒳` with field spectrum
`Spec k`. -/
noncomputable def fieldFibreDimensionAt
    {𝒯 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒯 ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯)
    (p : FieldValuedPoint B S hS 𝒳.val)
    (q : points B S hS (fieldFibreSquare B S hS f p).pt.val
      (fieldFibreSquare B S hS f p).pt.property) : WithBot ℕ∞ :=
  representedDimensionAtPoint B S hS (fieldFibreSquare B S hS f p).pt
    (isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f h𝒳 h𝒯 p) q

variable (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)

/-- The point of the stack of `T` determined by a point of `T`, under the canonical bijection
on points of Stacks 04XL. -/
noncomputable abbrev stackPointOfSpacePoint (t : Space.points B S hS T) :
    points B S hS (fibredCategory B S hS T).val (fibredCategory B S hS T).property :=
  spacePointMap B S hS T (fibredCategory B S hS T)
    (BasedFunctor.id (fibredCategory B S hS T).val) t

/-- The relative dimension `dim_t(T_x)` at `t ∈ |T|` of a 1-morphism `f`, locally of finite type,
from an algebraic space `T` to an algebraic stack `𝒳`: the dimension of the algebraic space
`T ×_𝒳 Spec k` at a point above `t`, for a field-valued point `Spec k ⟶ 𝒳` representing the
image `x` of `t`. The representative and the point above `t` are the choices the source makes;
the point above `t` exists by Stacks 04XH. -/
@[stacks 0DRG, ega "IV 17.10.1"]
noncomputable def relativeDimensionAt
    (_hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T) :
    WithBot ℕ∞ :=
  fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT)
    (Quotient.out (pointsMap B S hS (fibredCategory B S hS T).val
      (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
      (stackPointOfSpacePoint B S hS T t)))
    (exists_point_fieldFibreSquare B S hS f.hom (stackPointOfSpacePoint B S hS T t) _
      (Quotient.out_eq _)).choose

/-- `AlgebraicGeometry.Stack.relativeDimensionAt` is the value of the formula of Stacks 0DRG at
a field-valued representative of the image of `t` and a point of the fibre above `t`, that is,
at choices satisfying the two conditions the source imposes. -/
theorem exists_eq_fieldFibreDimensionAt
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T) :
    ∃ (p : FieldValuedPoint B S hS 𝒳.val.val)
      (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
        (fieldFibreSquare B S hS f.hom p).pt.property),
      pointClass B S hS 𝒳.val.val 𝒳.val.property p =
          pointsMap B S hS (fibredCategory B S hS T).val
            (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
            (stackPointOfSpacePoint B S hS T t) ∧
        pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
            (fieldFibreSquare B S hS f.hom p).pt.property
            (fibredCategory B S hS T).property
            (fieldFibreSquare B S hS f.hom p).fst.hom q =
          stackPointOfSpacePoint B S hS T t ∧
        relativeDimensionAt B S hS T hT 𝒳 f hf t =
          fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property
            (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p q :=
  ⟨_, _, Quotient.out_eq _,
    (exists_point_fieldFibreSquare B S hS f.hom (stackPointOfSpacePoint B S hS T t) _
      (Quotient.out_eq _)).choose_spec, rfl⟩

end RelativeDimension

/-! ### Towards the independence of the choices: the field base as a field spectrum -/

section FieldBase

variable {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}

/-- The field spectrum of a field-valued point lies in the chosen big fppf site: it has the
size of the recorded base, which is an object of the site. -/
theorem contains_spectrum_fieldValuedPoint (p : FieldValuedPoint B S hS 𝒜) :
    B.Contains (Spec (.of p.carrier)) := by
  have hb : ((BigFppfOver.toScheme B S hS).obj p.base).size < B.cutoff := p.base.left.2
  rw [Scheme.size_congr p.isSpec] at hb
  exact hb

/-- The structure morphism of the field spectrum of a field-valued point: the structure
morphism of the recorded base, read through the identification of that base with the field
spectrum. -/
noncomputable def spectrumStructureMorphism (p : FieldValuedPoint B S hS 𝒜) :
    Spec (.of p.carrier) ⟶ S :=
  p.isSpec.inv ≫ B.inclusion.map p.base.hom

/-- The field spectrum of a field-valued point, as an object of the site over `S`. -/
noncomputable abbrev spectrumSiteObject (p : FieldValuedPoint B S hS 𝒜) :
    BigFppfOver B S hS :=
  Over.mk (⟨spectrumStructureMorphism B S hS p⟩ :
    B.obj (contains_spectrum_fieldValuedPoint B S hS p) ⟶ B.obj hS)

/-- The field spectrum of a field-valued point is isomorphic, over `S`, to its recorded base:
the identification recorded by the point is a morphism of the site in both directions. -/
noncomputable def spectrumSiteObjectIso (p : FieldValuedPoint B S hS 𝒜) :
    spectrumSiteObject B S hS p ≅ p.base := by
  let e : (spectrumSiteObject B S hS p).left ⟶ p.base.left := B.inclusion.preimage p.isSpec.inv
  let f : p.base.left ⟶ (spectrumSiteObject B S hS p).left := B.inclusion.preimage p.isSpec.hom
  have heMap : B.inclusion.map e = p.isSpec.inv := B.inclusion.map_preimage _
  have hfMap : B.inclusion.map f = p.isSpec.hom := B.inclusion.map_preimage _
  have hsiteMap : B.inclusion.map (spectrumSiteObject B S hS p).hom =
      spectrumStructureMorphism B S hS p := by
    simp [spectrumStructureMorphism, BigFppfOver.toScheme, BigFppfOver.forget]
  have he : e ≫ p.base.hom = (spectrumSiteObject B S hS p).hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, heMap, hsiteMap]
    rfl
  have hf : f ≫ (spectrumSiteObject B S hS p).hom = p.base.hom := by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, hfMap, hsiteMap]
    change p.isSpec.hom ≫ p.isSpec.inv ≫ B.inclusion.map p.base.hom =
      B.inclusion.map p.base.hom
    simp
  refine ⟨Over.homMk e he, Over.homMk f hf, ?_, ?_⟩ <;>
    refine Over.OverMorphism.ext (B.inclusion.map_injective ?_)
  · change B.inclusion.map (e ≫ f) = B.inclusion.map (𝟙 _)
    rw [B.inclusion.map_comp, heMap, hfMap]
    exact p.isSpec.inv_hom_id
  · change B.inclusion.map (f ≫ e) = B.inclusion.map (𝟙 _)
    rw [B.inclusion.map_comp, hfMap, heMap]
    exact p.isSpec.hom_inv_id

/-- The recorded base of a field-valued point of `𝒜`, read as a field-valued point of the
presheaf it represents in the sense of Stacks 03BU: the field is that of `p`, and the section
is the identification of the field spectrum with that base. -/
noncomputable def baseSpacePoint (p : FieldValuedPoint B S hS 𝒜) :
    Space.FieldValuedPoint B S hS (yoneda.obj p.base) where
  carrier := p.carrier
  field := p.field
  contained := contains_spectrum_fieldValuedPoint B S hS p
  toBase := spectrumStructureMorphism B S hS p
  value := (spectrumSiteObjectIso B S hS p).hom

/-- The presheaf represented by the recorded base of a field-valued point is the presheaf
represented by the field spectrum of `AlgebraicGeometry.Stack.baseSpacePoint`. -/
noncomputable def baseSpectrumIso (p : FieldValuedPoint B S hS 𝒜) :
    yoneda.obj p.base ≅
      yoneda.obj ((baseSpacePoint B S hS p).siteObject B S hS (yoneda.obj p.base)) :=
  yoneda.mapIso (spectrumSiteObjectIso B S hS p).symm

/-- **The dimension at a point of a base change over the field spectrum of a field-valued
point is the relative dimension of the morphism base-changed, at the image point.** -/
theorem dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback
    (p : FieldValuedPoint B S hS 𝒜) {W X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ yoneda.obj p.base} {b : W ⟶ X} {c : yoneda.obj p.base ⟶ Y} {g : X ⟶ Y}
    (sq : IsPullback a b c g) (hW : IsAlgebraicSpace B S hS W)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hg : Space.IsLocallyOfFiniteType B S hS g) (x : Space.points B S hS W) (d : ℕ∞) :
    Space.dimensionAtPoint B S hS W hW x = (d : WithBot ℕ∞) ↔
      Space.HasRelativeDimensionAt d B S hS g (Space.pointsMap B S hS W b x) := by
  have sq' : IsPullback (a ≫ (baseSpectrumIso B S hS p).hom) b
      ((baseSpectrumIso B S hS p).inv ≫ c) g :=
    sq.of_iso (Iso.refl _) (baseSpectrumIso B S hS p) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  rw [← Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B S hS hW
    (baseSpacePoint B S hS p) (a ≫ (baseSpectrumIso B S hS p).hom) x d]
  exact Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS d sq' hX hY
    (isAlgebraicSpace_yoneda B S hS _) hg x

/-- Two base changes of one locally-of-finite-type morphism `g` of algebraic spaces, along
morphisms out of the field spectra of two field-valued points of possibly different based
categories, have the same dimension at any two points with the same image under `g`. -/
private theorem dimensionAtPoint_eq_of_isPullback_of_isPullback_fieldValuedPoints
    {ℬ : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (p : FieldValuedPoint B S hS 𝒜) (p' : FieldValuedPoint B S hS ℬ)
    {W W' X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ yoneda.obj p.base} {b : W ⟶ X} {c : yoneda.obj p.base ⟶ Y}
    {a' : W' ⟶ yoneda.obj p'.base} {b' : W' ⟶ X} {c' : yoneda.obj p'.base ⟶ Y} {g : X ⟶ Y}
    (sq : IsPullback a b c g) (sq' : IsPullback a' b' c' g)
    (hW : IsAlgebraicSpace B S hS W) (hW' : IsAlgebraicSpace B S hS W')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hg : Space.IsLocallyOfFiniteType B S hS g)
    (x : Space.points B S hS W) (x' : Space.points B S hS W')
    (hx : Space.pointsMap B S hS W b x = Space.pointsMap B S hS W' b' x') :
    Space.dimensionAtPoint B S hS W hW x = Space.dimensionAtPoint B S hS W' hW' x' := by
  obtain ⟨d, hd⟩ :=
    WithBot.ne_bot_iff_exists.mp (Space.dimensionAtPoint_ne_bot B S hS W hW x)
  have h₁ : Space.dimensionAtPoint B S hS W hW x = (d : WithBot ℕ∞) := hd.symm
  have h₂ : Space.HasRelativeDimensionAt d B S hS g (Space.pointsMap B S hS W' b' x') := by
    rw [← hx]
    exact (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS p sq hW hX hY
      hg x d).mp h₁
  rw [h₁, (dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS p' sq' hW' hX hY
    hg x' d).mpr h₂]

/-- **Independence of the field spectrum and of the lifted point, at the level of algebraic
spaces.** Two base changes of one locally-of-finite-type morphism `g` of algebraic spaces,
along morphisms out of the field spectra of two field-valued points, have the same dimension
at any two points with the same image under `g`. -/
theorem dimensionAtPoint_eq_of_isPullback_of_isPullback
    (p p' : FieldValuedPoint B S hS 𝒜) {W W' X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ yoneda.obj p.base} {b : W ⟶ X} {c : yoneda.obj p.base ⟶ Y}
    {a' : W' ⟶ yoneda.obj p'.base} {b' : W' ⟶ X} {c' : yoneda.obj p'.base ⟶ Y} {g : X ⟶ Y}
    (sq : IsPullback a b c g) (sq' : IsPullback a' b' c' g)
    (hW : IsAlgebraicSpace B S hS W) (hW' : IsAlgebraicSpace B S hS W')
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hg : Space.IsLocallyOfFiniteType B S hS g)
    (x : Space.points B S hS W) (x' : Space.points B S hS W')
    (hx : Space.pointsMap B S hS W b x = Space.pointsMap B S hS W' b' x') :
    Space.dimensionAtPoint B S hS W hW x = Space.dimensionAtPoint B S hS W' hW' x' :=
  dimensionAtPoint_eq_of_isPullback_of_isPullback_fieldValuedPoints B S hS p p' sq sq' hW hW' hX
    hY hg x x' hx

/-- The dimension at a point of a base change of `g` over a field spectrum is the dimension of
the source of `g` at the image point, for `g` with target the field spectrum of a field-valued
point. -/
private theorem dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra_aux
    {ℬ : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (π : FieldValuedPoint B S hS 𝒜) (p : FieldValuedPoint B S hS ℬ)
    {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : E ⟶ yoneda.obj π.base} {b : E ⟶ F}
    {c : yoneda.obj π.base ⟶ yoneda.obj p.base} {g : F ⟶ yoneda.obj p.base}
    (sq : IsPullback a b c g) (hE : IsAlgebraicSpace B S hS E)
    (hF : IsAlgebraicSpace B S hS F) (hg : Space.IsLocallyOfFiniteType B S hS g)
    (x : Space.points B S hS E) :
    Space.dimensionAtPoint B S hS E hE x =
      Space.dimensionAtPoint B S hS F hF (Space.pointsMap B S hS E b x) :=
  dimensionAtPoint_eq_of_isPullback_of_isPullback_fieldValuedPoints B S hS π p sq
    IsPullback.of_id_snd hE hF hF (isAlgebraicSpace_yoneda B S hS p.base) hg x _ (by simp)

end FieldBase

section FieldFibreRepresented

variable {𝒯 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- `AlgebraicGeometry.Stack.fieldFibreDimensionAt` is computed by every algebraic space
representing the fibre `𝒯 ×_𝒳 Spec k`: its value at the point of the fibre corresponding to a
point `x` of such a space is the dimension of that space at `x`. -/
theorem fieldFibreDimensionAt_eq_dimensionAtPoint (f : 𝒯 ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯) (p : FieldValuedPoint B S hS 𝒳.val)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver (fieldFibreSquare B S hS f p).pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (x : Space.points B S hS F) :
    fieldFibreDimensionAt.{u, w} B S hS f h𝒳 h𝒯 p
        (spacePointMap B S hS F (fieldFibreSquare B S hS f p).pt
          (representingEquivalence B S hS F (fieldFibreSquare B S hS f p).pt e).functor x) =
      Space.dimensionAtPoint B S hS F hF x :=
  representedDimensionAtPoint_eq B S hS (fieldFibreSquare B S hS f p).pt
    (isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f h𝒳 h𝒯 p) F hF e x

end FieldFibreRepresented

/-! ### Refinement of a field-valued point along an arrow of its object -/

section Refinement

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The arrow of the site underlying an arrow between the objects of two field-valued points of
`𝒳`: the image of that arrow under the structure functor, read on the recorded bases. -/
def refinementBaseMap {p q : FieldValuedPoint B S hS 𝒳.val} (g : p.obj ⟶ q.obj) :
    p.base ⟶ q.base :=
  eqToHom p.«over».symm ≫ 𝒳.val.p.map g ≫ eqToHom q.«over»

/-- **The 2-Yoneda lift of a field-valued point factors through a refinement.** An arrow
`g : p.obj ⟶ q.obj` between the objects of two field-valued points of `𝒳` is a lift of
`AlgebraicGeometry.Stack.refinementBaseMap g`, hence strongly cartesian; comparing the chosen
lift of `p.obj` at the unit object of the slice of `p.base` with the chosen lift of `q.obj` at
the image of that unit object identifies the two based functors over `p.base`, the comparison
being invertible because the fibres are groupoids. -/
noncomputable def refinementLiftIso {p q : FieldValuedPoint B S hS 𝒳.val}
    (g : p.obj ⟶ q.obj) :
    Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property p.base
        (Functor.Fiber.mk (a := p.obj) p.«over») ≅
      BasedFunctor.comp (BasedFunctor.overMap (refinementBaseMap B S hS g))
        (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property q.base
          (Functor.Fiber.mk (a := q.obj) q.«over»)) := by
  let r := refinementBaseMap B S hS (𝒳 := 𝒳) g
  let F := Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property p.base
    (Functor.Fiber.mk (a := p.obj) p.«over»)
  let G := BasedFunctor.comp (BasedFunctor.overMap r)
    (Functor.TwoYoneda.liftBased 𝒳.val.p 𝒳.property q.base
      (Functor.Fiber.mk (a := q.obj) q.«over»))
  let z : Over p.base := Over.mk (𝟙 p.base)
  let lp := Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.property p.base
    (Functor.Fiber.mk (a := p.obj) p.«over») z
  let z' := (Over.map r).obj z
  let lq := Functor.TwoYoneda.chosenLift 𝒳.val.p 𝒳.property q.base
    (Functor.Fiber.mk (a := q.obj) q.«over») z'
  have hz' : z'.hom = r := by simp [z, z']
  let _ : 𝒳.val.p.IsStronglyCartesian r lq.φ := hz' ▸ lq.isStronglyCartesian
  have hg : 𝒳.val.p.IsHomLift r g :=
    IsHomLift.of_fac 𝒳.val.p r g p.«over» q.«over» rfl
  let _ : Functor.IsHomLift 𝒳.val.p r g := hg
  have hlp : 𝒳.val.p.IsHomLift (𝟙 p.base) lp.φ := by
    simpa [z, Functor.TwoYoneda.Lift.isStronglyCartesian] using lp.isStronglyCartesian.toIsHomLift
  have hcomp : 𝒳.val.p.IsHomLift (𝟙 p.base ≫ r) (lp.φ ≫ g) :=
    @CategoryTheory.IsHomLift.comp _ _ _ _ 𝒳.val.p p.base p.base q.base lp.y p.obj q.obj
      (𝟙 p.base) r lp.φ g hlp hg
  let _ : Functor.IsHomLift 𝒳.val.p (𝟙 p.base ≫ r) (lp.φ ≫ g) := hcomp
  let θ : lp.y ⟶ lq.y :=
    @Functor.IsStronglyCartesian.map _ _ _ _ 𝒳.val.p p.base q.base lq.y q.obj r lq.φ
      (hz' ▸ lq.isStronglyCartesian) p.base lp.y (𝟙 p.base) (𝟙 p.base ≫ r) rfl (lp.φ ≫ g) hcomp
  have hθ : 𝒳.val.p.IsHomLift (𝟙 p.base) θ :=
    @Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ 𝒳.val.p p.base q.base lq.y q.obj r lq.φ
      (hz' ▸ lq.isStronglyCartesian) p.base lp.y (𝟙 p.base) (𝟙 p.base ≫ r) rfl (lp.φ ≫ g) hcomp
  let _ : Functor.IsHomLift 𝒳.val.p (𝟙 p.base) θ := hθ
  let ev := Functor.twoYonedaEvaluation 𝒳.val.p p.base
  let θF : ev.obj F ⟶ ev.obj G := Functor.Fiber.homMk 𝒳.val.p p.base θ
  have : ev.Full := Functor.twoYonedaEvaluation_full 𝒳.val.p 𝒳.property p.base
  let η := ev.preimage θF
  have : IsGroupoid (BasedCategory.slice p.base ⥤ᵇ BasedCategory.ofFunctor 𝒳.val.p) :=
    CategoryTheory.isGroupoid_basedFunctor_slice 𝒳.val.p 𝒳.property p.base
  exact asIso η

/-- **A refinement of a field-valued point induces a morphism of the 1-morphisms it determines.**
An arrow `g : p.obj ⟶ q.obj` between the objects of two field-valued points of `𝒳` exhibits the
1-morphism `Spec κ(p) ⟶ 𝒳` of `p` as the composite of the morphism of field spectra underlying
`g` with the 1-morphism `Spec κ(q) ⟶ 𝒳` of `q`. -/
noncomputable def refinementMorphismIso {p q : FieldValuedPoint B S hS 𝒳.val}
    (g : p.obj ⟶ q.obj) :
    fieldValuedPointMorphism B S hS 𝒳 p ≅
      schemeMorphism B (refinementBaseMap B S hS g) ≫ fieldValuedPointMorphism B S hS 𝒳 q :=
  Bicategory.InducedBicategory.isoMk (refinementLiftIso B S hS g)

end Refinement

/-! ### The fibre over a refinement as a base change of the fibre -/

section RefinedFibre

variable {𝒯 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The canonical 2-fibre product square exhibiting the base change of the fibre of `f` over a
field-valued point `p` along the morphism of field spectra underlying a refinement. -/
noncomputable abbrev refinementBaseChangeSquare (f : 𝒯 ⟶ 𝒳)
    {π p : FieldValuedPoint B S hS 𝒳.val} (g : π.obj ⟶ p.obj) :
    Bicategory.TwoCommSq (fieldFibreSquare B S hS f p).snd
      (schemeMorphism B (refinementBaseMap B S hS g)) :=
  CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (fieldFibreSquare B S hS f p).snd (schemeMorphism B (refinementBaseMap B S hS g))

/-- **The fibre of `f` over a refinement `π` of a field-valued point `p`, presented as the base
change along `Spec κ(π) ⟶ Spec κ(p)` of the fibre of `f` over `p`.** Its apex is the iterated
2-fibre product `(𝒯 ×_𝒳 Spec κ(p)) ×_{Spec κ(p)} Spec κ(π)`, and the square recorded here is the
one over the *outer* cospan, so that it is a 2-fibre product of `f` and the 1-morphism of `π`. -/
noncomputable def refinedFieldFibreSquare (f : 𝒯 ⟶ 𝒳)
    {π p : FieldValuedPoint B S hS 𝒳.val} (g : π.obj ⟶ p.obj) :
    Bicategory.TwoCommSq f (fieldValuedPointMorphism B S hS 𝒳 π) :=
  CatFiberedInGroupoids.cancelSndSquare.{u, u, u + 1, u + 1} f
    (fieldValuedPointMorphism B S hS 𝒳 p) (schemeMorphism B (refinementBaseMap B S hS g))
    (fieldValuedPointMorphism B S hS 𝒳 π) (refinementMorphismIso B S hS g).symm

/-- The apex of `AlgebraicGeometry.Stack.refinedFieldFibreSquare` is the apex of the canonical
2-fibre product square of the fibre over `p` and the morphism of field spectra underlying the
refinement: the fibre over the refinement *is* a base change of the fibre over `p`. -/
theorem refinedFieldFibreSquare_pt (f : 𝒯 ⟶ 𝒳)
    {π p : FieldValuedPoint B S hS 𝒳.val} (g : π.obj ⟶ p.obj) :
    (refinedFieldFibreSquare B S hS f g).pt =
      (refinementBaseChangeSquare B S hS f g).pt :=
  rfl

/-- **`AlgebraicGeometry.Stack.refinedFieldFibreSquare` is a 2-fibre product of `f` and the
1-morphism of the refinement**, by Stacks 02XD. -/
noncomputable def isTwoFibreProduct_refinedFieldFibreSquare (f : 𝒯 ⟶ 𝒳)
    {π p : FieldValuedPoint B S hS 𝒳.val} (g : π.obj ⟶ p.obj) :
    Bicategory.IsTwoFibreProduct (refinedFieldFibreSquare B S hS f g) :=
  CatFiberedInGroupoids.isTwoFibreProduct_cancelSndSquare.{u, u, u + 1, u + 1} f
    (fieldValuedPointMorphism B S hS 𝒳 p) (schemeMorphism B (refinementBaseMap B S hS g))
    (fieldValuedPointMorphism B S hS 𝒳 π) (refinementMorphismIso B S hS g).symm

/-- **Stacks 0300 at the fibre over a refinement.** -/
theorem isRepresentableByAlgebraicSpace_refinedFieldFibreSquare (f : 𝒯 ⟶ 𝒳)
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯)
    {π p : FieldValuedPoint B S hS 𝒳.val} (g : π.obj ⟶ p.obj) :
    IsRepresentableByAlgebraicSpace B S hS (refinedFieldFibreSquare B S hS f g).pt :=
  isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
    (schemeFibredCategory B S hS π.base) 𝒳 𝒯 (fieldValuedPointMorphism B S hS 𝒳 π) f
    (refinedFieldFibreSquare B S hS f g)
    (isTwoFibreProduct_refinedFieldFibreSquare B S hS f g)
    (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS h𝒳
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS π.base) _) h𝒯

end RefinedFibre

/-! ### The fibre over a field-valued point is locally of finite type over its field spectrum -/

section FibreFiniteType

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The second projection of the fibre over a field-valued point passes the smooth-diagram
test of Stacks 06FS.** The fibre square of `f` over `p`, read with its legs exchanged, is a
2-fibre product of the cospan whose first leg is the 1-morphism of `p`, so its projection to the
field spectrum is a base change of `f` and Stacks 06FU applies. -/
theorem hasPropertyOnEverySmoothDiagram_fieldFibreSquare_snd (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val) :
    HasPropertyOnEverySmoothDiagram B S hS
      (fun _ _ h => Space.IsLocallyOfFiniteType B S hS h)
      (fieldFibreSquare B S hS f.hom p).snd :=
  AlgebraicStacks.isLocallyOfFiniteType_baseChange.{u, w} B S hS f
    (fieldValuedPointStackMorphism B S hS 𝒳 p)
    (twoFibreProductSquareAlgebraicStacks B S hS f
      (fieldValuedPointStackMorphism B S hS 𝒳 p)).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f
        (fieldValuedPointStackMorphism B S hS 𝒳 p))) hf

/-- **The fibre `𝒯 ×_𝒳 Spec k ⟶ Spec k` is locally of finite type as a morphism of algebraic
spaces.** Both source and target of the second projection of the fibre square are represented by
algebraic spaces, so the equivalence of parts (1) and (2) of Stacks 06FM together with its
representable-source-and-target form turn the smooth-diagram test of
`AlgebraicGeometry.Stack.hasPropertyOnEverySmoothDiagram_fieldFibreSquare_snd` into local finite
type of the induced morphism of representing presheaves. Local finite type of morphisms of
algebraic spaces is smooth local on source and target by Stacks 06FC, which is what both
directions of Stacks 06FM require. -/
theorem isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd (f : 𝒯 ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      (fieldFibreSquare B S hS f.hom p).pt.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      (schemeFibredCategory B S hS p.base).val.p
      (presheafOfCategories (G ⋙ typeToCat)).p) :
    Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS (fieldFibreSquare B S hS f.hom p).pt
        (schemeFibredCategory B S hS p.base) F G eF eG
        (fieldFibreSquare B S hS f.hom p).snd) :=
  (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (isAlgebraicStack_twoFibreProductSquare B S hS f
      (fieldValuedPointStackMorphism B S hS 𝒳 p))
    (schemeStack.{u, w} B S hS p.base).property F G hF hG eF eG
    (fieldFibreSquare B S hS f.hom p).snd).mp
      ((hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
        (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
        (isAlgebraicStack_twoFibreProductSquare B S hS f
          (fieldValuedPointStackMorphism B S hS 𝒳 p))
        (schemeStack.{u, w} B S hS p.base).property
        (fieldFibreSquare B S hS f.hom p).snd).1
          (hasPropertyOnEverySmoothDiagram_fieldFibreSquare_snd.{u, w} B S hS f hf p))

end FibreFiniteType

/-! ### Independence of the chosen field-valued point under refinement -/

section RefinementInvariance

/-- **The dimension of a base change along a morphism of field spectra agrees with the dimension
upstairs.** For a locally-of-finite-type morphism `g` of algebraic spaces whose target is the
field spectrum of a field-valued point, the dimension at a point of a base change of `g` along a
morphism out of another field spectrum is the dimension of the source of `g` at the image point. -/
theorem dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra
    {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (π p : FieldValuedPoint B S hS 𝒜)
    {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : E ⟶ yoneda.obj π.base} {b : E ⟶ F}
    {c : yoneda.obj π.base ⟶ yoneda.obj p.base} {g : F ⟶ yoneda.obj p.base}
    (sq : IsPullback a b c g) (hE : IsAlgebraicSpace B S hS E)
    (hF : IsAlgebraicSpace B S hS F) (hg : Space.IsLocallyOfFiniteType B S hS g)
    (x : Space.points B S hS E) :
    Space.dimensionAtPoint B S hS E hE x =
      Space.dimensionAtPoint B S hS F hF (Space.pointsMap B S hS E b x) :=
  dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra_aux B S hS π p sq hE hF hg x

/-- The square of morphisms of representing presheaves attached to a 2-fibre product square is a
pullback square. -/
private theorem isPullback_representingMap_of_isTwoFibreProduct_aux
    {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {P : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P)
    (F G H T C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒵.val.p
      (presheafOfCategories (H ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver P.pt.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (eC : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.val.p
      (presheafOfCategories (C ⋙ typeToCat)).p) :
    IsPullback (representingMap B S hS P.pt 𝒳 T F eT eF P.fst)
        (representingMap B S hS P.pt 𝒴 T G eT eG P.snd)
      (representingMap B S hS 𝒳 𝒵 F H eF eH f)
      (representingMap B S hS 𝒴 𝒵 G H eG eH g) := by
  have hfib : (twoFibreProductStructureFunctor B S hS 𝒳 𝒴 𝒵 f g).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.property.isFibered
  have hcan :=
    isPullback_representingMap_twoFibreProductSquare B S hS 𝒳 𝒴 𝒵 F G H eF eG eH f g C eC
  have A := Bicategory.twoFibreProductPreHom hP
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
  have D := Bicategory.twoFibreProductPreHom
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g) P
  refine hcan.of_iso
    (Iso.mk
      (representingMap B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt P.pt C T eC eT
        A.hom)
      (representingMap B S hS P.pt
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt T C eT eC
        D.hom) ?_ ?_)
    (Iso.refl F) (Iso.refl G) (Iso.refl H) ?_ ?_ (by simp) (by simp)
  · obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f g)
      (A.comp D) (Bicategory.TwoCommSq.PreHom.id _)
    have key : representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt C C eC eC
          (A.hom ≫ D.hom) =
        representingMap B S hS
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt C C eC eC
          (𝟙 _) :=
      representingMap_congr_twoIso B S hS C C eC eC θ
    rw [← representingMap_comp B S hS C T C eC eT eC, key, representingMap_id]
  · obtain ⟨θ, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hP (D.comp A)
      (Bicategory.TwoCommSq.PreHom.id P)
    have key : representingMap B S hS P.pt P.pt T T eT eT (D.hom ≫ A.hom) =
        representingMap B S hS P.pt P.pt T T eT eT (𝟙 _) :=
      representingMap_congr_twoIso B S hS T T eT eT θ
    rw [← representingMap_comp B S hS T C T eT eC eT, key, representingMap_id]
  · rw [Iso.refl_hom, Category.comp_id,
      representingMap_congr_twoIso B S hS C F eC eF A.isoFst,
      representingMap_comp B S hS C T F eC eT eF]
  · rw [Iso.refl_hom, Category.comp_id,
      representingMap_congr_twoIso B S hS C G eC eG A.isoSnd,
      representingMap_comp B S hS C T G eC eT eG]

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- The value of the formula of Stacks 0DRG is computed by every base change of the fibre to a
field spectrum. -/
private theorem representedDimensionAtPoint_eq_fieldFibreDimensionAt_aux
    (f : 𝒯 ⟶ 𝒳) (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (ρ : FieldValuedPoint B S hS 𝒜)
    {c : schemeFibredCategory B S hS ρ.base ⟶ schemeFibredCategory B S hS p.base}
    {P : Bicategory.TwoCommSq (fieldFibreSquare B S hS f.hom p).snd c}
    (hP : Bicategory.IsTwoFibreProduct P)
    (hPpt : IsRepresentableByAlgebraicSpace B S hS P.pt)
    (y : points B S hS P.pt.val P.pt.property)
    (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (hy : pointsMap B S hS P.pt.val P.pt.property
        (fieldFibreSquare B S hS f.hom p).pt.property P.fst.hom y = q) :
    representedDimensionAtPoint B S hS P.pt hPpt y =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q := by
  classical
  obtain ⟨F, hF, ⟨eF⟩⟩ :=
    isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f.hom 𝒳.property h𝒯 p
  obtain ⟨E, hE, ⟨eE⟩⟩ := id hPpt
  obtain ⟨C, -, ⟨eC⟩⟩ :
      IsRepresentableByAlgebraicSpace B S hS
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (fieldFibreSquare B S hS f.hom p).snd c).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (schemeFibredCategory B S hS ρ.base) (schemeFibredCategory B S hS p.base)
      (fieldFibreSquare B S hS f.hom p).pt c (fieldFibreSquare B S hS f.hom p).snd
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldFibreSquare B S hS f.hom p).snd c)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldFibreSquare B S hS f.hom p).snd c)
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
        (isAlgebraicStack_schemeFibredCategory.{u, w} B S hS p.base)
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS ρ.base) c)
      (isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f.hom 𝒳.property h𝒯 p)
  obtain ⟨x, hx⟩ :=
    (bijective_spacePointMap_representing B S hS F
      (fieldFibreSquare B S hS f.hom p).pt eF).surjective q
  obtain ⟨z, hz⟩ := (bijective_spacePointMap_representing B S hS E P.pt eE).surjective y
  have hsq := (isPullback_representingMap_of_isTwoFibreProduct_aux B S hS hP F (yoneda.obj ρ.base)
    (yoneda.obj p.base) E C eF (PresheafOfCategories.sliceElementsEquivalenceOver ρ.base)
    (PresheafOfCategories.sliceElementsEquivalenceOver p.base) eE eC).flip
  have hbx : Space.pointsMap B S hS E
      (representingMap B S hS P.pt (fieldFibreSquare B S hS f.hom p).pt E F eE eF P.fst) z =
      x := by
    refine (bijective_spacePointMap_representing B S hS F
      (fieldFibreSquare B S hS f.hom p).pt eF).injective ?_
    rw [spacePointMap_representing_naturality B S hS E F P.pt
      (fieldFibreSquare B S hS f.hom p).pt eE eF P.fst z, hz, hy, hx]
  have h₁ : representedDimensionAtPoint B S hS P.pt hPpt y =
      Space.dimensionAtPoint B S hS E hE z := by
    rw [← hz]
    exact representedDimensionAtPoint_eq B S hS _ _ E hE eE z
  have h₂ : fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q =
      Space.dimensionAtPoint B S hS F hF x := by
    rw [← hx]
    exact fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} B S hS f.hom 𝒳.property h𝒯 p F hF eF x
  rw [h₁, h₂, dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra_aux B S hS ρ p hsq
    hE hF
    (isLocallyOfFiniteType_representingMap_fieldFibreSquare_snd.{u, w} B S hS f hf p F
      (yoneda.obj p.base) hF (isAlgebraicSpace_yoneda B S hS p.base) eF
      (PresheafOfCategories.sliceElementsEquivalenceOver p.base)) z, hbx]

/-- **The value of the formula of Stacks 0DRG is unchanged by refining the field-valued point.**
Let `g : π.obj ⟶ p.obj` be an arrow between the objects of two field-valued points of `𝒳`, so that
`π` refines `p`. The fibre over `π` is the base change of the fibre over `p` along the induced
morphism of field spectra (`AlgebraicGeometry.Stack.refinedFieldFibreSquare`), and the dimension of
the former at a point `y` is the value of `AlgebraicGeometry.Stack.fieldFibreDimensionAt` at `p`
and the image of `y`. -/
theorem representedDimensionAtPoint_refinedFieldFibreSquare (f : 𝒯 ⟶ 𝒳)
    (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    {π p : FieldValuedPoint B S hS 𝒳.val.val} (g : π.obj ⟶ p.obj)
    (y : points B S hS (refinementBaseChangeSquare B S hS f.hom g).pt.val
      (refinementBaseChangeSquare B S hS f.hom g).pt.property)
    (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (hy : pointsMap B S hS (refinementBaseChangeSquare B S hS f.hom g).pt.val
        (refinementBaseChangeSquare B S hS f.hom g).pt.property
        (fieldFibreSquare B S hS f.hom p).pt.property
        (refinementBaseChangeSquare B S hS f.hom g).fst.hom y = q) :
    representedDimensionAtPoint B S hS (refinementBaseChangeSquare B S hS f.hom g).pt
        (isRepresentableByAlgebraicSpace_refinedFieldFibreSquare.{u, w} B S hS f.hom
          𝒳.property h𝒯 g) y =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q :=
  representedDimensionAtPoint_eq_fieldFibreDimensionAt_aux.{u, w} B S hS f h𝒯 hf p π
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (fieldFibreSquare B S hS f.hom p).snd (schemeMorphism B (refinementBaseMap B S hS g)))
    (isRepresentableByAlgebraicSpace_refinedFieldFibreSquare.{u, w} B S hS f.hom 𝒳.property h𝒯 g)
    y q hy

end RefinementInvariance

/-! ### Stacks 04SD at a recognised 2-fibre product -/

section RecognisedTwoFibreProduct

variable {𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- **Stacks 04SD at a 2-fibre product square recognised rather than constructed.** For *any*
2-commutative square which is a 2-fibre product of a cospan of categories fibred in groupoids,
all five categories in sight represented by presheaves, the square of morphisms of representing
presheaves of Stacks 04SW is a pullback square. -/
theorem isPullback_representingMap_of_isTwoFibreProduct
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {P : Bicategory.TwoCommSq f g}
    (hP : Bicategory.IsTwoFibreProduct P)
    (F G H T C : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver 𝒵.val.p
      (presheafOfCategories (H ⋙ typeToCat)).p)
    (eT : StacksRepresentableCFG.EquivalenceOver P.pt.val.p
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (eC : StacksRepresentableCFG.EquivalenceOver
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f g).pt.val.p
      (presheafOfCategories (C ⋙ typeToCat)).p) :
    IsPullback (representingMap B S hS P.pt 𝒳 T F eT eF P.fst)
        (representingMap B S hS P.pt 𝒴 T G eT eG P.snd)
      (representingMap B S hS 𝒳 𝒵 F H eF eH f)
      (representingMap B S hS 𝒴 𝒵 G H eG eH g) :=
  isPullback_representingMap_of_isTwoFibreProduct_aux B S hS hP F G H T C eF eG eH eT eC

end RecognisedTwoFibreProduct

/-! ### The field base of a base change, for points of two different based categories -/

section FieldBaseTwoCategories

/-- **The dimension at a point of a base change over the field spectrum of a field-valued point
is the relative dimension of the morphism base-changed**, for field-valued points of two
*different* based categories. -/
theorem dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra'
    {𝒜 ℬ : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (π : FieldValuedPoint B S hS 𝒜) (p : FieldValuedPoint B S hS ℬ)
    {E F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : E ⟶ yoneda.obj π.base} {b : E ⟶ F}
    {c : yoneda.obj π.base ⟶ yoneda.obj p.base} {g : F ⟶ yoneda.obj p.base}
    (sq : IsPullback a b c g) (hE : IsAlgebraicSpace B S hS E)
    (hF : IsAlgebraicSpace B S hS F) (hg : Space.IsLocallyOfFiniteType B S hS g)
    (x : Space.points B S hS E) :
    Space.dimensionAtPoint B S hS E hE x =
      Space.dimensionAtPoint B S hS F hF (Space.pointsMap B S hS E b x) :=
  dimensionAtPoint_eq_dimensionAtPoint_of_isPullback_fieldSpectra_aux B S hS π p sq hE hF hg x

end FieldBaseTwoCategories

/-! ### Independence of both choices of Stacks 0DRG -/

section ChoiceInvariance

variable {𝒯 𝒳 : AlgebraicStacks.{u, w} B S hS}

/-- **The value of the formula of Stacks 0DRG is computed by every base change of the fibre to a
field spectrum.** Let `P` be a 2-fibre product of the second projection `𝒯 ×_𝒳 Spec k ⟶ Spec k` of
the fibre over a field-valued point `p` of `𝒳` and a 1-morphism `Spec Ω ⟶ Spec k` of field spectra,
`Spec Ω` being the field spectrum of a field-valued point `ρ` of an arbitrary based category. Then
the dimension of `P` at a point `y` is the value of `AlgebraicGeometry.Stack.fieldFibreDimensionAt`
at `p` and the image of `y` in `|𝒯 ×_𝒳 Spec k|`. -/
theorem representedDimensionAtPoint_eq_fieldFibreDimensionAt
    (f : 𝒯 ⟶ 𝒳) (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    {𝒜 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)} (ρ : FieldValuedPoint B S hS 𝒜)
    {c : schemeFibredCategory B S hS ρ.base ⟶ schemeFibredCategory B S hS p.base}
    {P : Bicategory.TwoCommSq (fieldFibreSquare B S hS f.hom p).snd c}
    (hP : Bicategory.IsTwoFibreProduct P)
    (hPpt : IsRepresentableByAlgebraicSpace B S hS P.pt)
    (y : points B S hS P.pt.val P.pt.property)
    (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (hy : pointsMap B S hS P.pt.val P.pt.property
        (fieldFibreSquare B S hS f.hom p).pt.property P.fst.hom y = q) :
    representedDimensionAtPoint B S hS P.pt hPpt y =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q :=
  representedDimensionAtPoint_eq_fieldFibreDimensionAt_aux.{u, w} B S hS f h𝒯 hf p ρ hP hPpt y q hy

/-- **The value of the formula of Stacks 0DRG depends on neither of the two choices.** Two
field-valued points `p`, `p'` of `𝒳` and two points `q`, `q'` of the respective fibres
`𝒯 ×_𝒳 Spec κ(p)` and `𝒯 ×_𝒳 Spec κ(p')` whose images in `|𝒯|` agree give the same value. -/
theorem fieldFibreDimensionAt_eq_fieldFibreDimensionAt_of_pointsMap_eq
    (f : 𝒯 ⟶ 𝒳) (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p p' : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (q' : points B S hS (fieldFibreSquare B S hS f.hom p').pt.val
      (fieldFibreSquare B S hS f.hom p').pt.property)
    (h : pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
          (fieldFibreSquare B S hS f.hom p).pt.property 𝒯.val.property
          (fieldFibreSquare B S hS f.hom p).fst.hom q =
        pointsMap B S hS (fieldFibreSquare B S hS f.hom p').pt.val
          (fieldFibreSquare B S hS f.hom p').pt.property 𝒯.val.property
          (fieldFibreSquare B S hS f.hom p').fst.hom q') :
    fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p' q' := by
  classical
  obtain ⟨r, hr₁, hr₂⟩ :=
    exists_point_of_isTwoFibreProduct B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldFibreSquare B S hS f.hom p).fst (fieldFibreSquare B S hS f.hom p').fst)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldFibreSquare B S hS f.hom p).fst (fieldFibreSquare B S hS f.hom p').fst) q q' h
  obtain ⟨ρ, hρ⟩ : ∃ ρ : FieldValuedPoint B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldValuedPointMorphism B S hS 𝒳.val p')
        (fieldValuedPointMorphism B S hS 𝒳.val p)).pt.val,
      pointClass B S hS _ _ ρ =
        pointsMap B S hS _ _
          (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (fieldValuedPointMorphism B S hS 𝒳.val p')
            (fieldValuedPointMorphism B S hS 𝒳.val p)).pt.property
          (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} f.hom
            (fieldValuedPointMorphism B S hS 𝒳.val p)
            (fieldValuedPointMorphism B S hS 𝒳.val p')).hom r :=
    ⟨Quotient.out _, Quotient.out_eq _⟩
  obtain ⟨s, hs, -⟩ :=
    exists_point_of_isTwoFibreProduct B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} f.hom
          (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
        (fieldValuedPointMorphism B S hS _ ρ))
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _) r
      (pointClass B S hS _ _ (baseFieldValuedPoint B S hS ρ))
      (by rw [pointsMap_baseFieldValuedPoint, hρ])
  have hW := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f.hom 𝒳.property h𝒯 p
  have hW' := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS f.hom 𝒳.property h𝒯 p'
  have hR : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldValuedPointMorphism B S hS 𝒳.val p')
        (fieldValuedPointMorphism B S hS 𝒳.val p)).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (schemeFibredCategory B S hS p.base) 𝒳.val (schemeFibredCategory B S hS p'.base)
      (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p')
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒳.property
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p.base) _)
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS p'.base)
  have hV : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldFibreSquare B S hS f.hom p).fst (fieldFibreSquare B S hS f.hom p').fst).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (fieldFibreSquare B S hS f.hom p').pt 𝒯.val (fieldFibreSquare B S hS f.hom p).pt
      (fieldFibreSquare B S hS f.hom p').fst (fieldFibreSquare B S hS f.hom p).fst
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒯.property hW' _) hW
  have hE : IsRepresentableByAlgebraicSpace B S hS
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} f.hom
          (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
        (fieldValuedPointMorphism B S hS _ ρ)).pt :=
    isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u + 1} B S hS
      (schemeFibredCategory B S hS ρ.base)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldValuedPointMorphism B S hS 𝒳.val p')
        (fieldValuedPointMorphism B S hS 𝒳.val p)).pt
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (fieldFibreSquare B S hS f.hom p).fst (fieldFibreSquare B S hS f.hom p').fst).pt
      (fieldValuedPointMorphism B S hS _ ρ)
      (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} f.hom
        (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
        (isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS _ hR)
        (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS ρ.base) _) hV
  have hy₁ : pointsMap B S hS _ _ (fieldFibreSquare B S hS f.hom p).pt.property
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} f.hom
              (fieldValuedPointMorphism B S hS 𝒳.val p)
              (fieldValuedPointMorphism B S hS 𝒳.val p'))
            (fieldValuedPointMorphism B S hS _ ρ)).fst.hom.comp
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (fieldFibreSquare B S hS f.hom p).fst
          (fieldFibreSquare B S hS f.hom p').fst).fst.hom) s = q := by
    rw [← pointsMap_comp, hs]
    exact hr₁
  have hy₂ : pointsMap B S hS _ _ (fieldFibreSquare B S hS f.hom p').pt.property
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
            (CatFiberedInGroupoids.triplePairingMor.{u, u, u + 1, u + 1} f.hom
              (fieldValuedPointMorphism B S hS 𝒳.val p)
              (fieldValuedPointMorphism B S hS 𝒳.val p'))
            (fieldValuedPointMorphism B S hS _ ρ)).fst.hom.comp
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          (fieldFibreSquare B S hS f.hom p).fst
          (fieldFibreSquare B S hS f.hom p').fst).snd.hom) s = q' := by
    rw [← pointsMap_comp, hs]
    exact hr₂
  have key₁ := representedDimensionAtPoint_eq_fieldFibreDimensionAt
    B S hS f h𝒯 hf p ρ
    (Bicategory.isTwoFibreProduct_pasteSnd
      (CatFiberedInGroupoids.tripleProductSquare.{u, u, u + 1, u + 1} f.hom
        (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
      (CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSquare.{u, u, u + 1, u + 1} f.hom
        (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _
        (fieldValuedPointMorphism B S hS _ ρ))
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _))
    hE s q hy₁
  have key₂ := representedDimensionAtPoint_eq_fieldFibreDimensionAt
    B S hS f h𝒯 hf p' ρ
    (Bicategory.isTwoFibreProduct_pasteSnd
      (CatFiberedInGroupoids.tripleProductSndSquare.{u, u, u + 1, u + 1} f.hom
        (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
      (CatFiberedInGroupoids.isTwoFibreProduct_tripleProductSndSquare.{u, u, u + 1, u + 1} f.hom
        (fieldValuedPointMorphism B S hS 𝒳.val p) (fieldValuedPointMorphism B S hS 𝒳.val p'))
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} _
        (fieldValuedPointMorphism B S hS _ ρ))
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _))
    hE s q' hy₂
  exact key₁.symm.trans key₂

/-- **Independence of the chosen lift.** For a fixed field-valued point `p` of `𝒳`, the value of
the formula of Stacks 0DRG does not depend on which point of `𝒯 ×_𝒳 Spec κ(p)` above `t` is
chosen. This is the case `p' = p` of
`AlgebraicGeometry.Stack.fieldFibreDimensionAt_eq_fieldFibreDimensionAt_of_pointsMap_eq`. -/
theorem fieldFibreDimensionAt_eq_of_pointsMap_eq
    (f : 𝒯 ⟶ 𝒳) (h𝒯 : IsRepresentableByAlgebraicSpace B S hS 𝒯.val)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q q' : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (h : pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
          (fieldFibreSquare B S hS f.hom p).pt.property 𝒯.val.property
          (fieldFibreSquare B S hS f.hom p).fst.hom q =
        pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
          (fieldFibreSquare B S hS f.hom p).pt.property 𝒯.val.property
          (fieldFibreSquare B S hS f.hom p).fst.hom q') :
    fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property h𝒯 p q' :=
  fieldFibreDimensionAt_eq_fieldFibreDimensionAt_of_pointsMap_eq.{u, w} B S hS f h𝒯 hf p p q q' h

end ChoiceInvariance

/-! ### Stacks 0DRH (1): the relative dimension is well defined -/

section WellDefined

variable (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)

/-- **The relative dimension `relativeDimensionAt` is well defined.** The value of the
formula of Stacks 0DRG at *every* field-valued point `p` representing the image of `t` and every
point `q` of the fibre `T ×_𝒳 Spec κ(p)` above `t` is `relativeDimensionAt`, the value at the two
choices the definition makes. So any two admissible pairs of choices give the same value, which
is what makes `relativeDimensionAt` an invariant of `(f, t)`. -/
@[stacks 0DRH "relative_dimension_well_defined"]
theorem relativeDimensionAt_eq_fieldFibreDimensionAt
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f) (t : Space.points B S hS T)
    (p : FieldValuedPoint B S hS 𝒳.val.val)
    (q : points B S hS (fieldFibreSquare B S hS f.hom p).pt.val
      (fieldFibreSquare B S hS f.hom p).pt.property)
    (_hp : pointClass B S hS 𝒳.val.val 𝒳.val.property p =
      pointsMap B S hS (fibredCategory B S hS T).val
        (fibredCategory B S hS T).property 𝒳.val.property f.hom.hom
        (stackPointOfSpacePoint B S hS T t))
    (hq : pointsMap B S hS (fieldFibreSquare B S hS f.hom p).pt.val
        (fieldFibreSquare B S hS f.hom p).pt.property
        (fibredCategory B S hS T).property
        (fieldFibreSquare B S hS f.hom p).fst.hom q =
      stackPointOfSpacePoint B S hS T t) :
    relativeDimensionAt B S hS T hT 𝒳 f hf t =
      fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property
        (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p q := by
  obtain ⟨p₀, q₀, -, hq₀, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 f hf t
  rw [hval]
  exact fieldFibreDimensionAt_eq_fieldFibreDimensionAt_of_pointsMap_eq.{u, w} B S hS f
    (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) hf p₀ p q₀ q
    (by rw [hq₀, hq])

end WellDefined

/-! ### Stacks 0DRH (2): agreement with the relative dimension of a morphism of spaces -/

section AgreesWithSpaces

/-- **The 1-morphism of algebraic stacks attached to a morphism of algebraic spaces over `S`**:
the associated 1-morphism of categories of elements of Stacks 0458, read between the algebraic
stacks of Stacks 03YS that the two algebraic spaces determine. -/
noncomputable abbrev algebraicSpaceStackMap {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G) :
    algebraicSpaceStack.{u, w} B S hS T hT ⟶ algebraicSpaceStack.{u, w} B S hS G hG :=
  Bicategory.InducedBicategory.mkHom (associatedMap B S hS g).1

/-- **A morphism of algebraic spaces over `S` is locally of finite type exactly when the
1-morphism of algebraic stacks it induces is.** The smooth-diagram test of Stacks 06FS is read
on the representable source and target by Stacks 06FM, through the identity comparisons of
Stacks 04SW; what Stacks 06FM asks of the property is that it be smooth local on source and
target, which for local finite type is Stacks 06FC. -/
theorem isLocallyOfFiniteType_algebraicSpaceStackMap_iff
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g) ↔
      Space.IsLocallyOfFiniteType B S hS g := by
  refine Iff.trans (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS T hT)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS G hG) _) ?_
  refine Iff.trans (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS T hT)
    (isAlgebraicStack_fibredCategory.{u, w} B S hS G hG) T G hT hG
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) _) ?_
  rw [representingMap_associatedMap B S hS T G g]

/-- **Stacks 0DRH (2) for a target merely represented by an algebraic space.** If the algebraic
stack `𝒳` is represented by an algebraic space `G`, then the relative dimension of Stacks 0DRG
of `f : T ⟶ 𝒳` at `t ∈ |T|` is `d` exactly when the morphism `T ⟶ G` of algebraic spaces that
`f` induces has relative dimension `d` at `t` in the sense of Stacks 04NM. -/
theorem relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS f)
    (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hG : IsAlgebraicSpace B S hS G)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (t : Space.points B S hS T) (d : ℕ∞) :
    relativeDimensionAt.{u, w} B S hS T hT 𝒳 f hf t = (d : WithBot ℕ∞) ↔
      Space.HasRelativeDimensionAt d B S hS
        (representingMap B S hS (fibredCategory B S hS T) 𝒳.val T G
          (StacksRepresentableCFG.EquivalenceOver.refl _) eG f.hom) t := by
  classical
  have hg : Space.IsLocallyOfFiniteType B S hS
      (representingMap B S hS (fibredCategory B S hS T) 𝒳.val T G
        (StacksRepresentableCFG.EquivalenceOver.refl _) eG f.hom) :=
    (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (isAlgebraicStack_fibredCategory.{u, w} B S hS T hT) 𝒳.property T G hT hG
      (StacksRepresentableCFG.EquivalenceOver.refl _) eG f.hom).mp
      (hasPropertyOnSomeSmoothDiagram_of_hasPropertyOnEverySmoothDiagram.{u, w} B S hS _
        (isAlgebraicStack_fibredCategory.{u, w} B S hS T hT) 𝒳.property f.hom hf)
  obtain ⟨p, q, -, hq, hval⟩ := exists_eq_fieldFibreDimensionAt B S hS T hT 𝒳 f hf t
  rw [hval]
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_fieldFibreSquare.{u, w} B S hS
    f.hom 𝒳.property (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p
  obtain ⟨x, hx⟩ := (bijective_spacePointMap_representing B S hS W
    (fieldFibreSquare B S hS f.hom p).pt eW).surjective q
  have hsq := (isPullback_representingMap_of_isTwoFibreProduct B S hS
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      f.hom (fieldValuedPointMorphism B S hS 𝒳.val p))
    T (yoneda.obj p.base) G W W
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver p.base) eG eW eW).flip
  have hpt : Space.pointsMap B S hS W
      (representingMap B S hS (fieldFibreSquare B S hS f.hom p).pt
        (fibredCategory B S hS T) W T eW (StacksRepresentableCFG.EquivalenceOver.refl _)
        (fieldFibreSquare B S hS f.hom p).fst) x = t := by
    refine (bijective_spacePointMap_representing B S hS T (fibredCategory B S hS T)
      (StacksRepresentableCFG.EquivalenceOver.refl _)).injective ?_
    rw [spacePointMap_representing_naturality B S hS W T
      (fieldFibreSquare B S hS f.hom p).pt (fibredCategory B S hS T) eW
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (fieldFibreSquare B S hS f.hom p).fst x, hx, hq]
    rfl
  have hdim : fieldFibreDimensionAt.{u, w} B S hS f.hom 𝒳.property
      (isRepresentableByAlgebraicSpace_fibredCategory B S hS T hT) p q =
      Space.dimensionAtPoint B S hS W hW x := by
    rw [← hx]
    exact fieldFibreDimensionAt_eq_dimensionAtPoint.{u, w} B S hS _ _ _ p W hW eW x
  rw [hdim, dimensionAtPoint_eq_iff_hasRelativeDimensionAt_of_isPullback B S hS p hsq hW hT hG
    hg x d, hpt]

/-- **The relative dimension of Stacks 0DRG agrees with the relative dimension of a morphism of
algebraic spaces.** For a morphism `g : T ⟶ G` of algebraic spaces over `S`, the relative
dimension of Stacks 0DRG of the induced 1-morphism of algebraic stacks is, at every point
`t ∈ |T|`, the relative dimension `d` of `g` at `t` in the sense of Stacks 04NM. -/
@[stacks 0DRH "relative_dimension_agrees_with_spaces"]
theorem relativeDimensionAt_eq_iff_hasRelativeDimensionAt
    {T G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hT : IsAlgebraicSpace B S hS T) (hG : IsAlgebraicSpace B S hS G) (g : T ⟶ G)
    (hf : AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (algebraicSpaceStackMap.{u, w} B S hS hT hG g))
    (t : Space.points B S hS T) (d : ℕ∞) :
    relativeDimensionAt.{u, w} B S hS T hT (algebraicSpaceStack.{u, w} B S hS G hG)
        (algebraicSpaceStackMap.{u, w} B S hS hT hG g) hf t = (d : WithBot ℕ∞) ↔
      Space.HasRelativeDimensionAt d B S hS g t := by
  rw [relativeDimensionAt_eq_iff_hasRelativeDimensionAt_representingMap.{u, w} B S hS T hT
    (algebraicSpaceStack.{u, w} B S hS G hG) (algebraicSpaceStackMap.{u, w} B S hS hT hG g) hf
    G hG (StacksRepresentableCFG.EquivalenceOver.refl _) t d,
    representingMap_associatedMap B S hS T G g]

end AgreesWithSpaces

end AlgebraicGeometry.Stack

end
