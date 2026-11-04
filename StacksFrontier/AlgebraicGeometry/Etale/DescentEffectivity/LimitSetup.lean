module

public import StacksFrontier.AlgebraicGeometry.Limits.FibreProductLimit
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.PullbackSquare

/-!
# The double and triple fibre products of a morphism presented as a limit

A descent datum relative to `f : X ⟶ S` lives on three schemes: its underlying scheme sits over
`X`, its gluing isomorphism over `X ×_S X`, and its cocycle condition over `X ×_S X ×_S X`.
Let `f` be the limit of an inverse system of morphisms `f_i : X_i ⟶ S_i`. This file presents
`X ×_S X` and `X ×_S X ×_S X` as the limits of `X_i ×_{S_i} X_i` and of
`X_i ×_{S_i} X_i ×_{S_i} X_i`, applying `AlgebraicGeometry.FibreProductLimit.isLimit` once and
then again to its own output, and shows that every stage of both systems is affine when every
stage of the two given systems is.

## Main definitions

* `AlgebraicGeometry.LimitDatum.sqDiagram`, `sqCone`, `sqIsLimit`: the double fibre product
  `X ×_S X` as the limit of `i ↦ X_i ×_{S_i} X_i`.
* `AlgebraicGeometry.LimitDatum.triDiagram`, `triCone`, `triIsLimit`: the triple fibre product
  as the limit of `i ↦ X_i ×_{S_i} X_i ×_{S_i} X_i`.

## References

* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

namespace LimitDatum

variable {I : Type u} [Category.{u} I] {𝒳 𝒮 : I ⥤ Scheme.{u}} (φ : 𝒳 ⟶ 𝒮)
  {cX : Cone 𝒳} {cS : Cone 𝒮} (f : cX.pt ⟶ cS.pt)
  (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)

section Square

/-- **The diagram of double fibre products** `i ↦ X_i ×_{S_i} X_i`. -/
abbrev sqDiagram : I ⥤ Scheme.{u} := FibreProductLimit.diagram φ φ

include hf

/-- **The cone on the diagram of double fibre products with vertex `X ×_S X`.** -/
abbrev sqCone : Cone (sqDiagram φ) := FibreProductLimit.cone φ φ f f hf hf

/-- **The double fibre product of a limit of morphisms is the limit of the double fibre
products.** -/
def sqIsLimit (hX : IsLimit cX) (hS : IsLimit cS) : IsLimit (sqCone φ f hf) :=
  FibreProductLimit.isLimit φ φ f f hf hf hX hX hS

end Square

section Triple

/-- The structure morphism of the double fibre product over the base, through the first
projection.

Marked `implicit_reducible`: the triple fibre product is a `pullback` along this morphism, so a
goal mentioning a projection of that `pullback` is not type-correct at `implicit` transparency
unless this unfolds there. -/
@[simps, implicit_reducible]
def sqToBase : sqDiagram φ ⟶ 𝒮 where
  app i := pullback.fst (φ.app i) (φ.app i) ≫ φ.app i
  naturality i j e := by
    simp only [Category.assoc, FibreProductLimit.diagram_map_fst_assoc, φ.naturality e]

/-- **The diagram of triple fibre products** `i ↦ (X_i ×_{S_i} X_i) ×_{S_i} X_i`. -/
abbrev triDiagram : I ⥤ Scheme.{u} := FibreProductLimit.diagram (sqToBase φ) φ

include hf

/-- The structure morphism of `X ×_S X` over `S` through the first projection. -/
abbrev sqToBaseLimit : (sqCone φ f hf).pt ⟶ cS.pt := pullback.fst f f ≫ f

/-- The legs of the cone on the double fibre products are compatible with the two structure
morphisms over the base. -/
theorem sqCone_π_comp_sqToBase (i : I) :
    (sqCone φ f hf).π.app i ≫ (sqToBase φ).app i = sqToBaseLimit φ f hf ≫ cS.π.app i := by
  simp only [sqToBase_app, sqToBaseLimit, Category.assoc,
    FibreProductLimit.cone_π_app_fst_assoc, hf i]

/-- **The cone on the diagram of triple fibre products with vertex `X ×_S X ×_S X`.** -/
abbrev triCone : Cone (triDiagram φ) :=
  FibreProductLimit.cone (sqToBase φ) φ (sqToBaseLimit φ f hf) f (sqCone_π_comp_sqToBase φ f hf) hf

/-- **The triple fibre product of a limit of morphisms is the limit of the triple fibre
products.** -/
def triIsLimit (hX : IsLimit cX) (hS : IsLimit cS) : IsLimit (triCone φ f hf) :=
  FibreProductLimit.isLimit (sqToBase φ) φ (sqToBaseLimit φ f hf) f
    (sqCone_π_comp_sqToBase φ f hf) hf (sqIsLimit φ f hf hX hS) hX hS

end Triple

section Affine

variable [∀ i, IsAffine (𝒳.obj i)] [∀ i, IsAffine (𝒮.obj i)]

/-- Each double fibre product `X_i ×_{S_i} X_i` of affine schemes is affine. -/
instance isAffine_sqDiagram_obj (i : I) : IsAffine ((sqDiagram φ).obj i) :=
  FibreProductLimit.isAffine_diagram_obj φ φ i

/-- Each triple fibre product `X_i ×_{S_i} X_i ×_{S_i} X_i` of affine schemes is affine. -/
instance isAffine_triDiagram_obj (i : I) : IsAffine ((triDiagram φ).obj i) :=
  FibreProductLimit.isAffine_diagram_obj (sqToBase φ) φ i

end Affine

end LimitDatum

end AlgebraicGeometry

end
