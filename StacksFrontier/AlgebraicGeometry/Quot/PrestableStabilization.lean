module

public import StacksFrontier.AlgebraicGeometry.Quot.StableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.StableModelCharacterization
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureContraction

/-!
# The stabilization of a prestable family of curves: vocabulary

Let `f : X ⟶ S` be a prestable family of curves of genus `g ≥ 2`. Stacks 0E8A factors `f` as
`X ⟶ Y ⟶ S` with `Y ⟶ S` a stable family of curves and `c : X ⟶ Y` such that

1. `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after base change by any morphism
   `S' ⟶ S`, and
2. for every `s ∈ S` the morphism `c_s : X_s ⟶ Y_s` is the contraction of rational tails and
   bridges of Algebraic Curves, Section 0E7N,

and `c` is unique up to unique isomorphism. This file names the conditions.

## Main definitions

* `AlgebraicGeometry.CurveFamily.IsUniversalStructureContraction`: condition (1).
* `AlgebraicGeometry.CurveFamily.HasStableContractionFibres`: condition (2).

## Implementation notes

The two families have the same base; as in the statement of Stacks 0E88 in this library, the
second family `Y` is an arbitrary family of curves together with an equality `Y.base = X.base`,
and its structure morphism to the base of `X` is `Y.toBase` followed by the transport along this
equality.

Condition (1) quantifies over every base change: for every scheme `T` of the site over `S` and
every pair of cartesian squares exhibiting `X'` and `Y'` as `X ×_S T` and `Y ×_S T`, the induced
morphism `c' : X' ⟶ Y'` has `𝒪_{Y'} ≅ c'_*𝒪_{X'}` and `R¹c'_*𝒪_{X'} = 0`
(`AlgebraicGeometry.Space.IsStructureContraction`). Taking `T = S` gives the condition for `c`.

Condition (2) is asserted at every field-valued point of the base, which includes the points
`Spec κ(s) ⟶ S`, and for every presentation of the two fibres by schemes of the site (the fibres
of a family of curves over a field are schemes; presentations are unique up to unique
isomorphism). The contraction of Section 0E7N is characterized by the three conditions of
Stacks 0E7Q (`Stacks.Curves.StableModel.IsStableContraction`), see
`AlgebraicGeometry.exists_isStableContraction_comp_tails_bridges`.

The genus of a prestable family is read on its fibres: a prestable family has genus `g` when
its classifying morphism factors through the open substack of prestable curves of genus `g`
(Stacks 0E6V), which happens exactly when every fibre over a field has genus `g` (Stacks 0E6V,
part (2)); this is `AlgebraicGeometry.CurveFamily.HasFibresOfGenus`.

## References

* [Stacks Project, Tag 0E8A](https://stacks.math.columbia.edu/tag/0E8A)
* [Stacks Project, Tag 0E7N](https://stacks.math.columbia.edu/tag/0E7N)
* [Stacks Project, Tag 0E7Q](https://stacks.math.columbia.edu/tag/0E7Q)
* [Stacks Project, Tag 0E6V](https://stacks.math.columbia.edu/tag/0E6V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

namespace CurveFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- **Condition (1) of Stacks 0E8A.** For a morphism `c : X ⟶ Y` over the common base `S` of two
families of curves, `𝒪_Y = c_*𝒪_X` and `R¹c_*𝒪_X = 0`, and this remains true after base change by
any morphism `T ⟶ S`: whenever `X'` and `Y'` are the fibre products `X ×_S T` and `Y ×_S T` and
`c' : X' ⟶ Y'` is the morphism induced by `c`, the structure map `𝒪_{Y'} ⟶ c'_*𝒪_{X'}` is an
isomorphism and `R¹c'_*𝒪_{X'} = 0`. -/
def IsUniversalStructureContraction (X Y : CurveFamily B hZ) (hb : Y.base = X.base)
    (c : X.total ⟶ Y.total) : Prop :=
  ∀ (T : BigFppfOver B integerBase hZ) (h : T ⟶ X.base)
    (X' Y' : AlgebraicSpaces B integerBase hZ) (pX' : X' ⟶ X.total) (fX' : X' ⟶ schemeSpace T)
    (pY' : Y' ⟶ Y.total) (fY' : Y' ⟶ schemeSpace T) (c' : X' ⟶ Y'),
    IsPullback pX' fX' X.toBase (schemeSpaceMap h) →
    IsPullback pY' fY' (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)) (schemeSpaceMap h) →
    c' ≫ pY' = pX' ≫ c → c' ≫ fY' = fX' →
    Space.IsStructureContraction B integerBase hZ c'

/-- **Condition (2) of Stacks 0E8A.** For a morphism `c : X ⟶ Y` over the common base `S` of two
families of curves, at every field-valued point `p` of `S` the fibre `c_p : X_p ⟶ Y_p` is the
contraction to a stable curve of Algebraic Curves, Section 0E7N: for all schemes `V_X`, `V_Y` of
the site presenting the fibres of `X` and `Y` over `p`, the morphism `a : V_X ⟶ V_Y` over `p`
induced by `c` satisfies the three conditions of Stacks 0E7Q, which characterize that
contraction. -/
def HasStableContractionFibres (X Y : CurveFamily B hZ) (hb : Y.base = X.base)
    (c : X.total ⟶ Y.total) : Prop :=
  ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
    (VX VY : BigFppfOver B integerBase hZ) (vX : VX ⟶ p.siteObject) (vY : VY ⟶ p.siteObject)
    (qX : yoneda.obj VX ⟶ X.total.obj) (qY : yoneda.obj VY ⟶ Y.total.obj) (a : VX ⟶ VY),
    IsPullback qX (yoneda.map vX) X.toBase.hom (yonedaEquiv.symm p.value) →
    IsPullback qY (yoneda.map vY) (Y.toBase ≫ eqToHom (congrArg schemeSpace hb)).hom
      (yonedaEquiv.symm p.value) →
    a ≫ vY = vX → qX ≫ c.hom = yoneda.map a ≫ qY →
    Stacks.Curves.StableModel.IsStableContraction ((𝒯).map vX) ((𝒯).map vY) ((𝒯).map a)

end CurveFamily

end AlgebraicGeometry

end
