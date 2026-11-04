module

public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ZeroSectionComparison
public import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ChartGeneration

/-!
# The deformation spaces of a nested pair of effective Cartier divisors

Let `Z ⊆ Y ⊆ X` be closed subschemes which are effective Cartier divisors in `X`. This file
relates the three deformation spaces

  `D(Z ⊆ Y) ⟶ D(Z ⊆ X) ⟶ D(Y ⊆ X)`

induced by the squares `Z = Z, Y ⊆ X` and `Z ⊆ Y, X = X`. The first is a closed immersion, and both
are compatible with the embeddings of the normal cones in the special fibres.

## Main definitions

* `Stacks.Deformation.coborderMap`: the morphism of coborders over a morphism of ambient schemes.
* `Stacks.Deformation.nestedOuterMap`: `D(Z ⊆ X) ⟶ D(Y ⊆ X)`.
* `Stacks.Deformation.nestedInnerMap`: `D(Z ⊆ Y) ⟶ D(Z ⊆ X)`.

## Main results

* `Stacks.Deformation.isClosedImmersion_nestedInnerMap`: `D(Z ⊆ Y) ⟶ D(Z ⊆ X)` is a closed
  immersion.
* `Stacks.Deformation.normalConeToDeformation_comp_nestedOuterMap`,
  `Stacks.Deformation.normalConeToDeformation_comp_nestedInnerMap`: both morphisms are compatible
  with the embeddings of the normal cones.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.Blowup Stacks.Conormal

universe u

namespace Stacks.Deformation

/-! ### Coborders of closed immersions -/

section Coborder

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X')
  [IsClosedImmersion i] [IsClosedImmersion i'] (g : X ⟶ X')

/-- For a closed immersion the ideal of the closed factorization is the inverse image of the
ideal. -/
theorem coborderIdeal_eq_comap : coborderIdeal i = i.ker.comap i.coborderRange.ι :=
  Stacks.Algebraization.ker_liftCoborder_eq_comap i

/-- **The morphism of coborders of two closed immersions over a morphism of ambient schemes.**
Both coborders are the whole ambient scheme. -/
def coborderMap : i.coborderRange.toScheme ⟶ i'.coborderRange.toScheme :=
  haveI := Stacks.Divisors.isIso_coborderRange_ι i'
  i.coborderRange.ι ≫ g ≫ inv i'.coborderRange.ι

/-- The morphism of coborders commutes with `g` and the inclusions of the coborders. -/
@[reassoc]
theorem coborderMap_ι : coborderMap i i' g ≫ i'.coborderRange.ι = i.coborderRange.ι ≫ g := by
  have := Stacks.Divisors.isIso_coborderRange_ι i'
  simp [coborderMap]

/-- The morphism of coborders over an affine morphism is affine. -/
instance [IsAffineHom g] : IsAffineHom (coborderMap i i' g) := by
  have := Stacks.Divisors.isIso_coborderRange_ι i
  have := Stacks.Divisors.isIso_coborderRange_ι i'
  unfold coborderMap
  infer_instance

/-- The morphism of coborders over a closed immersion is a closed immersion. -/
instance [IsClosedImmersion g] : IsClosedImmersion (coborderMap i i' g) := by
  have := Stacks.Divisors.isIso_coborderRange_ι i
  have := Stacks.Divisors.isIso_coborderRange_ι i'
  unfold coborderMap
  infer_instance

/-- The inverse image of the ideal of the coborder of `i'` under `coborderMap` is the inverse
image of the pulled back ideal of `i'`. -/
private theorem comap_coborderIdeal_coborderMap :
    (coborderIdeal i').comap (coborderMap i i' g) = (i'.ker.comap g).comap i.coborderRange.ι := by
  simp [coborderIdeal_eq_comap, ← Scheme.IdealSheafData.comap_comp, coborderMap_ι]

variable {i i'} in
/-- The ideals of a commutative square of closed immersions are compatible. -/
theorem comap_coborderIdeal_le {f : Z ⟶ Z'} (comm : f ≫ i' = i ≫ g) :
    (coborderIdeal i').comap (coborderMap i i' g) ≤ coborderIdeal i := by
  rw [comap_coborderIdeal_coborderMap, coborderIdeal_eq_comap]
  refine Scheme.IdealSheafData.comap_mono _ ?_
  rw [← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_ker, ← comm]
  exact Scheme.Hom.le_ker_comp _ _

/-- If the square is cartesian on ideals, the ideals of the coborders correspond. -/
theorem comap_coborderIdeal_eq (hpb : i'.ker.comap g = i.ker) :
    (coborderIdeal i').comap (coborderMap i i' g) = coborderIdeal i := by
  rw [comap_coborderIdeal_coborderMap, hpb, coborderIdeal_eq_comap]

end Coborder

/-! ### The nested pair -/

section Nested

variable {X : Scheme.{u}} (DY DZ : X.IdealSheafData) (hZY : DY ≤ DZ)

/-- The ideal of `Z ⊆ X` on its coborder. -/
abbrev idealZX : DZ.subschemeι.coborderRange.toScheme.IdealSheafData := coborderIdeal DZ.subschemeι

/-- The ideal of `Y ⊆ X` on its coborder. -/
abbrev idealYX : DY.subschemeι.coborderRange.toScheme.IdealSheafData := coborderIdeal DY.subschemeι

/-- The ideal of `Z ⊆ Y` on its coborder. -/
abbrev idealZY : (Scheme.IdealSheafData.inclusion hZY).coborderRange.toScheme.IdealSheafData :=
  coborderIdeal (Scheme.IdealSheafData.inclusion hZY)

/-- The base map `U_{Z ⊆ X} ⟶ U_{Y ⊆ X}`. -/
abbrev outerBase := coborderMap DZ.subschemeι DY.subschemeι (𝟙 X)

/-- The base map `U_{Z ⊆ Y} ⟶ U_{Z ⊆ X}`. -/
abbrev innerBase := coborderMap (Scheme.IdealSheafData.inclusion hZY) DZ.subschemeι DY.subschemeι

/-- The square formed by `Z ⊆ Y`, `Y ⊆ X`, `Z ⊆ X` and the identity of `X` commutes. -/
theorem outer_comm : Scheme.IdealSheafData.inclusion hZY ≫ DY.subschemeι =
    DZ.subschemeι ≫ 𝟙 X := by
  simp

/-- The square formed by the identity of `Z`, `Z ⊆ X`, `Z ⊆ Y` and `Y ⊆ X` commutes. -/
theorem inner_comm : 𝟙 _ ≫ DZ.subschemeι =
    Scheme.IdealSheafData.inclusion hZY ≫ DY.subschemeι := by
  simp

include hZY in
/-- The inverse image of the ideal of `Y ⊆ X` under `outerBase` is contained in the ideal of
`Z ⊆ X`. -/
theorem outer_le : (idealYX DY).comap (outerBase DY DZ) ≤ idealZX DZ :=
  comap_coborderIdeal_le _ (outer_comm DY DZ hZY)

/-- The inverse image of the ideal of `Z ⊆ X` under `innerBase` is the ideal of `Z ⊆ Y`. -/
theorem inner_eq : (idealZX DZ).comap (innerBase DY DZ hZY) = idealZY DY DZ hZY := by
  refine comap_coborderIdeal_eq _ _ _ ?_
  have hsq : IsPullback (Scheme.IdealSheafData.inclusion hZY) (𝟙 DZ.subscheme) DY.subschemeι
      DZ.subschemeι :=
    IsPullback.of_vert_isIso_mono ⟨(inner_comm DY DZ hZY).symm⟩
  have hker : (Scheme.IdealSheafData.inclusion hZY).ker = DZ.comap DY.subschemeι := by
    rw [← hsq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]
    rfl
  rw [hker, Scheme.IdealSheafData.ker_subschemeι]

/-- The inverse image of the ideal of `Z ⊆ X` under `innerBase` is contained in the ideal of
`Z ⊆ Y`. -/
theorem inner_le : (idealZX DZ).comap (innerBase DY DZ hZY) ≤ idealZY DY DZ hZY :=
  (inner_eq DY DZ hZY).le

include hZY in
/-- **The morphism `D(Z ⊆ X) ⟶ D(Y ⊆ X)`.** -/
def nestedOuterMap :
    deformationSpace (idealZX DZ) ⟶ deformationSpace (idealYX DY) :=
  deformationMap (outerBase DY DZ) (idealYX DY) (idealZX DZ) (outer_le DY DZ hZY)

/-- **The morphism `D(Z ⊆ Y) ⟶ D(Z ⊆ X)`**, a closed immersion. -/
def nestedInnerMap :
    deformationSpace (idealZY DY DZ hZY) ⟶ deformationSpace (idealZX DZ) :=
  deformationMap (innerBase DY DZ hZY) (idealZX DZ) (idealZY DY DZ hZY) (inner_le DY DZ hZY)

/-- The morphism `D(Z ⊆ Y) ⟶ D(Z ⊆ X)` is a closed immersion. -/
instance isClosedImmersion_nestedInnerMap : IsClosedImmersion (nestedInnerMap DY DZ hZY) :=
  isClosedImmersion_deformationMap _ _ _ _ (inner_eq DY DZ hZY).symm

/-- **The normal cones sit compatibly in the outer square.** -/
theorem normalConeToDeformation_comp_nestedOuterMap :
    normalConeToDeformation DZ.subschemeι ≫ nestedOuterMap DY DZ hZY =
      normalConeMapOfFactorization DZ.subschemeι DY.subschemeι
          (Scheme.IdealSheafData.inclusion hZY) (Scheme.IdealSheafData.inclusion_subschemeι hZY) ≫
        normalConeToDeformation DY.subschemeι :=
  normalConeToDeformation_comp_deformationMap DZ.subschemeι DY.subschemeι
    (Scheme.IdealSheafData.inclusion hZY) (𝟙 X) _ (outerBase DY DZ)
    (coborderMap_ι _ _ _) (outer_le DY DZ hZY)

/-- **The normal cones sit compatibly in the inner square.** -/
theorem normalConeToDeformation_comp_nestedInnerMap :
    normalConeToDeformation (Scheme.IdealSheafData.inclusion hZY) ≫ nestedInnerMap DY DZ hZY =
      normalConeMapOfSquare (Scheme.IdealSheafData.inclusion hZY) DZ.subschemeι (𝟙 _)
          DY.subschemeι (inner_comm DY DZ hZY) ≫
        normalConeToDeformation DZ.subschemeι :=
  normalConeToDeformation_comp_deformationMap (Scheme.IdealSheafData.inclusion hZY)
    DZ.subschemeι (𝟙 _) DY.subschemeι _ (innerBase DY DZ hZY) (coborderMap_ι _ _ _)
    (inner_le DY DZ hZY)

end Nested

end Stacks.Deformation

end
