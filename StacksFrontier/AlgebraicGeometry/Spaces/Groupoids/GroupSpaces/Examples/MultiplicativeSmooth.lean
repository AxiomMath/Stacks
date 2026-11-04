module

public import Mathlib.Algebra.Polynomial.Laurent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.Examples.MultiplicativeSmoothDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.SmoothProductProjection

/-!
# The multiplicative group is smooth over its base

The Laurent polynomial ring `R[T, T⁻¹]` is a localization of `R[T]` away from `T`, so it is a
smooth `R`-algebra: the polynomial ring is smooth and inverting one element is smooth.  Hence
the structure morphism `Gₘ ⟶ Spec ℤ` of the integral multiplicative group scheme is a smooth
morphism of schemes, and therefore a smooth morphism of algebraic spaces over `Spec ℤ`.  So the
structure morphism `B ×_{Spec ℤ} Gₘ ⟶ B` of the group algebraic space of Stacks 043I is smooth
for every algebraic space `B` over `Spec ℤ`.

## Main definitions

* `AlgebraicGeometry.Space.multiplicativeGroupULiftSiteObject`: the integral multiplicative
  group scheme, read as an object of the big fppf site over `Spec ℤ` through its own structure
  morphism, together with its group-object structure
  `AlgebraicGeometry.Space.multiplicativeGroupULiftSiteObjectGrpObj`.

## Main results

* `AlgebraicGeometry.Space.isSmooth_multiplicativeGroupULiftSiteObject`: the structure morphism
  `Gₘ ⟶ Spec ℤ` is a smooth morphism of algebraic spaces over `Spec ℤ`.
* `AlgebraicGeometry.Space.isSmooth_prod_fst_multiplicativeGroupULift`: the structure morphism
  of the group algebraic space `Gₘ,B = B ×_{Spec ℤ} Gₘ` is smooth, for an arbitrary algebraic
  space `B` over `Spec ℤ`.

## References

* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/- **Stacks 022U.** The structure morphism of the integral multiplicative group scheme is a
smooth morphism of schemes: `AlgebraicGeometry.smooth_multiplicativeGroupULift`. -/
add_to_stacks 022U "the structure morphism is smooth"
  AlgebraicGeometry.smooth_multiplicativeGroupULift

namespace Space

variable (𝒞 : BigFppfSite.{u})

/-- The integral multiplicative group scheme, read as an object of the big fppf site over
`Spec ℤ` through its own structure morphism. -/
noncomputable def multiplicativeGroupULiftSiteObject :
    BigFppfOver 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞) :=
  siteObject 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞)
    (contains_multiplicativeGroupULift 𝒞) (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))

/-- `AlgebraicGeometry.Space.multiplicativeGroupULiftSiteObject`, read as a scheme over
`Spec ℤ`, is the slice object `Gₘ.asOver (Spec ℤ)` on the nose. -/
theorem toSchemeOver_obj_multiplicativeGroupULiftSiteObject :
    (toSchemeOver 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞)).obj
        (multiplicativeGroupULiftSiteObject 𝒞) =
      (multiplicativeGroupULift : Scheme.{u}).asOver (Spec (.of (ULift.{u} ℤ))) :=
  rfl

/-- The group-scheme structure of **Stacks 022U** on
`AlgebraicGeometry.Space.multiplicativeGroupULiftSiteObject`. -/
@[instance_reducible]
noncomputable def multiplicativeGroupULiftSiteObjectGrpObj :
    GrpObj ((toSchemeOver 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞)).obj
      (multiplicativeGroupULiftSiteObject 𝒞)) :=
  instGrpObjSpecAsOverSpec (R := .of (ULift.{u} ℤ))
    (A := .of (LaurentPolynomial (ULift.{u} ℤ)))

/-- **The structure morphism of the multiplicative group scheme is a smooth morphism of
algebraic spaces over `Spec ℤ`.** -/
@[sga "3 I 4.4.4" "special case", sga "3 VIII 2.1" "2.1(e), special case"]
theorem isSmooth_multiplicativeGroupULiftSiteObject :
    IsSmooth 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞)
      (yoneda.map (Over.mkIdTerminal.from (multiplicativeGroupULiftSiteObject 𝒞))) :=
  isSmooth_yoneda_map_mkIdTerminal_from 𝒞 _ _ _
    ((toScheme_map_mkIdTerminal_from_siteObject 𝒞 (Spec (.of (ULift.{u} ℤ)))
      (contains_specULiftZ 𝒞) (contains_multiplicativeGroupULift 𝒞)
      (multiplicativeGroupULift ↘ Spec (.of (ULift.{u} ℤ)))) ▸
      smooth_multiplicativeGroupULift.{u})

/-- The structure morphism of the group algebraic space `Gₘ,B = B ×_{Spec ℤ} Gₘ` over an
arbitrary algebraic space `B` over `Spec ℤ` is a smooth morphism of algebraic spaces. -/
@[stacks 043I "the structure morphism of the multiplicative group algebraic space is smooth",
  sga "3 VIII 2.1" "(e), special case"]
theorem isSmooth_prod_fst_multiplicativeGroupULift
    (B : (BigFppfOver 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞))ᵒᵖ ⥤ Type u)
    (hB : IsAlgebraicSpace 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞) B) :
    IsSmooth 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞)
      (prod.fst : B ⨯ (pointsOnSite 𝒞 (Spec (.of (ULift.{u} ℤ))) (contains_specULiftZ 𝒞)
        (multiplicativeGroupULiftSiteObject 𝒞)
        (multiplicativeGroupULiftSiteObjectGrpObj 𝒞) ⋙ forget GrpCat) ⟶ B) :=
  isSmooth_prod_fst_pointsOnSite 𝒞 _ _ B hB _ _ (isSmooth_multiplicativeGroupULiftSiteObject 𝒞)

end Space

end AlgebraicGeometry

end
