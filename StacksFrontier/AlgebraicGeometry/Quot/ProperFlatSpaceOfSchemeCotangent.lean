module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatObstructionBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.Cotangent.Spaces.ModelCotangentSmooth

/-!
# The cotangent complex at the point given by a smooth proper scheme over a field

Let `k` be a field with `Spec k` in a big fppf site `B`, and let `f : X ⟶ Spec k` be a smooth,
proper morphism. The point `x₀` of `Spaces'_{fp, flat, proper}` over `Spec k` given by `X`
(`AlgebraicGeometry.ProperFlatSpaceOfScheme.point`) has, at the chart `Spec k ⟶ Spec k` it lies
over, the structure morphism `X ⟶ Spec k` of algebraic spaces
(`AlgebraicGeometry.Space.ProperFlatLift.chartStructureMap`). This file proves that this morphism
is smooth with affine target, so that its cotangent complex `L_{X/k}`, formed on the model of the
small étale site of `X`, has cohomology only in degree `0` and is its degree `0` cohomology sheaf
placed in degree `0` (`StacksFrontier/Cotangent/Spaces/ModelCotangentSmooth.lean`).

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.isSmooth_commaHomAsSpaceMap_comp_eqToHom`
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.isSmooth_chartStructureMap_point`
* `ProperFlatSpaceOfScheme.isZero_homology_cotangentComplex_chartStructureMap_point`:
  the cohomology of `L_{X/k}` vanishes outside degree `0`.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.cotangentComplexDerivedIsoChartStructureMapPoint`

## References

* [Stacks Project, Tag 08R5](https://stacks.math.columbia.edu/tag/08R5)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t u

namespace AlgebraicGeometry.Space.ProperFlatLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure morphism of a family of algebraic spaces over a scheme, read through an
equality of the base, is smooth when the family is. -/
theorem isSmooth_commaHomAsSpaceMap_comp_eqToHom
    {G : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {V : BigFppfOver B S hS} (e : G.right = V) (h : IsSmooth B S hS G.hom) :
    IsSmooth B S hS (commaHomAsSpaceMap G ≫ (schemeSpaceFunctor B S hS).map (eqToHom e)).hom := by
  subst e
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact h

end AlgebraicGeometry.Space.ProperFlatLift

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]

/-- **The structure morphism `X ⟶ Spec k` of the point given by a smooth proper scheme is
smooth**, at the chart `Spec k ⟶ Spec k` the point lies over. -/
theorem isSmooth_chartStructureMap_point :
    Space.IsSmooth B (Spec (.of k)) hk (Space.ProperFlatLift.chartStructureMap (point B k hk f)
      (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
        (projection_point B k hk f))).hom :=
  Space.ProperFlatLift.isSmooth_commaHomAsSpaceMap_comp_eqToHom _
    ((Space.isSmooth_yoneda_map_iff B _ hk (toBaseObj B k hk f)).2 (by
      change Smooth f
      infer_instance))

/-- The base `Spec k` of the chart of the point is affine. -/
theorem isAffine_toScheme_obj_specialFibre :
    IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj
      (Deformation.Artin.algebraOver k B (Spec (.of k)) hk
        (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k)))
        (ProperFlatSpaceDeformation.contains_specialFibre (point B k hk f)
          (projection_point B k hk f)))) :=
  inferInstanceAs (IsAffine (Spec (.of k)))

/-- **The cotangent complex `L_{X/k}` of the point given by a smooth proper scheme has cohomology
only in degree `0`**: `H^i(L_{X/k}) = 0` for `i ≠ 0`, on the model of the small étale site of
`X`. -/
theorem isZero_homology_cotangentComplex_chartStructureMap_point (i : ℤ) (hi : i ≠ 0) :
    Limits.IsZero ((Space.modelRingedToposHom (Space.ProperFlatLift.chartStructureMap
      (point B k hk f) (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
        (projection_point B k hk f)))).cotangentComplex.homology i) :=
  Space.isZero_homology_modelCotangentComplex_of_isSmooth _
    (isAffine_toScheme_obj_specialFibre B k hk f) (isSmooth_chartStructureMap_point B k hk f) i hi

variable [HasDerivedCategory.{t} (Space.modelModules (point B k hk f).obj.obj.left)]

/-- **The cotangent complex `L_{X/k}` of the point given by a smooth proper scheme is its degree
`0` cohomology sheaf placed in degree `0`**, in the derived category of `𝒪_X`-modules on the model
of the small étale site of `X`. -/
def cotangentComplexDerivedIsoChartStructureMapPoint :
    (Space.modelRingedToposHom (Space.ProperFlatLift.chartStructureMap (point B k hk f)
      (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
        (projection_point B k hk f)))).cotangentComplexDerived ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((Space.modelRingedToposHom (Space.ProperFlatLift.chartStructureMap (point B k hk f)
          (ProperFlatSpaceDeformation.obj_eq_specialFibre (point B k hk f)
            (projection_point B k hk f)))).cotangentComplex.homology 0) :=
  Space.modelCotangentComplexDerivedIsoOfIsSmooth _
    (isAffine_toScheme_obj_specialFibre B k hk f) (isSmooth_chartStructureMap_point B k hk f)

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end
