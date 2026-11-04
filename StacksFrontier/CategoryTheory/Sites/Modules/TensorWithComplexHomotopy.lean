module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplex

/-!
# Tensoring with a complex of modules on a ringed site, on homotopy categories

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let
`(E, d) = Hom_{Comp^dg(O)}(K, K)` be its endomorphism differential graded algebra. Tensoring with
`K` is a functor `- ⊗_E K : Mod^dg_(E, d) ⥤ Comp^dg(O)` of differential graded categories; this
file descends it to the homotopy categories and shows that the descended functor
`K(Mod_(E, d)) ⥤ K(O)` is an exact functor of triangulated categories.

## Main definitions

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy`: the induced functor
  `K(Mod_(E, d)) ⥤ K(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_spec`: the induced functor is a lift of
  the ordinary tensor functor on complexes along the two quotient functors; together with
  `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_obj` and
  `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_map` this pins the functor down to the
  differential graded functor it comes from.
* `AlgebraicGeometry.RingedSite.tensorWithComplexHomotopy_isTriangulated`: the induced functor
  commutes with the translation and carries distinguished triangles to distinguished triangles,
  that is, it is an exact functor of triangulated categories.

## Implementation notes

Everything is an instance of the general statement of
`StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes`: a functor of differential
graded categories over a commutative ring `R`, from the differential graded modules over a
differential graded `R`-algebra to the complexes in an `R`-linear preadditive category, descends
to the homotopy categories and is exact there, because such a functor acts on all homogeneous
morphisms and therefore transports the graded splittings of an admissible short exact sequence.
The input is the differential graded functor of Tag 09LV and the preadditive category is the
ambient category of `O`-modules chosen there.

The base ring is the source's `R`, with the `AlgebraicGeometry.RingedSite.ScalarSections`
hypothesis under which Tag 09LV's differential graded tensor functor is built.

The two finiteness instances on the ambient category of `O`-modules recorded below are what the
triangulated structure on `K(O)` needs; they come from the existence of finite limits of sheaves
of modules.

## References

* [Stacks Project, Tag 09LW](https://stacks.math.columbia.edu/tag/09LW)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
-/

@[expose] public section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

/-- The ambient category of `O`-modules has finite biproducts, since it has finite limits. -/
public instance tensorModOHasFiniteBiproducts :
    Limits.HasFiniteBiproducts (TensorModO.{u, v, w, t, s} X) := by
  let _ : Limits.HasFiniteLimits (TensorModO.{u, v, w, t, s} X) :=
    SheafOfModules.Finite.hasFiniteLimits (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let _ : Limits.HasFiniteProducts (TensorModO.{u, v, w, t, s} X) :=
    Limits.hasFiniteProducts_of_hasFiniteLimits _
  exact Limits.HasFiniteBiproducts.of_hasFiniteProducts

/-- The ambient category of `O`-modules has a zero object. -/
public instance tensorModOHasZeroObject :
    Limits.HasZeroObject (TensorModO.{u, v, w, t, s} X) := by
  let _ : Limits.HasFiniteLimits (TensorModO.{u, v, w, t, s} X) :=
    SheafOfModules.Finite.hasFiniteLimits (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let _ : Limits.HasFiniteProducts (TensorModO.{u, v, w, t, s} X) :=
    Limits.hasFiniteProducts_of_hasFiniteLimits _
  infer_instance

/-- The ambient category of `O`-modules has binary biproducts. -/
public instance tensorModOHasBinaryBiproducts :
    Limits.HasBinaryBiproducts (TensorModO.{u, v, w, t, s} X) :=
  Limits.hasBinaryBiproducts_of_finite_biproducts _

section BaseRing

variable (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]

/-- **Stacks 09LW.** The functor `K(Mod_(E, d)) ⥤ K(O)` induced on homotopy categories by
tensoring differential graded modules over the endomorphism differential graded algebra of `K`
with `K`. -/
@[stacks 09LW "the induced functor on homotopy categories"]
public noncomputable def tensorWithComplexHomotopy
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    DifferentialGradedModule.HomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra ⥤
      _root_.HomotopyCategory (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) :=
  DifferentialGradedModule.dgFunctorToHomotopyCategory
    (tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor

/-- The induced functor on homotopy categories commutes with the translation. -/
public noncomputable instance tensorWithComplexHomotopyCommShift
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).CommShift ℤ :=
  DifferentialGradedModule.dgFunctorToHomotopyCategoryCommShift _

/-- The induced functor on homotopy categories is the lift, along the two quotient functors, of
the ordinary functor on complexes attached to the differential graded tensor functor. -/
@[stacks 09LW "compatibility with the differential graded functor"]
public theorem tensorWithComplexHomotopy_spec
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    DifferentialGradedModule.toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra ⋙
        tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K =
      DifferentialGradedModule.dgFunctorToComplexes
          (tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor ⋙
        HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ) :=
  DifferentialGradedModule.dgFunctorToHomotopyCategory_spec _

/-- On objects, the induced functor is the differential graded tensor functor. -/
public theorem tensorWithComplexHomotopy_obj
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    (M : DifferentialGradedModule (Rep.{u, v, w, t, s, o} X R K).algebra) :
    (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).obj
        ((DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, v, w, t, s, o} X R K).algebra).obj M) =
      (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).obj
        ((tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor.obj M) := rfl

/-- On morphisms, the induced functor is the homotopy class of the image of the associated closed
degree-zero homogeneous morphism under the differential graded tensor functor. -/
public theorem tensorWithComplexHomotopy_map
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
    {M N : DifferentialGradedModule (Rep.{u, v, w, t, s, o} X R K).algebra} (f : M ⟶ N) :
    (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).map
        ((DifferentialGradedModule.toHomotopyCategory
          (Rep.{u, v, w, t, s, o} X R K).algebra).map f) =
      (HomotopyCategory.quotient (TensorModO.{u, v, w, t, s} X) (ComplexShape.up ℤ)).map
        (DifferentialGradedModule.dgFunctorToComplexes
          (tensorWithComplexDG.{u, v, w, t, s, o} X R K).functor |>.map f) :=
  DifferentialGradedModule.dgFunctorToHomotopyCategory_map _ f

/-- **Stacks 09LW.** Tensoring with `K` is an exact functor of triangulated categories
`K(Mod_(E, d)) ⥤ K(O)`: it commutes with the translation and carries distinguished triangles to
distinguished triangles. -/
@[stacks 09LW "exactness of the induced functor"]
public theorem tensorWithComplexHomotopy_isTriangulated
    (K : CochainComplex (ModO.{u, v, w, t} X) ℤ) :
    (tensorWithComplexHomotopy.{u, v, w, t, s, o} X R K).IsTriangulated :=
  DifferentialGradedModule.dgFunctorToHomotopyCategory_isTriangulated _

end BaseRing

end AlgebraicGeometry.RingedSite

end
