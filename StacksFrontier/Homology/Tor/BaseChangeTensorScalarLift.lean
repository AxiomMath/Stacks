module

public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse

/-!
# The tensor comparisons across the scalar lift of [stacks 0E1W]

The keystone of Chapter 47 compares two monoidality isomorphisms of degreewise extension of
scalars.  The [stacks 068I] side carries the comparison of total complexes over the ring map
`f : R → A` itself, at independent universes, pinned only by the summand formula
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso`; the [stacks 0E1W] side carries
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` over the *lifted* ring map
`f' : ULift R → ULift A`, which is available only in a single universe.  Nothing related the two.

This file supplies the first of the two ingredients a comparison needs: the summand formula for
`CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso`, the comparison of restriction of
scalars along a ring isomorphism with the total tensor product: on each summand it is the
module-level comparison at the two components followed by the restriction of the inclusion of
the corresponding summand.

The second ingredient -- the comparison of "lift scalars, then extend along `f'`" with "extend
along `f`, then lift scalars" -- is in
`StacksFrontier.Homology.Tor.BaseChangeExtendScalarsLift`.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main results

* `HomologicalComplex₂.TotalMap.totalIso_hom_f` and
  `HomologicalComplex₂.TotalMap.ιTotal_mapIso_trans_totalIso_hom` -- the summand formula for an
  isomorphism of bicomplexes followed by the comparison of a functor with the total complex.
* `CochainComplex.DerivedTensor.ι_restrictScalarsTensorComplexIso_hom` -- **the summand
  formula** for the comparison of restriction of scalars with the total tensor product.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings

universe u v

namespace HomologicalComplex₂.TotalMap

/-- The degree-`n` component of `totalIso` is `totalMapf`. -/
public theorem totalIso_hom_f
    {C : Type*} {D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    (G : C ⥤ D) [G.Additive] (B : HomologicalComplex₂ C c₁ c₂) [B.HasTotal c₁₂]
    [(mapBicomplex G B).HasTotal c₁₂]
    [∀ n : I₁₂, Limits.PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G] (n : I₁₂) :
    (totalIso (c₁₂ := c₁₂) G B).hom.f n =
      totalMapf G B n := rfl

/-- The summand formula for the composite of `HomologicalComplex₂.total.mapIso` with
`totalIso`. -/
public theorem ιTotal_mapIso_trans_totalIso_hom
    {C : Type*} {D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {I₁ I₂ I₁₂ : Type*} {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₁₂ : ComplexShape I₁₂}
    [TotalComplexShape c₁ c₂ c₁₂] [DecidableEq I₁₂]
    (G : C ⥤ D) [G.Additive] {A : HomologicalComplex₂ D c₁ c₂} {B : HomologicalComplex₂ C c₁ c₂}
    [A.HasTotal c₁₂] [B.HasTotal c₁₂]
    [(mapBicomplex G B).HasTotal c₁₂]
    [∀ n : I₁₂, Limits.PreservesColimitsOfShape
      (Discrete ↥(ComplexShape.π c₁ c₂ c₁₂ ⁻¹' {n})) G]
    (iso : A ≅ mapBicomplex G B)
    (i₁ : I₁) (i₂ : I₂) (n : I₁₂) (h : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = n) :
    A.ιTotal c₁₂ i₁ i₂ n h ≫
        (HomologicalComplex₂.total.mapIso iso c₁₂ ≪≫
          totalIso G B).hom.f n =
      (iso.hom.f i₁).f i₂ ≫ G.map (B.ιTotal c₁₂ i₁ i₂ n h) := by
  rw [Iso.trans_hom, HomologicalComplex.comp_f, ← Category.assoc,
    HomologicalComplex₂.total.mapIso_hom, HomologicalComplex₂.ιTotal_map, Category.assoc,
    totalIso_hom_f, ι_totalMapf]

end HomologicalComplex₂.TotalMap

namespace CochainComplex.DerivedTensor

/-- **The summand formula for the comparison of restriction of scalars with the total tensor
product.**  On the antidiagonal summand of bidegree `(p, q)`,
`CochainComplex.DerivedTensor.restrictScalarsTensorComplexIso` is the module-level comparison
`CochainComplex.DerivedTensor.restrictScalarsTensorIso` at the two components, followed by the
restriction of the inclusion of the corresponding summand. -/
public theorem ι_restrictScalarsTensorComplexIso_hom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (e : R ≃+* S)
    (K L : CochainComplex (ModuleCat.{max u v} S) ℤ) (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor
          (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj K)
          (((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex (.up ℤ)).obj L)
          (moduleTensor.{u, v} R) (ComplexShape.up ℤ) p q n h ≫
        (restrictScalarsTensorComplexIso e K L).hom.f n =
      (restrictScalarsTensorIso e (K.X p) (L.X q)).hom ≫
        (ModuleCat.restrictScalars e.toRingHom).map
          (HomologicalComplex.ιMapBifunctor K L (moduleTensor.{v, u} S)
            (ComplexShape.up ℤ) p q n h) :=
  HomologicalComplex₂.TotalMap.ιTotal_mapIso_trans_totalIso_hom
    (ModuleCat.restrictScalars e.toRingHom)
    (restrictScalarsTensorBicomplexIso e K L) p q n h

end CochainComplex.DerivedTensor

end
