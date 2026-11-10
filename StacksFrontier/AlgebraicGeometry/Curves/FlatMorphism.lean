module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.FlatDescent
public import StacksFrontier.Topology.Dimension.IrreducibleDimensionOne
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat morphisms of curves

A nonconstant morphism of curves over a field is flat as soon as the target curve is normal.
The local rings of the target are then either the function field, at the generic point, or
discrete valuation rings, at the closed points; a module over a field is flat, and over a
discrete valuation ring flatness is torsion-freeness, which follows from the injectivity of the
stalk maps of a dominant morphism of integral schemes.

Combined with flat descent of smoothness, this makes a normal curve smooth as soon as some
smooth curve maps onto it: a surjection of curves is in particular nonconstant, hence flat.

## Main results

* `AlgebraicGeometry.isFlat_of_nonconstant_of_isNormal`: a nonconstant morphism of curves over a
  field with normal target is flat.
* `AlgebraicGeometry.smooth_of_surjective_of_isNormal`: a normal curve surjectively dominated by
  a smooth curve is smooth.

## Implementation notes

The curves are presented by their structure morphisms to the spectrum of the ground field, and
the equation making the given morphism a morphism over that field is an explicit argument.
Nonconstancy is expressed by requiring the range of the underlying map on points to contain at
least two points, which for a morphism of curves is exactly dominance. Flatness is
`AlgebraicGeometry.IsFlat`, the pointwise stalkwise condition on the underlying morphism of
ringed spaces.

## References

* [Stacks Project, Tag 0CCK](https://stacks.math.columbia.edu/tag/0CCK)
* [Stacks Project, Tag 0CCW](https://stacks.math.columbia.edu/tag/0CCW)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0CCK.** A nonconstant morphism of curves over a field is flat if the
target curve is normal. -/
@[stacks 0CCK]
lemma isFlat_of_nonconstant_of_isNormal
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY]
    (f : X ⟶ Y) (_hf : f ≫ pY = pX) (hnonconstant : (Set.range f).Nontrivial)
    [IsNormal Y] :
    IsFlat f.toLRSHom.toShHom := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace pY
  have hinjAll : ∀ x : X, Function.Injective (f.stalkMap x) :=
    ((tfae_isDominant_of_isIntegral f).out 1 6).mp (IsDominant.mk
      (Stacks.Topology.Dimension.denseRange_of_nontrivial_of_topologicalKrullDim_eq_one
        f f.continuous hnonconstant
        (IsCurve.topologicalKrullDim_eq_one (k := k) (f := pY))))
  intro x
  let y := f x
  have hinj : Function.Injective (f.stalkMap x) := hinjAll x
  change ((f.toLRSHom.toShHom).hom.stalkMap x).hom.Flat
  by_cases hy : IsClosed ({y} : Set Y)
  · let φ := (f.stalkMap x).hom
    change φ.Flat
    have : IsIntegrallyClosed (Y.presheaf.stalk y) := IsNormal.stalk_normal y
    have : IsDiscreteValuationRing (Y.presheaf.stalk y) :=
      ((isDiscreteValuationRing_stalk_tfae_of_isCurve k pY hy).out 2 3).mp
        (IsNormalRing.of_isIntegrallyClosed _)
    have : EuclideanDomain (Y.presheaf.stalk y) :=
      IsDiscreteValuationRing.toEuclideanDomain (Y.presheaf.stalk y)
    let _ : Algebra (Y.presheaf.stalk y) (X.presheaf.stalk x) := φ.toAlgebra
    change Module.Flat (Y.presheaf.stalk y) (X.presheaf.stalk x)
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot,
      Module.isTorsionFree_iff_algebraMap_injective]
    simpa only [RingHom.algebraMap_toAlgebra] using hinj
  · have hyη : f x = genericPoint Y := by
      by_contra hne
      exact hy (Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint
        Y (IsCurve.topologicalKrullDim_eq_one (k := k) (f := pY)) hne)
    change ((f.stalkMap x).hom).Flat
    exact RingHom.Flat.of_isField
      (AlgebraicGeometry.isField_stalk_of_closure_mem_irreducibleComponents Y (f x)
        (by rw [hyη]; simp [irreducibleComponents_eq_singleton])) _

/-- **Stacks Project, Tag 0CCW.** A normal curve over a field is smooth if it is surjectively
dominated by a smooth curve over that field. A surjection onto a curve has nontrivial range, so
it is flat by `AlgebraicGeometry.isFlat_of_nonconstant_of_isNormal`, and smoothness descends
along a flat surjection. -/
@[stacks 0CCW]
theorem smooth_of_surjective_of_isNormal
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
    [IsCurve k pX] [IsCurve k pY]
    (f : X ⟶ Y) (_hf : f ≫ pY = pX)
    [Surjective f] [Smooth pX] [IsNormal Y] :
    Smooth pY := by
  have : Nontrivial Y := by
    by_contra h
    have : Subsingleton Y := not_nontrivial_iff_subsingleton.mp h
    have : Subsingleton (TopologicalSpace.IrreducibleCloseds Y) := ⟨fun A B => by
      apply TopologicalSpace.IrreducibleCloseds.ext
      have hwhole : ∀ s : Set Y, s.Nonempty → s = Set.univ :=
        fun s ⟨y, hy⟩ => Set.eq_univ_of_forall fun z => Subsingleton.elim y z ▸ hy
      rw [hwhole _ A.isIrreducible.nonempty, hwhole _ B.isIrreducible.nonempty]⟩
    have hdim := Order.krullDim_nonpos_of_subsingleton
      (α := TopologicalSpace.IrreducibleCloseds Y)
    change topologicalKrullDim Y ≤ 0 at hdim
    rw [IsCurve.topologicalKrullDim_eq_one pY] at hdim
    norm_num at hdim
  have hrange : (Set.range f).Nontrivial := by
    simpa [Set.range_eq_univ.mpr (‹Surjective f›.surj)] using
      (Set.nontrivial_univ : (Set.univ : Set Y).Nontrivial)
  have : Flat f :=
    (AlgebraicGeometry.Flat.iff_flat_stalkMap f).2
      (isFlat_of_nonconstant_of_isNormal pX pY f _hf hrange)
  have : Smooth (f ≫ pY) := _hf ▸ (inferInstance : Smooth pX)
  exact smooth_of_flat_of_surjective f pY

end AlgebraicGeometry

end
