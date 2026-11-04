module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-!
# Limit preservation for the proper flat families, reduced to stage descent (Stacks 0D1I)

**Stacks 0D1I** asserts that the category `Spaces'_{fp, flat, proper}` of finitely presented, flat
and proper families of algebraic spaces over varying base schemes is limit preserving in the sense
of Stacks 07XL: for every cofiltered inverse system of affine schemes of the big fppf site with
limit `T`, the canonical comparison `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence of categories.

This file reduces that assertion to three descent conditions. Being an equivalence is
faithfulness, fullness and essential surjectivity, and each of the three follows, with no geometric
input, from a colimit-free descent condition at a stage of the system:
`Deformation.Artin.DescentObj`, `Deformation.Artin.DescentHom` and `Deformation.Artin.DescentEq`
for the projection `AlgebraicGeometry.cartesianProperFlatProjection` of Stacks 0D1E.

## Main results

* `AlgebraicGeometry.isEquivalence_colimitComparison_cartesianProperFlat`: the comparison functor
  of Stacks 07XL for the proper flat families is an equivalence as soon as the three descent
  conditions hold at the cone.
* `AlgebraicGeometry.isLimitPreserving_cartesianProperFlatFiberedCategory_of_stageDescent`: the
  predicate of Stacks 07XL for the proper flat families, from the three descent conditions at every
  affine cofiltered cone.

## Implementation notes

The colimit of Stacks 07XL is a categorical colimit in `Cat`, taken over the split fibres of
Stacks 004A. Its objects and morphisms are read back at a stage by
`Deformation.Artin.essSurj_of_descentObj`, `Deformation.Artin.full_of_descentHom` and
`Deformation.Artin.faithful_of_descentEq`, which need the projection to be fibred in groupoids;
for the proper flat families this is Stacks 0D1E,
`AlgebraicGeometry.cartesianProperFlatProjection_isFiberedInGroupoids`.

The universes `v` and `w` of the index category are left free.

## References

* [Stacks Project, Tag 0D1I](https://stacks.math.columbia.edu/tag/0D1I)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 004A](https://stacks.math.columbia.edu/tag/004A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The comparison functor of Stacks 07XL for the proper flat families is an equivalence, given
stage descent.** For a cofiltered inverse system of affine schemes of the big fppf site, the
canonical functor `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` of Stacks 07XL is faithful, full and essentially
surjective as soon as objects, vertical morphisms and equalities of vertical morphisms over the
vertex of the cone descend to a stage. -/
theorem isEquivalence_colimitComparison_cartesianProperFlat
    {I : Type v} [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hobj : Deformation.Artin.DescentObj (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c))
    (hhom : Deformation.Artin.DescentHom (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c))
    (heq : Deformation.Artin.DescentEq (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c)) :
    letI : (cartesianProperFlatProjection B S hS).IsFibered :=
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS).isFibered
    (Deformation.Artin.colimitComparison (cartesianProperFlatProjection B S hS)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).IsEquivalence :=
  have hF := cartesianProperFlatProjection_isFiberedInGroupoids B S hS
  letI := hF.isFibered
  { faithful := Deformation.Artin.faithful_of_descentEq _ hF _ _ heq
    full := Deformation.Artin.full_of_descentHom _ hF _ _ hhom
    essSurj := Deformation.Artin.essSurj_of_descentObj _ hF _ _ hobj }

/-- The category of finitely presented, flat and proper
families of algebraic spaces over varying base schemes is limit preserving in the sense of Stacks
07XL as soon as, at every affine cofiltered cone whose cone of underlying schemes is a limit,
objects, vertical morphisms and equalities of vertical morphisms over the vertex descend to a
finite stage. -/
theorem isLimitPreserving_cartesianProperFlatFiberedCategory_of_stageDescent
    (hobj : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      Deformation.Artin.DescentObj (cartesianProperFlatProjection B S hS)
        (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c))
    (hhom : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      Deformation.Artin.DescentHom (cartesianProperFlatProjection B S hS)
        (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c))
    (heq : ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
      (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
      IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
      Deformation.Artin.DescentEq (cartesianProperFlatProjection B S hS)
        (D ⋙ BigAffineFppf.inclusion B S hS) ((BigAffineFppf.inclusion B S hS).mapCone c)) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u + 1} B S hS
      (cartesianProperFlatFiberedCategory B S hS) := fun I _ _ D c hc =>
  isEquivalence_colimitComparison_cartesianProperFlat B S hS D c
    (hobj I D c hc) (hhom I D c hc) (heq I D c hc)

end AlgebraicGeometry

end
