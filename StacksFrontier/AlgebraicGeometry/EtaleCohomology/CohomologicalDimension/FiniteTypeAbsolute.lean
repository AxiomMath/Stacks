module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineFiniteType
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteType

/-!
# Finite cohomological dimension of a scheme of finite type over a field

[Stacks, Tag 0F10], part (2): if `cd(K) < ∞`, then `cd(X) < ∞` for every scheme `X` of
finite type over the field `K`. Part (1) and the overview are in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteType`.

The induction principle of [Stacks, Tag 08DR], with the Mayer--Vietoris sequence of
[Stacks, Tag 0A50] as its step (`Scheme.etaleCohomologicalDimension_lt_top_of_isAffineOpen`),
reduces to an affine scheme. There [Stacks, Tag 0F0V] bounds `cd(X)` by `dim X + cd(K)`,
which is finite.

## Main results

* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_lt_top_of_finiteType`: **part (2)**,
  from `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_lt_top_of_isAffine`
  ([Stacks, Tag 0F0V]).

## Status

Part (2) is unconditional and carries its own registration of the tag. Part (1) is registered
separately, in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FiniteType`,
once its input [Stacks, Tag 0F0W] is unconditional.

## References

* [Stacks Project, Tag 0F10](https://stacks.math.columbia.edu/tag/0F10)
* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **Stacks Project, Tag 0F10, part (2).** If the field `K` has finite cohomological dimension
`cd(K) = cd(Spec K) < ∞`, then every scheme `X` of finite type over `K` has finite cohomological
dimension: `cd(X) < ∞`. -/
@[stacks 0F10 "(2): cd(X) < ∞ for X of finite type over a field K with cd(K) < ∞"]
theorem etaleCohomologicalDimension_lt_top_of_finiteType (K : Type u) [Field K]
    {X : Scheme.{u}} (x : X ⟶ Spec (.of K)) [LocallyOfFiniteType x] [QuasiCompact x]
    (hK : etaleCohomologicalDimension (Spec (.of K)) < ⊤) :
    haveI : CompactSpace X := compactSpace_of_finiteType K x
    haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_finiteType K x
    etaleCohomologicalDimension X < ⊤ := by
  have : CompactSpace X := compactSpace_of_finiteType K x
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_finiteType K x
  refine etaleCohomologicalDimension_lt_top_of_isAffineOpen X fun V hV => ?_
  have : IsAffine V.toScheme := hV
  have : LocallyOfFiniteType (V.ι ≫ x) := inferInstance
  exact etaleCohomologicalDimension_lt_top_of_isAffine K V.toScheme
    (V.ι ≫ x) hK

end AlgebraicGeometry.Scheme

end
