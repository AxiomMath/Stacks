module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericallyFiniteQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral

/-!
# Codimension-zero points of a relative normalization, for a universally closed morphism

Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`
and let `Y ⟶ X' ⟶ X` be the normalization of `X` in `Y` (Stacks 0822).  Stacks 0AYG says that
every point of `|X'|` of codimension `0` is the image of a point of `|Y|` of codimension `0`.

This file proves that statement when `f` is moreover universally closed and `X` is decent.
The argument is topological.  The morphism `f' : Y ⟶ X'` is surjective
(`AlgebraicGeometry.Space.isSurjective_toNormalizationInQcqs`), so a codimension-zero point
`x'` is `f'(y)` for some `y`.  The space `Y` is decent, being quasi-separated over the decent
space `X`, so `|Y|` is sober and `y` is a specialization of the generic point `y₀` of an
irreducible component.  Then `f'(y₀)` specializes to `x'`, and a codimension-zero point of the
decent space `X'` has no proper generization, so `f'(y₀) = x'`;  finally `y₀` has codimension
`0` by Stacks 0ABV.

## Main results

* `AlgebraicGeometry.Space.exists_localRingDimension_eq_zero_of_universallyClosed`: every
  codimension-zero point of the normalization of a decent `X` in `Y` is the image of a
  codimension-zero point of `Y`, for `f` universally closed.

## Implementation notes

No `@[stacks 0AYG]` attribute is placed: the tag asks only that `f` be quasi-compact and
quasi-separated, and assumes nothing on `X`, so universal closedness of `f` and decency of `X`
are hypotheses the source does not make.  This is the case Stacks 0AYI uses: there `f` is
proper and `X` is integral, hence decent.

## References

* [Stacks Project, Tag 0AYG](https://stacks.math.columbia.edu/tag/0AYG)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- The normalization of a decent algebraic space in another is decent: the structure morphism
`ν : X' ⟶ X` is separated, hence quasi-separated, so Stacks 03M5 and Stacks 0ABY apply. -/
theorem isDecentSpace_normalizationInQcqs (hXdec : IsDecentSpace B S hS X.1) :
    IsDecentSpace B S hS (normalizationInQcqs B S hS f hfqc hfqs).1 :=
  isDecentSpace_source_of_isQuasiSeparated B S hS (normalizationInQcqs B S hS f hfqc hfqs).2 X.2
    _ (isQuasiSeparated_normalizationInQcqsHom B S hS f hfqc hfqs) hXdec

/-- Every point of a decent algebraic space is a specialization of a generic point of an
irreducible component of its point space: the point space is sober. -/
theorem exists_mem_genericPoints_specializes (hY : IsAlgebraicSpace B S hS Y.1)
    (hYdec : IsDecentSpace B S hS Y.1) (y : points B S hS Y.1) :
    ∃ y₀ ∈ genericPoints (points B S hS Y.1), y₀ ⤳ y := by
  have := quasiSober_points_of_isDecentSpace B S hS hY hYdec
  obtain ⟨Z, hZ, hyZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({y} : Set (points B S hS Y.1)) isIrreducible_singleton
  have hZirr : IsIrreducible Z := hZ.1
  have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZirr.genericPoint Z := by
    simpa only [hZcl.closure_eq] using hZirr.isGenericPoint_genericPoint_closure
  refine ⟨hZirr.genericPoint, ?_, ?_⟩
  · change closure {hZirr.genericPoint} ∈ irreducibleComponents (points B S hS Y.1)
    rw [hgen.def]
    exact hZ
  · exact hgen.specializes (hyZ rfl)

/-- **Codimension-zero points of the normalization, for a universally closed morphism.**  Let
`f : Y ⟶ X` be a quasi-compact, quasi-separated and universally closed morphism of algebraic
spaces over `S` with `X` decent, and let `Y ⟶ X' ⟶ X` be the normalization of `X` in `Y`.  Every
point `x'` of `|X'|` of codimension `0` is the image under `f' : Y ⟶ X'` of a point of `|Y|` of
codimension `0`.  This is Stacks 0AYG under the two extra hypotheses that `f` is universally
closed and `X` decent. -/
theorem exists_localRingDimension_eq_zero_of_universallyClosed
    (hfuc : UniversallyClosed B S hS f.hom) (hXdec : IsDecentSpace B S hS X.1)
    (x' : points B S hS (normalizationInQcqs B S hS f hfqc hfqs).1)
    (hx' : localRingDimension B S hS x' = 0) :
    ∃ y : points B S hS Y.1, localRingDimension B S hS y = 0 ∧
      pointsMap B S hS Y.1 (toNormalizationInQcqs f hfqc hfqs).hom y = x' := by
  have hYdec : IsDecentSpace B S hS Y.1 :=
    isDecentSpace_source_of_isQuasiSeparated B S hS Y.2 X.2 f.hom hfqs hXdec
  obtain ⟨y, rfl⟩ := isSurjective_toNormalizationInQcqs B S hS f hfqc hfqs hfuc x'
  obtain ⟨y₀, hy₀, hy₀y⟩ := exists_mem_genericPoints_specializes B S hS Y.2 hYdec y
  refine ⟨y₀, localRingDimension_eq_zero_of_mem_genericPoints B S hS Y.2 hYdec hy₀,
    eq_of_specializes_of_localRingDimension_eq_zero B S hS
      (normalizationInQcqs B S hS f hfqc hfqs).2
      (isDecentSpace_normalizationInQcqs B S hS f hfqc hfqs hXdec) hx' _ ?_⟩
  exact hy₀y.map (continuous_pointsMap B S hS _)

end AlgebraicGeometry.Space

end
