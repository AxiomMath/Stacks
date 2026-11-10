module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescentHom
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescentObjects

/-!
# The stack of polarized proper schemes is limit preserving

This file assembles Stacks 0D43: the stack in groupoids `𝒫olarized` of polarized proper schemes
of Stacks 0D1M is limit preserving in the sense of Stacks 07XL. For every cofiltered inverse
system of affine schemes over a terminal base whose limit of underlying schemes is `T`, the
canonical comparison `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is an equivalence of categories.

## Main results

* `AlgebraicGeometry.isEquivalence_colimitComparison_polarized`: the comparison functor of
  Stacks 07XL for `𝒫olarized` is an equivalence.
* `AlgebraicGeometry.isLimitPreservingPolarizedUnconditional`: **Stacks 0D43**, the predicate
  `AlgebraicGeometry.IsLimitPreservingPolarizedUnconditional`, at index categories in the scheme
  universe.

## Implementation notes

`CategoryTheory.Functor.IsEquivalence` is faithfulness, fullness and essential surjectivity, and
each of the three is reduced by
`StacksFrontier/AlgebraicGeometry/Stacks/LimitPreservingStageDescent`
to a colimit-free descent condition at a stage of the system:
`AlgebraicGeometry.descentObj_polarizedSliceProjection`,
`AlgebraicGeometry.descentHom_polarizedSliceProjection` and
`AlgebraicGeometry.descentEq_polarizedSliceProjection`. Nothing further is needed here.

The index universes are both the scheme universe. This is faithful to Stacks 07XL, which
quantifies over a directed inverse system of affine schemes: a directed set is small. It is also
forced, because the geometric inputs — Stacks 09MT through
`AlgebraicGeometry.exists_isAmple_pullback_map_of_isLimit_of_qcqs` and the limit presentation of
the system of base changes through `AlgebraicGeometry.isLimitPullbackCone` — ask the index
category to live in the scheme universe.

## References

* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The comparison functor of Stacks 07XL for `𝒫olarized` is an equivalence.** For every
cofiltered inverse system of affine schemes over the terminal base whose limit of underlying
schemes is `T`, the canonical functor `colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is faithful, full and
essentially surjective. -/
theorem isEquivalence_colimitComparison_polarized (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) {I : Type u} [Category.{u} I]
    [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c)) :
    letI : (polarizedSliceProjection B hS hT).IsFibered :=
      (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
    (Deformation.Artin.colimitComparison (polarizedSliceProjection B hS hT)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).IsEquivalence :=
  let : (polarizedSliceProjection B hS hT).IsFibered :=
    (polarizedProjection_isFiberedInGroupoids_unconditional.sliceAtTerminal hT).isFibered
  { faithful := faithful_colimitComparison_polarized B hS hT D c hc
    full := full_colimitComparison_polarized B hS hT D c hc
    essSurj := essSurj_colimitComparison_polarized B hS hT D c hc }

/-- **Stacks 0D43.** The stack in groupoids `𝒫olarized` of polarized proper schemes is limit
preserving in the sense of Stacks 07XL: for every cofiltered inverse system of affine schemes over
the terminal base whose limit of underlying schemes is `T`, the canonical comparison
`colim 𝒫olarized_{Tᵢ} ⥤ 𝒫olarized_T` is an equivalence of categories. The index category is taken
in the scheme universe, which is the smallness the source's directed sets have. -/
@[stacks 0D43 "at a small index category"]
theorem isLimitPreservingPolarizedUnconditional (B : BigFppfSite.{u}) {S : Scheme.{u}}
    (hS : B.Contains S) (hT : IsTerminal (B.obj hS)) :
    IsLimitPreservingPolarizedUnconditional.{u, u, u} B hS hT := by
  intro I _ _ D c hc
  exact isEquivalence_colimitComparison_polarized B hS hT D c hc

end AlgebraicGeometry

end
