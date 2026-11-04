module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusCycleOnDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.VanishingLocusDeltaDimension

/-!
# The cycle `[D]_{n-1}` of an effective Cartier divisor, as an element of `Z_{n-1}(D)`

In Situation 0EDT let `X/B` be good and integral with `n = dim_δ(X)`, let `ℒ` be an invertible
`𝒪_X`-module, let `s ∈ Γ(X, ℒ)` be a **nonzero** global section and let `i : E → X` be the closed
immersion of the vanishing locus `E = Z(s)` of Stacks 0845.  The right-hand side
`c₁(𝒩) ∩ [D]_{n-1}` of Stacks 0ER9 is a class on `D`, so the cycle `[D]_{n-1}` it caps has to be
formed **on `D` itself**, as an element of `Z_{n-1}(D)` and not of `Z_{n-1}(X)`.

This file forms it, and reconciles the two spellings in which the cycle of a vanishing locus
occurs in this library:

* `AlgebraicGeometry.Space.closedSubspaceCycle`, the cycle `[Y]_k` of Stacks 0EE9 of a closed
  subspace `Y`, which needs the δ-dimension bound `dim_δ(Y) ≤ k`, and
* `AlgebraicGeometry.Space.zeroSchemeCycle`, the same cycle at `Y = Z(s)`, which instead asks
  for local finiteness of the coefficient family.

The two are the same element of `Z_k(X)`, the coefficient family of the second being by
definition that of the first; the inputs differ because local finiteness is all that
`AlgebraicGeometry.Space.zeroSchemeCycle` needs and is what Stacks 0EQF supplies for a nonzero
section, while the δ-dimension bound is what Stacks 0EE9 is stated with and is
`AlgebraicGeometry.Space.deltaDimensionSubspace_vanishingLocus_le`.

## Main results

* `AlgebraicGeometry.Space.subspacePointSet_top`: the point set of the top subfunctor is the
  whole point space.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_top_vanishingLocus_le`: the bound
  `dim_δ(E) ≤ n - 1` in the shape `AlgebraicGeometry.Space.closedSubspaceCycle` asks for on `E`,
  namely for the top subfunctor of `E`.
* `AlgebraicGeometry.Space.vanishingLocusTopCycle`: **the cycle `[D]_{n-1}` of Stacks 0EE9 formed
  on `D = Z(s)`, as an element of `Z_{n-1}(D)`.**
* `AlgebraicGeometry.Space.zeroSchemeCycle_eq_closedSubspaceCycle`: the reconciliation of the two
  spellings on `X`.
* `cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_sectionWeilDivisor`:
  **`i_*[D]_{n-1} = div_ℒ(s)` in `Z_{n-1}(X)`**, as an equality of cycles rather than of
  coefficient families.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EE9](https://stacks.math.columbia.edu/tag/0EE9)
* [Stacks Project, Tag 0845](https://stacks.math.columbia.edu/tag/0845)
* [Stacks Project, Tag 0EQF](https://stacks.math.columbia.edu/tag/0EQF)
* [Stacks Project, Tag 0ER9](https://stacks.math.columbia.edu/tag/0ER9)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- The point set of the top subfunctor of an algebraic space is the whole point space: the
inclusion of the top subfunctor is an isomorphism, hence surjective on points. -/
theorem subspacePointSet_top (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    subspacePointSet B S hS F (⊤ : Subfunctor F) = Set.univ :=
  Set.range_eq_univ.2 (pointsMap_surjective_of_isIso B S hS (⊤ : Subfunctor F).ι)

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hint : IsIntegralSpace D.site D.base D.base_mem X)
    (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleSheaf D sX hX L)

include hint hL in
/-- **The δ-dimension bound on `E = Z(s)` read on the top subfunctor of `E`.**  For a nonzero
global section `s` of an invertible module on a good integral space `X` with `n = dim_δ(X)`, the
top subfunctor of `E = Z(s)`, as a closed subspace of `E`, has δ-dimension at most `n - 1`. -/
theorem deltaDimensionSubspace_top_vanishingLocus_le {s : L.sections} (hs : s ≠ 0) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    deltaDimensionSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s)
        (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)
        (isClosedSubspace_top_subfunctor D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).2.1) ≤ ((n - 1 : ℤ) : EInt) := by
  have hE := isGood_vanishingLocus D sX hX L s
  have hpt := (deltaDimensionClosed_le_coe_iff D _ hE _ _ (n - 1)).1
    (deltaDimensionClosed_univ_vanishingLocus_le D sX hX hint L hL hs hn)
  rw [deltaDimensionSubspace_eq_deltaDimensionClosed]
  exact (deltaDimensionClosed_le_coe_iff D _ hE _ _ (n - 1)).2 fun t _ => hpt t (Set.mem_univ t)

/-- **The cycle `[D]_{n-1}` of Stacks 0EE9 formed on `D = Z(s)`.**  In Situation 0EDT let `X/B` be
good and integral with `n = dim_δ(X)`, let `ℒ` be invertible and let `s ∈ Γ(X, ℒ)` be a nonzero
global section, with `i : D → X` the closed immersion of `D = Z(s)`.  This is the cycle of
Stacks 0EE9 of the top subfunctor of `D`, as an element of `Z_{n-1}(D)`. -/
def vanishingLocusTopCycle {s : L.sections} (hs : s ≠ 0) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    CycleGroup D ((vanishingLocus D sX hX L s).1.ι ≫ sX) (n - 1) :=
  closedSubspaceCycle D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
    (isGood_vanishingLocus D sX hX L s)
    (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)
    (isClosedSubspace_top_subfunctor D.site D.base D.base_mem
      (vanishingLocus D sX hX L s).2.1) (n - 1)
    (deltaDimensionSubspace_top_vanishingLocus_le D sX hX hint L hL hs hn)

/-- The coefficient family of `[D]_{n-1}` formed on `D` is the one of Stacks 0EE9 for the top
subfunctor of `D`, read at the canonical geometric representatives. -/
@[simp]
theorem vanishingLocusTopCycle_coe {s : L.sections} (hs : s ≠ 0) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    (vanishingLocusTopCycle D sX hX hint L hL hs hn).1 =
      cycleCoeffOfClosedSubspace D ((vanishingLocus D sX hX L s).1.ι ≫ sX)
        (isGood_vanishingLocus D sX hX L s)
        (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor)
        (isClosedSubspace_top_subfunctor D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).2.1) (n - 1)
        (canonicalGeometricPoint D.site D.base D.base_mem
          (⊤ : Subfunctor (vanishingLocus D sX hX L s).1.toFunctor).toFunctor) :=
  rfl

/-- **The two spellings of `[Z(s)]_k` on `X` agree.**  The cycle of the vanishing locus formed
through `AlgebraicGeometry.Space.zeroSchemeCycle`, whose input is local finiteness of the
coefficient family, and the cycle of Stacks 0EE9 of the same closed subspace formed through
`AlgebraicGeometry.Space.closedSubspaceCycle`, whose input is the δ-dimension bound, are the same
element of `Z_k(X)`: the coefficient family of the former is by definition that of the latter at
the canonical geometric representatives. -/
theorem zeroSchemeCycle_eq_closedSubspaceCycle (s : L.sections) (k : ℤ)
    (hfin : LocallyFinite fun Z : IntegralClosedSubspace D.site D.base D.base_mem X =>
      if zeroSchemeCycleCoeff D sX hX L s k
          (canonicalGeometricPoint D.site D.base D.base_mem
            (vanishingLocus D sX hX L s).1.toFunctor) Z = 0 then ∅
      else subspacePointSet D.site D.base D.base_mem X Z.subspace)
    (hdim : deltaDimensionSubspace D sX hX (vanishingLocus D sX hX L s).1
      (vanishingLocus D sX hX L s).2 ≤ (k : EInt)) :
    zeroSchemeCycle D sX hX L s k
        (canonicalGeometricPoint D.site D.base D.base_mem
          (vanishingLocus D sX hX L s).1.toFunctor) hfin =
      closedSubspaceCycle D sX hX (vanishingLocus D sX hX L s).1
        (vanishingLocus D sX hX L s).2 k hdim :=
  Subtype.ext rfl

include hint hL in
/-- **`i_*[D]_{n-1} = div_ℒ(s)` in `Z_{n-1}(X)`.**  In Situation 0EDT let `X/B` be good and
integral with `n = dim_δ(X)`, let `ℒ` be invertible and let `s ∈ Γ(X, ℒ)` be a nonzero global
section, with `i : D → X` the closed immersion of `D = Z(s)`.  The pushforward along `i` of the
cycle `[D]_{n-1}` of Stacks 0EE9 formed *on `D`* is the Weil divisor `div_ℒ(s)` of Stacks 0EQE
part (1) on `X`. -/
theorem cycleGroupClosedPushforward_vanishingLocusTopCycle_eq_sectionWeilDivisor
    {s : L.sections} (hs : s ≠ 0) {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    cycleGroupClosedPushforward D hX.1 (vanishingLocus D sX hX L s).2.1
        (D.isDecentSpace_of_isGood sX hX) (vanishingLocus D sX hX L s).2.2 sX hX.2.2
        ((vanishingLocus D sX hX L s).1.ι ≫ sX) rfl (n - 1)
        (vanishingLocusTopCycle D sX hX hint L hL hs hn) =
      sectionWeilDivisor D sX hX hint L hL hn
        (globalSectionMeromorphic D.site D.base D.base_mem hX.1 L s)
        (globalSectionMeromorphic_ne_zero_of_isInvertibleSheaf D sX hX L hL hs) :=
  Subtype.ext
    (cycleClosedPushforward_topCycleCoeff_eq_sectionWeilDivisor D sX hX L s hint hL hn hs)

end AlgebraicGeometry.Space

end
