module

public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.MultiplePointLength
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistDivisible.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.TwistSectionMinimality
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RegularCompactification
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 0A27: a curve is an affine scheme or H-projective

[Stacks, Tag 0A27] says that a curve over a field `k` — a variety over `k` whose underlying space
has Krull dimension one — is either an affine scheme or H-projective over `k`. The two
possibilities are mutually exclusive (`AlgebraicGeometry.not_isAffine_of_isCurve`), and the
statement below is the disjunction itself.

The source's proof has two halves.

*The outer half.* Choose a compactification `j : X ⟶ X̄` as in [Stacks, Tag 0BXW]: `X̄` is
H-projective over `k` and `X̄ ∖ j(X)` is a finite set of closed points at which the local rings of
`X̄` are discrete valuation rings. If that set is empty then `j` is an isomorphism and `X` is
itself H-projective; otherwise pick one of its points `x₁`, and [Stacks, Tag 09N9] reduces the
affineness of `X` to the affineness of the open `X̄ ∖ {x₁}`.

*The inner half, the source's "Claim".* For `X̄` an H-projective curve over `k` and `x` a closed
point at which `𝒪_{X̄,x}` is a discrete valuation ring, `X̄ ∖ {x}` is affine. The point is an
effective Cartier divisor ([Stacks, Tag 0B8Y]), its multiples `n·x` are effective Cartier divisors
([Stacks, Tag 01WT]), and the first short exact sequence of [Stacks, Tag 0C6K] together with the
finiteness of `dim_k H¹(X̄, 𝒪_{X̄})` ([Stacks, Tag 02O6]) and the dimension count
`dim_k H⁰(X̄, 𝒪_{n·x}) ≥ n` ([Stacks, Tag 0AYT]) produce, for the least `n` that works, a section
of `𝒪_{X̄}(n·x)` generating the stalk at `x`. Together with the canonical section it generates the
invertible module, hence defines a morphism `X̄ ⟶ ℙ¹_k` ([Stacks, Tag 01ND]) which is finite and
pulls `D₊(T₀)` back to `X̄ ∖ {x}`, an affine open.

## Main results

* `AlgebraicGeometry.exists_isCurve_isProjectiveMorphism_completion`: the compactification of
  [Stacks, Tag 0BXW] with the curve structure of the compactification added — `X̄` is again a
  curve over `k`.
* `AlgebraicGeometry.isAffineOpen_compl_singleton_of_isCurve`: the source's inner claim.
* `AlgebraicGeometry.isAffine_or_isProjectiveMorphism`: **[Stacks, Tag 0A27]**.

## Where the source's citations are discharged

**[Stacks, Tag 0BXW]** is
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`,
the form of that tag whose only hypothesis on `X` is reducedness. A curve is integral, hence
reduced, so that is the form which applies here. Its proof takes the first step of the source's
proof of Tag 0BXW, [Stacks, Tag 0A25], in the reduced case
`Stacks.CurveProjectiveCompletion.isHQuasiProjective_of_isReduced`, whose ample invertible sheaf
is [Stacks, Tag 09NX]. The general Tag 0A25 is
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_dimension_le_one`, whose ample
invertible sheaf is [Stacks, Tag 09NZ],
`Stacks.AmpleNoetherianDimensionOne.exists_isAmple_of_isNoetherian_of_topologicalKrullDim_le_one`.

**[Stacks, Tag 09N9]** enters through
`AlgebraicGeometry.isAffine_or_exists_isClosedImmersion_of_compactification`, whose own use of
it is `AlgebraicGeometry.isAffineOpen_of_isCompact_of_krullDimLE_one`: a quasi-compact open of a
locally Noetherian scheme of dimension at most one which lies in an affine open is affine.

**[Stacks, Tag 02O6]** is `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`,
which supplies the `FiniteDimensional k (cohomologyOverField k q 𝒪 1)` instance the inner claim
asks for; the structure sheaf is coherent by
`Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit`, available because a curve is
locally of finite type over `k` and hence locally Noetherian.

**Clause (2) of [Stacks, Tag 0AYT]** is
`AlgebraicGeometry.finrank_cohomologyOverField_multiplePoint_ge`: the `k`-vector space
`H⁰(X̄, i_* i^* 𝒪_{X̄}((N+1)x))` has dimension at least `N + 1`. The source reads this bound off
the identification of that space with `𝒪_{X̄,x}/(π^{N+1})` for `π` a uniformizer; in the
development the `(N+1)`-fold point is a one-point scheme whose global sections are its local
ring `𝒪_{X̄,x}/𝔪^{N+1}`, of length `N + 1` over itself and therefore of dimension
`(N+1)·[κ(x):k]` over `k`.

**The minimality step** — the source's "otherwise it would define a section of
`𝒪_X((n-1)x) ⊂ 𝒪_X(n·x)`" — is
`Stacks.Divisors.mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingChart`: a global
section of `𝒪_{X̄}((p+1)x)` whose germ at `x` does not generate the stalk comes from a global
section of `𝒪_{X̄}(p·x)`.

**Tags 0B8Y, 01WT, 0C6K, 01ND, 0BCL, 01W6, 02OH and 01WM** enter only through existing
declarations: the point as an effective Cartier divisor and its multiples through
`AlgebraicGeometry.isEffectiveCartierDivisor_vanishingIdeal_pow`, the first short exact sequence
through `Stacks.Divisors.isShortExactUnitSequence_canonicalSections`, and the morphism to `ℙ¹_k`
with its finiteness through `Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank`
and `Stacks.ProjectiveSpaceSections.isAffineOpen_compl_singleton_of_nonvanishingChart_eq`.

## Implementation notes

**The compactification is again a curve.** Clause (1) of [Stacks, Tag 0BXW] gives `X̄`
H-projective over `k` and clause (4) gives the discrete valuation rings, but the source's remark
that "`X̄` is a curve as well" is not part of the conclusion of
`Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced`,
and both the reduction step and the inner claim need it. It is recovered exactly as in
`AlgebraicGeometry.exists_isRegular_isProjectiveMorphism_compactification`, except for reducedness:
there `X̄` is reduced because it is regular, which is unavailable here, so instead every local ring
of `X̄` is shown to be reduced one point at a time — at a point of `j(X)` the stalk is isomorphic
to a stalk of the reduced `X`, because `j` is an open immersion, and at a point of the complement
it is a discrete valuation ring, hence a domain. Irreducibility comes from dominance of `j` and the
dimension from the two inequalities along the open immersion, as there.

**The numerical input of the inner claim is instantiated at the first `N` that works.**
`Stacks.Divisors.isAffineOpen_compl_singleton_of_mem_range_of_finrank` asks for `d` and `N` with
`dim_k H¹(X̄, 𝒪_{X̄}) < d ≤ dim_k H⁰(X̄, 𝒪_{(N+1)x})`; taking `d = h + 1` and `N = h` for
`h = dim_k H¹(X̄, 𝒪_{X̄})` makes the left inequality `h < h + 1` and the right one clause (2) of
[Stacks, Tag 0AYT] at `N = h`. The minimality step is then applied at every `p`, because the
least `p` for which a section escapes `𝒪_{X̄}` is produced by a search.

## References

* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0BXW](https://stacks.math.columbia.edu/tag/0BXW)
* [Stacks Project, Tag 09N9](https://stacks.math.columbia.edu/tag/09N9)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01ND](https://stacks.math.columbia.edu/tag/01ND)
* [Stacks Project, Tag 0BCL](https://stacks.math.columbia.edu/tag/0BCL)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Divisors Stacks.ProjectiveSpaceSections

universe u

namespace AlgebraicGeometry

/-! ### The inner claim -/

/-- **The inner claim of [Stacks, Tag 0A27].** Let `Y` be a proper curve over a field `k` and let
`y` be a closed point of `Y` at which `𝒪_{Y,y}` is a discrete valuation ring. Then `Y ∖ {y}` is an
affine open. -/
theorem isAffineOpen_compl_singleton_of_isCurve (k : Type u) [Field k]
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k)) [IsLocallyNoetherian Y] [IsIntegral Y]
    (hq : IsProper q) (hc : IsCurve k q) {y : Y} (hy : IsClosed ({y} : Set Y))
    [IsDiscreteValuationRing (Y.presheaf.stalk y)] :
    IsAffineOpen (⟨({y} : Set Y)ᶜ, hy.isOpen_compl⟩ : Y.Opens) := by
  have _ : IsProper q := hq
  have _ : _root_.SheafOfModules.IsCoherent (_root_.SheafOfModules.unit Y.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have _ : FiniteDimensional k
      (cohomologyOverField k q (_root_.SheafOfModules.unit Y.ringCatSheaf) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k q
      (_root_.SheafOfModules.unit Y.ringCatSheaf) 1
  exact isAffineOpen_compl_singleton_of_mem_range_of_finrank q hq hc hy
    (fun p => Stacks.Divisors.mem_range_sectionsMap_invertibleSheafMap_of_notMem_nonvanishingChart
      k q hq hc hy p)
    (d := Module.finrank k
      (cohomologyOverField k q (_root_.SheafOfModules.unit Y.ringCatSheaf) 1) + 1)
    (N := Module.finrank k
      (cohomologyOverField k q (_root_.SheafOfModules.unit Y.ringCatSheaf) 1))
    (Nat.lt_succ_self _) (finrank_cohomologyOverField_multiplePoint_ge k q hq hc hy _)

/-! ### The compactification is again a curve -/

/-- **The compactification of [Stacks, Tag 0BXW], with the source's remark that it is again a
curve.** Let `X` be a curve over a field `k`. Then there is a curve `Y` over `k`, H-projective
over `k`, and an open immersion `j : X ⟶ Y` over `k` such that at every point of `Y` outside the
image of `j` the singleton is closed and the local ring is a discrete valuation ring. -/
theorem exists_isCurve_isProjectiveMorphism_completion
    (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsCurve k p] :
    ∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of k)) (j : X ⟶ Y) (_ : IsOpenImmersion j),
      j ≫ q = p ∧ IsCurve k q ∧ IsProjectiveMorphism q ∧
        ∀ y : Y, y ∉ Set.range j.base →
          IsClosed ({y} : Set Y) ∧
            ∃ _ : IsDomain (Y.presheaf.stalk y),
              IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  have hdimX : topologicalKrullDim (X : Type u) = 1 :=
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := p)
  obtain ⟨Y, q, j, hj, hjq, hproj, hdom, -, -, hbdry⟩ :=
    Stacks.CurveProjectiveCompletion.exists_projective_completion_discreteValuation_of_isReduced
      k p hdimX.le
  have _ : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have hdvr : ∀ y : Y, y ∉ Set.range j.base → ∃ _ : IsDomain (Y.presheaf.stalk y),
      IsDiscreteValuationRing (Y.presheaf.stalk y) := fun y hy => (hbdry y hy).2
  have hstalkred : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    by_cases hy : y ∈ Set.range (j.base : X → Y)
    · obtain ⟨x, rfl⟩ := hy
      have : IsIso (j.stalkMap x) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 x
      exact isReduced_of_injective (j.stalkMap x).hom
        (ConcreteCategory.bijective_of_isIso (j.stalkMap x)).1
    · obtain ⟨_, _⟩ := hdvr y hy
      infer_instance
  have _ : AlgebraicGeometry.IsReduced Y := isReduced_of_isReduced_stalk Y
  have _ : IrreducibleSpace Y := irreducibleSpace_of_isDominant j
  have _ : AlgebraicGeometry.IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  have hdimY : topologicalKrullDim (Y : Type u) = 1 :=
    le_antisymm
      (topologicalKrullDim_le_one_of_isOpenImmersion_of_isDVR_stalk_compl j hdimX.le hdvr)
      (hdimX ▸ Topology.IsInducing.topologicalKrullDim_le
        (f := (j.base : X → Y)) j.isOpenEmbedding.isEmbedding.isInducing)
  exact ⟨Y, q, j, hj, hjq, { toIsVariety := { }, topologicalKrullDim_eq_one := hdimY }, hproj,
    hbdry⟩

/-! ### Stacks Tag 0A27 -/

/-- Let `k` be a field and let `X` be a curve over `k`. Then `X` is an affine scheme or `X` is
H-projective over `k`. -/
@[stacks 0A27]
theorem isAffine_or_isProjectiveMorphism
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] :
    IsAffine X ∨ IsProjectiveMorphism f := by
  obtain ⟨Y, q, j, hj, hjq, hcq, hproj, hbdry⟩ :=
    exists_isCurve_isProjectiveMorphism_completion k f
  have hq : IsProper q := isProper_of_isProjectiveMorphism q hproj
  have _ : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  have hinner : ∀ z : Y, z ∉ Set.range j.base →
      ∃ U : Y.Opens, (U : Set Y) = ({z} : Set Y)ᶜ ∧ IsAffineOpen U := by
    intro z hz
    obtain ⟨hzc, _, _⟩ := hbdry z hz
    exact ⟨⟨({z} : Set Y)ᶜ, hzc.isOpen_compl⟩, rfl,
      isAffineOpen_compl_singleton_of_isCurve k q hq hcq hzc⟩
  exact isAffine_or_exists_isClosedImmersion_of_compactification k (f := f) (g := q)
    j hjq hproj hinner

end AlgebraicGeometry

end
