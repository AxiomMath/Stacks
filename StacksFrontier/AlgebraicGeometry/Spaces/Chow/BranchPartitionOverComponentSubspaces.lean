module

public import StacksFrontier.AlgebraicGeometry.Spaces.BranchesOverComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentMultiplicityBranchIndexing
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackPrincipalDivisor

/-!
# The branches at a point, partitioned over the irreducible components as subspaces

`AlgebraicGeometry.Space.finsum_branch_eq_finsum_component_finsum_branch` regroups a sum over the
branches of `𝒪_{W, u}` as a sum over the irreducible components of `|X|` through the image of
`u`, the branches being indexed by `{q : PrimeSpectrum 𝒪_{W,u} // q.asIdeal ∈ minimalPrimes _}`
and the components by `irreducibleComponents (points B S hS X)`. The consumers in Stacks 0EQ2 —
`AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_finsum_branch_on_component` and
`AlgebraicGeometry.Space.PrimeDivisor.ord_eq_finsum_minimalPrimeOrd_etaleChartComp` — index the
branches by the *ideals*, `↥(minimalPrimes 𝒪_{W,u})`, and the components by the *subspaces*,
`AlgebraicGeometry.Space.IrreducibleComponentSubspace`. This file supplies the two reindexings
and the partition statement in the shape those consumers need.

## Main definitions and results

* `AlgebraicGeometry.Space.minimalPrimesEquivPrimeSpectrum`: the branches as ideals are the
  branches as points of the spectrum.
* `AlgebraicGeometry.Space.irreducibleComponentSubspaceEquiv`: Stacks 0ENF restricted to the
  irreducible components — taking the set of points is a bijection from the irreducible
  components of `X` as integral closed subspaces onto the irreducible components of `|X|`.
* `AlgebraicGeometry.Space.irreducibleComponentSubspaceThroughEquiv`: the same bijection between
  the components through a fixed point.
* `AlgebraicGeometry.Space.finsum_minimalPrimes_eq_finsum_componentSubspace`: the partition of
  the branches at a point over the irreducible components through it, with both indexings in the
  form the two order-of-vanishing formulas of Stacks 0EQ2 use.

## Implementation notes

Both reindexings are `Equiv`s and the transport is `finsum_comp_equiv`.

The surjectivity half of `AlgebraicGeometry.Space.irreducibleComponentSubspaceEquiv` is Stacks
0ENF, `AlgebraicGeometry.Space.integralClosedSubspaceOfComponent`, and the injectivity half is
`AlgebraicGeometry.Space.injective_integralClosedSubspaceSupport`; decency of `X` is needed for
the former only.

## References

* [Stacks Project, Tag 00ET](https://stacks.math.columbia.edu/tag/00ET)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 0ENF](https://stacks.math.columbia.edu/tag/0ENF)
* [Stacks Project, Tag 0EQ2](https://stacks.math.columbia.edu/tag/0EQ2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### The branches as ideals and as points of the spectrum -/

/-- The minimal primes of a commutative ring, indexed as ideals, are the minimal primes indexed
as points of the prime spectrum. The second indexing is the one
`AlgebraicGeometry.Space.componentOfBranch` and
`AlgebraicGeometry.irreducibleComponentsEquivMinimalPrimes` use, the first the one the sums of
Stacks 02QG in this repository use. -/
def minimalPrimesEquivPrimeSpectrum (R : Type*) [CommRing R] :
    ↥(minimalPrimes R) ≃ {q : PrimeSpectrum R // q.asIdeal ∈ minimalPrimes R} where
  toFun p := ⟨⟨p.1, p.2.1.1⟩, p.2⟩
  invFun q := ⟨q.1.asIdeal, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The irreducible components as subspaces and as subsets -/

section ComponentSubspaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)

/-- **Stacks 0ENF on the irreducible components.** Taking the set of points is a bijection from
the irreducible components of `X` as integral closed subspaces, Remark 0EE8 in the form
`AlgebraicGeometry.Space.IrreducibleComponentSubspace`, onto the irreducible components of
`|X|`. -/
def irreducibleComponentSubspaceEquiv :
    IrreducibleComponentSubspace B S hS hX ≃ irreducibleComponents (points B S hS X) where
  toFun V := ⟨subspacePointSet B S hS X V.1.subspace, V.2.2.2⟩
  invFun V := ⟨integralClosedSubspaceOfComponent B S hS hX hdec V,
    (integralClosedSubspaceOfComponent B S hS hX hdec V).isClosedSubspace,
    (integralClosedSubspaceOfComponent B S hS hX hdec V).isIntegralSpace, by
      rw [show Set.range (pointsMap B S hS
            (integralClosedSubspaceOfComponent B S hS hX hdec V).subspace.toFunctor
            (integralClosedSubspaceOfComponent B S hS hX hdec V).subspace.ι) =
          (V : Set (points B S hS X)) from
        subspacePointSet_integralClosedSubspaceOfComponent B S hS hX hdec V]
      exact V.2⟩
  left_inv V := by
    refine Subtype.ext (injective_integralClosedSubspaceSupport B S hS hX
      (IrreducibleCloseds.ext ?_))
    exact subspacePointSet_integralClosedSubspaceOfComponent B S hS hX hdec _
  right_inv V := Subtype.ext
    (subspacePointSet_integralClosedSubspaceOfComponent B S hS hX hdec V)

/-- **Stacks 0ENF on the irreducible components through a point.** The bijection of
`AlgebraicGeometry.Space.irreducibleComponentSubspaceEquiv` between the components containing a
fixed point of `|X|`. -/
def irreducibleComponentSubspaceThroughEquiv (x : points B S hS X) :
    {V : IrreducibleComponentSubspace B S hS hX //
        x ∈ subspacePointSet B S hS X V.1.subspace} ≃
      {V : irreducibleComponents (points B S hS X) // x ∈ (V : Set (points B S hS X))} :=
  (irreducibleComponentSubspaceEquiv B S hS hX hdec).subtypeEquiv fun _ => Iff.rfl

/-! ### The partition of the branches -/

include hX hdec in
/-- **The partition of the branches at a point over the irreducible components through it, in the
indexings Stacks 0EQ2 uses.** For `W` an étale chart of a decent algebraic space `X` over `S` and
`u` a point of its scheme, a sum over the minimal primes of `𝒪_{W, u}` — indexed as ideals, the
shape of the sum of Stacks 02QG in this repository — is the sum over the irreducible components
`X'` of `X`, taken as integral closed subspaces and restricted to those containing the image of
`u`, of the sum over the branches lying on `X'`.

This is `AlgebraicGeometry.Space.finsum_branch_eq_finsum_component_finsum_branch` reindexed on
both sums by `AlgebraicGeometry.Space.minimalPrimesEquivPrimeSpectrum` and
`AlgebraicGeometry.Space.irreducibleComponentSubspaceEquiv`. The condition cutting out the
branches lying on `X'` is written as an equality of *point sets*, which is the form
`AlgebraicGeometry.Space.ord_rationalFunctionMap_eq_finsum_branch_on_component` states its
subsum in. -/
theorem finsum_minimalPrimes_eq_finsum_componentSubspace {M : Type v} [AddCommMonoid M]
    (W : SmallEtale B S hS X) (u : chartScheme W)
    (hfin : Finite ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)))
    (F : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)) → M) :
    ∑ᶠ p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)), F p =
      ∑ᶠ V : {V : IrreducibleComponentSubspace B S hS hX //
          chartSchemeToPoints B S hS X W u ∈ subspacePointSet B S hS X V.1.subspace},
        ∑ᶠ p : {p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)) //
            ((componentOfBranch B S hS hX hdec W u
                (minimalPrimesEquivPrimeSpectrum _ p)).1 :
              irreducibleComponents (points B S hS X)).1 =
              subspacePointSet B S hS X V.1.1.subspace},
          F p.1 := by
  classical
  set e := minimalPrimesEquivPrimeSpectrum ((chartScheme W).presheaf.stalk u) with he
  set ec := irreducibleComponentSubspaceThroughEquiv B S hS hX hdec
    (chartSchemeToPoints B S hS X W u) with hec
  set cob := componentOfBranch B S hS hX hdec W u with hcob
  have hfin' : Finite {q : PrimeSpectrum ((chartScheme W).presheaf.stalk u) //
      q.asIdeal ∈ minimalPrimes ((chartScheme W).presheaf.stalk u)} :=
    Finite.of_equiv _ e
  -- the condition on a branch of lying on a given component, in the two indexings
  have hiff : ∀ (V : {V : IrreducibleComponentSubspace B S hS hX //
        chartSchemeToPoints B S hS X W u ∈ subspacePointSet B S hS X V.1.subspace})
      (p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u))),
      ((cob (e p)).1 : irreducibleComponents (points B S hS X)).1 =
          subspacePointSet B S hS X V.1.1.subspace ↔ cob (e p) = ec V := by
    refine fun V p => ⟨fun h => Subtype.ext (Subtype.ext h), fun h => ?_⟩
    exact congrArg (fun T : irreducibleComponents (points B S hS X) =>
      (T : Set (points B S hS X))) (congrArg Subtype.val h)
  have h1 := (finsum_comp_equiv e.symm (f := F)).symm
  have h2 := finsum_branch_eq_finsum_component_finsum_branch B S hS hX hdec W u hfin'
    (fun q => F (e.symm q))
  have h3 : ∑ᶠ V' : {V' : irreducibleComponents (points B S hS X) //
        chartSchemeToPoints B S hS X W u ∈ (V' : Set (points B S hS X))},
        ∑ᶠ q : {q // cob q = V'}, F (e.symm q.1) =
      ∑ᶠ V : {V : IrreducibleComponentSubspace B S hS hX //
        chartSchemeToPoints B S hS X W u ∈ subspacePointSet B S hS X V.1.subspace},
        ∑ᶠ q : {q // cob q = ec V}, F (e.symm q.1) :=
    (finsum_comp_equiv ec
      (f := fun V' => ∑ᶠ q : {q // cob q = V'}, F (e.symm q.1))).symm
  rw [h1, h2, h3]
  refine finsum_congr fun V => ?_
  have hstep : ∑ᶠ p : {p : ↥(minimalPrimes ((chartScheme W).presheaf.stalk u)) //
        ((cob (e p)).1 : irreducibleComponents (points B S hS X)).1 =
          subspacePointSet B S hS X V.1.1.subspace}, F p.1 =
      ∑ᶠ q : {q // cob q = ec V}, F (e.symm q.1) := by
    exact (finsum_comp_equiv (Equiv.subtypeEquiv e (hiff V)).symm
      (f := fun p => F p.1)).symm
  exact hstep.symm

end ComponentSubspaces

end AlgebraicGeometry.Space

end
