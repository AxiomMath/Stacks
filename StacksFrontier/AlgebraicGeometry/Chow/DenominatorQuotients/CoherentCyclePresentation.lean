module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# The cycle of a coherent sheaf as a locally finite sum of integral components

The cap-product formula of [Stacks, Tag 02SO] —
`Stacks.Chow.firstChernClassCapOfInvertible_finsum` — consumes a `k`-cycle **presented** as a
locally finite combination `α = ∑ⱼ nⱼ [Wⱼ]` of fundamental cycles of integral closed subschemes
of delta-dimension `k`. This file supplies that presentation for the cycle
`[ℱ]_k = Stacks.Chow.cycleAssociatedToCoherentSheaf` of a coherent sheaf:

  `[ℱ]_k = ∑_ξ mult(ℱ, ξ) · [closure {ξ}]`,

the sum being over the points `ξ` of the support of `ℱ` of relative dimension `k`, each of which
is the generic point of an irreducible component of the support.

`StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle` does exactly this for
the cycle of a *closed subscheme*; nothing there applies to a coherent sheaf, and the only bridge
between the two cycles,
`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_cycleAssociatedToCoherentSheaf`, goes the other
way and only for a structure sheaf. So the apparatus is rebuilt here, with that
file as the template.

## Main definitions

* `Stacks.Chow.topSupportPoints` — the index: the points of the support of `ℱ` of relative
  dimension `k`.
* `Stacks.Chow.topSupportSubscheme` — the integral closed subscheme attached to such a point, the
  reduced structure on the closure of it.

## Main results

* `Stacks.Chow.isIntegral_topSupportSubscheme`,
  `Stacks.Chow.schemeDeltaDimension_topSupportSubscheme`,
  `Stacks.Chow.genericPointOf_topSupportSubscheme` — the three properties of each member that the
  cap-product formula asks for.
* `Stacks.Chow.locallyFinite_topSupportSubscheme` — the family is locally finite.
* `Stacks.Chow.cycleAssociatedToCoherentSheaf_apply_eq_finsum` — the presentation, coefficientwise.

## Implementation notes

**The index is by generic points, not by components.** The template indexes by
`irreducibleComponents` of the ambient scheme and packages each as a closed irreducible subset in
order to speak of its `deltaDimension`. Here the support is a *subspace*, so that packaging would
have to be redone, and it is avoidable: a point determines its component
(`Stacks.Chow.integralComponentAt` is the reduced structure on its closure) and the relative
dimension of the point is directly what
`Stacks.Chow.schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq` consumes. So the
index carries the two conditions on a point and every member property is one rewrite.

Local finiteness is the only place the component picture is still needed: the family of closures
is carried into the family of irreducible components of the support by
`Stacks.Chow.isGenericPoint_component_supp_of_relativeDimension_eq` (Stacks 02QW (3)), injectively
because a component has a unique generic point, and that family is locally finite by
`Stacks.Chow.locallyFinite_irreducibleComponents_supp` (Stacks 02QW (1)). This is where the
dimension bound `hFk` is used; the other statements do not need it.

The coefficientwise identity collapses the sum at each point: the fundamental cycle of an integral
closed subscheme is `1` at its generic point and `0` elsewhere (Stacks 02QU,
`Stacks.Chow.cycleAssociatedToClosedSubscheme_integral_apply` and `..._integral_apply_of_ne`), so
at a point of the index the sum has one surviving term and off the index every term vanishes.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 02QX](https://stacks.math.columbia.edu/tag/02QX)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (F : X.Modules) [F.IsCoherent] (k : ℤ)

/-- **The index of the presentation of `[ℱ]_k`**: the points of the support of `ℱ` whose relative
dimension over the base is `k`. Each is the generic point of an irreducible component of the
support, by Stacks 02QW (3). -/
def topSupportPoints : Type u :=
  {ξ : X // ξ ∈ SheafOfModules.supp F ∧ relativeDimension C.dimensionFunction f ξ = k}

/-- The integral closed subscheme of `X` attached to a point of the index: the reduced structure
on the closure of it. -/
def topSupportSubscheme (j : topSupportPoints C f F k) : X.IdealSheafData :=
  integralComponentAt j.1

omit [LocallyOfFiniteType f] [SheafOfModules.IsCoherent F] in
/-- The member subschemes are integral. -/
theorem isIntegral_topSupportSubscheme (j : topSupportPoints C f F k) :
    IsIntegral (topSupportSubscheme C f F k j).subscheme :=
  isIntegral_integralComponentAt _

omit [LocallyOfFiniteType f] [SheafOfModules.IsCoherent F] in
/-- The member subschemes are supported on the closure of the point. -/
theorem coe_support_topSupportSubscheme (j : topSupportPoints C f F k) :
    ((topSupportSubscheme C f F k j).support : Set X) = closure {j.1} :=
  coe_support_integralComponentAt _

omit [SheafOfModules.IsCoherent F] in
/-- The member subschemes have delta-dimension `k` over the base. -/
theorem schemeDeltaDimension_topSupportSubscheme (j : topSupportPoints C f F k) :
    schemeDeltaDimension C ((topSupportSubscheme C f F k j).subschemeι ≫ f) = (k : EInt) :=
  schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f j.1 j.2.2

omit [LocallyOfFiniteType f] [SheafOfModules.IsCoherent F] in
/-- The generic point of a member subscheme is the point it came from. -/
theorem genericPointOf_topSupportSubscheme (j : topSupportPoints C f F k) :
    genericPointOf (topSupportSubscheme C f F k j) (isIntegral_topSupportSubscheme C f F k j) =
      j.1 :=
  genericPointOf_integralComponentAt _

/-- **The family of member subschemes is locally finite.** Each closure is an irreducible
component of the support of `ℱ`, distinct points give distinct components, and the components of
the support of a coherent sheaf on a locally Noetherian scheme are locally finite by Stacks
02QW (1). -/
theorem locallyFinite_topSupportSubscheme
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) :
    LocallyFinite fun j : topSupportPoints C f F k =>
      ((topSupportSubscheme C f F k j).support : Set X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  choose Z hZ using fun j : topSupportPoints C f F k =>
    isGenericPoint_component_supp_of_relativeDimension_eq C f F k j.1 hFk j.2.1 j.2.2
  have hinj : Function.Injective Z := by
    intro j₁ j₂ h
    refine Subtype.ext ?_
    have h1 := hZ j₁
    rw [h] at h1
    exact h1.eq (hZ j₂)
  refine ((locallyFinite_irreducibleComponents_supp F).comp_injective hinj).subset fun j => ?_
  rw [coe_support_topSupportSubscheme]
  exact (hZ j).subset

/-- **The cycle of a coherent sheaf, presented coefficientwise as a locally finite combination of
fundamental cycles of integral closed subschemes.** This is the `hα` that
`Stacks.Chow.firstChernClassCapOfInvertible_finsum` consumes, at each point. -/
theorem cycleAssociatedToCoherentSheaf_apply_eq_finsum
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt)) (x : X) :
    (cycleAssociatedToCoherentSheaf C f F k hFk).1 x =
      ∑ᶠ j : topSupportPoints C f F k, sheafMultiplicity F j.1 *
        (cycleAssociatedToClosedSubscheme C f
          (topSupportSubscheme C f F k j).subschemeι k).1 x := by
  classical
  rw [cycleAssociatedToCoherentSheaf_apply]
  have hzero : ∀ j : topSupportPoints C f F k, x ≠ j.1 →
      sheafMultiplicity F j.1 *
        (cycleAssociatedToClosedSubscheme C f
          (topSupportSubscheme C f F k j).subschemeι k).1 x = 0 := by
    intro j hne
    refine mul_eq_zero_of_right _ (cycleAssociatedToClosedSubscheme_integral_apply_of_ne C f
      (topSupportSubscheme C f F k j) (isIntegral_topSupportSubscheme C f F k j) k ?_)
    intro h
    exact hne (h.trans (genericPointOf_topSupportSubscheme C f F k j))
  split_ifs with hx
  · refine Eq.trans ?_ (finsum_eq_single _ (⟨x, hx⟩ : topSupportPoints C f F k)
      (fun j hj => hzero j fun h => hj (Subtype.ext h.symm))).symm
    refine (mul_one _).symm.trans (congrArg (fun z : ℤ => sheafMultiplicity F x * z) ?_)
    refine (cycleAssociatedToClosedSubscheme_integral_apply C f
      (topSupportSubscheme C f F k ⟨x, hx⟩) (isIntegral_topSupportSubscheme C f F k ⟨x, hx⟩)
      (schemeDeltaDimension_topSupportSubscheme C f F k ⟨x, hx⟩)).symm.trans ?_
    exact congrArg _ (genericPointOf_topSupportSubscheme C f F k ⟨x, hx⟩)
  · refine (finsum_eq_zero_of_forall_eq_zero fun j => hzero j fun h => hx ?_).symm
    rw [h]
    exact j.2

end Stacks.Chow

end
