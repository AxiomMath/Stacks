module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentCoefficient
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.CoordinateFromRatio
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.RatioPullback
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.SectionRatioChart

/-!
# The local ratio on a component computes the order of vanishing of the restricted section

This file relates, as in part (4) of [Stacks, Tag 02SW], the orders of vanishing of the
numerator and the denominator of a local ratio of `s` to the order of vanishing of the restricted
section `sη` of `ℒ|_{Xη}`.

Let `ξ` be a point of delta-dimension `k` and `η` the generic point of an irreducible component
of `X` of delta-dimension `k + 1` through `ξ`, let `Xη` be the integral closed subscheme supported
on the closure of `η`, and let `z` be the point of `Xη` over `ξ`. Over an affine open `V ∋ ξ` the
section is a ratio `a / b` against a trivializing section `e` of `ℒ`, that is

  `a · e = b · s`   in   `Γ(𝒦_X(ℒ), V)`.

Pulling this back along `Xη → X` gives the same identity over `Xη` between `sη`, the restrictions
of `a` and `b`, and the restriction of `e`, which still generates the stalk. So `a|_{Xη} / b|_{Xη}`
is a coordinate of `sη` at `z` and

  `ord_{Xη, ξ}(a) - ord_{Xη, ξ}(b) = ord_{Xη, ℒ|_{Xη}}(sη)`,

which is the coefficient at `ξ` of `(Xη → X)_* div_{ℒ|_{Xη}}(sη)`.

## Main results

* `Stacks.Chow.isStalkBasis_pullbackUnit` — the restriction of a trivializing section to a
  closed subscheme still generates the stalk.
* `Stacks.Chow.smul_componentMeromorphicSection_eq` — the restricted ratio identity.
* `Stacks.Chow.germToFunctionField_subschemeι_app_ne_zero` — a section with nonzerodivisor germ
  at `ξ` restricts to a nonzero rational function on the component.
* `Stacks.Chow.coheight_eq_one_of_relativeDimension` — a point of the component over a point of
  delta-dimension `k` has coheight one in the component.
* `Stacks.Chow.ord_sub_eq_componentDivisorCycle_apply`,
  `Stacks.Chow.componentOrdAt_sub_eq_componentDivisorCycle_apply` — the identity
  `ord_{Xη, ξ}(a) - ord_{Xη, ξ}(b) = ((Xη → X)_* div_{ℒ|_{Xη}}(sη))_ξ`.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02SF](https://stacks.math.columbia.edu/tag/02SF)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order Topology TopologicalSpace
open Stacks.DenominatorIdeal (sectionMap toK)

universe u

namespace Stacks.Chow

/-! ### The restriction of a trivializing section -/

/-- **The restriction of a trivializing section still generates the stalk.** If the germ of `e` at
`ι z` is a basis of the stalk of `ℒ` there, then the germ at `z` of the pullback of `e` is a basis
of the stalk of `ι^* ℒ`. -/
theorem isStalkBasis_pullbackUnit {W X : Scheme.{u}} (ι : W ⟶ X) (L : X.Modules) {V : X.Opens}
    {z : W} (hz : ι.base z ∈ V) (e : Γ(L, V))
    (he : Stacks.Divisors.IsStalkBasis L (ι.base z) ((L.presheaf.germ V (ι.base z) hz).hom e)) :
    Stacks.Divisors.IsStalkBasis ((Scheme.Modules.pullback ι).obj L) z
      ((((Scheme.Modules.pullback ι).obj L).presheaf.germ (ι ⁻¹ᵁ V) z hz).hom
        (Stacks.RingedSpace.pullbackUnit ι.toLRSHom.toShHom L (op V) e)) :=
  AlgebraicGeometry.bijective_smul_germ_pullbackUnit' ι.toLRSHom L z V hz e he

/-! ### The restricted ratio -/

/-- **The ratio identity restricts to a closed subscheme.** Applying the pullback of meromorphic
sections to `a · e = b · s` gives the same identity over `ι⁻¹V` between the restriction of `s`
and the restrictions of `a`, `b` and `e`. -/
theorem smul_componentMeromorphicSection_eq {W X : Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
    (ι : W ⟶ X) (hι : PullbacksMeromorphicSections ι.toLRSHom) (L : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L) {V : X.Opens} {a b : Γ(X, V)}
    {e : Γ(L, V)}
    (hbt : (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b) :
    structureScalar (ι ⁻¹ᵁ V) ((ι.app V).hom b) •
        meromorphicValue ((Scheme.Modules.pullback ι).obj L)
          (AlgebraicGeometry.pullbackMeromorphicSection ι.toLRSHom hι L s) (ι ⁻¹ᵁ V) =
      structureScalar (ι ⁻¹ᵁ V) ((ι.app V).hom a) •
        ((Stacks.Divisors.toMeromorphicSectionSheaf W.sheaf
            ((Scheme.Modules.pullback ι).obj L)).app (op (ι ⁻¹ᵁ V))).hom
          (Stacks.RingedSpace.pullbackUnit ι.toLRSHom.toShHom L (op V) e) := by
  refine Eq.trans (congrArg
    (fun y : ↑((Stacks.Divisors.meromorphicSectionRestrict W.sheaf
        ((Scheme.Modules.pullback ι).obj L)).obj (op (ι ⁻¹ᵁ V))) =>
      structureScalar (ι ⁻¹ᵁ V) ((ι.app V).hom b) • y)
    (meromorphicValue_eq ((Scheme.Modules.pullback ι).obj L)
      (AlgebraicGeometry.pullbackMeromorphicSection ι.toLRSHom hι L s) (ι ⁻¹ᵁ V)))
    (AlgebraicGeometry.smul_pullbackMeromorphicSection_val_eq hι L s e b a hbt.symm)

/-! ### Nonvanishing of the restricted ratio -/

/-- If the ideal sheaf of an integral closed subscheme has a minimal prime as its stalk at `ξ`, a
section whose germ at `ξ` is a nonzerodivisor restricts to a nonzero rational function on the
subscheme. -/
theorem germToFunctionField_subschemeι_app_ne_zero {X : Scheme.{u}} (Z : X.IdealSheafData)
    [AlgebraicGeometry.IsIntegral Z.subscheme] {ξ : X} {V : X.Opens} (hξV : ξ ∈ V)
    (hgen : genericPoint Z.subscheme ∈ (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens))
    [Nonempty (Z.subschemeι ⁻¹ᵁ V : Z.subscheme.Opens)]
    (hmin : Z.stalkIdeal ξ ∈ minimalPrimes (X.presheaf.stalk ξ)) {t : Γ(X, V)}
    (ht : (X.presheaf.germ V ξ hξV).hom t ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (z : Z.subscheme) (hz : Z.subschemeι z = ξ) :
    Z.subscheme.germToFunctionField (Z.subschemeι ⁻¹ᵁ V) ((Z.subschemeι.app V).hom t) ≠ 0 := by
  subst hz
  have hnotMem : (X.presheaf.germ V (Z.subschemeι z) hξV).hom t ∉
      Z.stalkIdeal (Z.subschemeι z) := fun hmem =>
    notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hmem hmin ht
  have ht0 : (Z.subschemeι.app V).hom t ≠ 0 :=
    subschemeι_app_ne_zero_of_germ_notMem_stalkIdeal Z z hξV hnotMem
  intro h0
  exact ht0 (germ_injective_of_isIntegral Z.subscheme (genericPoint Z.subscheme) hgen
    (by simpa using h0))

/-! ### The identity -/

variable {X : Scheme.{u}}

/-- If `η` has delta-dimension `k + 1`, a point of the integral closed subscheme through `η` lying
over a point of delta-dimension `k` has coheight one in that subscheme. -/
theorem coheight_eq_one_of_relativeDimension (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] {k : ℤ} {η : X}
    (hδη : relativeDimension C.dimensionFunction f η = k + 1)
    [AlgebraicGeometry.IsIntegral (integralComponentAt η).subscheme]
    (z : (integralComponentAt η).subscheme) {ξ : X}
    (hz : (integralComponentAt η).subschemeι z = ξ)
    (hδξ : relativeDimension C.dimensionFunction f ξ = k) :
    Order.coheight z = 1 := by
  subst hz
  exact (relativeDimension_eq_sub_one_iff_coheight_eq_one C
    ((integralComponentAt η).subschemeι ≫ f)
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδη) z).1 (by
      rw [relativeDimension_comp_closedImmersion C.dimensionFunction
        (integralComponentAt η).subschemeι f z, hδξ]
      ring)

/-- The difference of the orders of vanishing at `z` of the restrictions of `a` and `b` to the
component `Stacks.Chow.integralComponentAt η` is the coefficient at `ξ` of the pushforward of the
divisor of the restricted section, where `z` is a point of the component over `ξ`, `a · e = b · s`
over `V`, `e` generates the stalk of `ℒ` at `ξ` and the component cuts out a minimal prime at
`ξ`. -/
theorem ord_sub_eq_componentDivisorCycle_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (L : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) {k : ℤ} {η : X}
    (hη : η ∈ genericPoints X)
    (hδη : relativeDimension C.dimensionFunction f η = k + 1)
    [AlgebraicGeometry.IsIntegral (integralComponentAt η).subscheme]
    [IsLocallyNoetherian (integralComponentAt η).subscheme]
    (z : (integralComponentAt η).subscheme) {ξ : X}
    (hz : (integralComponentAt η).subschemeι z = ξ)
    (hδξ : relativeDimension C.dimensionFunction f ξ = k)
    (hmin : (integralComponentAt η).stalkIdeal ξ ∈ minimalPrimes (X.presheaf.stalk ξ))
    {V : X.Opens} (hξV : ξ ∈ V)
    [Nonempty ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
      (integralComponentAt η).subscheme.Opens)]
    {a b : Γ(X, V)} {e : Γ(L, V)}
    (hbas : Stacks.Divisors.IsStalkBasis L ξ ((L.presheaf.germ V ξ hξV).hom e))
    (hbt : (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b)
    (ha : (X.presheaf.germ V ξ hξV).hom a ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (hb : (X.presheaf.germ V ξ hξV).hom b ∈ nonZeroDivisors (X.presheaf.stalk ξ)) :
    (integralComponentAt η).subscheme.ord
          ((integralComponentAt η).subscheme.germToFunctionField
            ((integralComponentAt η).subschemeι ⁻¹ᵁ V)
            (((integralComponentAt η).subschemeι.app V).hom a)) z -
        (integralComponentAt η).subscheme.ord
          ((integralComponentAt η).subscheme.germToFunctionField
            ((integralComponentAt η).subschemeι ⁻¹ᵁ V)
            (((integralComponentAt η).subschemeι.app V).hom b)) z =
      (componentDivisorCycle C f L s hL hs hη hδη).1 ξ := by
  subst hz
  have hinv := isInvertible_componentModule L hL η
  have hqc := AlgebraicGeometry.isQuasicoherent_of_isInvertible
    ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
  have hdimZ := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδη
  have hmemcl : (integralComponentAt η).subschemeι.base z ∈ closure ({η} : Set X) := by
    rw [← coe_support_integralComponentAt η, ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hηV : η ∈ V := (specializes_iff_mem_closure.mpr hmemcl).mem_open V.isOpen hξV
  have hgen : genericPoint (integralComponentAt η).subscheme ∈
      ((integralComponentAt η).subschemeι ⁻¹ᵁ V : (integralComponentAt η).subscheme.Opens) := by
    simpa [subschemeι_genericPoint_integralComponentAt η] using hηV
  have hco : Order.coheight z = 1 :=
    coheight_eq_one_of_relativeDimension C f hδη z rfl hδξ
  have hord := ord_sub_eq_orderOfVanishingMeromorphic
    ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
    (componentMeromorphicSection L s hη)
    (isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη) hgen hξV hco
    (isStalkBasis_pullbackUnit (integralComponentAt η).subschemeι L hξV e hbas)
    (germToFunctionField_subschemeι_app_ne_zero (integralComponentAt η) hξV hgen hmin ha z rfl)
    (germToFunctionField_subschemeι_app_ne_zero (integralComponentAt η) hξV hgen hmin hb z rfl)
    (smul_componentMeromorphicSection_eq (integralComponentAt η).subschemeι
      (pullbacksMeromorphicSections_subschemeι_integralComponentAt hη) L s hbt)
  refine Eq.trans hord ?_
  refine Eq.trans
    (componentDivisorCycleOn_apply_of_coheight_eq_one C f L s hL hs hη hδη z hco).symm ?_
  exact (componentDivisorCycle_apply_image C f L s hL hs hη hδη z).symm

/-- Part (4) of [Stacks, Tag 02SW], at one point and one component:
`ord_{Xη, ξ}(a) - ord_{Xη, ξ}(b)` is the coefficient at `ξ` of `(Xη → X)_* div_{ℒ|_{Xη}}(sη)`,
for `η ⤳ ξ` of delta-dimensions `k + 1` and `k`. -/
theorem componentOrdAt_sub_eq_componentDivisorCycle_apply (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (L : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) {k : ℤ} {ξ η : X}
    (hη : η ∈ genericPoints X)
    (hδη : relativeDimension C.dimensionFunction f η = k + 1)
    (hspec : η ⤳ ξ)
    (hδξ : relativeDimension C.dimensionFunction f ξ = k)
    (hmin : (integralComponentAt η).stalkIdeal ξ ∈ minimalPrimes (X.presheaf.stalk ξ))
    {V : X.Opens} (hξV : ξ ∈ V) {a b : Γ(X, V)} {e : Γ(L, V)}
    (hbas : Stacks.Divisors.IsStalkBasis L ξ ((L.presheaf.germ V ξ hξV).hom e))
    (hbt : (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b)
    (ha : (X.presheaf.germ V ξ hξV).hom a ∈ nonZeroDivisors (X.presheaf.stalk ξ))
    (hb : (X.presheaf.germ V ξ hξV).hom b ∈ nonZeroDivisors (X.presheaf.stalk ξ)) :
    @componentOrdAt X (LocallyOfFiniteType.isLocallyNoetherian f) ξ η V hξV a -
        @componentOrdAt X (LocallyOfFiniteType.isLocallyNoetherian f) ξ η V hξV b =
      (componentDivisorCycle C f L s hL hs hη hδη).1 ξ := by
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  have := isIntegral_integralComponentAt η
  have := (integralComponentAt η).isLocallyNoetherian_subscheme
  have hex : ∃ w : (integralComponentAt η).subscheme,
      (integralComponentAt η).subschemeι w = ξ := by
    have hmem : ξ ∈ Set.range (integralComponentAt η).subschemeι.base := by
      rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt]
      exact specializes_iff_mem_closure.mp hspec
    exact hmem
  have hzV : hex.choose ∈ ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
      (integralComponentAt η).subscheme.Opens) := by
    simpa [hex.choose_spec] using hξV
  have : Nonempty ((integralComponentAt η).subschemeι ⁻¹ᵁ V :
    (integralComponentAt η).subscheme.Opens) := ⟨⟨hex.choose, hzV⟩⟩
  rw [componentOrdAt_eq ξ η hξV a hex, componentOrdAt_eq ξ η hξV b hex]
  exact ord_sub_eq_componentDivisorCycle_apply C f L s hL hs hη hδη hex.choose
    hex.choose_spec hδξ hmin hξV hbas hbt ha hb

end Stacks.Chow

end
