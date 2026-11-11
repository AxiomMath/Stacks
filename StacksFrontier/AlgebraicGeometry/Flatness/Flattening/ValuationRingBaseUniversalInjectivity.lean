module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.ContentIdeal
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PolynomialLocalizationReduction
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ValuationRingBase
public import StacksFrontier.RingTheory.Valuation.ContentIdealExistence

/-!
# The lemma of Situation 0AT0 over a valuation ring

Stacks 0AT5: if in Situation 0AT0 the ring `A` is a valuation ring, then the lemma holds, that
is `u : N → M` is `A`-universally injective, `N` is of finite presentation over `B`, and `N` is
flat over `A`.

Flatness and finite presentation are `AlgebraicGeometry.flat_of_valuationRing` and
`AlgebraicGeometry.finitePresentation_of_valuationRing`
(`StacksFrontier.AlgebraicGeometry.Flatness.Flattening.ValuationRingBase`), following the first
paragraph of the source's proof. This file proves the remaining assertion, universal
injectivity, and states the three together.

## The argument

Let `J ⊆ A` be an ideal and `x ∈ N` with `u(x) ∈ J M`. Since `N` is `A`-flat, Stacks 0ASX gives
`x` a content ideal `I`, and Stacks 0ASC shows that `u(x)` has content ideal `I` as well, so
`I ⊆ J` and `x ∈ I N ⊆ J N`. Hence `N/JN → M/JM` is injective for every ideal `J`, as in the
second paragraph of the source's proof.

The source then concludes with the criterion of Stacks 058K and the structure of finitely
presented modules over a valuation ring (Stacks 0ASP). Here the conclusion is drawn instead from
the cokernel: taking `J = 0` shows `u` is injective, and taking `J = (a)` shows that
`M/u(N)` is torsion free, because `a m = u(x)` forces `x = a y` and then `a (m - u(y)) = 0` in the
torsion free module `M`. Over the valuation ring `A` a torsion free module is flat
(`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout`), and an injective map whose cokernel is flat
is universally injective (`LinearMap.lTensor_injective_of_exact_of_flat`).

## Main results

* `AlgebraicGeometry.universallyInjective_of_valuationRing`: `u` is `A`-universally injective.
* `AlgebraicGeometry.injectiveModuloMaximalIdealConclusion_of_valuationRing`: Stacks 0AT5, the
  three assertions together.

## References

* [Stacks Project, Tag 0AT5](https://stacks.math.columbia.edu/tag/0AT5)
* [Stacks Project, Tag 0AT0](https://stacks.math.columbia.edu/tag/0AT0)
* [Stacks Project, Tag 0ASX](https://stacks.math.columbia.edu/tag/0ASX)
* [Stacks Project, Tag 0ASC](https://stacks.math.columbia.edu/tag/0ASC)
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅

namespace AlgebraicGeometry

/-- In Situation 0AT0 over a valuation ring, `u(x) ∈ J M` implies `x ∈ J N` for every ideal
`J ⊆ A`: the content ideal of `x` (Stacks 0ASX) is also that of `u(x)` (Stacks 0ASC). -/
theorem mem_smul_top_of_map_mem_smul_top_of_valuationRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsDomain S.A] [ValuationRing S.A] (J : Ideal S.A) {x : S.N}
    (hx : S.u x ∈ J • (⊤ : Submodule S.A S.M)) : x ∈ J • (⊤ : Submodule S.A S.N) := by
  have := flat_of_valuationRing S
  obtain ⟨I, hI, -⟩ :=
    exists_isContentIdeal_isPrincipal_of_valuationRing_of_flat (A := S.A) (B := S.B) x
  have hIu := isContentIdeal_map_of_injective_mapQ_maximalIdeal S.u
    S.injective_mod_maximalIdeal hI
  exact Submodule.smul_mono_left (hIu.le_of_mem_smul_top hx) hI.mem_smul_top

/-- In Situation 0AT0 over a valuation ring, the cokernel `M/u(N)` is torsion free, hence flat
over `A`. -/
theorem flat_quotient_range_of_valuationRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsDomain S.A] [ValuationRing S.A] :
    Module.Flat S.A (S.M ⧸ LinearMap.range S.u) := by
  have : Module.IsTorsionFree S.A S.M := Module.Flat.isTorsionFree
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  intro z hz
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ha⟩, ham⟩ := (Submodule.mem_torsion_iff _).mp hz
  have hmem : a • m ∈ LinearMap.range S.u := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
    exact ham
  obtain ⟨x, hx⟩ := hmem
  have hxa : x ∈ (Ideal.span {a} : Ideal S.A) • (⊤ : Submodule S.A S.N) := by
    refine mem_smul_top_of_map_mem_smul_top_of_valuationRing S _ ?_
    rw [hx]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a) Submodule.mem_top
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hxa
  obtain ⟨y, -, rfl⟩ := hxa
  have hsub : a • (S.u y - m) = 0 := by
    rw [smul_sub, ← S.u.map_smul, hx, sub_self]
  have hym : S.u y = m :=
    sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left (mem_nonZeroDivisors_iff_ne_zero.mp ha))
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, ← hym]
  exact LinearMap.mem_range_self S.u y

/-- **Stacks Project, Tag 0AT5 (universal injectivity).** In Situation 0AT0 with the base ring
`A` a valuation ring, the map `u : N → M` is `A`-universally injective. -/
@[stacks 0AT5 "universal injectivity"]
theorem universallyInjective_of_valuationRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsDomain S.A] [ValuationRing S.A] : UniversallyInjectivePoly.{_, u₅} S.u := by
  have hinj : Function.Injective S.u := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := mem_smul_top_of_map_mem_smul_top_of_valuationRing S ⊥ (x := x)
      (by rw [hx]; exact Submodule.zero_mem _)
    simpa [Submodule.bot_smul] using h
  have := flat_quotient_range_of_valuationRing S
  intro Q _ _ x y hxy
  apply (TensorProduct.comm S.A S.N Q).injective
  apply LinearMap.lTensor_injective_of_exact_of_flat (LinearMap.range S.u).mkQ
    (Submodule.mkQ_surjective _) S.u hinj (LinearMap.exact_map_mkQ_range S.u) Q
  rw [LinearMap.lTensor_comm, LinearMap.lTensor_comm, hxy]

/-- **Stacks Project, Tag 0AT5.** If in Situation 0AT0 the ring `A` is a valuation ring, then the
lemma holds: `u : N → M` is `A`-universally injective, `N` is of finite presentation over `B`,
and `N` is flat over `A`. -/
@[stacks 0AT5]
theorem injectiveModuloMaximalIdealConclusion_of_valuationRing
    (S : InjectiveModuloMaximalIdealSituation.{u₁, u₂, u₃, u₄})
    [IsDomain S.A] [ValuationRing S.A] : InjectiveModuloMaximalIdealConclusion.{u₅} S :=
  ⟨universallyInjective_of_valuationRing S, finitePresentation_of_valuationRing S,
    flat_of_valuationRing S⟩

end AlgebraicGeometry

end
