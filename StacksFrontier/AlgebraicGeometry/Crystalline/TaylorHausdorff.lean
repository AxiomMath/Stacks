module

public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorFormula

/-!
# The `p`-adic topology of [Stacks, Tag 07JH] is discrete, and Taylor sums are unique

Several statements of the Taylor section of this chapter carry a hypothesis `huniq`: that the sum
of a Taylor series is unique.  That is Hausdorffness of the `p`-adic topology of `B ⊗_D M`, and the
reason it was carried rather than discharged is recorded in
`Crystalline.pPowSmul_eq_bot_of_pow_eq_zero`: "What is proved here is the algebraic half of that;
the step from a basic neighbourhood equal to `⊥` to `T2Space` needs the topological group structure
of `Ideal.adicModuleTopology`, which this library does not set up."

**This module sets it up and discharges the hypothesis.**  Mathlib's `Ideal.adicModuleTopology` is
built from a `SubmodulesBasis`, whose `ModuleFilterBasis` carries
`AddGroupFilterBasis.isTopologicalAddGroup`, and whose `SubmodulesBasis.openAddSubgroup` makes each
`I^n M` an open subgroup.  So when `I^N M = ⊥` the singleton `{0}` is open and
`discreteTopology_iff_isOpen_singleton_zero` applies: the topology is discrete, hence Hausdorff,
hence `HasSum.unique` is available.  In the setting of [Stacks, Tag 07JH] the hypothesis of that
chain is nilpotence of `p` in `B`, which is part of the definition of a divided power thickening in
[Stacks, Tag 07HM] and so holds for every object of `Cris(X/S)`.

## Main results

* `Crystalline.discreteTopology_adicModuleTopology_of_eq_bot` — the `I`-adic topology of a module
  is discrete as soon as one of its basic neighbourhoods of `0` is the zero submodule.
* `Crystalline.discreteTopology_pAdic_of_pow_eq_zero` and
  `Crystalline.t2Space_pAdic_of_pow_eq_zero` — the same for the `p`-adic topology, from `p^N = 0`,
  via `Crystalline.pPowSmul_eq_bot_of_pow_eq_zero`.
* `Crystalline.hasTaylorSum_unique` — **the sum of a Taylor series of [Stacks, Tag 07JH] is
  unique** when `p^N = 0` in `B`.  This is the hypothesis `huniq` of
  `Crystalline.taylorSum_smul_eq_of_isTaylorComparison` and of
  `Crystalline.ringHom_eq_algebraMap_of_untwisted`, discharged.
* `Crystalline.taylorSum_smul_eq_of_isTaylorComparison_of_pow_eq_zero` and
  `Crystalline.ringHom_eq_algebraMap_of_untwisted_self_of_pow_eq_zero` — those two theorems with
  `huniq` removed.  The second is **the defect of `Crystalline.IsTaylorComparison` with nothing
  carried but the source's own hypotheses**: in the tag's setting, a twisted comparison that also
  satisfies the untwisted identity forces `f = algebraMap`.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Nothing here is about crystals in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`.

**Hypotheses carried.**  One, and it is the source's own: `hpB`, that `p^N = 0` in `B`, which
[Stacks, Tag 07HM] requires of every divided power thickening.  Nothing else is assumed; the
`huniq` of the theorems quoted above is *removed* here rather than replaced.

**A note elsewhere that this module invalidates.**  Three docstrings say that the passage from
`Crystalline.pPowSmul_eq_bot_of_pow_eq_zero` to `T2Space` "needs the topological group structure of
`Ideal.adicModuleTopology`, which this library does not set up": the module documentation and the
docstring of `Crystalline.pPowSmul_eq_bot_of_pow_eq_zero` in
`StacksFrontier/AlgebraicGeometry/Crystalline/TaylorConvergence.lean`, and the `huniq` entry of the
module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/TwistedTaylorComparison.lean`.  The structure is
Mathlib's and needed no setting up, only locating; those notes are out of date.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open scoped TensorProduct

universe u uI w

namespace Crystalline

/-! ### The adic topology of a module with a vanishing basic neighbourhood is discrete -/

section Discrete

/-- **The `I`-adic topology of a module is discrete as soon as `I^N M = ⊥`.**  The submodules
`I^n M` are a basis of neighbourhoods of `0` for `Ideal.adicModuleTopology`, and
`SubmodulesBasis.openAddSubgroup` presents each of them as an *open* subgroup; the topology is an
additive group topology because the basis is a `ModuleFilterBasis`.  So if one of the basic
neighbourhoods is `⊥` then `{0}` is open, which for a topological additive group is
discreteness. -/
theorem discreteTopology_adicModuleTopology_of_eq_bot {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type w) [AddCommGroup M] [Module R M] {N : ℕ}
    (hI : I ^ N • (⊤ : Submodule R M) = ⊥) :
    @DiscreteTopology M (Ideal.adicModuleTopology I M) := by
  let := I.adicTopology
  let := Ideal.adicModuleTopology I M
  have hbas := I.ringFilterBasis.submodulesBasisIsBasis (I.adic_module_basis M)
  have hopen : IsOpen ((I ^ N • (⊤ : Submodule R M) : Submodule R M) : Set M) :=
    (SubmodulesBasis.openAddSubgroup hbas N).isOpen'
  rw [hI] at hopen
  have : IsTopologicalAddGroup M :=
    hbas.toModuleFilterBasis.toAddGroupFilterBasis.isTopologicalAddGroup
  exact discreteTopology_iff_isOpen_singleton_zero.mpr (by simpa using hopen)

/-- **The `p`-adic topology of a module is discrete when `p^N = 0` in the ring.**  This is
`Crystalline.discreteTopology_adicModuleTopology_of_eq_bot` with its hypothesis supplied by
`Crystalline.pPowSmul_eq_bot_of_pow_eq_zero`.  In the setting of [Stacks, Tag 07JH] it applies to
`B ⊗_D M` for the section ring `B` of an object of `Cris(X/S)`, in which `p` is nilpotent by
[Stacks, Tag 07HM]. -/
theorem discreteTopology_pAdic_of_pow_eq_zero (p : ℕ) (D : Type u) [CommRing D] (M : Type w)
    [AddCommGroup M] [Module D M] {N : ℕ} (hp : ((p : D) ^ N) = 0) :
    @DiscreteTopology M
      (Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p) M) :=
  discreteTopology_adicModuleTopology_of_eq_bot _ M
    (pPowSmul_eq_bot_of_pow_eq_zero p D M hp)

/-- **The `p`-adic topology of a module is Hausdorff when `p^N = 0` in the ring**, because it is
discrete.  This is the hypothesis `huniq` of the Taylor section of this chapter, in the form
`HasSum.unique` consumes. -/
theorem t2Space_pAdic_of_pow_eq_zero (p : ℕ) (D : Type u) [CommRing D] (M : Type w)
    [AddCommGroup M] [Module D M] {N : ℕ} (hp : ((p : D) ^ N) = 0) :
    @T2Space M (Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p) M) :=
  let := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := D) p) M
  have := discreteTopology_pAdic_of_pow_eq_zero p D M hp
  DiscreteTopology.toT2Space

end Discrete

/-! ### The sum of a Taylor series is unique -/

section Unique

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The sum of a Taylor series of [Stacks, Tag 07JH] is unique.**  The series converges in the
`p`-adic topology of `B ⊗_D M`, which by
`Crystalline.t2Space_pAdic_of_pow_eq_zero` is Hausdorff as soon as `p^N = 0` in `B` — and that is
part of the definition of a divided power thickening in [Stacks, Tag 07HM], so it holds for every
object of `Cris(X/S)`.

This is the hypothesis `huniq` of `Crystalline.taylorSum_smul_eq_of_isTaylorComparison` and of
`Crystalline.ringHom_eq_algebraMap_of_untwisted`, discharged under the source's own hypothesis. -/
theorem hasTaylorSum_unique {N : ℕ} (hpB : ((p : (B : Type u))) ^ N = 0) (xi : ι → (B : Type u))
    (m : M) (t t' : (B : Type u) ⊗[(D : Type u)] M)
    (h : HasTaylorSum p D B M thetaPow xi m t)
    (h' : HasTaylorSum p D B M thetaPow xi m t') : t = t' :=
  let := Ideal.adicModuleTopology (DividedPowers.pAdicIdeal (A := (B : Type u)) p)
    ((B : Type u) ⊗[(D : Type u)] M)
  have := t2Space_pAdic_of_pow_eq_zero p (B : Type u)
    ((B : Type u) ⊗[(D : Type u)] M) hpB
  HasSum.unique h h'

/-- **The identity a Taylor comparison forces on its series, with nothing carried but the source's
own hypothesis.**  This is `Crystalline.taylorSum_smul_eq_of_isTaylorComparison` with `huniq`
replaced by nilpotence of `p` in `B`, which [Stacks, Tag 07HM] requires of every divided power
thickening and so of every object of `Cris(X/S)`.  The conclusion is the **untwisted**
`D`-linearity of the Taylor sum; see that theorem's docstring for why it is not what the proof of
[Stacks, Tag 07JH] establishes. -/
theorem taylorSum_smul_eq_of_isTaylorComparison_of_pow_eq_zero {N : ℕ}
    (hpB : ((p : (B : Type u))) ^ N = 0) (xi : ι → (B : Type u))
    (c : ((B : Type u) ⊗[(D : Type u)] M) →ₗ[(B : Type u)] ((B : Type u) ⊗[(D : Type u)] M))
    (hc : IsTaylorComparison p D B M thetaPow xi c) (a : (D : Type u)) (m : M)
    (t ta : (B : Type u) ⊗[(D : Type u)] M)
    (ht : HasTaylorSum p D B M thetaPow xi m t)
    (hta : HasTaylorSum p D B M thetaPow xi (a • m) ta) : ta = a • t :=
  taylorSum_smul_eq_of_isTaylorComparison p D B M xi c hc
    (fun m' u u' hu hu' ↦ hasTaylorSum_unique p D B M thetaPow hpB xi m' u u' hu hu') a m t ta ht
    hta

end Unique

/-! ### The defect of the old predicate, with nothing carried -/

section Defect

/-- **The defect of `Crystalline.IsTaylorComparison`, with nothing carried but the source's own
hypothesis.**  This is `Crystalline.ringHom_eq_algebraMap_of_untwisted_self` with `huniq`
discharged by `Crystalline.hasTaylorSum_unique`: in the setting of [Stacks, Tag 07JH], where `p` is
nilpotent in `B` by [Stacks, Tag 07HM], a twisted Taylor comparison for the module `M = D` that
*also* satisfies the untwisted identity of the old predicate forces the second divided power map to
be the structure map.

So the statement that the old predicate is the `f = g` shadow of the comparison and not a
formalization of it is now a theorem of the tag's own setting, with no hypothesis about the
topology left in it. -/
theorem ringHom_eq_algebraMap_of_untwisted_self_of_pow_eq_zero {p : ℕ}
    {D B : DividedPowerRing.{u}} [Algebra D.carrier B.carrier]
    {f : SecondDividedPowerMap D B} {ι : Type uI}
    {thetaPow : (ι →₀ ℕ) → D.carrier → D.carrier} {xi : ι → B.carrier}
    {T : D.carrier →ₛₗ[f.ringHom] (B.carrier ⊗[D.carrier] D.carrier)} {N : ℕ}
    (hpB : ((p : B.carrier)) ^ N = 0)
    (hT : IsTwistedTaylorComparison p D B D.carrier f thetaPow xi T)
    (huntwisted : ∀ a m : D.carrier,
      HasTaylorSum p D B D.carrier thetaPow xi (a • m) (a • T m))
    (hone : T 1 = (1 : B.carrier) ⊗ₜ[D.carrier] (1 : D.carrier)) (a : D.carrier) :
    f.ringHom a = algebraMap D.carrier B.carrier a :=
  ringHom_eq_algebraMap_of_untwisted_self hT
    (fun m u u' hu hu' ↦ hasTaylorSum_unique p D B D.carrier thetaPow hpB xi m u u' hu hu')
    huntwisted hone a

end Defect

end Crystalline

end
