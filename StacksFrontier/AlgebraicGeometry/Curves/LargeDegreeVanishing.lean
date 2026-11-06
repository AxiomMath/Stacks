module

public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CohomologicalCriterion
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.ZeroDimensional
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegree
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Smooth
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.ReducedSections
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of `H¹` of an invertible module of large degree on a proper curve

Let `k` be an algebraically closed field, let `X` be a proper curve over `k` and set
`g = dim_k H¹(X, 𝒪_X)`. [Stacks, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90) asserts
that `H¹(X, ℒ) = 0` for every invertible `𝒪_X`-module `ℒ` with `deg(ℒ) ≥ 2g - 1`.

The source's argument is followed. An invertible `𝒩` with `H⁰(X, 𝒩) = H¹(X, 𝒩) = 0`
([Stacks, Tag 0B8Z] (2)) has degree `g - dim_k H⁰(X, 𝒪_X)`, so `ℒ ⊗ 𝒩^{⊗ -1}` has Euler
characteristic at least one and therefore a nonzero global section `s`; the zero scheme `D` of
`s` is finite over `k`, and the sequence of [Stacks, Tag 0C6K] twisted by `𝒩` reads

`0 ⟶ 𝒩 ⟶ 𝒩 ⊗ ℒ ⊗ 𝒩^{⊗ -1} ⟶ i_*(i^*(𝒩 ⊗ ℒ ⊗ 𝒩^{⊗ -1})) ⟶ 0`

with `i : D ⟶ X` the inclusion. Its outer terms have vanishing `H¹` — the first by the choice of
`𝒩`, the last because `D` is affine — so the middle term does too, and the middle term is
isomorphic to `ℒ`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `exists_invertible_isZero_cohomologyOverField_one`: on a proper curve over a field there is an
  invertible module with vanishing `H¹`. Proved from the ample invertible module of
  [Stacks, Tag 09ND] and Serre vanishing, [Stacks, Tag 0B5U] (1) ⟹ (2).
* `finrank_cohomologyOverField_zero_sub_one_eq`: on a proper curve,
  `dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = deg(ℒ) + dim_k H⁰(X, 𝒪_X) - g` for every invertible `ℒ`.
* `invertibleCurveDegree_eq_genus_sub_finrank_of_isZero`: an invertible module with vanishing
  `H⁰` and `H¹` has degree `g - dim_k H⁰(X, 𝒪_X)`.
* `isZero_cohomologyOverField_one_of_tensorInverse_section`: the geometric step — for invertible
  `𝒩` and `ℒ` with `H¹(X, 𝒩) = 0` and `H⁰(X, ℒ ⊗ 𝒩^{⊗ -1}) ≠ 0` one has `H¹(X, ℒ) = 0`.
* `isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree`:
  **[Stacks, Tag 0B90]**: on a proper curve over an algebraically closed field,
  `H¹(X, ℒ) = 0` for every invertible `ℒ` with `deg(ℒ) ≥ 2g - 1`.

## Implementation notes

**Spellings.** `dim_k Hⁱ(X, ℱ)` is `Module.finrank k (cohomologyOverField k f ℱ i)`
([Stacks, Tag 0BEF]) and vanishing is `CategoryTheory.Limits.IsZero`, as in
`StacksFrontier/AlgebraicGeometry/Curves/PrescribedLowCohomology.lean`. The genus is
`AlgebraicGeometry.genus` ([Stacks, Tag 0BY7]), defined from
`AlgebraicGeometry.structureSheafCohomology`; the identification with `cohomologyOverField` is
`AlgebraicGeometry.structureSheafCohomologyIsoCohomologyOverField`. The degree is
`AlgebraicGeometry.invertibleCurveDegree` ([Stacks, Tag 0AYR]). The monoidal structure on
`X.Modules` is `Stacks.SheafOfModules.sheafTensorMonoidal`, whose tensor product is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` on the nose, as in
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean`; its symmetry is
`Stacks.SheafOfModules.sheafTensorSymmetric`.

**Why [Stacks, Tag 0B8Z] is used.** The degree is by definition
`deg(ℒ) = χ(X, ℒ) - χ(X, 𝒪_X)` (`AlgebraicGeometry.invertibleCurveDegree`), so the degree
hypothesis says exactly `dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) ≥ g`, which bounds `H¹` only once `H⁰`
is bounded, and nothing in the hypothesis bounds `H⁰`. Some input beyond the numerics is
therefore needed. The two classical ones are Serre duality and the source's own `𝒩`, which is
Tag 0B8Z (2), `AlgebraicGeometry.exists_invertible_isZero_cohomologyOverField_zero_one`; the
second is used. Serre duality for a proper curve over a field is clause (5) of
[Stacks, Tag 0BS2] at the canonical dualizing sheaf `Stacks.Duality.dualizingSheafOverField`,
`AlgebraicGeometry.CohenMacaulayCurveSituation.firstCohomologyDuality_dualizingSheafOverField`,
with the duality of dimensions `dim_k H⁰(X, ℰ) = dim_k H¹(X, ℰ^∨ ⊗ ω_X)` as
`AlgebraicGeometry.finrank_cohomologyOverField_zero_eq_one_dualTensorDualizingSheafOverField`;
that statement asks `ℰ` and `ℰ^∨ ⊗ ω_X` to be finite locally free of one common rank and
carries the isomorphism `(ℰ^∨ ⊗ ω_X)^∨ ⊗ ω_X ≅ ℰ`, all of which would follow from clause (1) of
Tag 0BS2 — that `ω_X` is invertible — which this development does not have. The library's
Riemann–Roch, `AlgebraicGeometry.eulerCharacteristic_eq_curveChernDegree_add`, is the
Chow-group formula of Tag 0BRZ and carries hypotheses of its own; it computes the same Euler
characteristic and so cannot replace the missing bound on `H⁰` either.

**The ample module.** [Stacks, Tag 09ND] —
`AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one` — produces an ample
invertible module on a Noetherian integral separated scheme of dimension one, and a curve over a
field is one. Serre vanishing for its powers is the implication (1) ⟹ (2) of [Stacks, Tag 0B5U],
`AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple`, whose
conclusion is stated for the derived global sections; the passage to `cohomologyOverField` is
`isZero_cohomologyOverField_of_isZero_rightDerived` below, both being the right derived functors
of the same evaluation functor.

**[Stacks, Tag 0B8Z] (2).** The module `𝒩` is
`AlgebraicGeometry.exists_invertible_isZero_cohomologyOverField_zero_one`, proved in
`StacksFrontier/AlgebraicGeometry/Curves/PrescribedLowCohomology.lean` by the source's descending
induction, whose geometric step is `AlgebraicGeometry.exists_pointTwistDown` in
`StacksFrontier/AlgebraicGeometry/Curves/PointTwistDown.lean`. The lemmas of this file about a
nonsingular closed point are the same geometry in standalone form:

* the point, `exists_closedPoint_smoothAt_mem` — the smooth locus of a reduced scheme locally of
  finite type over a perfect field is open and dense ([Stacks, Tag 0B8X]), so it meets a given
  nonempty open, and a nonempty locally closed subset of a Jacobson space contains a closed point;
* the divisor, `isEffectiveCartierDivisor_vanishingIdeal_of_smoothAt`, from items (4), (5) of
  [Stacks, Tag 0B8Y] (through the TFAE `smoothAt_closedPoint_tfae_of_isCurve_of_perfectField`):
  the reduced point is an effective Cartier divisor;
* `finrank_globalSections_eq_one`: a scheme integral and proper over an algebraically closed
  field `k` has `Γ(Z, 𝒪_Z) = k`, which applies to a reduced closed point;
* `exists_cohomologyOverFieldMap_ne_zero_of_notMem_nonvanishingLocus`: a section in the image of
  multiplication by a section `t` of `𝒜` vanishes wherever `t` does
  (`nonvanishingLocus_sectionsMap_mulRight_subset`), so a section not vanishing at such a point
  has nonzero image in `H⁰` of the cokernel.

**Reading a product in either order.** `nonvanishingLocus_sectionsMap_mulRight_subset` is the one
place a monoidal identity is needed. `Stacks.SheafOfModules.nonvanishingLocus_sectionsMap_subset`
bounds the nonvanishing locus of the image of a section by that of the section itself, which for
the first map of the twisted sequence gives the wrong factor; rewriting the product as the image
of the *canonical* section under multiplication by the other factor exchanges the two, and that
rewriting is `comp_rightUnitor_inv_whiskerLeft`, an identity of any monoidal category.

## References

* [Stacks Project, Tag 0B90](https://stacks.math.columbia.edu/tag/0B90)
* [Stacks Project, Tag 0B8Z](https://stacks.math.columbia.edu/tag/0B8Z)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0B8X](https://stacks.math.columbia.edu/tag/0B8X)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 04L2](https://stacks.math.columbia.edu/tag/04L2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry

open Stacks.SheafOfModules (sheafTensorMonoidal sheafTensorSymmetric)
open Stacks.SheafOfModules.Invertible (tensorPowerModule mulNegOneIso)
open Stacks.AlgebraicGeometry.ComponentDegrees
  (discreteTopology_of_isProper_of_topologicalKrullDim_le_zero)

-- The tensor product sheaf of [Stacks, Tag 01CA] as a monoidal structure on the `𝒪_X`-modules
-- of a scheme, with the symmetry of [Stacks, Tag 01CU]; both are re-activated from
-- `StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeExactSequenceTwist.lean`.
attribute [local instance] schemeModulesMonoidal schemeModulesSymmetric

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Cancelling an invertible factor against its inverse -/

/-- **`𝒩 ⊗ (ℒ ⊗ 𝒩^{⊗ -1}) ≅ ℒ`**: move `𝒩` past `ℒ` by the symmetry, reassociate, and cancel
`𝒩 ⊗ 𝒩^{⊗ -1}` against the structure sheaf by
`Stacks.SheafOfModules.Invertible.mulNegOneIso`. -/
public def tensorInverseIso (N L : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N] :
    (N ⊗ (L ⊗ tensorPowerModule N (-1)) : X.Modules) ≅ L :=
  (α_ N L (tensorPowerModule N (-1))).symm ≪≫
    whiskerRightIso (β_ N L) (tensorPowerModule N (-1)) ≪≫
      α_ L N (tensorPowerModule N (-1)) ≪≫
        whiskerLeftIso L (mulNegOneIso X.presheaf X.ringCatSheaf.property N) ≪≫ ρ_ L

/-! ### Reading off a nonzero global section -/

/-- **A module whose `H⁰` is not zero-dimensional has a nonzero global section.** The degree-zero
cohomology is in bijection with the global sections by
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`, so a positive dimension makes the
sections nontrivial, and a nonzero element over `⊤` extends to a global section by restricting
it to every open. -/
public theorem exists_section_of_finrank_pos [IsProper f] (M : X.Modules)
    (h : 0 < Module.finrank k (cohomologyOverField k f M 0)) :
    ∃ s : M.sections, s.eval (op ⊤) ≠ 0 := by
  have := Module.nontrivial_of_finrank_pos h
  have : Nontrivial Γ(M, ⊤) := (cohomologyOverFieldZeroEquivSections k f M).symm.nontrivial
  obtain ⟨a, ha⟩ := exists_ne (0 : Γ(M, ⊤))
  exact ⟨Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) M a, fun hc =>
    ha ((Stacks.SheafOfModules.sectionsOfTop_eval_top (X := X.toRingedSpace) M a).symm.trans hc)⟩

/-! ### An invertible module with no first cohomology -/

/-- **Vanishing of the derived global sections gives vanishing of the cohomology over `k`.**
Both are the right derived functors of the evaluation of a module at `⊤`, the second with its
scalars restricted along `k ⟶ Γ(X, 𝒪_X)`, so the underlying modules have the same carrier and a
subsingleton on one side is a subsingleton on the other. -/
public theorem isZero_cohomologyOverField_of_isZero_rightDerived (G : X.Modules) (p : ℕ)
    (h : IsZero (((moduleGlobalSections X).rightDerived p).obj G)) :
    IsZero (cohomologyOverField k f G p) := by
  have hs : Subsingleton (((moduleGlobalSections X).rightDerived p).obj G) :=
    ModuleCat.subsingleton_of_isZero h
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

/-- **On a proper curve over a field there is an invertible module with `H¹ = 0`.**

A curve is Noetherian, integral and separated of dimension one, so it carries an ample invertible
module `𝒜` by [Stacks, Tag 09ND]; the implication (1) ⟹ (2) of [Stacks, Tag 0B5U] applied to the
structure sheaf gives an exponent `n` beyond which `H¹(X, 𝒪_X ⊗ 𝒜^{⊗ n})` vanishes, and the left
unitor identifies that module with `𝒜^{⊗ n}`. -/
public theorem exists_invertible_isZero_cohomologyOverField_one [IsProper f] [IsCurve k f] :
    ∃ L₀ : X.Modules,
      SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L₀ ∧
        IsZero (cohomologyOverField k f L₀ 1) := by
  have _ : IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have _ : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  obtain ⟨A, hA, hample⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_isAmple_of_topologicalKrullDim_one X
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f))
  have hOcoh : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  obtain ⟨n₀, hn₀⟩ :=
    AlgebraicGeometry.Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple A f hample
      (SheafOfModules.unit X.ringCatSheaf) hOcoh
  have hAs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property A :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hA
  refine ⟨tensorPowerModule A (n₀ : ℤ), ?_, ?_⟩
  · exact Stacks.SheafOfModules.Invertible.tensorPower_isInvertible X.presheaf
      X.ringCatSheaf.property A (n₀ : ℤ)
  · exact (isZero_cohomologyOverField_of_isZero_rightDerived k f _ 1
      (hn₀ n₀ 1 le_rfl Nat.one_pos)).of_iso
      (cohomologyOverFieldIso k f (λ_ (tensorPowerModule A (n₀ : ℤ))).symm 1)

/-! ### The Euler characteristic of an invertible module -/

/-- The alternating sum of the dimensions of the cohomology of a module on a proper scheme of
dimension at most one is `dim_k H⁰ - dim_k H¹`: everything above degree one vanishes by
[Stacks, Tag 02UZ]. -/
private theorem finsum_alternating_finrank_eq_sub [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (F : X.Modules) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f F n) : ℤ))
      = (Module.finrank k (cohomologyOverField k f F 0) : ℤ)
        - (Module.finrank k (cohomologyOverField k f F 1) : ℤ) :=
  finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k f F fun n hn =>
    isZero_cohomologyOverField_of_topologicalKrullDim_le k f F (d := 1) (i := n) hdim hn

/-- **Riemann–Roch as the definition of the degree unfolds it.** On a proper scheme of dimension
at most one over `k`,

`dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = deg(ℒ) + dim_k H⁰(X, 𝒪_X) - g`

for every invertible `ℒ`: the degree is by definition the difference of the two Euler
characteristics, and each of them is cut down to its first two terms by [Stacks, Tag 02UZ]. -/
public theorem finrank_cohomologyOverField_zero_sub_one_eq [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L) :
    (Module.finrank k (cohomologyOverField k f L 0) : ℤ)
        - (Module.finrank k (cohomologyOverField k f L 1) : ℤ) =
      @invertibleCurveDegree k _ X f _ hdim L hL
        + (Module.finrank k
            (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ)
        - (genus f : ℤ) := by
  have hgenus : (genus f : ℤ) = (Module.finrank k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) : ℤ) := by
    rw [genus_eq_finrank_structureSheafCohomology,
      (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq]
  have hdef : @invertibleCurveDegree k _ X f _ hdim L hL =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k f L n) : ℤ)) -
        (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k
          (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ)) := rfl
  rw [hdef, finsum_alternating_finrank_eq_sub k f hdim L,
    finsum_alternating_finrank_eq_sub k f hdim (SheafOfModules.unit X.ringCatSheaf), hgenus]
  ring

/-- **An invertible module with vanishing `H⁰` and `H¹` has degree `g - dim_k H⁰(X, 𝒪_X)`**, by
the previous identity with both of its left-hand terms zero. -/
public theorem invertibleCurveDegree_eq_genus_sub_finrank_of_isZero [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (N : X.Modules)
    (hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N)
    (hzero : IsZero (cohomologyOverField k f N 0)) (hone : IsZero (cohomologyOverField k f N 1)) :
    @invertibleCurveDegree k _ X f _ hdim N hN = (genus f : ℤ)
      - (Module.finrank k
          (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) : ℤ) := by
  have h := finrank_cohomologyOverField_zero_sub_one_eq k f hdim N hN
  have hz (n : ℕ) (hn : IsZero (cohomologyOverField k f N n)) :
      Module.finrank k (cohomologyOverField k f N n) = 0 :=
    have := ModuleCat.subsingleton_of_isZero hn
    Module.finrank_zero_of_subsingleton
  rw [hz 0 hzero, hz 1 hone] at h
  lia

/-- **The structure sheaf of a proper integral scheme over a field has a nonzero global
section**, so `dim_k H⁰(X, 𝒪_X) ≥ 1`: the ring of global functions is a field
([Stacks, Tag 04L2] (1)), hence nontrivial. -/
public theorem zero_lt_finrank_cohomologyOverField_zero_unit [IsProper f] [IsIntegral X] :
    0 < Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) := by
  have _ := forall_finiteDimensional_cohomologyOverField_unit k f 0
  have _ : Nontrivial Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) :=
    ⟨(isField_of_universallyClosed k f).exists_pair_ne⟩
  exact Module.finrank_pos_iff.mpr (cohomologyOverFieldZeroEquivSections k f _).nontrivial

/-! ### The geometric step: the exact sequence of the zero divisor of a section -/

/-- **The geometric step of [Stacks, Tag 0B90]**, with no hypothesis beyond the source's.

Let `𝒩` and `ℒ` be invertible on a proper integral scheme of dimension at most one over `k`,
with `H¹(X, 𝒩) = 0` and with `ℒ ⊗ 𝒩^{⊗ -1}` having a global section of positive-dimensional
`H⁰`. Then `H¹(X, ℒ) = 0`.

A nonzero global section `s` of `ℳ = ℒ ⊗ 𝒩^{⊗ -1}` is regular because `X` is integral, so
[Stacks, Tag 0C6K] twisted by `𝒩` gives `0 ⟶ 𝒩 ⟶ 𝒩 ⊗ ℳ ⟶ i_* i^*(𝒩 ⊗ ℳ) ⟶ 0` for `i` the
inclusion of the zero scheme `Z(s)`. That zero scheme is finite over `k` ([Stacks, Tag 0AYY]),
hence affine, so the higher cohomology of the coherent module `i^*(𝒩 ⊗ ℳ)` on it vanishes
([Stacks, Tag 01XB]) and so does that of its direct image. The two outer terms therefore force
`H¹(X, 𝒩 ⊗ ℳ) = 0`, and `𝒩 ⊗ ℳ ≅ ℒ`. -/
public theorem isZero_cohomologyOverField_one_of_tensorInverse_section [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (N L : X.Modules)
    [hNs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N]
    [hNa : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    [hMa : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (L ⊗ tensorPowerModule N (-1) : X.Modules)]
    (hN1 : IsZero (cohomologyOverField k f N 1))
    (hpos : 0 < Module.finrank k
      (cohomologyOverField k f (L ⊗ tensorPowerModule N (-1) : X.Modules) 0)) :
    IsZero (cohomologyOverField k f L 1) := by
  have hnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set M : X.Modules := (L ⊗ tensorPowerModule N (-1) : X.Modules)
  obtain ⟨s, hs⟩ := exists_section_of_finrank_pos k f M hpos
  have hreg : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s :=
    isRegularSection_of_eval_top_ne_zero M s hs
  obtain ⟨w, hSE⟩ := shortExact_zeroScheme_twist_of_isRegularSection X M s hreg N
  have hfin : IsFinite ((zeroScheme X M (s.eval (op ⊤))).subschemeι ≫ f) :=
    isFinite_zeroScheme_of_eval_top_ne_zero k f hdim M s hs
  have haff : IsAffine (zeroScheme X M (s.eval (op ⊤))).subscheme :=
    isAffine_of_isAffineHom ((zeroScheme X M (s.eval (op ⊤))).subschemeι ≫ f)
  have hnoethZ : IsLocallyNoetherian (zeroScheme X M (s.eval (op ⊤))).subscheme :=
    isLocallyNoetherian_of_isFinite ((zeroScheme X M (s.eval (op ⊤))).subschemeι ≫ f)
  have hMs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hMa
  have hNMs : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (N ⊗ M : X.Modules) :=
    Stacks.SheafOfModules.isInvertible_tensorSheaf X.presheaf X.ringCatSheaf.property N M
  have hNMcoh : SheafOfModules.IsCoherent (N ⊗ M : X.Modules) :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X _
  have hpullcoh : SheafOfModules.IsCoherent
      ((Scheme.Modules.pullback (zeroScheme X M (s.eval (op ⊤))).subschemeι).obj
        (N ⊗ M : X.Modules)) :=
    isCoherent_pullback (zeroScheme X M (s.eval (op ⊤))).subschemeι _
  have hqc : ((Scheme.Modules.pullback (zeroScheme X M (s.eval (op ⊤))).subschemeι).obj
      (N ⊗ M : X.Modules)).IsQuasicoherent :=
    have _ := hpullcoh
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have h3' := isZero_cohomologyOverField_pos_of_isAffine k
    ((zeroScheme X M (s.eval (op ⊤))).subschemeι ≫ f)
    ((Scheme.Modules.pullback (zeroScheme X M (s.eval (op ⊤))).subschemeι).obj
      (N ⊗ M : X.Modules)) 1 Nat.one_pos
  have h3 := h3'.of_iso (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k
    (zeroScheme X M (s.eval (op ⊤))).subschemeι f
    ((Scheme.Modules.pullback (zeroScheme X M (s.eval (op ⊤))).subschemeι).obj
      (N ⊗ M : X.Modules)) 1).symm
  have hmid := isZero_cohomologyOverField_of_shortExact k f hSE 1 hN1 h3
  exact hmid.of_iso (cohomologyOverFieldIso k f (tensorInverseIso N L) 1).symm

/-! ### A nonsingular closed point of a curve -/

/-- **A nonempty open set of a reduced scheme locally of finite type over a perfect field
contains a closed point at which the scheme is smooth.** The smooth locus is open and dense
([Stacks, Tag 0B8X]), so it meets the given open set in a nonempty open set, and a nonempty
locally closed subset of a Jacobson space contains a closed point. -/
@[sga "4½ Th_finitude 2.7" "Perfect-field clause"]
public theorem exists_closedPoint_smoothAt_mem [PerfectField k] [IsReduced X]
    [LocallyOfFiniteType f] {U : Set X} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y : X, y ∈ U ∧ InfinitesimalLifting.SmoothAt f y ∧ IsClosed ({y} : Set X) := by
  have hdense := dense_smoothAt_locus k f
  have hopen := isOpen_smoothAt_locus f
  have hW : (U ∩ {x : X | InfinitesimalLifting.SmoothAt f x}).Nonempty :=
    hdense.inter_open_nonempty U hU hne
  have _ : _root_.JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, ⟨hyU, hys⟩, hyc⟩ :=
    _root_.nonempty_inter_closedPoints hW (hU.inter hopen).isLocallyClosed
  exact ⟨y, hyU, hys, _root_.mem_closedPoints_iff.mp hyc⟩

/-- **A closed point at which a curve over a perfect field is smooth is an effective Cartier
divisor**: items (4), (5) and (6) of [Stacks, Tag 0B8Y]. -/
public theorem isEffectiveCartierDivisor_vanishingIdeal_of_smoothAt [PerfectField k] [IsCurve k f]
    {y : X} (hyc : IsClosed ({y} : Set X)) (hys : InfinitesimalLifting.SmoothAt f y) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)) :=
  ((smoothAt_closedPoint_tfae_of_isCurve_of_perfectField k f hyc).out 5 4).mp hys

/-- **The underlying space of the reduced closed subscheme on a closed point is a single
point.** The range of its inclusion is the support of the vanishing ideal, which is `{y}`, and
the inclusion is injective. -/
public theorem subsingleton_subscheme_vanishingIdeal {y : X} (hyc : IsClosed ({y} : Set X)) :
    Subsingleton (Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)).subscheme := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
  have hrange : Set.range D.subschemeι.base = ({y} : Set X) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal
      (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
  have h (a : D.subscheme) : D.subschemeι.base a = y := hrange.subset ⟨a, rfl⟩
  exact ⟨fun a b => D.subschemeι.isClosedEmbedding.injective ((h a).trans (h b).symm)⟩

/-- **The reduced closed subscheme on a closed point is nonempty.** -/
public theorem nonempty_subscheme_vanishingIdeal {y : X} (hyc : IsClosed ({y} : Set X)) :
    Nonempty (Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)).subscheme := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
  have hrange : Set.range D.subschemeι.base = ({y} : Set X) :=
    Scheme.IdealSheafData.range_subschemeι_vanishingIdeal
      (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
  obtain ⟨z, -⟩ := hrange.symm.subset (Set.mem_singleton y)
  exact ⟨z⟩

/-- **The reduced closed subscheme on a closed point is integral**: it is reduced, and its space
is a nonempty single point, hence irreducible. -/
public theorem isIntegral_subscheme_vanishingIdeal {y : X} (hyc : IsClosed ({y} : Set X)) :
    IsIntegral (Scheme.IdealSheafData.vanishingIdeal
      (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)).subscheme := by
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hyc⟩ : TopologicalSpace.Closeds X)
  have hss : Subsingleton D.subscheme := subsingleton_subscheme_vanishingIdeal hyc
  have hne : Nonempty D.subscheme := nonempty_subscheme_vanishingIdeal hyc
  have hpre : PreirreducibleSpace D.subscheme := by
    refine ⟨fun u v _ _ hu hv => ?_⟩
    obtain ⟨a, -, hau⟩ := hu
    obtain ⟨b, -, hbv⟩ := hv
    exact ⟨a, Set.mem_univ a, hau, by rwa [Subsingleton.elim b a] at hbv⟩
  have _ : IrreducibleSpace D.subscheme := { toNonempty := hne }
  exact isIntegral_of_irreducibleSpace_of_isReduced D.subscheme

/-- **On a scheme integral and proper over an algebraically closed field the ring of global
functions is the base field.** It is a finite-dimensional `k`-algebra ([Stacks, Tag 0BUG] (1))
and a field ([Stacks, Tag 04L2] (1)), hence an algebraic extension of `k`, hence `k` itself. -/
public theorem finrank_globalSections_eq_one [IsAlgClosed k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsProper g] [IsIntegral Z] :
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = 1 := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  have hfin : Module.Finite k Γ(Z, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k g
  have hint : Algebra.IsIntegral k Γ(Z, ⊤) := Algebra.IsIntegral.of_finite k _
  have hbij : Function.Bijective (algebraMap k Γ(Z, ⊤)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  rw [← (AlgEquiv.ofBijective (Algebra.ofId k Γ(Z, ⊤)) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **An invertible module restricted to an effective Cartier divisor which is one reduced point
has one-dimensional `H⁰`.** The divisor subscheme has dimension at most zero on a scheme of
dimension at most one, and it is proper over `k`, so its space is discrete and the restriction is
isomorphic to its structure sheaf (`Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology`);
the structure sheaf has `dim_k H⁰ = dim_k Γ = 1` by `finrank_globalSections_eq_one`, the
subscheme being integral and proper over an algebraically closed field. -/
private theorem finrank_cohomologyOverField_zero_pullback_divisor_eq_one [IsAlgClosed k]
    [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (hint : IsIntegral D.subscheme)
    (N : X.Modules)
    [hN : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    Module.finrank k (cohomologyOverField k (D.subschemeι ≫ f)
        ((Scheme.Modules.pullback D.subschemeι).obj N) 0) = 1 := by
  have _ := hint
  have hdisc : DiscreteTopology (D.subscheme : Type u) :=
    discreteTopology_of_isProper_of_topologicalKrullDim_le_zero k (D.subschemeι ≫ f)
      (topologicalKrullDim_divisorSubscheme_le_zero hdim D)
  have hNpre : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 N := hN
  have hpull : SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback D.subschemeι).obj N) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback D.subschemeι N hNpre
  have _ : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf D.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback D.subschemeι).obj N) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨e⟩ : Nonempty ((Scheme.Modules.pullback D.subschemeι).obj N ≅
      SheafOfModules.unit D.subscheme.ringCatSheaf) :=
    Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology D.subscheme
      ((Scheme.Modules.pullback D.subschemeι).obj N)
  rw [finrank_cohomologyOverField_eq_of_iso k (D.subschemeι ≫ f) e 0,
    finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k (D.subschemeι ≫ f)]
  exact finrank_globalSections_eq_one k (D.subschemeι ≫ f)

/-! ### Multiplying a section by a global section of another module -/

/-- **The product of two morphisms out of the monoidal unit is symmetric in the two factors.**
Multiplying `m` on the right by `t` and multiplying `t` on the left by `m` are the same morphism
`𝟙_ C ⟶ M ⊗ A`: both are `Stacks.Monoidal.sectionTensor m t`, by the two unit laws
`Stacks.Monoidal.sectionTensor_comp_rightUnitor` and `..._comp_leftUnitor` and the two whiskering
laws `Stacks.Monoidal.sectionTensor_comp_whiskerLeft` and `..._comp_whiskerRight`. Those are
stated for an arbitrary monoidal category, so no coherence is re-derived here. -/
private theorem comp_rightUnitor_inv_whiskerLeft {C : Type*} [Category C] [MonoidalCategory C]
    {M A : C} (m : 𝟙_ C ⟶ M) (t : 𝟙_ C ⟶ A) :
    m ≫ (ρ_ M).inv ≫ M ◁ t = t ≫ (λ_ A).inv ≫ m ▷ A := by
  have hm : m ≫ (ρ_ M).inv = Stacks.Monoidal.sectionTensor m (𝟙 (𝟙_ C)) :=
    (Iso.comp_inv_eq _).mpr (Stacks.Monoidal.sectionTensor_comp_rightUnitor m).symm
  have ht : t ≫ (λ_ A).inv = Stacks.Monoidal.sectionTensor (𝟙 (𝟙_ C)) t :=
    (Iso.comp_inv_eq _).mpr (Stacks.Monoidal.sectionTensor_comp_leftUnitor t).symm
  calc m ≫ (ρ_ M).inv ≫ M ◁ t
      = Stacks.Monoidal.sectionTensor m (𝟙 (𝟙_ C)) ≫ M ◁ t := by rw [← Category.assoc, hm]
    _ = Stacks.Monoidal.sectionTensor m t := by
        rw [Stacks.Monoidal.sectionTensor_comp_whiskerLeft, Category.id_comp]
    _ = Stacks.Monoidal.sectionTensor (𝟙 (𝟙_ C)) t ≫ m ▷ A := by
        rw [Stacks.Monoidal.sectionTensor_comp_whiskerRight, Category.id_comp]
    _ = t ≫ (λ_ A).inv ≫ m ▷ A := by rw [← Category.assoc, ht]

/-- **Multiplication by a global section, read as a product in either order.** The image of a
section `m` of `ℳ` under multiplication by a global section `t` of `𝒜` — the first map of the
twisted sequence of [Stacks, Tag 0C6K] — is also the image of `t` under multiplication by `m`,
by `comp_rightUnitor_inv_whiskerLeft` and `SheafOfModules.unitHomEquiv_comp_apply`. -/
private theorem sectionsMap_eq_of_comp_eq {P Q R : X.Modules} (p : P ⟶ R) (q : Q ⟶ R)
    (a : 𝟙_ X.Modules ⟶ P) (b : 𝟙_ X.Modules ⟶ Q) (h : a ≫ p = b ≫ q) :
    _root_.SheafOfModules.sectionsMap p (P.unitHomEquiv a) =
      _root_.SheafOfModules.sectionsMap q (Q.unitHomEquiv b) :=
  (_root_.SheafOfModules.unitHomEquiv_comp_apply a p).symm.trans
    ((congrArg (_root_.SheafOfModules.unitHomEquiv R) h).trans
      (_root_.SheafOfModules.unitHomEquiv_comp_apply b q))

/-- **Multiplication by a global section, read as a product in either order.** -/
private theorem sectionsMap_mulRight_eq_sectionsMap_mulLeft (M A : X.Modules)
    (m : 𝟙_ X.Modules ⟶ M) (t : 𝟙_ X.Modules ⟶ A) :
    _root_.SheafOfModules.sectionsMap ((ρ_ M).inv ≫ M ◁ t) (M.unitHomEquiv m) =
      _root_.SheafOfModules.sectionsMap ((λ_ A).inv ≫ m ▷ A) (A.unitHomEquiv t) :=
  sectionsMap_eq_of_comp_eq _ _ m t (comp_rightUnitor_inv_whiskerLeft m t)

/-- **A section multiplied by a global section of another module vanishes wherever that global
section does.** Applying `Stacks.SheafOfModules.nonvanishingLocus_sectionsMap_subset` to the
first map of the twisted sequence of [Stacks, Tag 0C6K] directly bounds the nonvanishing locus
of the product by that of `ℳ`; reading the product in the other order, which is
`sectionsMap_mulRight_eq_sectionsMap_mulLeft`, bounds it by that of `𝒜` instead, and that is the
factor whose zero locus is the chosen point.

No invertibility of either module is needed. -/
private theorem nonvanishingLocus_sectionsMap_mulRight_subset (M A : X.Modules) (m : M.sections)
    (t : A.sections) :
    Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (M ⊗ A : X.Modules)
        (_root_.SheafOfModules.sectionsMap ((ρ_ M).inv ≫ M ◁ A.unitHomEquiv.symm t) m) ⊆
      Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) A t := by
  have h := sectionsMap_mulRight_eq_sectionsMap_mulLeft M A (M.unitHomEquiv.symm m)
    (A.unitHomEquiv.symm t)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact (congrArg (Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
    (M ⊗ A : X.Modules)) h).subset.trans
      (Stacks.SheafOfModules.nonvanishingLocus_sectionsMap_subset _ t)

/-! ### The twisting-down step of [Stacks, Tag 0B8Z] -/

/-- **Moving the middle term of an ideal-sheaf sequence along an isomorphism.** A short exact
sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ i_* i^* ℱ₂ ⟶ 0` and an isomorphism `ℱ₂ ≅ ℒ` give a short exact sequence
`0 ⟶ ℱ₁ ⟶ ℒ ⟶ i_* i^* ℒ ⟶ 0`, whose first map is the old one followed by the isomorphism: the two
complexes are isomorphic by `CategoryTheory.ShortComplex.isoMk` at the identity, at `ℒ` and at
`i_* i^* ℒ`. -/
private theorem exists_shortExact_of_iso_middle {Z : Scheme.{u}} (i : Z ⟶ X)
    {F₁ F₂ G : X.Modules} (α : F₁ ⟶ F₂)
    (β : F₂ ⟶ (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj F₂))
    (w : α ≫ β = 0) (hSE : (ShortComplex.mk α β w).ShortExact) (e : F₂ ≅ G) :
    ∃ w' : (α ≫ e.hom) ≫ (e.inv ≫ β ≫ (Scheme.Modules.pushforward i).map
        ((Scheme.Modules.pullback i).map e.hom)) = 0,
      (ShortComplex.mk (α ≫ e.hom) (e.inv ≫ β ≫ (Scheme.Modules.pushforward i).map
        ((Scheme.Modules.pullback i).map e.hom)) w').ShortExact := by
  have w' : (α ≫ e.hom) ≫ (e.inv ≫ β ≫ (Scheme.Modules.pushforward i).map
      ((Scheme.Modules.pullback i).map e.hom)) = 0 := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, w, Limits.zero_comp]
  refine ⟨w', ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl F₁) e
    ((Scheme.Modules.pushforward i).mapIso ((Scheme.Modules.pullback i).mapIso e))
    (by simp) (by simp)) hSE⟩

/-- **A global section outside the image of the first map of a short exact sequence has nonzero
image in the `H⁰` of the third.** The long exact sequence of [Stacks, Tag 010Q] is exact at
`H⁰(X, ℱ₂)`, so a class killed by `H⁰(g)` comes from `H⁰(ℱ₁)`; the identification of `H⁰` with
global sections is natural, by
`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap`, so that class
corresponds to a section in the image of `f` on sections. -/
private theorem exists_cohomologyOverFieldMap_zero_ne_zero_of_notMem_range
    {F₁ F₂ F₃ : X.Modules} (α : F₁ ⟶ F₂) (β : F₂ ⟶ F₃) (w : α ≫ β = 0)
    (hS : (ShortComplex.mk α β w).ShortExact) (v : F₂.sections)
    (hv : ∀ u : F₁.sections, _root_.SheafOfModules.sectionsMap α u ≠ v) :
    ∃ a, cohomologyOverFieldMap k f β 0 a ≠ 0 := by
  obtain ⟨-, -, hab, -, -⟩ := exists_cohomologyOverField_longExactSequence k f hS
  refine ⟨(cohomologyOverFieldZeroEquivSections k f F₂).symm (v.eval (op ⊤)), fun hc => ?_⟩
  have hker : LinearMap.ker (cohomologyOverFieldMap k f β 0).hom
      = LinearMap.range (cohomologyOverFieldMap k f α 0).hom :=
    LinearMap.exact_iff.mp (hab 0)
  obtain ⟨b, hb⟩ : (cohomologyOverFieldZeroEquivSections k f F₂).symm (v.eval (op ⊤))
      ∈ LinearMap.range (cohomologyOverFieldMap k f α 0).hom := by
    rw [← hker]
    exact hc
  refine hv (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) F₁
      (cohomologyOverFieldZeroEquivSections k f F₁ b))
    (Scheme.Modules.sections_ext_of_eval_top ?_)
  have h2 : (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) F₁
      (cohomologyOverFieldZeroEquivSections k f F₁ b)).eval (op ⊤)
      = cohomologyOverFieldZeroEquivSections k f F₁ b :=
    Stacks.SheafOfModules.sectionsOfTop_eval_top _ _
  have h3 : α.app ⊤ (cohomologyOverFieldZeroEquivSections k f F₁ b) = v.eval (op ⊤) := by
    rw [← cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f α b,
      show cohomologyOverFieldMap k f α 0 b = (cohomologyOverFieldMap k f α 0).hom b from rfl,
      hb]
    exact Equiv.apply_symm_apply _ _
  exact (congrArg (fun z => α.app ⊤ z) h2).trans h3

/-- **A section not vanishing where `t` does survives in the cokernel.** Let `ℳ`, `𝒜` and
`ℒ` be `𝒪_X`-modules with an isomorphism `ℳ ⊗ 𝒜 ≅ ℒ`, let `t` be a global section of `𝒜` and let
`0 ⟶ ℳ ⟶ ℒ ⟶ ℱ₃ ⟶ 0` be short exact with first map multiplication by `t` followed by that
isomorphism. If some global section of `ℒ` does not vanish at a point at which `t` does, then
`H⁰(X, ℒ) ⟶ H⁰(X, ℱ₃)` is nonzero.

Every section of `ℒ` in the image of the first map is the image of a product with `t`, hence
vanishes wherever `t` does by `nonvanishingLocus_sectionsMap_mulRight_subset`; so the given
section is not in that image, and
`exists_cohomologyOverFieldMap_zero_ne_zero_of_notMem_range` applies. -/
private theorem exists_cohomologyOverFieldMap_ne_zero_of_notMem_nonvanishingLocus
    (M A L : X.Modules) (e : (M ⊗ A : X.Modules) ≅ L) (t : A.sections) (s : L.sections) {y : X}
    {F₃ : X.Modules} (β : L ⟶ F₃)
    (w : (((ρ_ M).inv ≫ M ◁ A.unitHomEquiv.symm t) ≫ e.hom) ≫ β = 0)
    (hSE : (ShortComplex.mk (((ρ_ M).inv ≫ M ◁ A.unitHomEquiv.symm t) ≫ e.hom) β w).ShortExact)
    (hyU : y ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s)
    (hynv : y ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) A t) :
    ∃ a, cohomologyOverFieldMap k f β 0 a ≠ 0 := by
  refine exists_cohomologyOverFieldMap_zero_ne_zero_of_notMem_range k f _ β w hSE s fun u hu => ?_
  refine hynv (nonvanishingLocus_sectionsMap_mulRight_subset M A u t ?_)
  refine Set.mem_of_mem_of_subset hyU (Eq.subset ?_)
  rw [← hu]
  exact Stacks.SheafOfModules.nonvanishingLocus_sectionsMap X.toRingedSpace e
    (_root_.SheafOfModules.sectionsMap ((ρ_ M).inv ≫ M ◁ A.unitHomEquiv.symm t) u)

/-! ### Tag 0B90 -/

/-- **[Stacks, Tag 0B90].** Let `k` be an algebraically closed field, let `X` be a proper curve
over `k` and let `g = dim_k H¹(X, 𝒪_X)`. Then `H¹(X, ℒ) = 0` for every invertible
`𝒪_X`-module `ℒ` with `deg(ℒ) ≥ 2g - 1`.

Let `𝒩` be the invertible module of [Stacks, Tag 0B8Z] (2), of degree `g - dim_k H⁰(X, 𝒪_X)`.
Then `ℒ ⊗ 𝒩^{⊗ -1}` has degree `deg(ℒ) - g + dim_k H⁰(X, 𝒪_X)`, so

`dim_k H⁰(ℒ ⊗ 𝒩^{⊗ -1}) - dim_k H¹(ℒ ⊗ 𝒩^{⊗ -1}) = deg(ℒ) - 2g + 2 dim_k H⁰(X, 𝒪_X) ≥ 1`

because `dim_k H⁰(X, 𝒪_X) ≥ 1` on a proper integral scheme; hence `ℒ ⊗ 𝒩^{⊗ -1}` has a nonzero
global section and `isZero_cohomologyOverField_one_of_tensorInverse_section` applies. -/
@[stacks 0B90 "the whole statement: `H¹(X, L) = 0` for every invertible `O_X`-module `L` with \
`deg(L) ≥ 2g - 1` on a proper curve `X` over an algebraically closed field, with `g` the genus"]
public theorem isZero_cohomologyOverField_one_of_two_mul_genus_sub_one_le_invertibleCurveDegree
    [IsAlgClosed k] [IsProper f] [IsCurve k f] (L : X.Modules)
    (hL : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hdeg : 2 * (genus f : ℤ) - 1 ≤ @invertibleCurveDegree k _ X f _
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le L hL) :
    IsZero (cohomologyOverField k f L 1) := by
  set hdim : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  obtain ⟨N, hN, hN₀, hN₁⟩ := exists_invertible_isZero_cohomologyOverField_zero_one k f
  have hNs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property N :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hN
  have hLs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL
  have hMa : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (L ⊗ tensorPowerModule N (-1) : X.Modules) :=
    @isInvertible_tensorSheaf_tensorPowerModule_neg_one X L N hL hN
  have hdegM : @invertibleCurveDegree k _ X f _ hdim
      (L ⊗ tensorPowerModule N (-1) : X.Modules) hMa =
      @invertibleCurveDegree k _ X f _ hdim L hL
        - @invertibleCurveDegree k _ X f _ hdim N hN :=
    @invertibleCurveDegree_tensorSheaf_tensorPowerModule_neg_one k _ X f _ _ hdim N L hN hL
  have hdegN := invertibleCurveDegree_eq_genus_sub_finrank_of_isZero k f hdim N hN hN₀ hN₁
  have hpos := zero_lt_finrank_cohomologyOverField_zero_unit k f
  have hrr := finrank_cohomologyOverField_zero_sub_one_eq k f hdim
    (L ⊗ tensorPowerModule N (-1) : X.Modules) hMa
  have hsec : 0 < Module.finrank k
      (cohomologyOverField k f (L ⊗ tensorPowerModule N (-1) : X.Modules) 0) := by
    rw [hdegM, hdegN] at hrr
    omega
  exact @isZero_cohomologyOverField_one_of_tensorInverse_section k _ X f _ _ hdim N L hNs hN hMa
    hN₁ hsec

end AlgebraicGeometry

end
