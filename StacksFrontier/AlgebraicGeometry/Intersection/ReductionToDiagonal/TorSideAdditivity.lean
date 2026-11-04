module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearMapExactness
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.DivisorFibreCycle
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorLongExactSequence
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.TorSheafSymmetry
public import StacksFrontier.RingTheory.Length.LongExactEuler

/-!
# Additivity of the `Tor` side of the Tor formula

The proof of Tag 0B0W compares, for coherent `𝒪_X`-modules `ℱ` and `𝒢` on a nonsingular
variety `X`, the two cycles

`RHS(ℱ, 𝒢) = [ℱ]_r · [𝒢]_s`  and  `LHS(ℱ, 𝒢) = ∑ₚ (-1)ᵖ [Torₚ^{𝒪_X}(ℱ, 𝒢)]_{r + s - dim X}`,

and its first step is that both are additive in the first variable along a short exact sequence
of coherent sheaves. The cycle-product side `RHS` is
`Stacks.Intersection.ReductionToDiagonal.cycleIntersectionProduct_coherentSheafCycle_add_left`.
This file proves it for the `Tor` side `LHS`, which is
`AlgebraicGeometry.TorFormula.intersectionProductCycle`, the alternating sum of Tag 0AZR:

`LHS(ℱ₂, 𝒢) = LHS(ℱ₁, 𝒢) + LHS(ℱ₃, 𝒢)`.

The source's reason is the long exact sequence of `Tor` sheaves together with additivity of
length, and that is the proof here. Both ingredients are available: the long exact sequence is
`AlgebraicGeometry.TorFormula.torSheaf_exact₁`, `torSheaf_exact₂`, `torSheaf_exact₃` and
`epi_torSheafMap_zero`; `Stacks.SheafOfModules.FlatShortExact.exact_stalkLinearMap` and
`surjective_stalkLinearMap` carry it to the local ring at a point; and
`Module.sum_range_alternating_length_add_of_exact` turns an exact sequence of three families of
finite-length modules into additivity of their alternating sums of lengths.

## Main results

* `Stacks.Intersection.ReductionToDiagonal.sum_range_alternating_sheafMultiplicity_torSheaf_add`
  — the local statement: at a point of relative dimension `k` the alternating sum of the
  multiplicities of the `Tor` sheaves is additive along the short exact sequence.
* `Stacks.Intersection.ReductionToDiagonal.intersectionProductCycle_add_left` — the statement
  for cycles, which is the second of the two additivity steps in the proof of Tag 0B0W.
* `Stacks.Intersection.ReductionToDiagonal.intersectionProductCycle_add_right` — the same in
  the second variable, which the dévissage of Tag 0B0W also runs in.

## Implementation notes

A cycle is its coefficient function, so the proof is pointwise. At a point `z` whose relative
dimension is not `k` every coefficient in sight vanishes, by the definition of
`Stacks.Chow.sheafCycleCoeff`. At a point of relative dimension exactly `k` the coefficient is
the honest length of the stalk, finite by
`Stacks.Chow.isFiniteLength_stalk_of_relativeDimension_eq`, and the three alternating sums are
compared by the Euler-characteristic lemma applied to the three families of stalks of the `Tor`
sheaves and the stalks of the maps of the long exact sequence.

Everything is truncated at `d + 2` where `d` bounds the dimension of `X`, which is where
`AlgebraicGeometry.TorFormula.intersectionProductCycle_apply` already reads the alternating sum
of Tag 0AZR; the Euler-characteristic lemma needs only that the third family vanishes one step
beyond the truncation, which `AlgebraicGeometry.TorFormula.isZero_torSheaf_of_lt` supplies.

Only the first variable has a long exact sequence here:
`AlgebraicGeometry.TorFormula.derivedTensorRight` fixes the second argument of the derived
tensor product, and no symmetry `Torₚ(ℱ, 𝒢) ≅ Torₚ(𝒢, ℱ)` of `Tor` *sheaves* is available in
this library. The second variable is nevertheless covered, because the alternating sum does not
see the sheaves themselves but only their supports and the lengths of their stalks, and those
are symmetric: `AlgebraicGeometry.TorFormula.intersectionProductCycle_comm`.

The regularity of `X` is the single hypothesis `IsRegular X`: the pointwise regularity of the
local rings that `AlgebraicGeometry.TorFormula.isZero_torSheaf_of_lt` and
`intersectionProductCycle_apply` ask for is derived from it by
`AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk`, rather than carried as a second
hypothesis.

No tag is attached here. These are two steps of the proof of Tag 0B0W, not that lemma, which is
`Stacks.Intersection.ReductionToDiagonal.torFormula` in
`StacksFrontier.AlgebraicGeometry.Intersection.ReductionToDiagonal.TorFormulaWhole`.

## References

* [Stacks Project, Lemma 43.19.4 (Tag 0B0W)](https://stacks.math.columbia.edu/tag/0B0W)
* [Stacks Project, Tag 0AZR](https://stacks.math.columbia.edu/tag/0AZR)
* [Stacks Project, Tag 0AZT](https://stacks.math.columbia.edu/tag/0AZT)
* [Stacks Project, Tag 00IV](https://stacks.math.columbia.edu/tag/00IV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.TorFormula
open Stacks.Chow

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Intersection.ReductionToDiagonal

variable {X : Scheme.{u}}

/-! ### The coefficient of the cycle of a coherent sheaf at a point -/

/-- At a point of relative dimension `k` the coefficient of `[ℱ]_k` is the multiplicity of `ℱ`
there, whether or not the point lies in the support: off the support the multiplicity is zero
too. -/
private theorem sheafCycleCoeff_eq_sheafMultiplicity (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ) {z : X}
    (hz : relativeDimension C.dimensionFunction f z = k) :
    sheafCycleCoeff C f F k z = sheafMultiplicity F z := by
  classical
  by_cases hsupp : z ∈ SheafOfModules.supp F
  · simp [sheafCycleCoeff, hsupp, hz]
  · simp [sheafCycleCoeff, hsupp, sheafMultiplicity_eq_zero_of_notMem_supp F hsupp]

/-- At a point whose relative dimension is not `k` the coefficient of `[ℱ]_k` vanishes. -/
private theorem sheafCycleCoeff_eq_zero_of_relativeDimension_ne (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ) {z : X}
    (hz : relativeDimension C.dimensionFunction f z ≠ k) :
    sheafCycleCoeff C f F k z = 0 := by
  classical
  simp [sheafCycleCoeff, hz]

/-- The stalks of a zero sheaf of modules are zero. -/
private theorem subsingleton_stalk_of_isZero (F : X.Modules) (h : IsZero F) (z : X) :
    Subsingleton (F.presheaf.stalk z) := by
  have hz : z ∉ SheafOfModules.supp F :=
    (Scheme.Modules.notMem_supp_iff_isZero_stalk F z).mpr
      (Functor.map_isZero (Scheme.Modules.stalkFunctor X z) h)
  exact not_nontrivial_iff_subsingleton.mp fun hn ↦
    hz ((SheafOfModules.mem_supp_iff_nontrivial_stalk F z).mpr hn)

/-! ### The local additivity -/

/-- **The alternating sum of the multiplicities of the `Tor` sheaves is additive along a short
exact sequence in the first variable.** For `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` a short exact sequence of
coherent sheaves on a regular scheme of dimension at most `d`, `𝒢` a coherent sheaf, and `z` a
point of relative dimension `k`,

`∑ᵢ (-1)ⁱ mult_z Torᵢ(ℱ₂, 𝒢) = ∑ᵢ (-1)ⁱ mult_z Torᵢ(ℱ₁, 𝒢) + ∑ᵢ (-1)ⁱ mult_z Torᵢ(ℱ₃, 𝒢)`.

This is the long exact sequence of `Tor` sheaves, read on stalks at `z`, fed to the
additivity of the Euler characteristic of a long exact sequence. -/
theorem sum_range_alternating_sheafMultiplicity_torSheaf_add (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (hX : IsRegular X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (G : X.Modules)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁)
    (h₂ : _root_.SheafOfModules.IsCoherent S.X₂)
    (h₃ : _root_.SheafOfModules.IsCoherent S.X₃)
    (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hk₁ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX S.X₁ G h₁ hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X S.X₁ G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hk₂ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX S.X₂ G h₂ hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X S.X₂ G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hk₃ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX S.X₃ G h₃ hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X S.X₃ G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {z : X}
    (hz : relativeDimension C.dimensionFunction f z = k) :
    ∑ i ∈ Finset.range (d + 2), ((-1 : ℤ) ^ i) * sheafMultiplicity (torSheaf X S.X₂ G i) z =
      ∑ i ∈ Finset.range (d + 2), ((-1 : ℤ) ^ i) * sheafMultiplicity (torSheaf X S.X₁ G i) z +
        ∑ i ∈ Finset.range (d + 2),
          ((-1 : ℤ) ^ i) * sheafMultiplicity (torSheaf X S.X₃ G i) z := by
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    fun x ↦ hX.isRegularLocalRing_stalk x
  simp only [sheafMultiplicity]
  refine Module.sum_range_alternating_length_add_of_exact
    (A := X.presheaf.stalk z)
    (T₁ := fun p ↦ (torSheaf X S.X₁ G p).presheaf.stalk z)
    (T₂ := fun p ↦ (torSheaf X S.X₂ G p).presheaf.stalk z)
    (T₃ := fun p ↦ (torSheaf X S.X₃ G p).presheaf.stalk z)
    (u := fun p ↦ SheafOfModules.FlatShortExact.stalkLinearMap (torSheafMap S.f G p) z)
    (v := fun p ↦ SheafOfModules.FlatShortExact.stalkLinearMap (torSheafMap S.g G p) z)
    (δ := fun p ↦ SheafOfModules.FlatShortExact.stalkLinearMap (torSheafδ hS G p) z)
    (fun p ↦ ?_) (fun p ↦ ?_) (fun p ↦ ?_) ?_ (fun p ↦ ?_) (fun p ↦ ?_) (fun p ↦ ?_)
    (d + 1) ?_
  · exact SheafOfModules.FlatShortExact.exact_stalkLinearMap _ (torSheaf_exact₁ hS G p) z
  · exact SheafOfModules.FlatShortExact.exact_stalkLinearMap _ (torSheaf_exact₂ hS G p) z
  · exact SheafOfModules.FlatShortExact.exact_stalkLinearMap _ (torSheaf_exact₃ hS G p) z
  · exact SheafOfModules.FlatShortExact.surjective_stalkLinearMap (torSheafMap S.g G 0)
      (epi_torSheafMap_zero hS G) z
  · have := isCoherent_torSheaf_of_isRegular X hX S.X₁ G h₁ hG p
    exact isFiniteLength_stalk_of_relativeDimension_eq C f (torSheaf X S.X₁ G p) (hk₁ p) hz
  · have := isCoherent_torSheaf_of_isRegular X hX S.X₂ G h₂ hG p
    exact isFiniteLength_stalk_of_relativeDimension_eq C f (torSheaf X S.X₂ G p) (hk₂ p) hz
  · have := isCoherent_torSheaf_of_isRegular X hX S.X₃ G h₃ hG p
    exact isFiniteLength_stalk_of_relativeDimension_eq C f (torSheaf X S.X₃ G p) (hk₃ p) hz
  · exact subsingleton_stalk_of_isZero (torSheaf X S.X₃ G (d + 1 + 1))
      (isZero_torSheaf_of_lt X hreg S.X₃ G d (d + 1 + 1) hd (by omega)) z

/-! ### The additivity of cycles -/

/-- **The second additivity of the proof of Stacks 0B0W: the `Tor` side is additive in the first
variable.** For a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of coherent sheaves on a regular
scheme of dimension at most `d`, a coherent sheaf `𝒢`, and a dimension index `k` bounding the
delta-dimension of the supports of all the `Tor` sheaves in play,

`∑ₚ (-1)ᵖ [Torₚ(ℱ₂, 𝒢)]_k = ∑ₚ (-1)ᵖ [Torₚ(ℱ₁, 𝒢)]_k + ∑ₚ (-1)ᵖ [Torₚ(ℱ₃, 𝒢)]_k`,

that is, `LHS(ℱ₂, 𝒢) = LHS(ℱ₁, 𝒢) + LHS(ℱ₃, 𝒢)` for the alternating sum of Tag 0AZR.

The source's reason is the long exact sequence of `Tor` sheaves together with additivity of
length, and that is the proof: the identity holds coefficient by coefficient, by
`sum_range_alternating_sheafMultiplicity_torSheaf_add` at the points of relative dimension `k`
and trivially elsewhere. -/
theorem intersectionProductCycle_add_left (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (G : X.Modules)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁)
    (h₂ : _root_.SheafOfModules.IsCoherent S.X₂)
    (h₃ : _root_.SheafOfModules.IsCoherent S.X₃)
    (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hk₁ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX S.X₁ G h₁ hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X S.X₁ G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hk₂ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX S.X₂ G h₂ hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X S.X₂ G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hk₃ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX S.X₃ G h₃ hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X S.X₃ G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    intersectionProductCycle C f hX S.X₂ G h₂ hG k hk₂ =
      intersectionProductCycle C f hX S.X₁ G h₁ hG k hk₁ +
        intersectionProductCycle C f hX S.X₃ G h₃ hG k hk₃ := by
  classical
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    fun x ↦ hX.isRegularLocalRing_stalk x
  apply Function.locallyFinsuppWithin.ext
  intro z
  simp only [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [intersectionProductCycle_apply C f hX S.X₂ G h₂ hG k hk₂ hreg d hd z,
    intersectionProductCycle_apply C f hX S.X₁ G h₁ hG k hk₁ hreg d hd z,
    intersectionProductCycle_apply C f hX S.X₃ G h₃ hG k hk₃ hreg d hd z]
  by_cases hz : relativeDimension C.dimensionFunction f z = k
  · have hcoeff : ∀ (F : X.Modules) (_ : _root_.SheafOfModules.IsCoherent F) (i : ℕ),
        have := isCoherent_torSheaf_of_isRegular X hX F G ‹_› hG i
        sheafCycleCoeff C f (torSheaf X F G i) k z = sheafMultiplicity (torSheaf X F G i) z :=
      fun F hF i ↦
        have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
        sheafCycleCoeff_eq_sheafMultiplicity C f (torSheaf X F G i) k hz
    simp only [hcoeff S.X₁ h₁, hcoeff S.X₂ h₂, hcoeff S.X₃ h₃]
    exact sum_range_alternating_sheafMultiplicity_torSheaf_add C f hX S hS G h₁ h₂ h₃ hG k
      hk₁ hk₂ hk₃ d hd hz
  · have hcoeff : ∀ (F : X.Modules) (_ : _root_.SheafOfModules.IsCoherent F) (i : ℕ),
        have := isCoherent_torSheaf_of_isRegular X hX F G ‹_› hG i
        sheafCycleCoeff C f (torSheaf X F G i) k z = 0 :=
      fun F hF i ↦
        have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
        sheafCycleCoeff_eq_zero_of_relativeDimension_ne C f (torSheaf X F G i) k hz
    simp only [hcoeff S.X₁ h₁, hcoeff S.X₂ h₂, hcoeff S.X₃ h₃, mul_zero, Finset.sum_const_zero,
      add_zero]

/-! ### The additivity in the second variable -/

/-- **The delta-dimension bound on the supports of the `Tor` sheaves is the same condition in
either order.** The two `Tor` sheaves of a pair of coherent modules have the same support, hence
the same reduced support, so a bound for one order is a bound for the other. -/
theorem torSheafDeltaDimension_le_comm (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X) (F G : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F) (hG : _root_.SheafOfModules.IsCoherent G) (k : ℤ)
    (hFk : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
      schemeDeltaDimension C ((reducedSupport (torSheaf X F G i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k) (i : ℕ) :
    haveI := isCoherent_torSheaf_of_isRegular X hX G F hG hF i
    schemeDeltaDimension C ((reducedSupport (torSheaf X G F i)).subschemeι ≫ f)
      ≤ WithBotTop.coe k := by
  have := isCoherent_torSheaf_of_isRegular X hX F G hF hG i
  have := isCoherent_torSheaf_of_isRegular X hX G F hG hF i
  rw [← reducedSupport_torSheaf_comm F G i]
  exact hFk i

/-- **The `Tor` side of the Tor formula is additive in the second variable too.** For a short
exact sequence `0 → 𝒢₁ → 𝒢₂ → 𝒢₃ → 0` of coherent sheaves on a regular scheme of dimension at
most `d`, a coherent sheaf `ℱ`, and a dimension index `k` bounding the delta-dimension of the
supports of all the `Tor` sheaves in play,

`∑ₚ (-1)ᵖ [Torₚ(ℱ, 𝒢₂)]_k = ∑ₚ (-1)ᵖ [Torₚ(ℱ, 𝒢₁)]_k + ∑ₚ (-1)ᵖ [Torₚ(ℱ, 𝒢₃)]_k`.

Only the first variable has a long exact sequence of `Tor` *sheaves* here, so this is the first
variable's additivity read through the symmetry of the alternating sum,
`AlgebraicGeometry.TorFormula.intersectionProductCycle_comm`. -/
theorem intersectionProductCycle_add_right (C : ChowSituation.{u}) (f : X ⟶ C.S)
    [LocallyOfFiniteType f] (hX : IsRegular X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (F : X.Modules)
    (hF : _root_.SheafOfModules.IsCoherent F)
    (h₁ : _root_.SheafOfModules.IsCoherent S.X₁)
    (h₂ : _root_.SheafOfModules.IsCoherent S.X₂)
    (h₃ : _root_.SheafOfModules.IsCoherent S.X₃) (k : ℤ)
    (hk₁ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F S.X₁ hF h₁ i
      schemeDeltaDimension C ((reducedSupport (torSheaf X F S.X₁ i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hk₂ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F S.X₂ hF h₂ i
      schemeDeltaDimension C ((reducedSupport (torSheaf X F S.X₂ i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (hk₃ : ∀ i : ℕ,
      haveI := isCoherent_torSheaf_of_isRegular X hX F S.X₃ hF h₃ i
      schemeDeltaDimension C ((reducedSupport (torSheaf X F S.X₃ i)).subschemeι ≫ f)
        ≤ WithBotTop.coe k)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    intersectionProductCycle C f hX F S.X₂ hF h₂ k hk₂ =
      intersectionProductCycle C f hX F S.X₁ hF h₁ k hk₁ +
        intersectionProductCycle C f hX F S.X₃ hF h₃ k hk₃ := by
  rw [intersectionProductCycle_comm C f hX F S.X₁ hF h₁ k hk₁
      (torSheafDeltaDimension_le_comm C f hX F S.X₁ hF h₁ k hk₁),
    intersectionProductCycle_comm C f hX F S.X₂ hF h₂ k hk₂
      (torSheafDeltaDimension_le_comm C f hX F S.X₂ hF h₂ k hk₂),
    intersectionProductCycle_comm C f hX F S.X₃ hF h₃ k hk₃
      (torSheafDeltaDimension_le_comm C f hX F S.X₃ hF h₃ k hk₃)]
  exact intersectionProductCycle_add_left C f hX S hS F h₁ h₂ h₃ hF k _ _ _ d hd

end Stacks.Intersection.ReductionToDiagonal

end
