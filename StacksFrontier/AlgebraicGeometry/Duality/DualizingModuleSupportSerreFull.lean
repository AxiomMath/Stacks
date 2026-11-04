module

public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleSupportSerre
import all StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleSupportSerre
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Depth
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleOfComplex
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DerivedStalkHomology
public import StacksFrontier.AlgebraicGeometry.Properties.DimensionFunctionStalk
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.RingTheory.Dualizing.CanonicalModuleDepth
public import StacksFrontier.Topology.Dimension.DimensionFunctionConnected
public import StacksFrontier.Topology.Sheaves.Modules.SupportCoproduct

/-!
# Support and Serre's condition for the dualizing module of a dualizing complex

Let `X` be a connected Noetherian scheme with a dualizing complex `K` and let `ω` be the
associated dualizing module, the cohomology sheaf of `K` in the leftmost degree `n` in which `K`
has nonvanishing cohomology (`Stacks.Duality.IsDualizingModuleOf`). [Stacks, Tag 0AWK] says that
the support of `ω` is the union of the irreducible components of `X` of maximal dimension with
respect to any dimension function, and that `ω` is a coherent `𝒪_X`-module having property `(S₂)`.

A component of `X` is named by the point of `TopologicalSpace.genericPoints X` whose closure it
is, and it has maximal dimension for the dimension function `δ` when `δ` takes its largest value
at that generic point.

## Main results

* `Stacks.Duality.IsDualizingModuleOf.neg_eq_max_associatedShiftFunction` — `-n` is the largest
  value of the dimension function attached to `K` at a generic point of `X` (the convention of
  [Stacks, Section 0AWH]).
* `Stacks.Duality.IsDualizingModuleOf.stalk_dichotomy` — at a point of a component of maximal
  dimension the stalk of `ω` is the canonical module of the local ring; at any other point it
  vanishes.
* `Stacks.Duality.IsDualizingModuleOf.supp_eq_maxDimensionalComponents_of_dimensionFunction` —
  the support clause, for an arbitrary dimension function on `X`.
* `Stacks.Duality.IsDualizingModuleOf.sheafHasPropertySk_two_of_dualizing` — `ω` satisfies `(S₂)`.
* `Stacks.Duality.IsDualizingModuleOf.supp_eq_and_isCoherent_and_sheafHasPropertySk_two` —
  **[Stacks, Tag 0AWK]**, the three assertions together.

## Implementation notes

The proof is the source's. Let `δ` be the dimension function attached to `K` ([Stacks, Tag 0AWF],
`Stacks.Duality.associatedShiftFunction` together with
`Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction`): the
derived stalk of `K` at `x`, shifted by `-δ(x)`, is a normalized dualizing complex over
`𝒪_{X,x}`. Since taking stalks is exact, the stalk of `H^i(K)` at `x` is the cohomology of that
normalized complex in degree `i + δ(x)`, which vanishes below `-dim 𝒪_{X,x}` and is the canonical
module in degree `-dim 𝒪_{X,x}` (`Stacks.Duality.stalk_homology_of_isDualizingComplex`, from
[Stacks, Tag 0A7U]). The dimension of `𝒪_{X,x}` is `δ(ξ) - δ(x)` for a generic point `ξ ⤳ x` at
which `δ` is largest among the generalizations of `x`
(`AlgebraicGeometry.DimensionFunction.exists_genericPoint_ringKrullDim_stalk_eq`). At a generic
point the local ring has dimension zero and the canonical module is nonzero, so `H^{-δ(ξ)}(K) ≠ 0`
and `n ≤ -δ(ξ)`; conversely a point where the stalk of `H^n(K)` is nonzero gives `n ≥ -δ(ξ)`.
Hence `-n` is the largest value of `δ` at a generic point, and at a point `x` the stalk of
`ω = H^n(K)` is the canonical module of `𝒪_{X,x}` when the component through `x` on which `δ` is
largest has maximal dimension, and is zero otherwise. This is the local statement
[Stacks, Tag 0AWE] read on every local ring of `X`: its support clause is the dichotomy, and its
`(S₂)` clause is the depth bound `Dualizing.min_two_le_depth_canonicalModule`.

The support for an arbitrary dimension function follows because, `X` being connected, two
dimension functions differ by a constant ([Stacks, Tag 02IB],
`TopologicalSpace.DimensionFunction.maximalComponents_eq`). Connectedness enters through that
step alone; the dichotomy and `(S₂)` hold on any Noetherian scheme.

Serre's condition is `AlgebraicGeometry.SheafHasPropertySk` of [Stacks, Tag 0341], a pointwise
condition on the stalks over the local rings of `X`. A module with
`depth ≥ min(dim 𝒪_{X,x}, 2)` and support of dimension at most `dim 𝒪_{X,x}` satisfies the
inequality defining `(S₂)` at that point, and a vanishing stalk satisfies it because the dimension
of its support is `⊥`.

`D(𝒪_X)` is an instance argument, inherited from `Stacks.Duality.IsDualizingModuleOf`, so no
model of the derived category of `X.Modules` is pinned. The derived category of
`ModuleCat 𝒪_{X,x}` is at `HasDerivedCategory.standard`, forced by
`Dualizing.IsNormalizedDualizingComplex`, which bakes that model into its own type.

## References

* [Stacks Project, Tag 0AWK](https://stacks.math.columbia.edu/tag/0AWK)
* [Stacks Project, Tag 0AWE](https://stacks.math.columbia.edu/tag/0AWE)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 02IB](https://stacks.math.columbia.edu/tag/02IB)
* [Stacks Project, Tag 0341](https://stacks.math.columbia.edu/tag/0341)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.Duality

variable {X : Scheme.{u}} [IsNoetherian X] [HasDerivedCategory.{w} X.Modules] {ω : X.Modules}
  {K : DerivedCategory X.Modules} {n : ℤ}

/-- The dimension function attached to a dualizing complex, as a
`TopologicalSpace.DimensionFunction` ([Stacks, Tag 0AWF]). -/
theorem exists_dimensionFunction_eq_associatedShiftFunction (hK : IsDualizingComplex K) :
    ∃ D : DimensionFunction X, ∀ x : X, D x = associatedShiftFunction K x :=
  (isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction hK).2.2

/-- At the generic point `ξ` of an irreducible component the stalk of `H^{-δ(ξ)}(K)` is nonzero,
so `n ≤ -δ(ξ)`. -/
theorem IsDualizingModuleOf.le_neg_associatedShiftFunction (h : IsDualizingModuleOf ω K n)
    {ξ : X} (hξ : ξ ∈ genericPoints X) : n ≤ -associatedShiftFunction K ξ := by
  have hd : ringKrullDim (X.presheaf.stalk ξ) = ((0 : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X ξ).mpr hξ
  obtain ⟨-, L, hL, ⟨e⟩⟩ := stalk_homology_of_isDualizingComplex h.isDualizingComplex ξ
    (associatedShiftFunction K ξ) 0 hd (by simp)
  have hnt := _root_.Dualizing.nontrivial_homology_neg_ringKrullDim L hL 0 hd
  by_contra hlt
  have hzero := h.isZero_of_lt (-associatedShiftFunction K ξ) (by omega)
  have hsub := ModuleCat.isZero_iff_subsingleton.mp
    ((modulesStalkFunctor ξ).map_isZero hzero)
  exact (not_subsingleton_iff_nontrivial.mpr hnt)
    (e.toLinearEquiv.toEquiv.subsingleton_congr.mp hsub)

/-- At a point `x` there is a generic point `ξ ⤳ x` at which the dimension function attached to
`K` is largest among the generalizations of `x`, and `dim 𝒪_{X,x} = δ(ξ) - δ(x)`. -/
private theorem exists_genericPoint_max_associatedShiftFunction (hK : IsDualizingComplex K)
    (x : X) : ∃ ξ ∈ genericPoints X, ξ ⤳ x ∧
      (∀ η : X, η ⤳ x → associatedShiftFunction K η ≤ associatedShiftFunction K ξ) ∧
      ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
        (d : ℤ) = associatedShiftFunction K ξ - associatedShiftFunction K x := by
  obtain ⟨D, hD⟩ := exists_dimensionFunction_eq_associatedShiftFunction hK
  obtain ⟨ξ, hξ, hξx, hmax, d, hd, hdξ⟩ :=
    DimensionFunction.exists_genericPoint_ringKrullDim_stalk_eq D x
  rw [hD, hD] at hdξ
  exact ⟨ξ, hξ, hξx, fun η hη => by rw [← hD, ← hD]; exact hmax η hη, d, hd, hdξ⟩

/-- **The leftmost degree of a dualizing complex.** `-n` is the largest value at a generic point
of `X` of the dimension function attached to `K`. -/
theorem IsDualizingModuleOf.neg_eq_max_associatedShiftFunction (h : IsDualizingModuleOf ω K n) :
    ∃ ξ₀ ∈ genericPoints X, n = -associatedShiftFunction K ξ₀ := by
  obtain ⟨x, hx⟩ : ∃ x : X, ¬ Subsingleton ((modulesStalkFunctor x).obj
      ((DerivedCategory.homologyFunctor X.Modules n).obj K)) := by
    by_contra hall
    push Not at hall
    exact h.nonzero (isZero_of_subsingleton_modulesStalkFunctor _ hall)
  obtain ⟨ξ, hξ, -, -, d, hd, hdξ⟩ :=
    exists_genericPoint_max_associatedShiftFunction h.isDualizingComplex x
  obtain ⟨hvan, -⟩ := stalk_homology_of_isDualizingComplex h.isDualizingComplex x
    (associatedShiftFunction K ξ) d hd (by omega)
  exact ⟨ξ, hξ, le_antisymm (h.le_neg_associatedShiftFunction hξ)
    (not_lt.mp fun hlt => hx (hvan n (by omega)))⟩

/-- **The stalks of a dualizing module.** At a point `x` lying on an irreducible component on
which the dimension function `δ` attached to `K` is largest, the stalk of `ω` is the canonical
module `H^{-d}(L)` of a normalized dualizing complex `L` over `𝒪_{X,x}`, where `d = dim 𝒪_{X,x}`;
at every other point the stalk of `ω` vanishes. -/
theorem IsDualizingModuleOf.stalk_dichotomy (h : IsDualizingModuleOf ω K n) (x : X) :
    (x ∈ {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧
        ∀ η ∈ genericPoints X, associatedShiftFunction K η ≤ associatedShiftFunction K ξ} ∧
      ∃ (L : DerivedCategory (ModuleCat.{u} (X.presheaf.stalk x))) (d : ℕ),
        _root_.Dualizing.IsNormalizedDualizingComplex.{u, u} L ∧
          ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
            Nonempty ((modulesStalkFunctor x).obj ω ≅
              (DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x))
                (-(d : ℤ))).obj L)) ∨
    (x ∉ {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧
        ∀ η ∈ genericPoints X, associatedShiftFunction K η ≤ associatedShiftFunction K ξ} ∧
      Subsingleton ((modulesStalkFunctor x).obj ω)) := by
  obtain ⟨ξ₀, hξ₀, hn⟩ := h.neg_eq_max_associatedShiftFunction
  obtain ⟨ξ, hξ, hξx, hmax', d, hd, hdξ⟩ :=
    exists_genericPoint_max_associatedShiftFunction h.isDualizingComplex x
  have hle := h.le_neg_associatedShiftFunction hξ
  obtain ⟨hvan, L, hL, ⟨e⟩⟩ := stalk_homology_of_isDualizingComplex h.isDualizingComplex x
    (associatedShiftFunction K ξ) d hd (by omega)
  have hω := h.eq_homology
  subst hω
  rcases eq_or_lt_of_le hle with heq | hlt
  · left
    refine ⟨⟨ξ, hξ, specializes_iff_mem_closure.mp hξx, fun η hη => ?_⟩, L, d, hL, hd, ?_⟩
    · have := h.le_neg_associatedShiftFunction hη
      omega
    · rw [heq]
      exact ⟨e⟩
  · right
    refine ⟨fun ⟨ξ', hξ', hxξ', hmaxξ'⟩ => ?_, hvan n (by omega)⟩
    have h1 := hmaxξ' ξ₀ hξ₀
    have h2 := hmax' ξ' (specializes_iff_mem_closure.mpr hxξ')
    omega

/-- The support of the dualizing module, for the dimension function attached to `K`. -/
theorem IsDualizingModuleOf.supp_eq_setOf_associatedShiftFunction
    (h : IsDualizingModuleOf ω K n) :
    (⟨ω.val, ω.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp =
      {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧
        ∀ η ∈ genericPoints X, associatedShiftFunction K η ≤ associatedShiftFunction K ξ} := by
  ext x
  rw [AlgebraicGeometry.SheafOfModules.mem_supp_iff_nontrivial_stalkFunctor]
  rcases h.stalk_dichotomy x with ⟨hx, L, d, hL, hd, ⟨e⟩⟩ | ⟨hx, hsub⟩
  · exact iff_of_true (e.toLinearEquiv.toEquiv.nontrivial_congr.mpr
      (_root_.Dualizing.nontrivial_homology_neg_ringKrullDim L hL d hd)) hx
  · exact iff_of_false (not_nontrivial_iff_subsingleton.mpr hsub) hx

/-- **The support of a dualizing module.** On a connected Noetherian scheme the support of the
dualizing module of a dualizing complex is the union of the irreducible components of maximal
dimension, for any dimension function `δ` on `X`. -/
theorem IsDualizingModuleOf.supp_eq_maxDimensionalComponents_of_dimensionFunction [ConnectedSpace X]
    (h : IsDualizingModuleOf ω K n) (δ : DimensionFunction X) :
    (⟨ω.val, ω.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp =
      {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧
        ∀ η ∈ genericPoints X, δ η ≤ δ ξ} := by
  obtain ⟨D, hD⟩ := exists_dimensionFunction_eq_associatedShiftFunction h.isDualizingComplex
  rw [h.supp_eq_setOf_associatedShiftFunction]
  simp_rw [← hD]
  exact DimensionFunction.maximalComponents_eq
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) D δ

/-- **Serre's condition for a dualizing module.** The dualizing module of a dualizing complex on
a Noetherian scheme satisfies `(S₂)`: at a point where its stalk is the canonical module of the
local ring the depth bound for canonical modules applies, and at a point where the stalk vanishes
the condition is empty. -/
theorem IsDualizingModuleOf.sheafHasPropertySk_two_of_dualizing (h : IsDualizingModuleOf ω K n) :
    SheafHasPropertySk X ω 2 := by
  intro x
  rcases h.stalk_dichotomy x with ⟨-, L, d, hL, hd, ⟨e⟩⟩ | ⟨-, hsub⟩
  · let φ := (stalkLinearEquivModulesStalkFunctor ω x).trans e.toLinearEquiv
    have hdepth := _root_.Dualizing.min_two_le_depth_canonicalModule d L hL hd
    rw [← Module.depth_eq_depth_of_linearEquiv _ φ] at hdepth
    have hsupp := (Module.supportDim_eq_of_equiv φ).trans_le
      ((Module.supportDim_le_ringKrullDim _ _).trans (le_of_eq hd))
    rcases le_total (d : ℕ∞) 2 with hle | hle
    · refine (min_le_right _ _).trans (hsupp.trans ?_)
      rw [min_eq_left hle] at hdepth
      exact_mod_cast hdepth
    · refine (min_le_left _ _).trans ?_
      rw [min_eq_right hle] at hdepth
      exact WithBot.coe_le_coe.mpr hdepth
  · have : Subsingleton ↑(TopCat.Presheaf.stalk
        (SheafOfModules.val (R := structureSheafRing X.toRingedSpace) ω).presheaf x) :=
      (stalkLinearEquivModulesStalkFunctor ω x).toEquiv.subsingleton_congr.mpr hsub
    rw [Module.supportDim_eq_bot_of_subsingleton]
    exact (min_le_right _ _).trans bot_le

/-- **Stacks Project, Tag 0AWK.** Let `X` be a connected Noetherian scheme and let `ω` be a
dualizing module on `X`, the cohomology sheaf of a dualizing complex `K` in the leftmost degree
`n` in which `K` has nonvanishing cohomology. Then the support of `ω` is the union of the
irreducible components of maximal dimension with respect to any dimension function `δ`, and `ω`
is a coherent `𝒪_X`-module having property `(S₂)`. -/
@[stacks 0AWK]
theorem IsDualizingModuleOf.supp_eq_and_isCoherent_and_sheafHasPropertySk_two
    [ConnectedSpace X] (h : IsDualizingModuleOf ω K n) :
    (∀ δ : DimensionFunction X,
      (⟨ω.val, ω.isSheaf⟩ : RingedSpace.ModuleSheaf.{u} X.toRingedSpace).supp =
        {x : X | ∃ ξ ∈ genericPoints X, x ∈ closure {ξ} ∧
          ∀ η ∈ genericPoints X, δ η ≤ δ ξ}) ∧
      _root_.SheafOfModules.IsCoherent ω ∧ SheafHasPropertySk X ω 2 :=
  ⟨h.supp_eq_maxDimensionalComponents_of_dimensionFunction, h.isCoherent,
    h.sheafHasPropertySk_two_of_dualizing⟩

end Stacks.Duality

end
