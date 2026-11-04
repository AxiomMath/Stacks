module

public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointFamilyFibreDifferenceExistence
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointInfinityFamilyFibreDifference
import StacksCore.Tactic.StacksAttribute

/-!
# The graph member at the pair `(t, ∞)`, with the extra invertibility discharged

`Stacks.Chow.exists_pointInfinityGraphFamilyMember` produces, from a rational function `gg` on
an integral closed subscheme `V ⊆ X` and a point `t` of the affine chart, the subvariety of
`X ×_S ℙ¹_S` whose fibre difference at the pair `(t, ∞)` is `pr_{X,*}(div_V(gg))`. It takes one
invertibility hypothesis, `baseSectionOn t + g₀`, which is not the source's: the graph
construction of Tag 02RQ starts from a unit *section* on an open rather than from a rational
map, so the section `σ = baseSectionOn t + g₀` has to be an honest unit of `Γ(V, U)`.

This file removes it. For a rational function represented by a unit section `g₀` on an affine
dense open `U`, the locus where `baseSectionOn t + g₀` is invertible is a basic open of `U`; it
is again affine, and it is nonempty — hence dense — unless `baseSectionOn t + g₀` vanishes
identically on `U`. So either the open can be shrunk, or that degenerate case holds, and then
`div_V(gg) = 0`: `g₀ = -baseSectionOn t` makes `gg` the restriction of `baseSectionOn (-t)`, a
ratio of the two base units `-t` and `1`, so `pr_{X,*}(div_V(gg)) = 0` by
`Stacks.Chow.principalDivisorPushforward_eq_zero_of_baseSectionOn_mul`.

Unlike the two-affine-point case there is no second degenerate branch (no analogue of
`g₀ = 1`, which there came from the Möbius section's own denominator) and no hypothesis
analogous to `t ≠ t'`: the point at infinity is never a point of the affine chart.

## Main results

* `Stacks.Chow.exists_pointInfinityGraphFamilyMember_or_eq_zero` — **the production step of part
  (3) of Tag 0B07 at the pair `(t, ∞)`, with `hw` discharged**: either the pushforward of the
  principal divisor vanishes, or there is a member of the family realising it as a fibre
  difference at `(t, ∞)`.
* `Stacks.Chow.exists_pointInfinityFamilyFibreDifferences` — **Tag 02S4 part (4) at the pair
  `(t, ∞)`**: the locally finite family of members whose total fibre difference at `(t, ∞)` is a
  given cycle rationally equivalent to zero.
* `Stacks.Chow.pointInfinityFibreDifferences` — the basic rational equivalences at the pair
  `(t, ∞)`.
* `Stacks.Chow.rationalEquivalences_eq_closure_pointInfinityFibreDifferences` — **Tag 0AZI at the
  pair `(t, ∞)`, for an arbitrary point `t` of the affine chart**: those differences generate
  exactly the cycles rationally equivalent to zero.

## References

* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 0AZI](https://stacks.math.columbia.edu/tag/0AZI)
* [Stacks Project, Tag 0B07](https://stacks.math.columbia.edu/tag/0B07)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The production step with the extra invertibility discharged -/

/-- **The production step of part (3) of Tag 0B07 at the pair `(t, ∞)`, with the hypothesis of
`Stacks.Chow.exists_pointInfinityGraphFamilyMember` that the source does not have discharged.**
Let `V ⊆ X` be an integral closed subscheme of delta-dimension `k + 1`, let `gg` be a rational
function on it, and let `t` be a point of the affine chart. Then either `pr_{X,*}(div_V(gg))` is
the zero cycle, or there is a closed subvariety `W ⊆ X ×_S ℙ¹_S` with every property Tag 02S4
part (3) asks of a family member at the pair `(t, ∞)` and with
`pr_{X,*}(div_V(gg)) = [W_t]_k - [W_∞]_k`.

Only the degenerate branch uses that every nonzero global function on the base is invertible. -/
theorem exists_pointInfinityGraphFamilyMember_or_eq_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (gg : (rationalFunctions V.subscheme)ˣ) (t : Γ(C.S, ⊤))
    (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) :
    (∀ x : X, principalDivisorPushforward C f V hV gg x = 0) ∨
      ∃ W : (projectiveLineProduct f).IdealSheafData,
        IsIntegral W.subscheme ∧
        (∀ ξ : genericPoints W.subscheme,
          relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1) ∧
        ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t) ∧
        ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f) ∧
        ((W.support : Set (projectiveLineProduct f)) ⊆
          pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ⁻¹' (V.support : Set X)) ∧
        (∀ x : X, principalDivisorPushforward C f V hV gg x =
          (cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k).1 x -
            (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k).1 x) := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  obtain ⟨U, hUaff, hU, s, hs⟩ := exists_unit_section V.subscheme gg
  have hUne : Nonempty U.toScheme := Set.nonempty_coe_sort.mpr hU.nonempty
  have hηU : genericPoint V.subscheme ∈ U :=
    ((genericPoint_spec V.subscheme).mem_open_set_iff U.isOpen).mpr
      (by simpa using hU.nonempty)
  by_cases h0 : baseSectionOn (V.subschemeι ≫ f) U t + (s : Γ(V.subscheme, U)) = 0
  · -- `s = -baseSectionOn t`: the rational function is the base function `-t/1`
    left
    have hb : baseSectionOn (V.subschemeι ≫ f) U t = -(s : Γ(V.subscheme, U)) :=
      add_eq_zero_iff_eq_neg.mp h0
    have hbIsUnit : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t) := hb ▸ s.isUnit.neg
    have hone : (1 : Γ(V.subscheme, U)) ≠ 0 := by
      intro h0'
      have hUb : U = ⊥ := by
        rw [← Scheme.basicOpen_one (X := V.subscheme) (U := U), h0', Scheme.basicOpen_zero]
      exact absurd hU.nonempty (by rw [hUb]; simp)
    have hzero : baseSectionOn (V.subschemeι ≫ f) U (0 : Γ(C.S, ⊤)) = 0 := by
      rw [baseSectionOn, map_zero, map_zero]
    have ht : IsUnit t := by
      refine hbase t fun h0t => hone ?_
      rw [h0t, hzero] at hbIsUnit
      exact (isUnit_zero_iff.mp hbIsUnit).symm
    have hbsneg : baseSectionOn (V.subschemeι ≫ f) U (-t) =
        -baseSectionOn (V.subschemeι ≫ f) U t := by
      rw [baseSectionOn, baseSectionOn, map_neg, map_neg]
    have hbsone : baseSectionOn (V.subschemeι ≫ f) U (1 : Γ(C.S, ⊤)) = 1 := by
      rw [baseSectionOn, map_one, map_one]
    have hrel' : baseSectionOn (V.subschemeι ≫ f) U (-t) =
        (s : Γ(V.subscheme, U)) * baseSectionOn (V.subschemeι ≫ f) U (1 : Γ(C.S, ⊤)) := by
      rw [hbsneg, hbsone, mul_one, hb, neg_neg]
    intro x
    rw [principalDivisorPushforward_eq_zero_of_baseSectionOn_mul C f V hV gg U hU s hs ht.neg
      isUnit_one hrel']
    rfl
  · -- the generic case: shrink `U` to the basic open of `baseSectionOn t + s`
    right
    set c : Γ(V.subscheme, U) :=
      baseSectionOn (V.subschemeι ≫ f) U t + (s : Γ(V.subscheme, U)) with hcdef
    set D : V.subscheme.Opens := V.subscheme.basicOpen c with hDdef
    have hDU : D ≤ U := V.subscheme.basicOpen_le c
    have hDne : Set.Nonempty ((D : V.subscheme.Opens) : Set V.subscheme) :=
      (Opens.ne_bot_iff_nonempty _).mp fun hb => h0 ((basicOpen_eq_bot_iff c).mp hb)
    have hD : Dense ((D : V.subscheme.Opens) : Set V.subscheme) := D.isOpen.dense hDne
    have hDne' : Nonempty D.toScheme := Set.nonempty_coe_sort.mpr hDne
    have hDqc : QuasiCompact D.ι :=
      AlgebraicGeometry.quasiCompact_ι_of_isCompact D (hUaff.basicOpen c).isCompact
    have hres : IsUnit (V.subscheme.presheaf.map (homOfLE hDU).op c) :=
      V.subscheme.toRingedSpace.isUnit_res_basicOpen c
    rw [hcdef, map_add] at hres
    have hsu : IsUnit (V.subscheme.presheaf.map (homOfLE hDU).op (s : Γ(V.subscheme, U))) :=
      s.isUnit.map (V.subscheme.presheaf.map (homOfLE hDU).op).hom
    have hw : IsUnit (baseSectionOn (V.subschemeι ≫ f) D t +
        (hsu.unit : Γ(V.subscheme, D))) := by
      rw [hsu.unit_spec, ← baseSectionOn_res (V.subschemeι ≫ f) hDU t]
      exact hres
    have hgD : ofSection V.subscheme ⟨D, hD⟩ (hsu.unit : Γ(V.subscheme, D)) =
        (gg : rationalFunctions V.subscheme) := by
      rw [hsu.unit_spec, ofSection_res hDU hU hD (s : Γ(V.subscheme, U))]
      exact hs
    exact exists_pointInfinityGraphFamilyMember C f k V hV hdim gg D hD hsu.unit hgD t hw

/-! ### The locally finite family of fibre differences at the pair `(t, ∞)` -/

/-- The coefficient at `x : X` of the sum over `j` of the fibre cycle at `t` minus the fibre
cycle at `∞` of a family `W` of closed subschemes of `X ×_S ℙ¹_S`. This is
`Stacks.Chow.pointFamilyFibreDifferenceCoefficient` at the pair `(t, ∞)` in place of an arbitrary
second point. -/
def pointInfinityFamilyFibreDifferenceCoefficient (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (t : Γ(C.S, ⊤))
    {J : Type u} (W : J → (projectiveLineProduct f).IdealSheafData) (x : X) : ℤ :=
  ∑ᶠ j : J,
    ((cycleAssociatedToClosedSubscheme C f (pointFiber f t (W j)).subschemeι k).1 x -
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f (W j)).subschemeι k).1 x)

/-- **Tag 02S4 part (4) at the pair `(t, ∞)`.** A `k`-cycle rationally equivalent to zero is the
total fibre difference, at the pair `(t, ∞)`, of a locally finite family of integral closed
subschemes of `X ×_S ℙ¹_S`, each of relative dimension `k + 1` at its generic points and
contained in neither section.

This is `Stacks.Chow.exists_pointFamilyFibreDifferences` with the pair `(t, ∞)` in place of an
arbitrary pair of the affine chart. The index type is not the one witnessing rational
equivalence but the subtype of those members whose principal divisor does not already vanish:
that is where the degenerate case of
`Stacks.Chow.exists_pointInfinityGraphFamilyMember_or_eq_zero` goes, and dropping it changes no
coefficient. -/
theorem exists_pointInfinityFamilyFibreDifferences (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (α : CycleGroup C f k)
    (hα : IsRationallyEquivalentToZero C f k α) (t : Γ(C.S, ⊤))
    (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) :
    ∃ (J : Type u) (W : J → (projectiveLineProduct f).IdealSheafData)
      (_ : ∀ j, IsIntegral (W j).subscheme)
      (_ : ∀ j, ∀ ξ : genericPoints (W j).subscheme,
        relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1),
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (pointSection f t)) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
      LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))) ∧
      (∀ x : X, α.1 x = pointInfinityFamilyFibreDifferenceCoefficient C f k t W x) := by
  classical
  obtain ⟨J, V, hV, hdim, hLocal, g, hg⟩ := hα
  have hstep := fun j ↦
    exists_pointInfinityGraphFamilyMember_or_eq_zero C f k (V j) (hV j) (hdim j) (g j) t hbase
  set N : Set J := {j | ¬ ∀ x : X, principalDivisorPushforward C f (V j) (hV j) (g j) x = 0}
  choose W hWint hWdim hWT hWInf hWsupp hWcoeff using fun j : N ↦ (hstep j.1).resolve_left j.2
  refine ⟨N, W, hWint, hWdim, hWT, hWInf, ?_, fun x ↦ ?_⟩
  · exact LocallyFinite.subset
      ((hLocal.preimage_continuous
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).continuous).comp_injective
          Subtype.val_injective) hWsupp
  · have hWc : ∀ j : N,
        (cycleAssociatedToClosedSubscheme C f (pointFiber f t (W j)).subschemeι k).1 x -
            (cycleAssociatedToClosedSubscheme C f (infinityFiber f (W j)).subschemeι k).1 x =
          principalDivisorPushforward C f (V j.1) (hV j.1) (g j.1) x :=
      fun j ↦ (hWcoeff j x).symm
    have hmem : ∀ j ∈ Function.support
        (fun j : J ↦ principalDivisorPushforward C f (V j) (hV j) (g j) x), j ∈ N :=
      fun j hj hall ↦ hj (hall x)
    rw [hg x, principalDivisorFamilyCoefficient, pointInfinityFamilyFibreDifferenceCoefficient,
      finsum_congr hWc]
    exact (finsum_subtype_eq_finsum_of_support_subset
      (fun j : J ↦ principalDivisorPushforward C f (V j) (hV j) (g j) x) _ hmem).symm

/-! ### The basic rational equivalences at the pair `(t, ∞)` -/

/-- The basic rational equivalences at the pair `(t, ∞)` of a point `t` of the affine chart and
the point at infinity: the differences `[W_t]ₖ - [W_∞]ₖ` of the two fibre cycles of an integral
closed subscheme `W ⊆ X ×_S ℙ¹_S` of relative dimension `k + 1` contained in neither section.
This is `Stacks.Chow.pointFibreDifferences` at the pair `(t, ∞)` in place of an arbitrary pair of
the affine chart, and `Stacks.Chow.fibreDifferences` of Tag 0AZG without the traditional choice
`a = 0` at the finite point. -/
def pointInfinityFibreDifferences (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (t : Γ(C.S, ⊤)) : Set (CycleGroup C p k) :=
  {γ | ∃ W : (projectiveLineProduct p).IdealSheafData,
    IsIntegral W.subscheme ∧
    (∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1) ∧
    (¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t)) ∧
    (¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p)) ∧
    γ = cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k -
      cycleAssociatedToClosedSubscheme C p (infinityFiber p W).subschemeι k}

/-- A basic rational equivalence at the pair `(t, ∞)` generates. -/
theorem sub_cycleAssociatedToPointInfinityFibres_mem_closure (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (t : Γ(C.S, ⊤))
    (W : (projectiveLineProduct p).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection p)) :
    cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k -
        cycleAssociatedToClosedSubscheme C p (infinityFiber p W).subschemeι k ∈
      AddSubgroup.closure (pointInfinityFibreDifferences C p k t) :=
  AddSubgroup.subset_closure ⟨W, hW, hDim, hT, hInf, rfl⟩

/-- **Tag 0AZI at the pair `(t, ∞)`, for an arbitrary point `t` of the affine chart.** On a
variety over an algebraically closed field the basic rational equivalences at the pair `(t, ∞)`
generate exactly the group of `k`-cycles rationally equivalent to zero.

The inclusion `⊇` is part (2) at the pair,
`Stacks.Chow.pointFiberCycle_rationallyEquivalent_infinityFiberCycle`. The inclusion `⊆` is the
production step `Stacks.Chow.exists_pointInfinityGraphFamilyMember_or_eq_zero`, assembled by
`Stacks.Chow.exists_pointInfinityFamilyFibreDifferences` and made a finite sum by compactness of
`X ×_S ℙ¹_S`. The generating set `Stacks.Chow.fibreDifferences` of Tag 0AZG, which has the two
distinguished points hard-coded, is never unfolded. Unlike the two-affine-point case there is no
hypothesis analogous to `t ≠ t'`: the point at infinity is never a point of the affine chart. -/
theorem rationalEquivalences_eq_closure_pointInfinityFibreDifferences (Kf : Type u) [Field Kf]
    [IsAlgClosed Kf] (C : ChowSituation.{u})
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf)) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)] (k : ℤ) (t : Γ(C.S, ⊤))
    (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) :
    rationalEquivalences C p k = AddSubgroup.closure (pointInfinityFibreDifferences C p k t) := by
  refine le_antisymm (fun α hα ↦ ?_) ?_
  · rw [mem_rationalEquivalences] at hα
    obtain ⟨J, W, hInt, hDim, hT, hInf, hLocal, hCoeff⟩ :=
      exists_pointInfinityFamilyFibreDifferences C p k α hα t hbase
    have : CompactSpace (projectiveLineProduct p) :=
      compactSpace_projectiveLineProduct Kf C hC p
    have : Finite J := finite_of_locallyFinite_of_nonempty
      (fun j ↦ ((W j).support : Set (projectiveLineProduct p))) hLocal
      (fun j ↦ @nonempty_support_of_isIntegral _ (W j) (hInt j))
    let _ : Fintype J := Fintype.ofFinite J
    set γ : J → CycleGroup C p k := fun j ↦
      cycleAssociatedToClosedSubscheme C p (pointFiber p t (W j)).subschemeι k -
        cycleAssociatedToClosedSubscheme C p (infinityFiber p (W j)).subschemeι k with hγdef
    have hsum : (∑ j, γ j) ∈ AddSubgroup.closure (pointInfinityFibreDifferences C p k t) :=
      AddSubmonoid.sum_mem
        (AddSubgroup.closure (pointInfinityFibreDifferences C p k t)).toAddSubmonoid
        fun j _ ↦ sub_cycleAssociatedToPointInfinityFibres_mem_closure C p k t (W j)
          (hInt j) (hDim j) (hT j) (hInf j)
    have hval : α = ∑ j, γ j := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      have hrhs : ((∑ j, γ j : CycleGroup C p k) : AlgebraicCycle X ℤ) x =
          ∑ j, ((cycleAssociatedToClosedSubscheme C p
              (pointFiber p t (W j)).subschemeι k).1 x -
            (cycleAssociatedToClosedSubscheme C p
              (infinityFiber p (W j)).subschemeι k).1 x) := by
        simp [hγdef]
      rw [hrhs, hCoeff x, pointInfinityFamilyFibreDifferenceCoefficient,
        finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by intro j _; simp)]
    rw [hval]
    exact hsum
  · refine (AddSubgroup.closure_le (rationalEquivalences C p k)).2 ?_
    rintro γ ⟨W, hW, hDim, hT, hInf, rfl⟩
    have := hW
    exact pointFiberCycle_rationallyEquivalent_infinityFiberCycle C p W t k hDim hT hInf

end Stacks.Chow

end
