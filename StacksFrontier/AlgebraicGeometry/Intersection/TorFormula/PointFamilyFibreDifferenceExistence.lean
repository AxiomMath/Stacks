module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.GeometricRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisor
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.PointFamilyFibreDifference
import StacksCore.Tactic.StacksAttribute

/-!
# The graph member at an arbitrary pair, with the two extra invertibilities discharged

`Stacks.Chow.exists_pointGraphFamilyMember` produces, from a rational function `gg` on an
integral closed subscheme `V ⊆ X` and a pair of points `t`, `t'` of the affine chart, the
subvariety of `X ×_S ℙ¹_S` whose fibre difference at that pair is `pr_{X,*}(div_V(gg))`. It
takes three invertibility hypotheses: `t - t'`, which is the source's `a ≠ b`, and `1 - g₀` and
`t - g₀ t'`, which are *not* the source's. They are there because the graph construction of Tag
02RQ starts from a unit *section* on an open rather than from a rational map, so the Möbius
section `φ = (t - g₀ t')/(1 - g₀)` has to be an honest unit of `Γ(V, U)`.

This file removes those two. For a rational function represented by a unit section `g₀` on an
affine dense open `U`, the locus where `(1 - g₀)(t - g₀ t')` is invertible is the basic open of
that product; it is again affine, and it is nonempty — hence dense — unless one of the two
factors vanishes identically on `U`. So either the open can be shrunk, or one of two degenerate
cases holds, and in both of those `div_V(gg) = 0`:

* `1 - g₀ = 0`, that is `g₀ = 1`: then `gg = 1`, and `div_V(1) = 0`;
* `t - g₀ t' = 0`, that is `g₀ t' = t`: then `(g₀ - 1) t' = t - t'` is invertible on `U`, so
  `t'` and with it `t` are invertible there, hence nonzero on the base; when `Γ(S, ⊤)` is a
  field — which is the case part (3) of Tag 0B07 is stated in — they are units of `Γ(S, ⊤)`,
  so `g₀` is the restriction of a *global* unit `t/t'` of `Γ(V, ⊤)` and every order of
  vanishing of `gg` is zero by `AlgebraicGeometry.Scheme.ord_of_isUnit`.

The field hypothesis enters only through the second case, and only as
`∀ c : Γ(S, ⊤), c ≠ 0 → IsUnit c`.

## Main results

* `Stacks.Chow.ofSection_res` — shrinking the open does not change the rational function
  represented by a section.
* `Stacks.Chow.principalCycle_eq_zero_of_mul_germToFunctionField_top` — **a rational function
  which is a ratio of two global units has zero principal divisor.**
* `Stacks.Chow.principalDivisorPushforward_eq_zero_of_baseSectionOn_mul` — the second
  degenerate case: a rational function equal to a ratio of two base functions, both units on
  the base, has vanishing principal-divisor pushforward.
* `Stacks.Chow.exists_pointGraphFamilyMember_or_eq_zero` — **the production step of part (3) of
  Tag 0B07 at an arbitrary pair, with `hw` and `hφ` discharged**: either the pushforward of the
  principal divisor vanishes, or there is a member of the family realising it as a fibre
  difference at `(t, t')`.
* `Stacks.Chow.exists_pointFamilyFibreDifferences` — **Tag 02S4 part (4) at an arbitrary pair**:
  the locally finite family of members whose total fibre difference at `(t, t')` is a given
  cycle rationally equivalent to zero.
* `Stacks.Chow.isUnit_of_ne_zero_of_eq_spec` — over the spectrum of a field every nonzero global
  function on the base is invertible.
* `Stacks.Chow.pointFibreDifferences` — the basic rational equivalences at the pair `(t, t')`.
* `Stacks.Chow.rationalEquivalences_eq_closure_pointFibreDifferences` and
  `Stacks.Chow.rationalEquivalences_eq_closure_pointFibreDifferences_of_ne` — **Tag 0AZI at an
  arbitrary pair of distinct points of the affine chart**: those differences generate exactly
  the cycles rationally equivalent to zero.

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

/-! ### Shrinking the open on which a rational function is represented -/

/-- Restricting a section to a smaller dense open does not change the rational function it
represents: both have the same germ at the generic point. -/
theorem ofSection_res {X : Scheme.{u}} [IsIntegral X] {U D : X.Opens} (h : D ≤ U)
    (hU : Dense (U : Set X)) (hD : Dense (D : Set X)) (s : Γ(X, U)) :
    ofSection X ⟨D, hD⟩ (X.presheaf.map (homOfLE h).op s) = ofSection X ⟨U, hU⟩ s := by
  have hηD : genericPoint X ∈ D :=
    ((genericPoint_spec X).mem_open_set_iff D.isOpen).mpr (by simpa using hD.nonempty)
  have hηU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hU.nonempty)
  refine (rationalFunctionsEquivFunctionField X).1.injective ?_
  rw [(rationalFunctionsEquivFunctionField X).2 ⟨D, hD⟩ _ hηD,
    (rationalFunctionsEquivFunctionField X).2 ⟨U, hU⟩ s hηU]
  exact X.presheaf.germ_res_apply (homOfLE h) (genericPoint X) hηD s

/-- A global function on the base, read on a smaller open, is the restriction of the one read on
the larger open. -/
theorem baseSectionOn_res {X S : Scheme.{u}} (sX : X ⟶ S) {U D : X.Opens} (h : D ≤ U)
    (t : Γ(S, ⊤)) :
    X.presheaf.map (homOfLE h).op (baseSectionOn sX U t) = baseSectionOn sX D t := by
  rw [baseSectionOn, baseSectionOn, ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

/-! ### A ratio of global units has no principal divisor -/

/-- **The principal divisor of a ratio of two global units vanishes.** If `a · u' = u` in the
function field for two invertible global sections `u`, `u'` then the order of vanishing of `a`
is zero at every point: the orders of `u` and of `u'` vanish everywhere by
`AlgebraicGeometry.Scheme.ord_of_isUnit`, applied on the whole of `X`, and the order of a
product is the sum of the orders. -/
theorem principalCycle_eq_zero_of_mul_germToFunctionField_top (Y : Scheme.{u}) [IsIntegral Y]
    [IsLocallyNoetherian Y] {a : Y.functionField} (ha : a ≠ 0) {u u' : Γ(Y, ⊤)}
    (hu : IsUnit u) (hu' : IsUnit u')
    (h : a * Y.germToFunctionField ⊤ u' = Y.germToFunctionField ⊤ u) :
    principalCycle Y a = 0 := by
  have hu'ne : Y.germToFunctionField ⊤ u' ≠ 0 :=
    (hu'.map (Y.germToFunctionField ⊤).hom).ne_zero
  refine Function.locallyFinsuppWithin.ext fun z => ?_
  have hmul : Y.ord (a * Y.germToFunctionField ⊤ u') z =
      Y.ord a z + Y.ord (Y.germToFunctionField ⊤ u') z := Y.ord_mul ha hu'ne
  rw [h, Y.ord_of_isUnit hu (Set.mem_univ z), Y.ord_of_isUnit hu' (Set.mem_univ z)] at hmul
  have hz : Y.ord a z = 0 := by omega
  simpa using hz

/-! ### The second degenerate case: the rational function is a ratio of base functions -/

/-- **The second degenerate case of the production step.** If the section representing `gg` on a
dense open `U` satisfies `t = g₀ t'` for two global functions `t`, `t'` on the base which are
units there, then `gg` is the restriction of the global unit `t/t'` of `Γ(V, ⊤)` and the
pushforward of its principal divisor is the zero cycle. -/
theorem principalDivisorPushforward_eq_zero_of_baseSectionOn_mul (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) (gg : (rationalFunctions V.subscheme)ˣ)
    (U : V.subscheme.Opens) (hU : Dense (U : Set V.subscheme))
    (s : (Γ(V.subscheme, U))ˣ)
    (hs : ofSection V.subscheme ⟨U, hU⟩ (s : Γ(V.subscheme, U)) =
      (gg : rationalFunctions V.subscheme))
    {t t' : Γ(C.S, ⊤)} (ht : IsUnit t) (ht' : IsUnit t')
    (hrel : baseSectionOn (V.subschemeι ≫ f) U t =
      (s : Γ(V.subscheme, U)) * baseSectionOn (V.subschemeι ≫ f) U t') :
    principalDivisorPushforward C f V hV gg = 0 := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  have hUne : Nonempty U.toScheme := Set.nonempty_coe_sort.mpr hU.nonempty
  have hηU : genericPoint V.subscheme ∈ U :=
    ((genericPoint_spec V.subscheme).mem_open_set_iff U.isOpen).mpr
      (by simpa using hU.nonempty)
  have hβ : IsUnit ((V.subschemeι ≫ f).appTop t) :=
    ht.map (V.subschemeι ≫ f).appTop.hom
  have hβ' : IsUnit ((V.subschemeι ≫ f).appTop t') :=
    ht'.map (V.subschemeι ≫ f).appTop.hom
  have hgerm : ∀ c : Γ(C.S, ⊤),
      V.subscheme.germToFunctionField U (baseSectionOn (V.subschemeι ≫ f) U c) =
        V.subscheme.germToFunctionField ⊤ ((V.subschemeι ≫ f).appTop c) := by
    intro c
    exact V.subscheme.presheaf.germ_res_apply (homOfLE (le_top : U ≤ ⊤))
      (genericPoint V.subscheme) hηU _
  have hgg : (rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme) =
      V.subscheme.germToFunctionField U (s : Γ(V.subscheme, U)) := by
    rw [← hs]
    exact (rationalFunctionsEquivFunctionField V.subscheme).2 ⟨U, hU⟩
      (s : Γ(V.subscheme, U)) hηU
  have hane : (rationalFunctionsEquivFunctionField V.subscheme).1
      (gg : rationalFunctions V.subscheme) ≠ 0 :=
    rationalFunctionsEquivFunctionField_ne_zero V.subscheme gg
  have hmul : (rationalFunctionsEquivFunctionField V.subscheme).1
        (gg : rationalFunctions V.subscheme) *
      V.subscheme.germToFunctionField ⊤ ((V.subschemeι ≫ f).appTop t') =
      V.subscheme.germToFunctionField ⊤ ((V.subschemeι ≫ f).appTop t) := by
    rw [hgg, ← hgerm t, ← hgerm t', ← map_mul, ← hrel]
  rw [principalDivisorPushforward_eq,
    principalCycle_eq_zero_of_mul_germToFunctionField_top V.subscheme hane hβ hβ' hmul,
    closedSubschemeCyclePushforward_zero]

/-! ### The production step with the two extra invertibilities discharged -/

/-- **The production step of part (3) of Tag 0B07 at an arbitrary pair of points, with the two
hypotheses of `Stacks.Chow.exists_pointGraphFamilyMember` that the source does not have
discharged.** Let `V ⊆ X` be an integral closed subscheme of delta-dimension `k + 1`, let `gg`
be a rational function on it, and let `t`, `t'` be two points of the affine chart with `t - t'`
invertible — the source's `a ≠ b`. Then either `pr_{X,*}(div_V(gg))` is the zero cycle, or there
is a closed subvariety `W ⊆ X ×_S ℙ¹_S` with every property Tag 02S4 part (3) asks of a family
member at the pair `(t, t')` and with `pr_{X,*}(div_V(gg)) = [W_t]_k - [W_{t'}]_k`.

Only the degenerate branch uses that every nonzero global function on the base is invertible. -/
theorem exists_pointGraphFamilyMember_or_eq_zero (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (gg : (rationalFunctions V.subscheme)ˣ) (t t' : Γ(C.S, ⊤)) (hne : IsUnit (t - t'))
    (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) :
    (∀ x : X, principalDivisorPushforward C f V hV gg x = 0) ∨
      ∃ W : (projectiveLineProduct f).IdealSheafData,
        IsIntegral W.subscheme ∧
        (∀ ξ : genericPoints W.subscheme,
          relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1) ∧
        ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t) ∧
        ¬ Set.range W.subschemeι ⊆ Set.range (pointSection f t') ∧
        ((W.support : Set (projectiveLineProduct f)) ⊆
          pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ⁻¹' (V.support : Set X)) ∧
        (∀ x : X, principalDivisorPushforward C f V hV gg x =
          (cycleAssociatedToClosedSubscheme C f (pointFiber f t W).subschemeι k).1 x -
            (cycleAssociatedToClosedSubscheme C f (pointFiber f t' W).subschemeι k).1 x) := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  obtain ⟨U, hUaff, hU, s, hs⟩ := exists_unit_section V.subscheme gg
  have hUne : Nonempty U.toScheme := Set.nonempty_coe_sort.mpr hU.nonempty
  have hηU : genericPoint V.subscheme ∈ U :=
    ((genericPoint_spec V.subscheme).mem_open_set_iff U.isOpen).mpr
      (by simpa using hU.nonempty)
  have he : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t -
      baseSectionOn (V.subschemeι ≫ f) U t') :=
    isUnit_baseSectionOn_sub (V.subschemeι ≫ f) U hne
  -- the two factors whose joint invertibility the construction needs
  by_cases h1 : (1 : Γ(V.subscheme, U)) - (s : Γ(V.subscheme, U)) = 0
  · -- `g₀ = 1`, so `gg = 1` and the principal divisor is zero
    left
    have hs1 : (s : Γ(V.subscheme, U)) = 1 := (sub_eq_zero.mp h1).symm
    have hgg : gg = 1 := by
      refine Units.ext ?_
      refine (rationalFunctionsEquivFunctionField V.subscheme).1.injective ?_
      rw [← hs, hs1, (rationalFunctionsEquivFunctionField V.subscheme).2 ⟨U, hU⟩ 1 hηU,
        map_one, Units.val_one, map_one]
    intro x
    rw [hgg, principalDivisorPushforward_one]
    rfl
  by_cases h2 : baseSectionOn (V.subschemeι ≫ f) U t -
      (s : Γ(V.subscheme, U)) * baseSectionOn (V.subschemeι ≫ f) U t' = 0
  · -- `g₀ t' = t`: the rational function is the base function `t/t'`
    left
    have hrel : baseSectionOn (V.subschemeι ≫ f) U t =
        (s : Γ(V.subscheme, U)) * baseSectionOn (V.subschemeι ≫ f) U t' := sub_eq_zero.mp h2
    have hkey : ((s : Γ(V.subscheme, U)) - 1) * baseSectionOn (V.subschemeι ≫ f) U t' =
        baseSectionOn (V.subschemeι ≫ f) U t - baseSectionOn (V.subschemeι ≫ f) U t' := by
      rw [hrel]; ring
    have hb' : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t') := by
      rw [← hkey] at he
      exact isUnit_of_mul_isUnit_right he
    have hb : IsUnit (baseSectionOn (V.subschemeι ≫ f) U t) := by
      rw [hrel]
      exact s.isUnit.mul hb'
    have hone : (1 : Γ(V.subscheme, U)) ≠ 0 := by
      intro h0
      have hUb : U = ⊥ := by
        rw [← Scheme.basicOpen_one (X := V.subscheme) (U := U), h0, Scheme.basicOpen_zero]
      exact absurd hU.nonempty (by rw [hUb]; simp)
    have hzero : baseSectionOn (V.subschemeι ≫ f) U (0 : Γ(C.S, ⊤)) = 0 := by
      rw [baseSectionOn, map_zero, map_zero]
    have ht : IsUnit t := by
      refine hbase t fun h0 => hone ?_
      rw [h0, hzero] at hb
      exact (isUnit_zero_iff.mp hb).symm
    have ht' : IsUnit t' := by
      refine hbase t' fun h0 => hone ?_
      rw [h0, hzero] at hb'
      exact (isUnit_zero_iff.mp hb').symm
    intro x
    rw [principalDivisorPushforward_eq_zero_of_baseSectionOn_mul C f V hV gg U hU s hs ht ht'
      hrel]
    rfl
  · -- the generic case: shrink `U` to the basic open of the product of the two factors
    right
    set c₁ : Γ(V.subscheme, U) := (1 : Γ(V.subscheme, U)) - (s : Γ(V.subscheme, U)) with hc₁
    set c₂ : Γ(V.subscheme, U) := baseSectionOn (V.subschemeι ≫ f) U t -
      (s : Γ(V.subscheme, U)) * baseSectionOn (V.subschemeι ≫ f) U t' with hc₂
    set D : V.subscheme.Opens := V.subscheme.basicOpen (c₁ * c₂) with hDdef
    have hDU : D ≤ U := V.subscheme.basicOpen_le (c₁ * c₂)
    have hd₁ : Dense ((V.subscheme.basicOpen c₁ : V.subscheme.Opens) : Set V.subscheme) :=
      (V.subscheme.basicOpen c₁).isOpen.dense
        ((Opens.ne_bot_iff_nonempty _).mp fun hb =>
          h1 ((basicOpen_eq_bot_iff c₁).mp hb))
    have hd₂ne : Set.Nonempty ((V.subscheme.basicOpen c₂ : V.subscheme.Opens) : Set V.subscheme) :=
      (Opens.ne_bot_iff_nonempty _).mp fun hb => h2 ((basicOpen_eq_bot_iff c₂).mp hb)
    have hDne : Set.Nonempty ((D : V.subscheme.Opens) : Set V.subscheme) := by
      rw [hDdef, Scheme.basicOpen_mul, Opens.coe_inf, Set.inter_comm]
      exact hd₁.inter_open_nonempty _ (V.subscheme.basicOpen c₂).isOpen hd₂ne
    have hD : Dense ((D : V.subscheme.Opens) : Set V.subscheme) := D.isOpen.dense hDne
    have hDne' : Nonempty D.toScheme := Set.nonempty_coe_sort.mpr hDne
    have hDqc : QuasiCompact D.ι :=
      AlgebraicGeometry.quasiCompact_ι_of_isCompact D (hUaff.basicOpen (c₁ * c₂)).isCompact
    have hprod : IsUnit (V.subscheme.presheaf.map (homOfLE hDU).op (c₁ * c₂)) :=
      V.subscheme.toRingedSpace.isUnit_res_basicOpen (c₁ * c₂)
    rw [map_mul] at hprod
    have hres₁ : IsUnit (V.subscheme.presheaf.map (homOfLE hDU).op c₁) :=
      isUnit_of_mul_isUnit_left hprod
    have hres₂ : IsUnit (V.subscheme.presheaf.map (homOfLE hDU).op c₂) :=
      isUnit_of_mul_isUnit_right hprod
    have hsu : IsUnit (V.subscheme.presheaf.map (homOfLE hDU).op (s : Γ(V.subscheme, U))) :=
      s.isUnit.map (V.subscheme.presheaf.map (homOfLE hDU).op).hom
    have hw : IsUnit ((1 : Γ(V.subscheme, D)) - (hsu.unit : Γ(V.subscheme, D))) := by
      rw [hsu.unit_spec]
      rw [hc₁, map_sub, map_one] at hres₁
      exact hres₁
    have hφ : IsUnit (baseSectionOn (V.subschemeι ≫ f) D t -
        (hsu.unit : Γ(V.subscheme, D)) * baseSectionOn (V.subschemeι ≫ f) D t') := by
      rw [hsu.unit_spec, ← baseSectionOn_res (V.subschemeι ≫ f) hDU t,
        ← baseSectionOn_res (V.subschemeι ≫ f) hDU t']
      rw [hc₂, map_sub, map_mul] at hres₂
      exact hres₂
    have hg₀ : ofSection V.subscheme ⟨D, hD⟩ (hsu.unit : Γ(V.subscheme, D)) =
        (gg : rationalFunctions V.subscheme) := by
      rw [hsu.unit_spec, ofSection_res hDU hU hD (s : Γ(V.subscheme, U))]
      exact hs
    exact exists_pointGraphFamilyMember C f k V hV hdim gg D hD hsu.unit hg₀ t t' hne hw hφ

/-! ### The locally finite family of fibre differences at an arbitrary pair -/

/-- A `finsum` over a subtype containing the support is the `finsum` over the whole index
type. -/
theorem finsum_subtype_eq_finsum_of_support_subset {ι : Type*} {M : Type*} [AddCommMonoid M]
    (F : ι → M) (S : Set ι) (h : ∀ i ∈ Function.support F, i ∈ S) :
    ∑ᶠ i : ↥S, F i.1 = ∑ᶠ i : ι, F i := by
  rw [finsum_set_coe_eq_finsum_mem,
    finsum_mem_inter_support_eq' F S Set.univ (fun i hi ↦ by simp [h i hi]), finsum_mem_univ]

/-- The coefficient at `x : X` of the sum over `j` of the fibre cycle at `t` minus the fibre
cycle at `t'` of a family `W` of closed subschemes of `X ×_S ℙ¹_S`. This is
`Stacks.Chow.familyFibreDifferenceCoefficient` at an arbitrary pair of points of the affine
chart in place of `0` and `∞`. -/
def pointFamilyFibreDifferenceCoefficient (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (t t' : Γ(C.S, ⊤))
    {J : Type u} (W : J → (projectiveLineProduct f).IdealSheafData) (x : X) : ℤ :=
  ∑ᶠ j : J,
    ((cycleAssociatedToClosedSubscheme C f (pointFiber f t (W j)).subschemeι k).1 x -
      (cycleAssociatedToClosedSubscheme C f (pointFiber f t' (W j)).subschemeι k).1 x)

/-- **Tag 02S4 part (4) at an arbitrary pair of points of the affine chart.** A `k`-cycle
rationally equivalent to zero is the total fibre difference, at the pair `(t, t')`, of a locally
finite family of integral closed subschemes of `X ×_S ℙ¹_S`, each of relative dimension `k + 1`
at its generic points and contained in neither of the two sections.

This is `Stacks.Chow.exists_familyFibreDifferences` with the arbitrary pair in place of `0` and
`∞`. The index type is not the one witnessing rational equivalence but the subtype of those
members whose principal divisor does not already vanish: that is where the two degenerate cases
of `Stacks.Chow.exists_pointGraphFamilyMember_or_eq_zero` go, and dropping them changes no
coefficient. -/
theorem exists_pointFamilyFibreDifferences (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ) (α : CycleGroup C f k)
    (hα : IsRationallyEquivalentToZero C f k α) (t t' : Γ(C.S, ⊤)) (hne : IsUnit (t - t'))
    (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) :
    ∃ (J : Type u) (W : J → (projectiveLineProduct f).IdealSheafData)
      (_ : ∀ j, IsIntegral (W j).subscheme)
      (_ : ∀ j, ∀ ξ : genericPoints (W j).subscheme,
        relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1),
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (pointSection f t)) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (pointSection f t')) ∧
      LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))) ∧
      (∀ x : X, α.1 x = pointFamilyFibreDifferenceCoefficient C f k t t' W x) := by
  classical
  obtain ⟨J, V, hV, hdim, hLocal, g, hg⟩ := hα
  have hstep := fun j ↦
    exists_pointGraphFamilyMember_or_eq_zero C f k (V j) (hV j) (hdim j) (g j) t t' hne hbase
  choose W hWint hWdim hWT hWT' hWsupp hWcoeff using fun j :
    ↥{j : J | ¬ ∀ x : X, principalDivisorPushforward C f (V j) (hV j) (g j) x = 0} ↦
      (hstep j.1).resolve_left j.2
  refine ⟨↥{j : J | ¬ ∀ x : X, principalDivisorPushforward C f (V j) (hV j) (g j) x = 0},
    W, hWint, hWdim, hWT, hWT', ?_, fun x ↦ ?_⟩
  · exact LocallyFinite.subset
      ((hLocal.preimage_continuous
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).continuous).comp_injective
          Subtype.val_injective) hWsupp
  · have hWc : ∀ j :
        ↥{j : J | ¬ ∀ x : X, principalDivisorPushforward C f (V j) (hV j) (g j) x = 0},
        (cycleAssociatedToClosedSubscheme C f (pointFiber f t (W j)).subschemeι k).1 x -
            (cycleAssociatedToClosedSubscheme C f (pointFiber f t' (W j)).subschemeι k).1 x =
          principalDivisorPushforward C f (V j.1) (hV j.1) (g j.1) x :=
      fun j ↦ (hWcoeff j x).symm
    have hmem : ∀ j ∈ Function.support
        (fun j : J ↦ principalDivisorPushforward C f (V j) (hV j) (g j) x),
        j ∈ {j : J | ¬ ∀ x : X, principalDivisorPushforward C f (V j) (hV j) (g j) x = 0} := by
      intro j hj
      simp only [Set.mem_ofPred_eq]
      exact fun hall ↦ hj (hall x)
    rw [hg x, principalDivisorFamilyCoefficient, pointFamilyFibreDifferenceCoefficient,
      finsum_congr hWc]
    exact (finsum_subtype_eq_finsum_of_support_subset
      (fun j : J ↦ principalDivisorPushforward C f (V j) (hV j) (g j) x) _ hmem).symm

/-! ### The base-field hypothesis, derived -/

/-- **Over the spectrum of a field every nonzero global function on the base is invertible.**
The ring `Γ(S, ⊤)` is then the ground field: the isomorphism `S ≅ Spec k` attached to the
equality of schemes, composed with `AlgebraicGeometry.Scheme.ΓSpecIso`, is a ring isomorphism
`Γ(S, ⊤) ≅ k`. This is the hypothesis `hbase` of the production step, discharged. -/
theorem isUnit_of_ne_zero_of_eq_spec {Kf : Type u} [Field Kf] (C : ChowSituation.{u})
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf)) (c : Γ(C.S, ⊤)) (hc : c ≠ 0) :
    IsUnit c := by
  set e : C.S ≅ AlgebraicGeometry.Spec (CommRingCat.of Kf) := eqToIso hC with he
  set φ : Γ(C.S, ⊤) ⟶ CommRingCat.of Kf :=
    e.inv.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Kf)).hom with hφ
  set φ' : CommRingCat.of Kf ⟶ Γ(C.S, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of Kf)).inv ≫ e.hom.appTop with hφ'
  have hcomp : φ ≫ φ' = CategoryTheory.CategoryStruct.id Γ(C.S, ⊤) := by
    rw [hφ, hφ', Category.assoc, Iso.hom_inv_id_assoc, ← Scheme.Hom.comp_appTop, e.hom_inv_id,
      Scheme.Hom.id_appTop]
  have hback : ∀ a : Γ(C.S, ⊤), φ' (φ a) = a := by
    intro a
    rw [← CommRingCat.comp_apply, hcomp, CommRingCat.id_apply]
  have hcne : φ c ≠ 0 := by
    intro h0
    exact hc (by rw [← hback c, h0, map_zero])
  have : IsUnit (φ c) := isUnit_iff_ne_zero.mpr hcne
  rw [← hback c]
  exact this.map φ'.hom

/-! ### The basic rational equivalences at an arbitrary pair -/

/-- The basic rational equivalences at an arbitrary pair of points `t`, `t'` of the affine
chart: the differences `[W_t]ₖ - [W_{t'}]ₖ` of the two fibre cycles of an integral closed
subscheme `W ⊆ X ×_S ℙ¹_S` of relative dimension `k + 1` contained in neither of the two
sections. This is `Stacks.Chow.fibreDifferences` of Tag 0AZG without the traditional choice
`a = 0`, `b = ∞`. -/
def pointFibreDifferences (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (t t' : Γ(C.S, ⊤)) : Set (CycleGroup C p k) :=
  {γ | ∃ W : (projectiveLineProduct p).IdealSheafData,
    IsIntegral W.subscheme ∧
    (∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1) ∧
    (¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t)) ∧
    (¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t')) ∧
    γ = cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k -
      cycleAssociatedToClosedSubscheme C p (pointFiber p t' W).subschemeι k}

/-- A basic rational equivalence at the pair `(t, t')` generates. -/
theorem sub_cycleAssociatedToPointFibres_mem_closure (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (t t' : Γ(C.S, ⊤))
    (W : (projectiveLineProduct p).IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase p W) ξ.1 = k + 1)
    (hT : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t))
    (hT' : ¬ Set.range W.subschemeι ⊆ Set.range (pointSection p t')) :
    cycleAssociatedToClosedSubscheme C p (pointFiber p t W).subschemeι k -
        cycleAssociatedToClosedSubscheme C p (pointFiber p t' W).subschemeι k ∈
      AddSubgroup.closure (pointFibreDifferences C p k t t') :=
  AddSubgroup.subset_closure ⟨W, hW, hDim, hT, hT', rfl⟩

/-- **Tag 0AZI at an arbitrary pair of points of the affine chart.** On a variety over an
algebraically closed field the basic rational equivalences at an arbitrary pair of points `t`,
`t'` of the affine chart generate exactly the group of `k`-cycles rationally equivalent to zero.

The inclusion `⊇` is part (2) at the pair,
`Stacks.Chow.pointFiberCycles_rationallyEquivalent`. The inclusion `⊆` is the production step
`Stacks.Chow.exists_pointGraphFamilyMember_or_eq_zero`, assembled by
`Stacks.Chow.exists_pointFamilyFibreDifferences` and made a finite sum by compactness of
`X ×_S ℙ¹_S`. The generating set `Stacks.Chow.fibreDifferences` of Tag 0AZG, which has the two
distinguished points hard-coded, is never unfolded. -/
theorem rationalEquivalences_eq_closure_pointFibreDifferences (Kf : Type u) [Field Kf]
    [IsAlgClosed Kf] (C : ChowSituation.{u})
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf)) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)] (k : ℤ) (t t' : Γ(C.S, ⊤))
    (hne : IsUnit (t - t')) (hbase : ∀ c : Γ(C.S, ⊤), c ≠ 0 → IsUnit c) :
    rationalEquivalences C p k = AddSubgroup.closure (pointFibreDifferences C p k t t') := by
  refine le_antisymm (fun α hα ↦ ?_) ?_
  · rw [mem_rationalEquivalences] at hα
    obtain ⟨J, W, hInt, hDim, hT, hT', hLocal, hCoeff⟩ :=
      exists_pointFamilyFibreDifferences C p k α hα t t' hne hbase
    have : CompactSpace (projectiveLineProduct p) :=
      compactSpace_projectiveLineProduct Kf C hC p
    have : Finite J := finite_of_locallyFinite_of_nonempty
      (fun j ↦ ((W j).support : Set (projectiveLineProduct p))) hLocal
      (fun j ↦ @nonempty_support_of_isIntegral _ (W j) (hInt j))
    let _ : Fintype J := Fintype.ofFinite J
    set γ : J → CycleGroup C p k := fun j ↦
      cycleAssociatedToClosedSubscheme C p (pointFiber p t (W j)).subschemeι k -
        cycleAssociatedToClosedSubscheme C p (pointFiber p t' (W j)).subschemeι k with hγdef
    have hsum : (∑ j, γ j) ∈ AddSubgroup.closure (pointFibreDifferences C p k t t') :=
      AddSubmonoid.sum_mem (AddSubgroup.closure (pointFibreDifferences C p k t t')).toAddSubmonoid
        fun j _ ↦ sub_cycleAssociatedToPointFibres_mem_closure C p k t t' (W j)
          (hInt j) (hDim j) (hT j) (hT' j)
    have hval : α = ∑ j, γ j := by
      refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
      have hrhs : ((∑ j, γ j : CycleGroup C p k) : AlgebraicCycle X ℤ) x =
          ∑ j, ((cycleAssociatedToClosedSubscheme C p
              (pointFiber p t (W j)).subschemeι k).1 x -
            (cycleAssociatedToClosedSubscheme C p
              (pointFiber p t' (W j)).subschemeι k).1 x) := by
        simp [hγdef]
      rw [hrhs, hCoeff x, pointFamilyFibreDifferenceCoefficient,
        finsum_eq_sum_of_support_subset _ (s := Finset.univ) (by intro j _; simp)]
    rw [hval]
    exact hsum
  · refine (AddSubgroup.closure_le (rationalEquivalences C p k)).2 ?_
    rintro γ ⟨W, hW, hDim, hT, hT', rfl⟩
    have := hW
    exact pointFiberCycles_rationallyEquivalent C p W t k t' hDim hT hT'

/-- **Tag 0AZI at an arbitrary pair of distinct points of the affine chart**, with the base-field
hypothesis discharged: the hypotheses are the source's own, two distinct points. -/
theorem rationalEquivalences_eq_closure_pointFibreDifferences_of_ne (Kf : Type u) [Field Kf]
    [IsAlgClosed Kf] (C : ChowSituation.{u})
    (hC : C.S = AlgebraicGeometry.Spec (CommRingCat.of Kf)) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    [AlgebraicGeometry.IsVariety Kf (p ≫ eqToHom hC)] (k : ℤ) (t t' : Γ(C.S, ⊤))
    (hne : t ≠ t') :
    rationalEquivalences C p k = AddSubgroup.closure (pointFibreDifferences C p k t t') :=
  rationalEquivalences_eq_closure_pointFibreDifferences Kf C hC p k t t'
    (isUnit_of_ne_zero_of_eq_spec C hC (t - t') (sub_ne_zero_of_ne hne))
    (isUnit_of_ne_zero_of_eq_spec C hC)

end Stacks.Chow

end
