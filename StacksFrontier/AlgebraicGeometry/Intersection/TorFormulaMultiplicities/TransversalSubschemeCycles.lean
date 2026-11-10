module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.MultiplicityOneSmoothness
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.TransversalCycleMultiplicity
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.Topology.Dimension.Krull

/-!
# Cycles of closed subschemes meeting transversally along a component

Let `X` be a nonsingular variety over a field `k`, let `r, s ≥ 0` and let `Y, Z ⊆ X` be closed
subschemes with `dim Y ≤ r` and `dim Z ≤ s` whose cycles `[Y]_r = ∑ nᵢ [Yᵢ]` and
`[Z]_s = ∑ mⱼ [Zⱼ]` intersect properly. Let `T` be an irreducible component of
`Y_{i₀} ∩ Z_{j₀}` along which the closed subscheme `Y ∩ Z` has multiplicity one. Then

1. the coefficient of `T` in `[Y]_r · [Z]_s` is `1`,
2. `Y` and `Z` are nonsingular at the generic point of `T`,
3. `n_{i₀} = 1` and `m_{j₀} = 1`, and
4. `T` lies in no `Yᵢ` with `i ≠ i₀` and in no `Zⱼ` with `j ≠ j₀`.

## Main results

* `TorFormula.torFormulaCycleIntersectionProduct_cycleAssociatedToClosedSubscheme_apply_eq_one`
  — the four conclusions above.
* `AlgebraicGeometry.ringKrullDim_stalk_add_topologicalKrullDim_closure_le` — on a scheme locally
  of finite type over a field, `dim 𝒪_{Y, y} + dim {y}‾ ≤ dim Y`.

## Implementation notes

Closed subschemes are ideal sheaves `IY`, `IZ`, their scheme-theoretic intersection is cut out
by `IY ⊔ IZ`, and the cycles are `Stacks.Chow.cycleAssociatedToClosedSubscheme` over the Chow
situation `Stacks.Chow.fieldChowSituation k`, whose delta-dimension is the dimension. Components
of cycles are their generic points `y₀`, `z₀`, and `T` is the closure of its generic point `t`.
The intersection product is `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` in
index `r + s - dim X`, the dimension of `X` being named `d` by `hd`.

The multiplicity of `T` in `Y ∩ Z` is the length over `𝒪_{X, ξ}` of
`𝒪_{Y ∩ Z, ξ} = 𝒪_{X, ξ} ⧸ (𝓘_Y + 𝓘_Z)_ξ`, which is how `hmult` states it. The point `ξ` is only
assumed to lie on both components `Y_{i₀}` and `Z_{j₀}`, not to be the generic point of an
irreducible component of `Y_{i₀} ∩ Z_{j₀}`. Nonsingularity of `Y` at `ξ` is regularity of the
local ring of the subscheme at the point over `ξ`.

## References

* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
* [Stacks Project, Tag 0B1I](https://stacks.math.columbia.edu/tag/0B1I)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Chow (fieldChowSituation relativeDimension cycleAssociatedToClosedSubscheme
  cycleAssociatedToClosedSubscheme_apply cycleAssociatedToClosedSubscheme_apply_eq_zero)

universe u

namespace AlgebraicGeometry

/-! ### Dimensions at a point -/

/-- **The local ring and the closure of a point together fit in the scheme.** On a scheme `Y`
locally of finite type over a field, `dim 𝒪_{Y, y} + dim {y}‾ ≤ dim Y`. -/
theorem ringKrullDim_stalk_add_topologicalKrullDim_closure_le (k : Type u) [Field k]
    (Y : Scheme.{u}) (f : Y ⟶ Spec (.of k)) [LocallyOfFiniteType f] (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) + topologicalKrullDim (closure ({y} : Set Y)) ≤
      topologicalKrullDim Y := by
  let : Algebra k (Y.residueField y) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ Y.Γevaluation y).hom.toAlgebra
  rw [topologicalKrullDim_closure_singleton_eq_trdeg k Y f y, add_comm,
    ← topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k Y f y]
  exact topologicalKrullDimAt_le_topologicalKrullDim y

/-- The local ring of a closed subscheme at a point is the quotient of the ambient local ring by
the stalk of the ideal sheaf, and the closure of the point has the same dimension in the
subscheme as in the ambient scheme. -/
theorem ringKrullDim_quotient_stalk_eq_and_topologicalKrullDim_closure_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    (ζ : I.subscheme) :
    ringKrullDim (X.presheaf.stalk (I.subschemeι ζ) ⧸ IdealSheafData.stalk I (I.subschemeι ζ)) =
        ringKrullDim (I.subscheme.presheaf.stalk ζ) ∧
      topologicalKrullDim (closure ({ζ} : Set I.subscheme)) =
        topologicalKrullDim (closure ({I.subschemeι ζ} : Set X)) := by
  refine ⟨ringKrullDim_eq_of_ringEquiv (IdealSheafData.subschemeStalkQuotEquiv I ζ), ?_⟩
  rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq k (I.subschemeι ≫ sX) ζ,
    Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX (I.subschemeι ζ),
    Stacks.Chow.relativeDimension_comp_closedImmersion]

/-- **The dimension bound on a closed subscheme, at a point.** For a closed subscheme cut out by
`I` and a point `t` of it, `dim (𝒪_{X, t} ⧸ I_t) + dim {t}‾ ≤ dim V(I)`. -/
theorem ringKrullDim_quotient_stalk_add_topologicalKrullDim_closure_le (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (I : X.IdealSheafData)
    {t : X} (ht : t ∈ I.support) :
    ringKrullDim (X.presheaf.stalk t ⧸ IdealSheafData.stalk I t) +
        topologicalKrullDim (closure ({t} : Set X)) ≤ topologicalKrullDim I.subscheme := by
  obtain ⟨h1, h2⟩ := ringKrullDim_quotient_stalk_eq_and_topologicalKrullDim_closure_eq k sX I
    (IdealSheafData.subschemePoint I t ht)
  rw [IdealSheafData.subschemeι_subschemePoint] at h1 h2
  rw [h1, ← h2]
  exact ringKrullDim_stalk_add_topologicalKrullDim_closure_le k I.subscheme (I.subschemeι ≫ sX)
    (IdealSheafData.subschemePoint I t ht)

namespace TorFormula

/-- **The dimension formula on the closure of a point.** For `t` in the closure `W` of `y`,
`dim (𝒪_{X, t} ⧸ 𝓘_{W, t}) + dim {t}‾ = dim W`. -/
theorem ringKrullDim_quotient_localIdealAt_add_topologicalKrullDim_closure (k : Type u)
    [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] {y t : X}
    (ht : t ∈ closure ({y} : Set X)) :
    ringKrullDim (X.presheaf.stalk t ⧸ localIdealAt y t) +
        topologicalKrullDim (closure ({t} : Set X)) =
      topologicalKrullDim (closure ({y} : Set X)) := by
  have hint := Stacks.Chow.isIntegral_integralComponentAt y
  have hirr : IrreducibleSpace (Stacks.Chow.integralComponentAt y).subscheme :=
    irreducibleSpace_of_isIntegral _
  have htW := mem_support_integralComponentAt ht
  obtain ⟨h1, h2⟩ := ringKrullDim_quotient_stalk_eq_and_topologicalKrullDim_closure_eq k sX
    (Stacks.Chow.integralComponentAt y)
    (IdealSheafData.subschemePoint (Stacks.Chow.integralComponentAt y) t htW)
  rw [IdealSheafData.subschemeι_subschemePoint] at h1 h2
  rw [localIdealAt, h1, ← h2]
  refine (Stacks.Algebraization.ringKrullDim_stalk_add_dimClosureAt k _
    ((Stacks.Chow.integralComponentAt y).subschemeι ≫ sX)
    (IdealSheafData.subschemePoint (Stacks.Chow.integralComponentAt y) t htW)).trans ?_
  rw [(Stacks.Chow.subschemeHomeoSupport _).isHomeomorph.topologicalKrullDim_eq,
    Stacks.Chow.coe_support_integralComponentAt]

/-- **Distinct points have distinct local ideals at a common specialization.** If `t` lies in the
closures of `y` and `y'` and the ideals of those closures agree in `𝒪_{X, t}`, then `y = y'`. -/
theorem eq_of_localIdealAt_eq {X : Scheme.{u}} {y y' t : X} (hy : t ∈ closure ({y} : Set X))
    (hy' : t ∈ closure ({y'} : Set X)) (h : localIdealAt y t = localIdealAt y' t) : y = y' := by
  obtain ⟨q, rfl⟩ : y ∈ Set.range (X.fromSpecStalk t) := by
    rw [Scheme.range_fromSpecStalk]
    exact specializes_iff_mem_closure.mpr hy
  obtain ⟨q', rfl⟩ : y' ∈ Set.range (X.fromSpecStalk t) := by
    rw [Scheme.range_fromSpecStalk]
    exact specializes_iff_mem_closure.mpr hy'
  exact congrArg _ <| PrimeSpectrum.ext <|
    (Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk t q).symm.trans
      (h.trans (Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk t q'))

/-- At its own generic point the ideal of the closure of a point is the maximal ideal. -/
theorem localIdealAt_self {X : Scheme.{u}} (y : X) :
    localIdealAt y y = IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  have h := Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk y
    (IsLocalRing.closedPoint (X.presheaf.stalk y))
  rwa [Scheme.fromSpecStalk_closedPoint] at h

/-- **A component whose ideal is that of its reduced closure has multiplicity one.** Let `ξ` be
the generic point of an irreducible component of the closed subscheme cut out by `I`, with image
`y` in `X`. If at some point `t` of the closure of `y` the stalk of `I` is the ideal of that
closure, then the multiplicity of the component is one. -/
theorem componentMultiplicity_eq_one_of_stalk_eq_localIdealAt {X : Scheme.{u}}
    (I : X.IdealSheafData) (ξ : genericPoints I.subscheme) {t : X}
    (ht : t ∈ closure ({I.subschemeι ξ.1} : Set X))
    (h : IdealSheafData.stalk I t = localIdealAt (I.subschemeι ξ.1) t) :
    Stacks.Chow.componentMultiplicity I.subschemeι ξ = 1 := by
  have hyt : I.subschemeι ξ.1 ⤳ t := specializes_iff_mem_closure.mpr ht
  have hstalk : IdealSheafData.stalk I (I.subschemeι ξ.1) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι ξ.1)) := by
    rw [Stacks.Chow.idealStalk_eq_map_stalkSpecializes I hyt, h, localIdealAt,
      ← Stacks.Chow.idealStalk_eq_map_stalkSpecializes _ hyt]
    exact localIdealAt_self _
  rw [componentMultiplicity_subschemeι_eq_toNat_length_quotient_stalk, hstalk]
  have hs : IsSimpleModule (X.presheaf.stalk (I.subschemeι ξ.1))
      (X.presheaf.stalk (I.subschemeι ξ.1) ⧸
        IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι ξ.1))) :=
    isSimpleModule_iff_isCoatom.mpr (IsLocalRing.maximalIdeal.isMaximal _).out
  rw [Module.length_eq_one_iff.mpr hs]
  rfl

/-! ### Arithmetic of dimensions -/

/-- A dimension `a` with `a + e = r` is the natural number `r - e`, and `e ≤ r`. -/
private theorem eq_natCast_sub_of_add_eq {a : WithBot ℕ∞} {e r : ℕ}
    (h : a + (e : WithBot ℕ∞) = (r : WithBot ℕ∞)) :
    a = ((r - e : ℕ) : WithBot ℕ∞) ∧ e ≤ r := by
  induction a using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe a =>
    have h' : a + (e : ℕ∞) = (r : ℕ∞) := by exact_mod_cast h
    induction a using ENat.recTopCoe with
    | top => exact absurd h' (by simp)
    | coe n =>
      have h'' : n + e = r := by exact_mod_cast h'
      refine ⟨?_, by omega⟩
      rw [← WithBot.coe_natCast, show r - e = n by omega]

/-- A dimension `a` with `a + e ≤ r` is at most the natural number `r - e`. -/
private theorem le_natCast_sub_of_add_le {a : WithBot ℕ∞} {e r : ℕ}
    (h : a + (e : WithBot ℕ∞) ≤ (r : WithBot ℕ∞)) : a ≤ ((r - e : ℕ) : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    have h' : a + (e : ℕ∞) ≤ (r : ℕ∞) := by exact_mod_cast h
    induction a using ENat.recTopCoe with
    | top => exact absurd h' (by simp)
    | coe n =>
      have h'' : n + e ≤ r := by exact_mod_cast h'
      have : n ≤ r - e := by omega
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast this)

/-! ### Components meeting with multiplicity one -/

/-- A point in the support of the cycle of a closed subscheme is the image of a generic point of
the subscheme, of relative dimension `n`. -/
private theorem exists_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero (k : Type u)
    [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [IsVariety k sX]
    (I : X.IdealSheafData) (n : ℕ) {y : X}
    (hy : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX I.subschemeι n).1 y ≠ 0) :
    ∃ ξ : genericPoints I.subscheme, I.subschemeι ξ.1 = y ∧
      relativeDimension (fieldChowSituation k).dimensionFunction sX y = n :=
  by_contra fun hne => hy (cycleAssociatedToClosedSubscheme_apply_eq_zero
    (fieldChowSituation k) sX _ _ y hne)

/-- A point in the support of the cycle of a closed subscheme has closure of dimension `n` and
lies in the support of the subscheme. -/
private theorem topologicalKrullDim_closure_eq_and_mem_support_of_cycle_ne_zero (k : Type u)
    [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [IsVariety k sX]
    (I : X.IdealSheafData) (n : ℕ) {y : X}
    (hy : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX I.subschemeι n).1 y ≠ 0) :
    topologicalKrullDim (closure ({y} : Set X)) = n ∧ y ∈ I.support := by
  obtain ⟨ξ, rfl, hrel⟩ := exists_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero k sX
    I n hy
  refine ⟨?_, ?_⟩
  · rw [Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX, hrel]
    simp
  · change I.subschemeι ξ.1 ∈ (I.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self _

/-- If the stalk of `I` at a point `t` of the closure of `y` is the ideal of that closure, then the
cycle of `I` has coefficient one at `y`. -/
private theorem cycleAssociatedToClosedSubscheme_apply_eq_one_of_stalk_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [IsVariety k sX] (I : X.IdealSheafData)
    (n : ℕ) {y t : X}
    (hy : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX I.subschemeι n).1 y ≠ 0)
    (ht : t ∈ closure ({y} : Set X)) (h : IdealSheafData.stalk I t = localIdealAt y t) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX I.subschemeι n).1 y = 1 := by
  obtain ⟨ξ, rfl, hrel⟩ := exists_genericPoint_of_cycleAssociatedToClosedSubscheme_ne_zero k sX
    I n hy
  rw [cycleAssociatedToClosedSubscheme_apply (fieldChowSituation k) sX _ _ ξ hrel]
  exact componentMultiplicity_eq_one_of_stalk_eq_localIdealAt I ξ ht h

/-- Let `t` be a point of dimension `e` in the closure of a component `y` of the cycle of a closed
subscheme `I` of dimension at most `r`. Then `I_t ≤ 𝓘_{y, t}`, `dim 𝒪_{X, t} ⧸ 𝓘_{y, t} = r - e`,
`e ≤ r`, and `𝒪_{X, t} ⧸ I_t` has the same dimension as `𝒪_{X, t} ⧸ 𝓘_{y, t}`. -/
private theorem stalk_le_localIdealAt_and_ringKrullDim_quotient_eq (k : Type u) [Field k]
    {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [IsVariety k sX] (I : X.IdealSheafData)
    (r e : ℕ) (hI : topologicalKrullDim I.subscheme ≤ r) {y t : X}
    (hy : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX I.subschemeι r).1 y ≠ 0)
    (hty : t ∈ closure ({y} : Set X)) (hT : topologicalKrullDim (closure ({t} : Set X)) = e) :
    IdealSheafData.stalk I t ≤ localIdealAt y t ∧
      ringKrullDim (X.presheaf.stalk t ⧸ localIdealAt y t) = ((r - e : ℕ) : WithBot ℕ∞) ∧
      e ≤ r ∧ ringKrullDim (X.presheaf.stalk t ⧸ IdealSheafData.stalk I t) =
        ringKrullDim (X.presheaf.stalk t ⧸ localIdealAt y t) := by
  obtain ⟨hdy, hsupp⟩ := topologicalKrullDim_closure_eq_and_mem_support_of_cycle_ne_zero k sX I r hy
  have hle : I ≤ Stacks.Chow.integralComponentAt y :=
    (Stacks.Chow.le_integralComponentAt_iff_mem_support I y).mpr hsupp
  have hII₀ : IdealSheafData.stalk I t ≤ localIdealAt y t := IdealSheafData.stalk_mono hle t
  have h₀ : ringKrullDim (X.presheaf.stalk t ⧸ localIdealAt y t) + (e : WithBot ℕ∞) = r := by
    rw [← hT, ← hdy]
    exact ringKrullDim_quotient_localIdealAt_add_topologicalKrullDim_closure k sX hty
  have h₁ : ringKrullDim (X.presheaf.stalk t ⧸ IdealSheafData.stalk I t) +
      (e : WithBot ℕ∞) ≤ r := by
    rw [← hT]
    exact (ringKrullDim_quotient_stalk_add_topologicalKrullDim_closure_le k sX I
      (Scheme.IdealSheafData.support_antitone hle (mem_support_integralComponentAt hty))).trans hI
  obtain ⟨h₀', her⟩ := eq_natCast_sub_of_add_eq h₀
  exact ⟨hII₀, h₀', her, le_antisymm ((le_natCast_sub_of_add_le h₁).trans h₀'.ge)
    (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hII₀)
      (Ideal.Quotient.factor_surjective hII₀))⟩

/-- Let `X` be a nonsingular variety over a field `k` of dimension `d`, let `r, s ≥ 0` and let `Y`,
`Z` be the closed subschemes cut out by `IY`, `IZ`, with `dim Y ≤ r` and `dim Z ≤ s`, whose cycles
`[Y]_r = ∑ nᵢ [Yᵢ]` and `[Z]_s = ∑ mⱼ [Zⱼ]` intersect properly. Let `Y_{i₀}` and `Z_{j₀}` be
components of the two cycles, with generic points `y₀` and `z₀`, and let `T` be the closure of a
point `t` of `Y_{i₀} ∩ Z_{j₀}` (for instance the generic point of an irreducible component of it)
along which the multiplicity of `Y ∩ Z`, `length_{𝒪_{X, t}} 𝒪_{X, t} ⧸ (𝓘_Y + 𝓘_Z)_t`, is `1`. Then

1. the coefficient of `T` in `[Y]_r · [Z]_s` is `1`,
2. `Y` and `Z` are nonsingular at `t`,
3. `n_{i₀} = 1` and `m_{j₀} = 1`, and
4. `T` is contained in no other component of `[Y]_r` and in no other component of `[Z]_s`. -/
@[stacks 0B1J]
theorem torFormulaCycleIntersectionProduct_cycleAssociatedToClosedSubscheme_apply_eq_one
    (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
    [IsVariety k sX] (hX : IsRegular X) {d : ℕ} (hd : topologicalKrullDim X = d) (r s : ℕ)
    (IY IZ : X.IdealSheafData) (hY : topologicalKrullDim IY.subscheme ≤ r)
    (hZ : topologicalKrullDim IZ.subscheme ≤ s)
    (hprop : AlgebraicCycle.IntersectProperly
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
        IY.subschemeι r).1
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
        IZ.subschemeι s).1)
    {y₀ z₀ t : X}
    (hy₀ : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
      IY.subschemeι r).1 y₀ ≠ 0)
    (hz₀ : (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
      IZ.subschemeι s).1 z₀ ≠ 0)
    (ht : t ∈ closure ({y₀} : Set X) ∩ closure ({z₀} : Set X))
    (hmult : Module.length (X.presheaf.stalk t)
      (X.presheaf.stalk t ⧸ IdealSheafData.stalk (IY ⊔ IZ) t) = 1) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    torFormulaCycleIntersectionProduct (fieldChowSituation k) sX hX ((r + s : ℤ) - d)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
          IY.subschemeι r).1
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
          IZ.subschemeι s).1 t = 1 ∧
      (∀ ζ : IY.subscheme, IY.subschemeι ζ = t →
        IsRegularLocalRing (IY.subscheme.presheaf.stalk ζ)) ∧
      (∀ ζ : IZ.subscheme, IZ.subschemeι ζ = t →
        IsRegularLocalRing (IZ.subscheme.presheaf.stalk ζ)) ∧
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
        IY.subschemeι r).1 y₀ = 1 ∧
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
        IZ.subschemeι s).1 z₀ = 1 ∧
      (∀ y, (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
        IY.subschemeι r).1 y ≠ 0 → t ∈ closure ({y} : Set X) → y = y₀) ∧
      (∀ z, (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX
        IZ.subschemeι s).1 z ≠ 0 → t ∈ closure ({z} : Set X) → z = z₀) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsRegularLocalRing (X.presheaf.stalk t) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX t
  set α := (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX IY.subschemeι r).1 with hα
  set β := (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX IZ.subschemeι s).1 with hβ
  set e := (relativeDimension (fieldChowSituation k).dimensionFunction sX t).toNat with he
  have hT : topologicalKrullDim (closure ({t} : Set X)) = e :=
    Stacks.Chow.topologicalKrullDim_closure_singleton_eq k sX t
  have hrelt : relativeDimension (fieldChowSituation k).dimensionFunction sX t = e := by
    have hnn : 0 ≤ relativeDimension (fieldChowSituation k).dimensionFunction sX t := by
      change 0 ≤ (fieldChowSituation k).dimensionFunction (sX.base t) + _
      rw [Stacks.Chow.fieldChowSituation_dimensionFunction]
      positivity
    rw [he, Int.toNat_of_nonneg hnn]
  set A := X.presheaf.stalk t with hA
  set I := IdealSheafData.stalk IY t with hI
  set J := IdealSheafData.stalk IZ t with hJ
  set I₀ := localIdealAt y₀ t with hI₀
  set J₀ := localIdealAt z₀ t with hJ₀
  have hmult' : Module.length A (A ⧸ (I ⊔ J)) = 1 := by
    rwa [hI, hJ, ← IdealSheafData.stalk_sup]
  obtain ⟨hdimY, -⟩ := topologicalKrullDim_closure_eq_and_mem_support_of_cycle_ne_zero k sX IY r hy₀
  obtain ⟨hdimZ, -⟩ := topologicalKrullDim_closure_eq_and_mem_support_of_cycle_ne_zero k sX IZ s hz₀
  have hdA : ringKrullDim A + (e : WithBot ℕ∞) ≤ d := by
    rw [← hT, ← hd]
    exact ringKrullDim_stalk_add_topologicalKrullDim_closure_le k X sX t
  obtain ⟨hII₀, hdI₀', her, hdIeq⟩ :=
    stalk_le_localIdealAt_and_ringKrullDim_quotient_eq k sX IY r e hY hy₀ ht.1 hT
  obtain ⟨hJJ₀, hdJ₀', hes, hdJeq⟩ :=
    stalk_le_localIdealAt_and_ringKrullDim_quotient_eq k sX IZ s e hZ hz₀ ht.2 hT
  have hprop₀ : AlgebraicGeometry.IntersectProperly
      ⟨closure {y₀}, isIrreducible_singleton.closure, isClosed_closure⟩
      ⟨closure {z₀}, isIrreducible_singleton.closure, isClosed_closure⟩ :=
    hprop _ _ (by rwa [genericPoint_closure_singleton]) (by rwa [genericPoint_closure_singleton])
  have hed : e + d ≤ r + s := by
    have h := (intersectProperly_iff _ _).mp hprop₀
    change topologicalKrullDim (↥(closure ({y₀} : Set X) ∩ closure ({z₀} : Set X))) +
        topologicalKrullDim X ≤ topologicalKrullDim (closure ({y₀} : Set X)) +
          topologicalKrullDim (closure ({z₀} : Set X)) at h
    rw [hd, hdimY, hdimZ] at h
    have hTle : (e : WithBot ℕ∞) ≤
        topologicalKrullDim (↥(closure ({y₀} : Set X) ∩ closure ({z₀} : Set X))) := by
      rw [← hT]
      exact topologicalKrullDim_le_of_subset
        (closure_minimal (Set.singleton_subset_iff.mpr ht)
          (isClosed_closure.inter isClosed_closure))
    have h' : ((e + d : ℕ) : WithBot ℕ∞) ≤ ((r + s : ℕ) : WithBot ℕ∞) := by
      push_cast
      exact (add_le_add_left hTle _).trans h
    exact_mod_cast h'
  have hproper : ringKrullDim A ≤ ringKrullDim (A ⧸ I₀) + ringKrullDim (A ⧸ J₀) := by
    rw [hdI₀', hdJ₀']
    refine (le_natCast_sub_of_add_le hdA).trans ?_
    have : d - e ≤ (r - e) + (s - e) := by omega
    exact_mod_cast this
  obtain ⟨hIeq, hJeq, -, -, hregI, hregJ, -⟩ :=
    IsRegularLocalRing.eq_and_isRegularLocalRing_quotient_and_localIntersectionMultiplicity_eq_one
      I I₀ J J₀ hII₀ hJJ₀ hmult' hdIeq hdJeq hproper
  obtain ⟨huniqY, huniqZ⟩ :=
    IsRegularLocalRing.eq_of_le_of_ringKrullDim_quotient_eq_of_length_quotient_sup_eq_one
      I I₀ J J₀ hII₀ hJJ₀ hmult' hdIeq hdJeq hproper
  have hproper' : ringKrullDim A ≤ ringKrullDim (A ⧸ I) + ringKrullDim (A ⧸ J) := by
    rwa [hdIeq, hdJeq]
  have hsum := IsRegularLocalRing.ringKrullDim_eq_add_of_length_quotient_sup_eq_one I J hmult'
    hproper'
  have hrs : r + s = d + e := by
    rw [hsum, hdIeq, hdJeq, hdI₀', hdJ₀'] at hdA
    have h : ((r - e + (s - e) + e : ℕ) : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      push_cast
      exact hdA
    have h' : r - e + (s - e) + e ≤ d := by exact_mod_cast h
    omega
  have hidx : ((r + s : ℤ) - d) = (e : ℤ) := by
    have : ((r + s : ℕ) : ℤ) = ((d + e : ℕ) : ℤ) := by rw [hrs]
    push_cast at this
    omega
  have h4Y : ∀ y, α y ≠ 0 → t ∈ closure ({y} : Set X) → y = y₀ := fun y hy hty => by
    obtain ⟨hle, hdim, -⟩ :=
      stalk_le_localIdealAt_and_ringKrullDim_quotient_eq k sX IY r e hY hy hty hT
    exact eq_of_localIdealAt_eq hty ht.1 (huniqY _ hle (hdim.trans hdI₀'.symm))
  have h4Z : ∀ z, β z ≠ 0 → t ∈ closure ({z} : Set X) → z = z₀ := fun z hz htz => by
    obtain ⟨hle, hdim, -⟩ :=
      stalk_le_localIdealAt_and_ringKrullDim_quotient_eq k sX IZ s e hZ hz htz hT
    exact eq_of_localIdealAt_eq htz ht.2 (huniqZ _ hle (hdim.trans hdJ₀'.symm))
  have h3Y : α y₀ = 1 :=
    cycleAssociatedToClosedSubscheme_apply_eq_one_of_stalk_eq k sX IY r hy₀ ht.1 hIeq
  have h3Z : β z₀ = 1 :=
    cycleAssociatedToClosedSubscheme_apply_eq_one_of_stalk_eq k sX IZ s hz₀ ht.2 hJeq
  have h1 : torFormulaCycleIntersectionProduct (fieldChowSituation k) sX hX
      ((r + s : ℤ) - d) α β t = 1 := by
    have hcomp : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
    have hbound : TorSupportBound (fieldChowSituation k) sX hX (e : ℤ) y₀ z₀ :=
      torSupportBound_of_intersectProperly k sX hX y₀ z₀ hd
        (by rw [hdimY, hdimZ]; exact_mod_cast hrs) hprop₀
    have hsep : ∀ y ∈ Function.support α, ∀ z ∈ Function.support β, (y, z) ≠ (y₀, z₀) →
        t ∉ closure ({y} : Set X) ∩ closure ({z} : Set X) := by
      rintro y hy z hz hne ⟨hty, htz⟩
      exact hne (Prod.ext (h4Y y hy hty) (h4Z z hz htz))
    have hmult₀ : Module.length A (A ⧸ (I₀ ⊔ J₀)) = 1 := by
      rwa [← hIeq, ← hJeq]
    rw [hidx, torFormulaCycleIntersectionProduct_apply_eq_mul (fieldChowSituation k) sX hX (e : ℤ)
      (finite_support_of_compactSpace α) (finite_support_of_compactSpace β) hbound d hd.le hrelt
      ht.1 ht.2 hy₀ hz₀ hsep I₀ J₀ le_rfl le_rfl hmult₀ rfl rfl hproper, h3Y, h3Z, mul_one]
  have h2Y : ∀ ζ : IY.subscheme, IY.subschemeι ζ = t →
      IsRegularLocalRing (IY.subscheme.presheaf.stalk ζ) := by
    rintro ζ rfl
    exact isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient IY ζ hregI
  have h2Z : ∀ ζ : IZ.subscheme, IZ.subschemeι ζ = t →
      IsRegularLocalRing (IZ.subscheme.presheaf.stalk ζ) := by
    rintro ζ rfl
    exact isRegularLocalRing_stalk_subscheme_of_isRegularLocalRing_quotient IZ ζ hregJ
  exact ⟨h1, h2Y, h2Z, h3Y, h3Z, h4Y, h4Z⟩

end TorFormula

end AlgebraicGeometry

end
