module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.GysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerStructureSheafClass
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Vanishing
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant42.FlatPullbackComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.LciGysinFundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.FundamentalClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinityClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCartierIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreModification
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic

/-!
# The class at infinity on a fundamental class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `b : W ⟶ 𝐏¹_X` be proper and an isomorphism over `𝐀¹_X`, with fibre
at infinity `W_∞`. The proof of Stacks 0FBM computes the cap product of the class
`C ∈ A⁰(W_∞ ⟶ X)` of Stacks 0F9J with the fundamental class `[X]_n` of a scheme of
`δ`-dimension at most `n`:

* `[W]_{n+1}` restricts over `𝐀¹_X` to the flat pullback of `[X]_n`, so it is a lift of `[X]_n`
  and `C ∩ [X]_n = i_∞^*[W]_{n+1}`;
* `W_∞` is an effective Cartier divisor on `W`, so `i_∞^*[W]_{n+1} = [W_∞]_n` by Stacks 02TB.

This file carries out that computation on a test scheme `T ⟶ X`, under the one hypothesis that
makes it work: the base-changed fibre at infinity `W_∞ ×_X T` is an effective Cartier divisor on
`W ×_X T`. Then no irreducible component of `W ×_X T` lies in `W_∞ ×_X T`, so
`dim_δ(W ×_X T) ≤ n + 1` and `dim_δ(W_∞ ×_X T) ≤ n` as soon as `dim_δ(T) ≤ n`, and both steps
above go through. For the blowup of `𝐏¹_X` in `∞(Z)` of Stacks 0FBG the hypothesis holds on every
flat test scheme, in particular on `T = X`.

## Main results

* `Stacks.Chow.schemeDeltaDimension_le_of_genericPoints_subset_range` — a scheme whose generic
  points lie in an open subscheme of `δ`-dimension at most `k` has `δ`-dimension at most `k`.
* `Stacks.Chow.schemeDeltaDimension_le_of_genericPoints_notMem_range` — a closed subscheme
  containing no generic point of a scheme of `δ`-dimension at most `k + 1` has `δ`-dimension at
  most `k`.
* `Stacks.Chow.schemeDeltaDimension_le_add_of_flat` — flat of relative dimension `r` over a
  scheme of `δ`-dimension at most `k` gives `δ`-dimension at most `k + r` (Stacks 02RE).
* `Stacks.Chow.isModificationLift_fundamentalChowClass` — `[W ×_X T]_{n+1}` lifts `[T]_n`.
* `Stacks.Chow.modificationInfinityGysin_fundamentalChowClass` — `i_∞^*[W ×_X T]_{n+1}` is
  `[W_∞ ×_X T]_n` (Stacks 02TB).
* `Stacks.Chow.gysinCapOfLift_fundamentalChowClass` and
  `Stacks.Chow.gysinAtInfinityClass_cap_fundamentalChowClass` — `C ∩ [T]_n = [W_∞ ×_X T]_n`.
* `Stacks.Chow.schemeDeltaDimension_modificationInfinityBaseChange_le` — `dim_δ(W_∞ ×_X T) ≤ n`,
  the bound under which the restriction of `[W_∞ ×_X T]_n` to an open subscheme, such as the
  normal cone `C_ZX ⊆ W_∞` of Stacks 0FBH, is the fundamental class of that open.
* `Stacks.Chow.isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity` —
  for the blowup of Stacks 0FBG the base-changed fibre at infinity along a flat test scheme is an
  effective Cartier divisor.

## References

* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0F9J](https://stacks.math.columbia.edu/tag/0F9J)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02RE](https://stacks.math.columbia.edu/tag/02RE)
* [Stacks Project, Tag 02QP](https://stacks.math.columbia.edu/tag/02QP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Dimension bounds from generic points -/

/-- A closed subscheme whose ideal sheaf is an effective Cartier divisor contains no generic point
of an irreducible component of the ambient scheme. -/
theorem notMem_range_of_mem_genericPoints_of_isEffectiveCartierDivisor {D W : Scheme.{u}}
    (j : D ⟶ W) [IsClosedImmersion j]
    (hj : Stacks.Divisors.IsEffectiveCartierDivisor j.ker) {x : W}
    (hx : x ∈ genericPoints W) : x ∉ Set.range j.base := by
  rw [← Stacks.AffineClosedUnion.support_ker_eq_range j]
  exact notMem_support_of_mem_genericPoints_of_isEffectiveCartierDivisor j.ker hj hx

/-- The generic point of an irreducible component is a generic point of the scheme. -/
private theorem genericPoint_mem_genericPoints_of_mem {W : Scheme.{u}} {Z : Set W}
    (hZ : Z ∈ irreducibleComponents W) : hZ.1.genericPoint ∈ genericPoints W := by
  have hgp := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  change closure ({hZ.1.genericPoint} : Set W) ∈ irreducibleComponents W
  rw [isGenericPoint_def.mp hgp]
  exact hZ

/-- **A scheme whose generic points lie in an open subscheme of `δ`-dimension at most `k` has
`δ`-dimension at most `k`.** The `δ`-dimension is the supremum of the relative dimensions of the
generic points of the irreducible components (Stacks 02QP), and an open immersion does not change
relative dimensions. -/
theorem schemeDeltaDimension_le_of_genericPoints_subset_range (C : ChowSituation.{u})
    {W U : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (v : U ⟶ W) [IsOpenImmersion v] (hv : v ≫ sW = sU)
    (hgen : genericPoints W ⊆ Set.range v.base) {k : ℤ}
    (hU : schemeDeltaDimension C sU ≤ (k : EInt)) :
    schemeDeltaDimension C sW ≤ (k : EInt) := by
  rw [schemeDeltaDimension_eq_iSup]
  refine iSup_le fun Z => WithBotTop.coe_le_coe.mpr ?_
  have hgp := Z.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents (Z : Set W) Z.2)
  obtain ⟨u, hu⟩ := hgen (genericPoint_mem_genericPoints_of_mem Z.2)
  rw [deltaDimension_eq_of_isGenericPoint C sW _ _ hgp, ← hu,
    ← relativeDimension_comp_isOpenImmersion, hv]
  exact relativeDimension_le_of_schemeDeltaDimension_le' C sU hU u

/-- **A closed subscheme containing no generic point drops the `δ`-dimension.** If `j : D ⟶ W` is
a closed immersion whose image contains no generic point of an irreducible component of `W`, and
`dim_δ(W) ≤ k + 1`, then `dim_δ(D) ≤ k`: every point of `D` is a proper specialization of the
generic point of a component of `W` through it, and the dimension function drops strictly along
a proper specialization (Stacks 02JW). -/
theorem schemeDeltaDimension_le_of_genericPoints_notMem_range (C : ChowSituation.{u})
    {W D : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (j : D ⟶ W)
    [IsClosedImmersion j] (hgen : ∀ x ∈ genericPoints W, x ∉ Set.range j.base) {k : ℤ}
    (hW : schemeDeltaDimension C sW ≤ ((k + 1 : ℤ) : EInt)) :
    schemeDeltaDimension C (j ≫ sW) ≤ (k : EInt) := by
  refine schemeDeltaDimension_le_of_forall_relativeDimension_le C sW j fun w => ?_
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({j.base w} : Set W)) isIrreducible_singleton.closure
  have hgp := hZ.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents Z hZ)
  have hmem : j.base w ∈ closure ({hZ.1.genericPoint} : Set W) := by
    rw [isGenericPoint_def.mp hgp]
    exact hsub (subset_closure rfl)
  have hne : j.base w ≠ hZ.1.genericPoint :=
    fun h => hgen _ (genericPoint_mem_genericPoints_of_mem hZ) ⟨w, h⟩
  have hlt := relativeDimension_lt_of_mem_closure_of_ne C sW hmem hne
  have hle := relativeDimension_le_of_schemeDeltaDimension_le' C sW hW hZ.1.genericPoint
  omega

/-- **Stacks 02RE, for the whole scheme.** A scheme flat of relative dimension `r` over a scheme
of `δ`-dimension at most `k` has `δ`-dimension at most `k + r`. This is the dimension bound of
Stacks 02RE for the inverse image of the whole target. -/
theorem schemeDeltaDimension_le_add_of_flat (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ}
    (hY : schemeDeltaDimension C sY ≤ (k : EInt)) :
    schemeDeltaDimension C sX ≤ ((k + (r : ℤ) : ℤ) : EInt) := by
  have h := schemeDeltaDimension_pullback_le C sX sY f hbase r hf (𝟙 Y) k (by simpa using hY)
  exact (schemeDeltaDimension_comp_iso C (asIso (pullback.fst f (𝟙 Y))) sX).ge.trans h

/-! ### The class at infinity on a fundamental class -/

section Modification

variable (C : ChowSituation.{u}) {X W T : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  (b : W ⟶ projectiveLineProduct f) [IsProper b]
  (hA : IsIso (pullback.snd b (projectiveLineAffineChart f)))
  (g : T ⟶ X) [LocallyOfFiniteType g] (n : ℤ)

omit [LocallyOfFiniteType f] [IsProper b] [LocallyOfFiniteType g] in
/-- If the base-changed fibre at infinity `W_∞ ×_X T` is an effective Cartier divisor on
`W ×_X T`, every generic point of `W ×_X T` lies over `𝐀¹_X`. -/
theorem genericPoints_subset_range_modificationAffineChartι
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    genericPoints (modificationBaseChange f b g) ⊆
      Set.range (modificationAffineChartι f b g).base := by
  intro x hx
  have h := notMem_range_of_mem_genericPoints_of_isEffectiveCartierDivisor _ hcart hx
  rw [range_modificationInfinityBaseChange] at h
  exact not_not.mp h

include hA in
/-- The chart `b^{-1}(𝐀¹_X) ×_X T` has `δ`-dimension at most `n + 1` when `dim_δ(T) ≤ n`: it is
flat of relative dimension one over `T`. -/
theorem schemeDeltaDimension_modificationAffineChart_le
    (hT : schemeDeltaDimension C (g ≫ f) ≤ (n : EInt)) :
    schemeDeltaDimension C (modificationAffineChartOver C f b g) ≤ ((n + 1 : ℤ) : EInt) := by
  have := flat_modificationAffineChartProjection f b g hA
  exact schemeDeltaDimension_le_add_of_flat C _ (g ≫ f) _
    (modificationAffineChartProjection_over C f b g) 1
    (relativeDimension_modificationAffineChartProjection f b g hA) hT

include hA in
/-- **`dim_δ(W ×_X T) ≤ n + 1`** when `dim_δ(T) ≤ n` and `W_∞ ×_X T` is an effective Cartier
divisor on `W ×_X T`: all generic points of `W ×_X T` lie in the chart over `𝐀¹_X`. -/
theorem schemeDeltaDimension_modificationBaseChange_le
    (hT : schemeDeltaDimension C (g ≫ f) ≤ (n : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    schemeDeltaDimension C (modificationBaseChangeOver f b g) ≤ ((n + 1 : ℤ) : EInt) :=
  schemeDeltaDimension_le_of_genericPoints_subset_range C _ _ (modificationAffineChartι f b g) rfl
    (genericPoints_subset_range_modificationAffineChartι C f b g hcart)
    (schemeDeltaDimension_modificationAffineChart_le C f b hA g n hT)

include hA in
/-- **`dim_δ(W_∞ ×_X T) ≤ n`** when `dim_δ(T) ≤ n` and `W_∞ ×_X T` is an effective Cartier
divisor on `W ×_X T`. This is the bound under which restricting `[W_∞ ×_X T]_n` to an open
subscheme gives the fundamental class of that open. -/
theorem schemeDeltaDimension_modificationInfinityBaseChange_le
    (hT : schemeDeltaDimension C (g ≫ f) ≤ (n : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    schemeDeltaDimension C (modificationInfinityBaseChangeOver f b g) ≤ (n : EInt) := by
  have h := schemeDeltaDimension_le_of_genericPoints_notMem_range C
    (modificationBaseChangeOver f b g) (modificationInfinityBaseChange f b g)
    (fun x hx => notMem_range_of_mem_genericPoints_of_isEffectiveCartierDivisor _ hcart hx)
    (schemeDeltaDimension_modificationBaseChange_le C f b hA g n hT hcart)
  rwa [schemeDeltaDimension_congr C (modificationInfinityBaseChange_over f b g)] at h

/-- **`[W ×_X T]_{n+1}` lifts `[T]_n`.** Its restriction to the chart over `𝐀¹_X` is the
fundamental class of the chart, which is the flat pullback of `[T]_n` along the projection of the
chart to `T` (Stacks 02RB). -/
theorem isModificationLift_fundamentalChowClass
    (hT : schemeDeltaDimension C (g ≫ f) ≤ (n : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    IsModificationLift C f b hA g n (fundamentalChowClass C (g ≫ f) n)
      (fundamentalChowClass C (modificationBaseChangeOver f b g) (n + 1)) := by
  have := flat_modificationAffineChartProjection f b g hA
  unfold IsModificationLift
  rw [chowGroupRestrict_fundamentalChowClass C _ _ _ rfl (n + 1)
      (schemeDeltaDimension_modificationBaseChange_le C f b hA g n hT hcart),
    flatPullbackChow_fundamentalChowClass C _ _ _ (modificationAffineChartProjection_over C f b g)
      1 (relativeDimension_modificationAffineChartProjection f b g hA) n _ hT]
  rfl

/-- **Stacks 02TB at infinity: `i_∞^*[W ×_X T]_{n+1} = [W_∞ ×_X T]_n`.** When `W_∞ ×_X T` is an
effective Cartier divisor on `W ×_X T` and `dim_δ(W ×_X T) ≤ n + 1`, the Gysin map of the divisor
at infinity carries the fundamental class of `W ×_X T` to the fundamental class of the divisor. -/
theorem modificationInfinityGysin_fundamentalChowClass
    (hW : schemeDeltaDimension C (modificationBaseChangeOver f b g) ≤ ((n + 1 : ℤ) : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    modificationInfinityGysin C f b g n
        (fundamentalChowClass C (modificationBaseChangeOver f b g) (n + 1)) =
      fundamentalChowClass C (modificationInfinityBaseChangeOver f b g) n := by
  have hD : Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme (modificationBaseChange f b g) (modificationInfinityModule f b g)
        (modificationInfinitySection f b g)) := by
    rw [zeroScheme_modificationInfinitySection]
    exact hcart
  unfold modificationInfinityGysin
  rw [AddMonoidHom.comp_apply, gysinSystemOfInvertible_onChow_eq_gysinChowOfInvertible,
    gysinChowOfInvertible_fundamentalChowClass C (modificationBaseChangeOver f b g) n
      (modificationInfinityModule f b g) (modificationInfinitySection f b g) hW hD]
  exact chowPushforwardOfIso_fundamentalChowClass C _ _ _ _ n

/-- **The class at infinity on a fundamental class, as a cap operation:
`C ∩ [T]_n = [W_∞ ×_X T]_n`.** If `dim_δ(T) ≤ n` and `W_∞ ×_X T` is an effective Cartier divisor
on `W ×_X T`, then `[W ×_X T]_{n+1}` is a lift of `[T]_n`, so the cap operation of Stacks 0F9J
is `i_∞^*[W ×_X T]_{n+1}`, which is `[W_∞ ×_X T]_n` by Stacks 02TB. -/
theorem gysinCapOfLift_fundamentalChowClass
    (hT : schemeDeltaDimension C (g ≫ f) ≤ (n : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    gysinCapAtInfinity C f b hA g n (fundamentalChowClass C (g ≫ f) n) =
      fundamentalChowClass C (modificationInfinityBaseChangeOver f b g) n := by
  rw [gysinCapAtInfinity_eq_of_isModificationLift C f b hA g n _ _
    (isModificationLift_fundamentalChowClass C f b hA g n hT hcart)]
  exact modificationInfinityGysin_fundamentalChowClass C f b g n
    (schemeDeltaDimension_modificationBaseChange_le C f b hA g n hT hcart) hcart

/-- **The class at infinity of Stacks 0F9J on a fundamental class: `C ∩ [T]_n = [W_∞ ×_X T]_n`**,
as the cap operation of the bivariant class `C ∈ A⁰(W_∞ ⟶ X)`, read in the degree `n - 0` in
which a class of degree `0` caps. -/
theorem gysinAtInfinityClass_cap_fundamentalChowClass
    (hT : schemeDeltaDimension C (g ≫ f) ≤ (n : EInt))
    (hcart : Stacks.Divisors.IsEffectiveCartierDivisor (modificationInfinityBaseChange f b g).ker) :
    (gysinAtInfinityClass C f b hA).cap g n (fundamentalChowClass C (g ≫ f) n) =
      fundamentalChowClass C (modificationInfinityBaseChangeOver f b g) (n - 0) := by
  rw [gysinAtInfinityClass_cap, gysinCapOfLift_fundamentalChowClass C f b hA g n hT hcart]
  refine (chowGroupDegreeEquiv_eq_iff_heq C _ _ _ _).2 ?_
  rw [sub_zero]

end Modification

/-! ### The blowup at infinity -/

/-- **For the blowup of `𝐏¹_X` in `∞(Z)`, the fibre at infinity stays an effective Cartier
divisor after flat base change.** If `g : T ⟶ X` is flat, the base-changed fibre at infinity
`W_∞ ×_X T` is an effective Cartier divisor on `W ×_X T`: it is the inverse image of the
effective Cartier divisor `W_∞ ⊆ W` (Stacks 0FBG) along the flat morphism `W ×_X T ⟶ W`. -/
theorem isEffectiveCartierDivisor_ker_modificationInfinityBaseChange_blowupAtInfinity
    {X S T : Scheme.{u}} (ℐ : X.IdealSheafData) (f : X ⟶ S) (g : T ⟶ X) [Flat g] :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (modificationInfinityBaseChange f (blowupAtInfinityToProjectiveLineProduct ℐ f) g).ker := by
  set b := blowupAtInfinityToProjectiveLineProduct ℐ f
  have hsq : IsPullback (modificationInfinityBaseChange f b g)
      (pullback.fst (modificationProjectionAtInfinity f b) g)
      (pullback.fst (modificationProjection f b) g) (modificationInclusionAtInfinity f b) := by
    refine (IsPullback.of_bot ?_ (modificationInfinityBaseChange_comp_fst f b g).symm
      (IsPullback.of_hasPullback (modificationProjection f b) g)).flip
    rw [modificationInfinityBaseChange_comp_snd]
    exact IsPullback.of_hasPullback (modificationProjectionAtInfinity f b) g
  have : Flat (pullback.fst (modificationProjection f b) g) :=
    Flat.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback (modificationProjection f b) g).flip inferInstance
  rw [AlgebraicGeometry.ker_eq_comap_ker_of_isPullback hsq]
  exact Stacks.Divisors.isPullbackDefined_of_flat _ _
    (isEffectiveCartierDivisor_ker_modificationInclusionAtInfinity ℐ f)

end Stacks.Chow

end
