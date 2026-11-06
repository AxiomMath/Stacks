module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FlatPullbackSectionWeilDivisorChart

/-!
# The coefficients of the two sides of Stacks 0EQQ at a prime divisor

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be flat of relative dimension `r`,
let `Y` be integral with `n = dim_δ(Y)`, and let `s` be a nonzero meromorphic section of an
invertible `𝒪_Y`-module `ℒ`. Let `Z ⊆ X` be an integral closed subspace of δ-dimension
`n + r - 1` with generic point `ξ`, let `U ⟶ V` be a diagram of affine étale charts over `f` with
`ℒ` free over `V` on `e`, and let `u` be a point of `U` over `ξ`. With `O = 𝒪_{U, u}` and
`c = φ(s / e) ∈ Q(O)` the reading of `s` at `u` (`AlgebraicGeometry.Space.flatChartReading`),
this file proves that the coefficients at `Z` of both sides of Stacks 0EQQ are `ord_O(c)`.

On the right-hand side `∑ m_{X_i, X} (X_i → X)_* div_{f^*ℒ|_{X_i}}(s_i)`, the components `X_i`
through `ξ` are finitely many. For each of them the coefficient at `Z` is
`m_{X_i, X} · ord_{O_i}(π_i(c))` by
`AlgebraicGeometry.Space.componentDivisor_apply_eq_ordTotalFracInt`, with `O_i` the local ring
of `U ×_X X_i` at a point over `u`; and the minimal primes of `O` are partitioned according to
the component on which their points lie, a minimal prime on `X_i` having branch multiplicity
`m_{X_i, X}`. So the sum is `ord_O(c)` by
`Ring.ordTotalFracInt_eq_finsum_mul_ordTotalFracInt_of_surjective`.

On the left-hand side `f^* div_ℒ(s)`, only the integral closed subspace `Z'` of `Y` with generic
point `f(ξ)` contributes, with multiplicity the colength `m` of `𝔪_v 𝒪_{U, u}`, and
`ord_O(c) = m · ord_{𝒪_{V, v}}(s / e)` by Stacks 02M1.

## Main results

* `AlgebraicGeometry.Space.componentDivisorSum_apply_eq_ordTotalFracInt`: the coefficient of the
  right-hand side at `Z`.
* `AlgebraicGeometry.Space.flatPullbackMap_sectionWeilDivisor_apply_eq_ordTotalFracInt`: the
  coefficient of the left-hand side at `Z`.

## References

* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
* [Stacks Project, Tag 0EQQ](https://stacks.math.columbia.edu/tag/0EQQ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace IsLocalRing
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] chartMeromorphicFunctionAlgebra

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (f : X ⟶ Y) (hbase : f ≫ sY = sX) (r : ℕ) (hflat : IsFlat D.site D.base D.base_mem f)
    (hr : HasRelativeDimension r D.site D.base D.base_mem f)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y) {n : ℤ}
    (hn : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1) (hL : IsInvertibleSheaf D sY hY L)
    (s : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L) (hs : s ≠ 0)

/-! ### The minimal primes of the local ring of a chart and the components through it -/

include hX in
/-- The image in `|X|` of the point of a minimal prime of the local ring of an étale chart is a
generic point of an irreducible component of `|X|`. -/
theorem chartSchemeToPoints_fromSpecStalk_mem_genericPoints
    (U : SmallEtale D.site D.base D.base_mem X) (u : chartScheme U)
    (p : minimalPrimes ((chartScheme U).presheaf.stalk u)) :
    chartSchemeToPoints D.site D.base D.base_mem X U
        ((chartScheme U).fromSpecStalk u ⟨p, p.2.1.1⟩) ∈
      genericPoints (points D.site D.base D.base_mem X) :=
  (mem_genericPoints_chartScheme_iff D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) U _).mp (fromSpecStalk_mem_genericPoints u _ p.2)

/-- The image in `|X|` of the point of a prime of the local ring of an étale chart at `u`
generizes the image of `u`. -/
theorem chartSchemeToPoints_fromSpecStalk_specializes
    (U : SmallEtale D.site D.base D.base_mem X) (u : chartScheme U)
    (p : PrimeSpectrum ((chartScheme U).presheaf.stalk u)) :
    chartSchemeToPoints D.site D.base D.base_mem X U ((chartScheme U).fromSpecStalk u p) ⤳
      chartSchemeToPoints D.site D.base D.base_mem X U u := by
  have h : (chartScheme U).fromSpecStalk u p ∈ Set.range ((chartScheme U).fromSpecStalk u) :=
    ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at h
  exact h.map (continuous_chartSchemeToPoints D.site D.base D.base_mem U)

include hX in
/-- **The component through a generic point.** For a generic point `ζ` of an irreducible
component of `|X|`, the integral closed subspace with set of points `closure {ζ}` is an
irreducible component, of δ-dimension `n + r`, and the only one containing `ζ`. -/
theorem existsUnique_component_of_mem_genericPoints (ζ : points D.site D.base D.base_mem X)
    (hζ : ζ ∈ genericPoints (points D.site D.base D.base_mem X)) :
    ∃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
      subspacePointSet D.site D.base D.base_mem X W.subspace =
          closure ({ζ} : Set (points D.site D.base D.base_mem X)) ∧
        ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X,
          ζ ∈ subspacePointSet D.site D.base D.base_mem X W'.subspace → W' = W := by
  have hcomp : closure ({ζ} : Set (points D.site D.base D.base_mem X)) ∈
      irreducibleComponents (points D.site D.base D.base_mem X) := hζ
  refine ⟨integralClosedSubspaceOfPoints D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) ⟨_, hcomp.1, isClosed_closure⟩,
    subspacePointSet_integralClosedSubspaceOfPoints D.site D.base D.base_mem _ _ _,
    fun W' hW' => ?_⟩
  refine eq_integralClosedSubspaceOfPoints D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) W' _ ?_
  have hsub : closure ({ζ} : Set (points D.site D.base D.base_mem X)) ⊆
      subspacePointSet D.site D.base D.base_mem X W'.subspace :=
    (isGenericPoint_closure.mem_closed_set_iff
      (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 W')).mp hW'
  exact (hcomp.2 (isIrreducible_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem
    W') hsub).antisymm hsub

/-! ### The right-hand side at a prime divisor -/


include hflat hintY hL hs in
/-- The coefficient of a pushed forward multiple of a component divisor at the image of an
integral closed subspace of the component, on the base-changed chart. -/
theorem integralClosedSubspacePushforward_componentDivisor_apply
    (W : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hW : subspacePointSet D.site D.base D.base_mem X W.subspace ∈
      irreducibleComponents (points D.site D.base D.base_mem X))
    (hWd : deltaDimension D sX W = n + r) (m : ℤ)
    (Zw : IntegralClosedSubspace D.site D.base D.base_mem W.subspace.toFunctor)
    (hZwd : deltaDimension D (W.subspace.ι ≫ sX) Zw = n + r - 1)
    (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale D.site D.base D.base_mem Y) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V),
      Function.Bijective fun x : chartRing D.site D.base D.base_mem Y hY.1 W ↦ x • e W k)
    (u : chartScheme d.U)
    (q : chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U))
    (hq : closedSubspaceBaseChangeChartProj D.site D.base D.base_mem hX.1 W.subspace
      W.isClosedSubspace d.U q = u)
    (hqZ : chartSchemeToPoints D.site D.base D.base_mem W.subspace.toFunctor
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 W.subspace W.isClosedSubspace
        d.U) q = Zw.ambientGenericPoint D.site D.base D.base_mem)
    [IsNoetherianRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)]
    [Ring.KrullDimLE 1 ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)] :
    (integralClosedSubspacePushforward D sX hX W (n + r - 1)
        (m • componentDivisor D sX hX sY hY f r hflat hintY L hL s hs W hW hWd)).1
        (IntegralClosedSubspace.pushforward D.site D.base D.base_mem hX.1 W.isClosedSubspace.1
          (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2 Zw) =
      m * Ring.ordTotalFracInt ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
          D.base_mem hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)
        (IsLocalization.map (T := ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
            D.base_mem hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q)⁰)
          (FractionRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
            hX.1 W.subspace W.isClosedSubspace d.U)).presheaf.stalk q))
          (closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 W d.U u q hq)
          (nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem
            hX.1 (D.isDecentSpace_of_isGood sX hX) W hW d.U u q hq)
          (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u))
        (((isUnit_flatChartReading D sY hY f hflat hintY L hL s hs d hV e hecompat hebij
          u)).map _) := by
  refine (cycleClosedPushforward_apply_pushforward D hX.1 W.isClosedSubspace.1
    (D.isDecentSpace_of_isGood sX hX) W.isClosedSubspace.2
    (m • componentDivisor D sX hX sY hY f r hflat hintY L hL s hs W hW hWd).1 Zw).trans ?_
  rw [AddSubgroup.coe_zsmul, Pi.smul_apply, smul_eq_mul,
    componentDivisor_apply_eq_ordTotalFracInt D sX hX sY hY f r hflat hintY L hL s hs W hW hWd
      Zw hZwd d hU hV e hecompat hebij u q hq hqZ]

include hbase hr hn in
/-- **The coefficient of the right-hand side of Stacks 0EQQ at a prime divisor, on a chart.** At
an integral closed subspace `Z` of δ-dimension `n + r - 1` the coefficient of
`∑ m_{X_i, X} (X_i → X)_* div_{f^*ℒ|_{X_i}}(s_i)` is the order of vanishing of the reading `c` of
`s` in the local ring `O` of a chart at a point over the generic point of `Z`. -/
theorem componentDivisorSum_apply_eq_ordTotalFracInt
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = n + r - 1)
    (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale D.site D.base D.base_mem Y) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V),
      Function.Bijective fun x : chartRing D.site D.base D.base_mem Y hY.1 W ↦ x • e W k)
    (u : chartScheme d.U)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X d.U u =
      Z.ambientGenericPoint D.site D.base D.base_mem)
    [IsNoetherianRing ((chartScheme d.U).presheaf.stalk u)]
    [Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u)]
    (hdimA : ringKrullDim ((chartScheme d.U).presheaf.stalk u) = 1) :
    (componentDivisorSum D sX hX sY hY f r hflat hintY (n := n) L hL s hs).1 Z =
      Ring.ordTotalFracInt ((chartScheme d.U).presheaf.stalk u)
        (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u)
        (isUnit_flatChartReading D sY hY f hflat hintY L hL s hs d hV e hecompat hebij u) := by
  classical
  set ξ := Z.ambientGenericPoint D.site D.base D.base_mem with hξ
  have hXdec := D.isDecentSpace_of_isGood sX hX
  have hXN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sX hX
  set term : topDimensionalComponents D sX (n + r) → ℤ := fun j =>
    (integralClosedSubspacePushforward D sX hX j.1 (n + r - 1)
      (spaceMultiplicity D X hX.1 j.1 •
        componentDivisor D sX hX sY hY f r hflat hintY L hL s hs j.1 j.2.1 j.2.2)).1 Z
    with hterm_def
  have hsum : (componentDivisorSum D sX hX sY hY f r hflat hintY (n := n) L hL s hs).1 Z =
      ∑ᶠ j, term j := rfl
  -- only the components through `ξ` contribute
  set SZ : Set (topDimensionalComponents D sX (n + r)) :=
    {j | ξ ∈ subspacePointSet D.site D.base D.base_mem X j.1.subspace} with hSZ
  have hξZ : ξ ∈ subspacePointSet D.site D.base D.base_mem X Z.subspace := ⟨_, rfl⟩
  have hzero : ∀ j, term j ≠ 0 → j ∈ SZ := fun j hj =>
    subspacePointSet_subset_of_pushforward_ne_zero D sX hX j.1 _ _ Z hj hξZ
  have hSZfin : SZ.Finite := by
    obtain ⟨t, ht, hfin⟩ := locallyFinite_topDimensionalComponents D sX hX (n + r) ξ
    exact hfin.subset fun j hj => ⟨ξ, hj, mem_of_mem_nhds ht⟩
  have : Finite SZ := hSZfin.to_subtype
  have hsplit : ∑ᶠ j, term j = ∑ᶠ j : SZ, term j.1 := by
    rw [finsum_set_coe_eq_finsum_mem, ← finsum_mem_univ]
    exact finsum_mem_inter_support_eq' _ _ _ fun j hj => ⟨fun _ => hzero j hj, fun _ => trivial⟩
  rw [hsum, hsplit]
  -- the data at each component through `ξ`
  have hsubZ : ∀ j : SZ, subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
      Set.range (pointsMap D.site D.base D.base_mem _ j.1.1.subspace.ι) := by
    intro j
    exact ((Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).mem_closed_set_iff
      (isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hX.1 j.1.1)).mp j.2
  choose Zj hZj using fun j : SZ => IntegralClosedSubspace.exists_pushforward_eq D.site D.base
    D.base_mem hX.1 j.1.1.isClosedSubspace.1 hXdec j.1.1.isIntegralSpace.isDecentSpace
    j.1.1.isClosedSubspace.2 Z (hsubZ j)
  choose q hq using fun j : SZ => exists_closedSubspaceBaseChangeChartProj_eq D.site D.base
    D.base_mem hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U u (by rw [hu]; exact j.2)
  have hqZ : ∀ j : SZ, chartSchemeToPoints D.site D.base D.base_mem j.1.1.subspace.toFunctor
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 j.1.1.subspace
        j.1.1.isClosedSubspace d.U) (q j) =
        (Zj j).ambientGenericPoint D.site D.base D.base_mem := by
    intro j
    refine pointsMap_ι_injective D hX.1 j.1.1.subspace j.1.1.isClosedSubspace ?_
    rw [← chartSchemeToPoints_closedSubspaceBaseChangeChartProj, hq j, hu, hξ, ← hZj j,
      IntegralClosedSubspace.ambientGenericPoint_pushforward]
  have hZjd : ∀ j : SZ, deltaDimension D (j.1.1.subspace.ι ≫ sX) (Zj j) = n + r - 1 := by
    intro j
    rwa [← IntegralClosedSubspace.deltaDimension_pushforward D sX hX.2.2 hX.1
      j.1.1.isClosedSubspace.1 hXdec j.1.1.isClosedSubspace.2, hZj j]
  -- the prime divisors of the components and the local rings of their charts
  choose P hP using fun j : SZ => exists_primeDivisor_of_deltaDimension_component D sX hX r
    j.1.1 j.1.2.2 (Zj j) (hZjd j)
  have hqP : ∀ j : SZ, chartSchemeToPoints D.site D.base D.base_mem j.1.1.subspace.toFunctor
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 j.1.1.subspace
        j.1.1.isClosedSubspace d.U) (q j) =
      (P j).genericPoint D.site D.base D.base_mem j.1.1.subspace.toFunctor := by
    intro j
    rw [PrimeDivisor.genericPoint_eq_ambientGenericPoint D j.1.1.isClosedSubspace.1, hP j]
    exact hqZ j
  have hdim' : ∀ j : SZ, ringKrullDim ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
      D.base_mem hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j)) = 1 :=
    fun j => (P j).ringKrullDim_chartStalk D.site D.base D.base_mem j.1.1.isClosedSubspace.1
      j.1.1.isIntegralSpace.isDecentSpace (closedSubspaceBaseChangeChart D.site D.base D.base_mem
        hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U) (q j) (hqP j)
  have hNj : ∀ j : SZ, IsNoetherianRing ((chartScheme (closedSubspaceBaseChangeChart D.site
      D.base D.base_mem hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j)) := by
    intro j
    have := isLocallyNoetherian_chartScheme D.site D.base D.base_mem
      (⟨j.1.1.subspace.toFunctor, j.1.1.isClosedSubspace.1⟩ : AlgebraicSpaces D.site D.base
        D.base_mem)
      (hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D (j.1.1.subspace.ι ≫ sX)
        (isGood_integralClosedSubspace D sX hX j.1.1))
      (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 j.1.1.subspace
        j.1.1.isClosedSubspace d.U)
    infer_instance
  have hKj : ∀ j : SZ, Ring.KrullDimLE 1 ((chartScheme (closedSubspaceBaseChangeChart D.site
      D.base D.base_mem hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j)) :=
    fun j => Ring.krullDimLE_iff.mpr (by rw [hdim' j]; exact_mod_cast le_rfl)
  have hRj : ∀ j : SZ, _root_.IsReduced ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
      D.base_mem hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j)) := by
    intro j
    have : IsReduced (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
        j.1.1.subspace j.1.1.isClosedSubspace d.U)) :=
      (exists_atlas_iff_forall_etale D.site D.base D.base_mem j.1.1.subspace.toFunctor
        (fun Y : Scheme.{u} => IsReduced Y) j.1.1.isClosedSubspace.1).mp
        j.1.1.isIntegralSpace.1 _ _
        (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1 j.1.1.subspace
          j.1.1.isClosedSubspace d.U).property
    infer_instance
  have hterm : ∀ j : SZ, term j.1 = spaceMultiplicity D X hX.1 j.1.1 *
      Ring.ordTotalFracInt ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
          hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j))
        (IsLocalization.map (T := ((chartScheme (closedSubspaceBaseChangeChart D.site D.base
            D.base_mem hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j))⁰)
          (FractionRing ((chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem
            hX.1 j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j)))
          (closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 j.1.1 d.U u (q j) (hq j))
          (nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem
            hX.1 hXdec j.1.1 j.1.2.1 d.U u (q j) (hq j))
          (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u))
        (((isUnit_flatChartReading D sY hY f hflat hintY L hL s hs d hV e hecompat hebij
          u)).map _) := fun j => by
    have h := integralClosedSubspacePushforward_componentDivisor_apply D sX hX sY hY f r hflat
      hintY L hL s hs j.1.1 j.1.2.1 j.1.2.2 (spaceMultiplicity D X hX.1 j.1.1) (Zj j) (hZjd j) d hU
      hV e hecompat hebij u (q j) (hq j) (hqZ j)
    rwa [hZj j] at h
  rw [finsum_congr hterm]
  have hcomp : ∀ p : minimalPrimes ((chartScheme d.U).presheaf.stalk u),
      ∃ W : IntegralClosedSubspace D.site D.base D.base_mem X,
        subspacePointSet D.site D.base D.base_mem X W.subspace =
            closure ({chartSchemeToPoints D.site D.base D.base_mem X d.U
                        ((chartScheme d.U).fromSpecStalk u ⟨p, p.2.1.1⟩)} :
                Set (points D.site D.base D.base_mem X)) ∧
          ∀ W' : IntegralClosedSubspace D.site D.base D.base_mem X,
            chartSchemeToPoints D.site D.base D.base_mem X d.U
                ((chartScheme d.U).fromSpecStalk u ⟨p, p.2.1.1⟩) ∈
              subspacePointSet D.site D.base D.base_mem X W'.subspace → W' = W :=
    fun p => existsUnique_component_of_mem_genericPoints D sX hX _
      (chartSchemeToPoints_fromSpecStalk_mem_genericPoints D sX hX d.U u p)
  refine (Ring.ordTotalFracInt_eq_finsum_mul_ordTotalFracInt_of_surjective hdimA
    (fun j : SZ => (chartScheme (closedSubspaceBaseChangeChart D.site D.base D.base_mem hX.1
      j.1.1.subspace j.1.1.isClosedSubspace d.U)).presheaf.stalk (q j))
    hdim'
    (fun j => closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 j.1.1 d.U u (q j)
      (hq j))
    (fun j => surjective_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem hX.1 j.1.1 d.U
      u (q j) (hq j))
    (fun j => nonZeroDivisors_le_comap_closedSubspaceBaseChangeStalkMap D.site D.base D.base_mem
      hX.1 hXdec j.1.1 j.1.2.1 d.U u (q j) (hq j))
    (fun j => comap_closedSubspaceBaseChangeStalkMap_mem_minimalPrimes D.site D.base D.base_mem
      hX.1 hXdec j.1.1 j.1.2.1 d.U u (q j) (hq j))
    (fun j => spaceMultiplicity D X hX.1 j.1.1) ?_ ?_ _ _).symm
  · -- every branch lies on exactly one component through `ξ`
    intro p
    obtain ⟨Wp, hWp, huniq⟩ := hcomp p
    have hWpcomp : subspacePointSet D.site D.base D.base_mem X Wp.subspace ∈
        irreducibleComponents (points D.site D.base D.base_mem X) := by
      rw [hWp]
      exact chartSchemeToPoints_fromSpecStalk_mem_genericPoints D sX hX d.U u p
    have hWpd := deltaDimension_eq_add_of_mem_irreducibleComponents_of_isFlat D sX hX sY hY f
      hbase r hflat hr hintY hn Wp hWpcomp
    have hξWp : ξ ∈ subspacePointSet D.site D.base D.base_mem X Wp.subspace := by
      rw [hWp, ← hu]
      exact specializes_iff_mem_closure.mp
        (chartSchemeToPoints_fromSpecStalk_specializes D d.U u ⟨p, p.2.1.1⟩)
    refine ⟨⟨⟨Wp, hWpcomp, hWpd⟩, hξWp⟩, ?_, fun j hj => ?_⟩
    · refine (ker_closedSubspaceBaseChangeStalkMap_le_iff D.site D.base D.base_mem hX.1 Wp d.U u
        _ _ ⟨p, p.2.1.1⟩).mpr ?_
      rw [hWp]
      exact subset_closure rfl
    · have hj' := (ker_closedSubspaceBaseChangeStalkMap_le_iff D.site D.base D.base_mem hX.1 j.1.1
        d.U u _ _ ⟨p, p.2.1.1⟩).mp hj
      exact Subtype.ext (Subtype.ext (huniq j.1.1 hj'))
  · -- a branch on a component has the multiplicity of that component
    intro p j hj
    have hj' := (ker_closedSubspaceBaseChangeStalkMap_le_iff D.site D.base D.base_mem hX.1 j.1.1
      d.U u _ _ ⟨p, p.2.1.1⟩).mp hj
    obtain ⟨Wp, hWp, huniq⟩ := hcomp p
    have hjW := huniq j.1.1 hj'
    have := t0Space_points_of_isDecentSpace D.site D.base D.base_mem hX.1 hXdec
    have hgen : j.1.1.ambientGenericPoint D.site D.base D.base_mem =
        chartSchemeToPoints D.site D.base D.base_mem X d.U
          ((chartScheme d.U).fromSpecStalk u ⟨p, p.2.1.1⟩) := by
      refine (j.1.1.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hX.1).eq ?_
      show closure _ = _
      rw [hjW, hWp]
    rw [minimalPrimeLength_eq_toNat_geometricLength D.site D.base D.base_mem hX.1 d.U u p
      (canonicalGeometricPoint D.site D.base D.base_mem X
        (j.1.1.ambientGenericPoint D.site D.base D.base_mem))
      (by rw [canonicalGeometricPoint_image, hgen])]
    rfl

/-! ### The left-hand side at a prime divisor -/

include hn in
/-- **The coefficient of the flat pullback of `div_ℒ(s)` at a prime divisor, on a chart.** At an
integral closed subspace `Z ⊆ X` of δ-dimension `n + r - 1` the coefficient of `f^* div_ℒ(s)` is
the order of vanishing of the reading `c` of `s` in the local ring `O` of a chart at a point over
the generic point `ξ` of `Z`.

Only the integral closed subspace `Z'` of `Y` with generic point `f(ξ)` can contribute. If
`f(ξ)` is the generic point of `Y` it does not, `div_ℒ(s)` being an `(n - 1)`-cycle, and `c` is
then the image of a unit of `O`. Otherwise `Z'` is a prime divisor, its coefficient is
`ord_{Z', ℒ}(s) = ord_{𝒪_{V, v}}(s / e)` (Stacks 0EPR on a chart), the multiplicity of `Z` in
`f^*[Z']` is the colength `m` of `𝔪_v 𝒪_{U, u}`
(`AlgebraicGeometry.Space.flatPullbackMult_eq_toNat_length_chartStalk`), and
`ord_O(c) = m · ord_{𝒪_{V, v}}(s / e)` by Stacks 02M1
(`Ring.ordTotalFracInt_map_of_flatHom_toNat`). -/
theorem flatPullbackMap_sectionWeilDivisor_apply_eq_ordTotalFracInt
    (Z : IntegralClosedSubspace D.site D.base D.base_mem X)
    (hZ : deltaDimension D sX Z = n + r - 1)
    (d : ChartDiagram D.site D.base D.base_mem X Y f)
    (hU : IsAffine (chartScheme d.U)) (hV : IsAffine (chartScheme d.V))
    (e : (W : SmallEtale D.site D.base D.base_mem Y) → (W ⟶ d.V) → L.val.obj (op W))
    (hecompat : ∀ (W W' : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V) (g : W' ⟶ W),
      (L.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hebij : ∀ (W : SmallEtale D.site D.base D.base_mem Y) (k : W ⟶ d.V),
      Function.Bijective fun x : chartRing D.site D.base D.base_mem Y hY.1 W ↦ x • e W k)
    (u : chartScheme d.U)
    (hu : chartSchemeToPoints D.site D.base D.base_mem X d.U u =
      Z.ambientGenericPoint D.site D.base D.base_mem)
    [IsNoetherianRing ((chartScheme d.U).presheaf.stalk u)]
    [Ring.KrullDimLE 1 ((chartScheme d.U).presheaf.stalk u)] :
    (flatPullbackMap D sX hX sY hY f hbase r hflat hr (n - 1) (n + r - 1) (by ring)
        (sectionWeilDivisor D sY hY hintY L hL hn s hs)).1 Z =
      Ring.ordTotalFracInt ((chartScheme d.U).presheaf.stalk u)
        (flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u)
        (isUnit_flatChartReading D sY hY f hflat hintY L hL s hs d hV e hecompat hebij u) := by
  classical
  rw [flatPullbackMap_apply]
  set ξ := Z.ambientGenericPoint D.site D.base D.base_mem with hξ
  set y := pointsMap D.site D.base D.base_mem X f ξ with hy_def
  set α := sectionWeilDivisor D sY hY hintY L hL hn s hs with hα_def
  have hYdec := D.isDecentSpace_of_isGood sY hY
  have hYN := hasEtaleLocalProperty_isLocallyNoetherian_of_isGood D sY hY
  have := t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1 hYdec
  obtain ⟨dY, hdY⟩ := exists_dimensionFunction_deltaValue_of_isGood D sY hY
  have hyge : n - 1 ≤ D.deltaValue sY y := by
    have h := inducedDimensionValue_le_add_of_hasRelativeDimension D sX hX sY hY f hbase r hr ξ
    have hξ' : D.deltaValue sX ξ = n + r - 1 := hZ
    have h' : D.deltaValue sX ξ ≤ D.deltaValue sY y + r := h
    omega
  have hv : chartSchemeToPoints D.site D.base D.base_mem Y d.V
      (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u) = y := by
    rw [chartSchemeToPoints_map_chartDiagram, hu]
  -- the integral closed subspace of `Y` with generic point `y`
  set Zy := integralClosedSubspaceOfPoints D.site D.base D.base_mem hY.1 hYdec
    (IrreducibleCloseds.closureSingleton y) with hZy
  have hZypts : subspacePointSet D.site D.base D.base_mem Y Zy.subspace = closure {y} :=
    subspacePointSet_integralClosedSubspaceOfPoints D.site D.base D.base_mem _ _ _
  have hZygen : IsGenericPoint y (subspacePointSet D.site D.base D.base_mem Y Zy.subspace) := by
    rw [hZypts]
    rfl
  have hZyamb : Zy.ambientGenericPoint D.site D.base D.base_mem = y :=
    (Zy.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).eq hZygen
  have hZyd : deltaDimension D sY Zy = D.deltaValue sY y :=
    deltaDimension_eq_of_isGenericPoint D sY hY.1 Zy y hZygen
  -- only `Zy` contributes to the coefficient
  have hsingle : ∀ W', W' ≠ Zy →
      α.1 W' * flatPullbackMult D sX hX sY hY f hbase r hflat hr W' Z = 0 := by
    intro W' hW'
    by_contra hne
    have hαW : α.1 W' ≠ 0 := left_ne_zero_of_mul hne
    have hm := right_ne_zero_of_mul hne
    have hWd : deltaDimension D sY W' = n - 1 := α.2.2 W' hαW
    have hyW : y ∈ subspacePointSet D.site D.base D.base_mem Y W'.subspace :=
      mem_subspacePointSet_of_flatPullbackMult_ne_zero D sX hX sY hY f hbase r hflat hr W' Z hm
    have hspec : W'.ambientGenericPoint D.site D.base D.base_mem ⤳ y :=
      (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).specializes hyW
    have hgen : W'.ambientGenericPoint D.site D.base D.base_mem = y := by
      by_contra hne'
      have hlt := dY.strictAnti_specializes hspec hne'
      rw [hdY, hdY] at hlt
      have hWd' : D.deltaValue sY (W'.ambientGenericPoint D.site D.base D.base_mem) = n - 1 := hWd
      omega
    apply hW'
    refine injective_integralClosedSubspaceSupport D.site D.base D.base_mem hY.1
      (IrreducibleCloseds.ext ?_)
    show subspacePointSet D.site D.base D.base_mem Y W'.subspace =
      subspacePointSet D.site D.base D.base_mem Y Zy.subspace
    rw [hZypts, ← hgen, (W'.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem hY.1).def]
  rw [finsum_eq_single _ Zy hsingle]
  have hreg : IsRegularMeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L s :=
    (isRegularMeromorphicSection_iff_ne_zero D.site D.base D.base_mem hY.1 hintY hYN L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s).mpr hs
  by_cases hy : y = genericPoint D.site D.base D.base_mem hY.1 hintY
  · -- `ξ` lies over the generic point of `Y`: both sides vanish
    have hyn : D.deltaValue sY y = n := by
      rw [hy]
      exact deltaValue_genericPoint_eq_of_deltaDimensionClosed D sY hY hintY hn
    have hα0 : α.1 Zy = 0 := by
      by_contra h
      have := α.2.2 Zy h
      omega
    rw [hα0, zero_mul]
    obtain ⟨r0, hr0, hr0eq⟩ := exists_isUnit_chartPointMeromorphicMap_chartRatio_of_eq_genericPoint
      D.site D.base D.base_mem ⟨Y, hY.1⟩ hintY
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY hintY)
      (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) L d.V hV e hecompat hebij s hreg
      _ (hv.trans hy)
    have hc : flatChartReading D sY hY f hflat hintY L s d hV e hecompat hebij u =
        algebraMap ((chartScheme d.U).presheaf.stalk u)
          (FractionRing ((chartScheme d.U).presheaf.stalk u))
          ((((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).stalkMap u).hom r0) := by
      rw [flatChartReading, hr0eq, IsLocalization.map_eq]
    rw [Ring.ordTotalFracInt_congr _ _ ((hr0.map _).map _) hc,
      Ring.ordTotalFracInt_algebraMap_of_isUnit (hr0.map _)]
  · -- `ξ` lies over the generic point of a prime divisor `Zy` of `Y`
    have hylt : D.deltaValue sY y < n := by
      have hspec := (isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hintY).specializes
        (Set.mem_univ y)
      have hlt := dY.strictAnti_specializes hspec (Ne.symm hy)
      rwa [hdY, hdY, deltaValue_genericPoint_eq_of_deltaDimensionClosed D sY hY hintY hn] at hlt
    have hyd : D.deltaValue sY y = n - 1 := by omega
    have htfae := isPrimeDivisor_tfae_of_isIntegralSpace D sY hY hintY dY hdY hn Zy
    obtain ⟨P, hP⟩ := (htfae.out 1 3).mpr (hZyd.trans hyd)
    have hPZ : P.toIntegralClosedSubspace D.site D.base D.base_mem = Zy :=
      IntegralClosedSubspace.ext hP
    have hPgen : P.genericPoint D.site D.base D.base_mem Y = y := by
      rw [P.genericPoint_eq_ambientGenericPoint D hY.1, hPZ, hZyamb]
    have hvP : chartSchemeToPoints D.site D.base D.base_mem Y d.V
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u) =
        P.genericPoint D.site D.base D.base_mem Y := hv.trans hPgen.symm
    have : IsNoetherianRing ((chartScheme d.V).presheaf.stalk
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u)) := by
      have := isLocallyNoetherian_chartScheme D.site D.base D.base_mem
        (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) hYN d.V
      infer_instance
    have : Ring.KrullDimLE 1 ((chartScheme d.V).presheaf.stalk
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u)) :=
      P.krullDimLE_chartStalk D.site D.base D.base_mem hY.1 hYdec d.V _ hvP
    -- the coefficient of `div_ℒ(s)` at `Zy` is the order of the chart ratio at `v`
    have hcV := (isUnit_chartRatio_of_isRegularMeromorphicSection D.site D.base D.base_mem
      ⟨Y, hY.1⟩
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY hintY)
      (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) L d.V hV e hecompat hebij s
      hreg).map (chartPointMeromorphicMap D.site D.base D.base_mem ⟨Y, hY.1⟩ d.V hV
        (isFractionRing_meromorphicFunctionSheaf_obj D.site D.base D.base_mem ⟨Y, hY.1⟩
          (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY
            hintY)
          (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) d.V hV)
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u))
    have h1 := sectionWeilDivisor_apply_toIntegralClosedSubspace D sY hY hintY L hL hn s hs P
    have h2 := P.orderOfVanishingSection_canonicalLocalRatio_eq_ordTotalFracInt D.site D.base
      D.base_mem hYdec hintY hYN
      (localRingDimension_eq_zero_of_mem_weaklyAssociatedPointsOfSpace_of_isGood D sY hY hintY)
      (hasLocallyFiniteIrreducibleComponents_of_isGood D sY hY) L
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hL) s hreg d.V hV e
      hecompat hebij _ hvP hcV
    have hαZy : α.1 Zy = Ring.ordTotalFracInt ((chartScheme d.V).presheaf.stalk
        (((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g).base u)) _ hcV := by
      rw [← hPZ]
      exact h1.trans h2
    -- the multiplicity of `Z` in `f^*[Zy]` is the colength of `𝔪_v 𝒪_{U, u}`
    have hpre := isClosedSubspace_preimage_integralClosedSubspace D sX hX sY hY f Zy
    have hsubZ : subspacePointSet D.site D.base D.base_mem X Z.subspace ⊆
        Set.range (pointsMap D.site D.base D.base_mem _ (Zy.subspace.preimage f).ι) := by
      show _ ⊆ subspacePointSet D.site D.base D.base_mem X (Zy.subspace.preimage f)
      rw [subspacePointSet_preimage]
      refine ((Z.isGenericPoint_ambientGenericPoint D.site D.base D.base_mem
        hX.1).mem_closed_set_iff
        ((isClosed_range_pointsMap_integralClosedSubspace D.site D.base D.base_mem hY.1
          Zy).preimage (continuous_pointsMap D.site D.base D.base_mem f))).mp ?_
      show y ∈ subspacePointSet D.site D.base D.base_mem Y Zy.subspace
      rw [hZypts]
      exact subset_closure rfl
    obtain ⟨Vs, hVs⟩ := IntegralClosedSubspace.exists_pushforward_eq D.site D.base D.base_mem
      hX.1 hpre.1 (D.isDecentSpace_of_isGood sX hX)
      (isDecentSpace_of_isClosedSubspace D.site D.base D.base_mem
        (D.isDecentSpace_of_isGood sX hX) hpre) hpre.2 Z hsubZ
    have hVsamb : pointsMap D.site D.base D.base_mem _ (Zy.subspace.preimage f).ι
        (Vs.ambientGenericPoint D.site D.base D.base_mem) = ξ := by
      rw [← IntegralClosedSubspace.ambientGenericPoint_pushforward D.site D.base D.base_mem hX.1
        hpre.1 (D.isDecentSpace_of_isGood sX hX) hpre.2 Vs, hVs]
    have hmult := flatPullbackMult_eq_toNat_length_chartStalk D sX hX sY hY f hbase r hflat hr Zy
      Vs (by
        show deltaDimension D sX (IntegralClosedSubspace.pushforward D.site D.base D.base_mem
          hX.1 hpre.1 (D.isDecentSpace_of_isGood sX hX) hpre.2 Vs) = _
        rw [hVs, hZ, hZyd, hyd]
        ring)
      (canonicalGeometricPoint D.site D.base D.base_mem _
        (Vs.ambientGenericPoint D.site D.base D.base_mem))
      (canonicalGeometricPoint_image _ _ _ _ _) (by rw [hVsamb, hZyamb]) d.U d.V d.g d.comm u
      (by rw [geometricPointMap_image, canonicalGeometricPoint_image, hVsamb, hu])
    have hVsZ : closedSubspaceComponentImage D sX hX (Zy.subspace.preimage f) hpre Vs = Z := hVs
    rw [hVsZ] at hmult
    rw [hαZy, hmult]
    have : Flat ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g) :=
      hflat d.U.1.left d.V.1.left d.U.1.hom d.V.1.hom d.g d.U.2 d.V.2 d.comm.symm
    have key := Ring.ordTotalFracInt_map_of_flatHom_toNat
      (Q' := FractionRing ((chartScheme d.U).presheaf.stalk u)) inferInstance
      (AlgebraicGeometry.Flat.stalkMap ((BigFppfOver.toScheme D.site D.base D.base_mem).map d.g) u)
      _ hcV
    refine Eq.trans ?_ key.symm
    ring

end AlgebraicGeometry.Space

end
