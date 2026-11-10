module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CodimensionCycleClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CohomologyOfPoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionInduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.BasePointChowIdentity
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.NonemptyScheme
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedOpenImmersionComposite
public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.GysinChernCharacter
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle class of the fundamental class, and nonvanishing of cohomology

Let `W` be data (D0)–(D3) of Section 45.9 (Tag 0FHA) over the actual category of smooth projective
schemes over `k`. This file proves the two clauses of the nonempty case of Stacks 0FHF: for every
smooth projective `X` over `k`, the cycle class of the fundamental class `[X] ∈ CH^0(X)` is the
unit of `H^0(X)`; and if `X` is nonempty and `F` has characteristic zero, then `1 ≠ 0` in
`H^0(X)`.

The proof of the first clause is the source's. The fundamental class is the pullback of
`[Spec k]` along the structure morphism `p : X ⟶ Spec k`, `[X] = p^![Spec k]`
(`Stacks.WeilCohomology.codimensionGysin_fundamentalClass_point`), so (C)(a) and `γ([Spec k]) = 1`
(Stacks 0FHE, `Stacks.WeilCohomology.WeilData.cycleClass_fundamentalClass_point`) give
`γ([X]) = p^*γ([Spec k]) = p^*1 = 1`.

For the second clause, the source chooses a closed point `x ∈ X` whose residue field is finite
separable over `k` (Varieties, Lemma 056U), and pushes the class of the point forward to
`Spec(k)`, where it becomes `[κ(x) : k] · [Spec(k)]` (Stacks 0AZ1). By (C)(b) and Stacks 0FHE the
cycle class of the point is carried by `p_*` to the nonzero scalar `[κ(x) : k]` of
`H^0(Spec k) = F`, so `H^*(X) ≠ 0`. Axiom (C)(b) concerns equidimensional schemes, so this is done
on the open and closed part of `X` of constant dimension containing `x`, which receives the
pullback `H^*(X) → H^*(X_d)`, a ring homomorphism.

## Main results

* `Stacks.WeilCohomology.WeilData.cycleClass_fundamentalClass`: `γ([X]) = 1` in `H^0(X)`.
* `Stacks.WeilCohomology.WeilData.nontrivial_of_isNonemptyEquidimensional`,
  `Stacks.WeilCohomology.WeilData.nontrivial_of_nonempty`: `H^*(X) ≠ 0` for `X` nonempty.

## References

* [Stacks Project, Tag 0FHF](https://stacks.math.columbia.edu/tag/0FHF)
* [Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

open SmoothProjectiveScheme

section PointClass

variable {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}

/-- The class in `CH^d(X)` of a zero cycle `β` on the part `X_d` of `X` of dimension `d`. -/
def codimensionClassOfZeroCycle (β : chowGroup (fieldChowSituation k) (partBase X.obj.hom d) 0) :
    codimensionChowGroup k X.obj.hom d :=
  Pi.single (M := fun e : ℕ ↦
      chowGroup (fieldChowSituation k) (partBase X.obj.hom e) ((e : ℤ) - d)) d
    (chowGroupDegreeEquiv _ _ (by ring) β)

/-- The component of `codimensionClassOfZeroCycle β` in degree `d` is `β`, regarded as a class in
`CH_{d - d}(X_d)`. -/
theorem codimensionClassOfZeroCycle_self
    (β : chowGroup (fieldChowSituation k) (partBase X.obj.hom d) 0) :
    codimensionClassOfZeroCycle β d = chowGroupDegreeEquiv _ _ (by ring) β :=
  Pi.single_eq_same (M := fun e : ℕ ↦
    chowGroup (fieldChowSituation k) (partBase X.obj.hom e) ((e : ℤ) - d)) d _

/-- The pushforward of a zero cycle to the point is its degree times `[Spec k]`, read in
`CH^0(Spec k)`: for `β ∈ CH_0(X_d)`, `p_*β = deg(β) · [Spec k]`. -/
theorem equidimensionalPushforward_codimensionClassOfZeroCycle
    (hδ : ∀ s : (fieldChowSituation k).S, (fieldChowSituation k).dimensionFunction s = 0)
    (s : (fieldChowSituation k).S)
    (β : chowGroup (fieldChowSituation k) (partBase X.obj.hom d) 0) :
    haveI := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
    equidimensionalPushforward (toPoint X) d 0 d 0 (by ring) (codimensionClassOfZeroCycle β) =
      chowDegree (fieldChowSituation k) hδ (partBase X.obj.hom d) s β •
        fundamentalClass (point k) := by
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  funext e'
  rcases eq_or_ne e' 0 with rfl | he
  · set n := chowDegree (fieldChowSituation k) hδ (partBase X.obj.hom d) s β
    have hu : ((dimPart X.obj.hom d).ι ≫ (toPoint X).hom.left) ≫ (point k).obj.hom =
        partBase X.obj.hom d := Category.comp_id _
    have : IsProper ((dimPart X.obj.hom d).ι ≫ (toPoint X).hom.left) :=
      show IsProper ((dimPart X.obj.hom d).ι ≫ X.obj.hom) from inferInstance
    have hfac := properPushforwardFactorsThroughRationalEquivalence_of_isProper
      (fieldChowSituation k) (partBase X.obj.hom d) (point k).obj.hom
      ((dimPart X.obj.hom d).ι ≫ (toPoint X).hom.left) hu 0
    have hP' : properChowPushforward (fieldChowSituation k) (partBase X.obj.hom d)
        (point k).obj.hom ((dimPart X.obj.hom d).ι ≫ (toPoint X).hom.left) hu 0 hfac β =
        n • fundamentalChowClass (fieldChowSituation k) (point k).obj.hom 0 :=
      eq_zsmul_fundamentalChowClass (fieldChowSituation k) hδ s _
    simp only [equidimensionalPushforward, AddMonoidHom.pi_apply,
      AddMonoidHom.coe_comp, Function.comp_apply, Pi.evalAddMonoidHom_apply,
      AddEquiv.coe_toAddMonoidHom, Pi.smul_apply, dite_true]
    rw [codimensionClassOfZeroCycle_self]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
    have h1 := properChowPushforward_heq_congr (fieldChowSituation k) (partBase X.obj.hom d)
      (point k).obj.hom ((dimPart X.obj.hom d).ι ≫ (toPoint X).hom.left) hu
      (by ring : (d : ℤ) - d = 0)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper (fieldChowSituation k)
        (partBase X.obj.hom d) (point k).obj.hom
        ((dimPart X.obj.hom d).ι ≫ (toPoint X).hom.left) hu ((d : ℤ) - d)) hfac
      (chowGroupDegreeEquiv (fieldChowSituation k) (partBase X.obj.hom d) (by ring) β) β
      (chowGroupDegreeEquiv_heq _ _ _ _)
    refine (chowGroupRestrict_heq_of_heq (fieldChowSituation k) (point k).obj.hom
      (partBase (point k).obj.hom 0) (dimPart (point k).obj.hom 0).ι rfl
      (by ring : (d : ℤ) - d = 0) _ _ (h1.trans (heq_of_eq hP'))).trans ?_
    rw [map_zsmul, chowGroupRestrict_fundamentalChowClass_of_isOpenImmersion]
    change _ ≍ n • chowGroupDegreeEquiv _ _ _ _
    rw [← map_zsmul]
    exact (chowGroupDegreeEquiv_heq _ _ _ _).symm
  · have := isEmpty_dimPart_of_ne (point k).obj.hom
      isNonemptyEquidimensional_point.relativeDimension he
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end PointClass

namespace WeilData

variable {F : Type w} [Field F] {W : WeilData k F}

/-- For every smooth projective scheme `X` over `k`, the cycle class of the fundamental class is
the unit: `γ([X]) = 1` in `H^0(X)`. -/
@[stacks 0FHF "the nonempty case, first clause γ([X]) = 1, on the actual category of smooth \
projective schemes over k with the actual CH^0(X) and Gysin map"]
theorem cycleClass_fundamentalClass (hBa : W.KunnethIsomorphism) (hCa : W.CycleClassPullback)
    (hCc : W.CycleClassMul) (hCd : W.CycleClassPoint)
    (X : (SmoothProjectiveScheme k).FullSubcategory) :
    W.cycleClass X 0 (fundamentalClass X) = W.unitTw X 0 0 rfl := by
  rw [← codimensionGysin_fundamentalClass_point (toPoint X), hCa,
    cycleClass_fundamentalClass_point hBa hCc hCd]
  refine (W.twCoord X _ _).injective (Subtype.ext ?_)
  rw [coe_twCoord_pullTw_unitTw]
  exact (W.coe_twCoord_unitTw X 0 0 rfl).symm

/-- If `X` is nonempty and equidimensional of dimension `d` and `F` has characteristic zero, then
`H^*(X) ≠ 0`. -/
@[stacks 0FHF "the nonempty case, second clause 1 ≠ 0 in H^0(X), for X equidimensional"]
theorem nontrivial_of_isNonemptyEquidimensional [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X : (SmoothProjectiveScheme k).FullSubcategory}
    {d : ℕ} (hX : IsNonemptyEquidimensional X d) : Nontrivial (W.H X) := by
  have hδ : ∀ s : (fieldChowSituation k).S, (fieldChowSituation k).dimensionFunction s = 0 :=
    fun _ ↦ rfl
  have := hX.nonempty
  obtain ⟨x, -, hxfin, -⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth X.obj.hom).nonempty
  have hxU : x ∈ dimPart X.obj.hom d := by
    rw [dimPart_self_eq_top X.obj.hom hX.relativeDimension]
    trivial
  obtain ⟨z, hz⟩ : x ∈ Set.range (dimPart X.obj.hom d).ι := by
    rwa [Scheme.Opens.range_ι]
  have hn : (partBase X.obj.hom d).residueDegree z ≠ 0 := by
    have h := residueDegree_isOpenImmersion_comp (dimPart X.obj.hom d).ι X.obj.hom z
    rw [hz] at h
    exact h.trans_ne (residueDegree_ne_zero_of_finite k X.obj.hom x hxfin)
  have hrd : relativeDimension (fieldChowSituation k).dimensionFunction
      (partBase X.obj.hom d) z = 0 :=
    relativeDimension_eq_zero_of_residueDegree_ne_zero (fieldChowSituation k).dimensionFunction
      hδ _ z hn
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : CycleGroup (fieldChowSituation k) (partBase X.obj.hom d) 0,
      β₀.1 = @Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _ z (1 : ℤ) :=
    ⟨⟨@Function.locallyFinsuppWithin.single _ _ ℤ (Classical.decEq _) _ z (1 : ℤ),
      @single_mem_cyclesOfDimension_zero (fieldChowSituation k) _ (Classical.decEq _)
        (partBase X.obj.hom d) _ z hrd⟩,
      rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : chowGroup (fieldChowSituation k) (partBase X.obj.hom d) 0,
      β = QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k)
        (partBase X.obj.hom d) 0) β₀ := ⟨_, rfl⟩
  have hdeg : chowDegree (fieldChowSituation k) hδ (partBase X.obj.hom d)
      ((partBase X.obj.hom d).base z) β = ((partBase X.obj.hom d).residueDegree z : ℤ) := by
    rw [hβ]
    exact (chowDegree_mk (fieldChowSituation k) hδ _ _ β₀).trans
      (cycleDegree_single (fieldChowSituation k) hδ _ z β₀ hβ₀)
  have hcalc := equidimensionalPushforward_codimensionClassOfZeroCycle hδ
    ((partBase X.obj.hom d).base z) β
  rw [hdeg] at hcalc
  have hpush := hC.pushforward (toPoint X) d 0 hX isNonemptyEquidimensional_point d 0 (by ring)
    (codimensionClassOfZeroCycle β)
  rw [hcalc, map_zsmul, cycleClass_fundamentalClass_point hB.kunnethIsomorphism hC.mul
    hC.point] at hpush
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have h0 : ∀ y : W.Tw X (2 * (d : ℤ)) d, y = 0 := by
    have : Subsingleton (W.grade X (2 * (d : ℤ))) :=
      ⟨fun a b ↦ Subtype.ext (Subsingleton.elim (a : W.H X) b)⟩
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
    | add y y' hy hy' => rw [hy, hy', add_zero]
  rw [h0 (W.cycleClass X d _), map_zero] at hpush
  have hcoord := congrArg (fun y ↦ (W.twCoord (point k) _ _ y : W.H (point k))) hpush
  simp only [map_zsmul, map_zero, ZeroMemClass.coe_zero] at hcoord
  have := nontrivial_point hC.point
  have hF : (((partBase X.obj.hom d).residueDegree z : ℤ) : F) = 0 := by
    apply (algebraMap F (W.H (point k))).injective
    rw [map_intCast, map_zero, ← zsmul_one, ← W.coe_twCoord_unitTw (point k) (2 * 0) 0 (by simp)]
    exact hcoord
  exact hn (by exact_mod_cast hF)

/-- If `X` is a nonempty smooth projective scheme over `k` and `F` has characteristic zero, then
`1 ≠ 0` in `H^0(X)`, i.e. `H^*(X)` is a nontrivial ring. -/
@[stacks 0FHF "the nonempty case, second clause: 1 ≠ 0 in H^0(X), on the actual category of \
smooth projective schemes over k"]
theorem nontrivial_of_nonempty [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) (X : (SmoothProjectiveScheme k).FullSubcategory)
    [Nonempty X.obj.left] : Nontrivial (W.H X) := by
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart X.obj.hom).exists_mem
    (Classical.arbitrary X.obj.left)
  let U := dimPart X.obj.hom d
  have hU : IsClopen (U : Set X.obj.left) := relativeDimensionOpen_isClopen _ _ d
  have hT : IsNonemptyEquidimensional (clopenObj X U hU) d :=
    ⟨⟨⟨_, hd⟩⟩, relativeDimension_partBase X.obj.hom d⟩
  have := nontrivial_of_isNonemptyEquidimensional hA hB hC hT
  let ι : clopenObj X U hU ⟶ X :=
    ObjectProperty.homMk (Over.homMk (U := (clopenObj X U hU).obj) (V := X.obj) U.ι rfl)
  exact (W.pull ι).toRingHom.domain_nontrivial

end WeilData

end Stacks.WeilCohomology

end
