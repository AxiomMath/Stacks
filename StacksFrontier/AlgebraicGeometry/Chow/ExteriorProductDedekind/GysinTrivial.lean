module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponentModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationData
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.CarrierAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Descent.TrivialOnOpen0BF3

/-!
# The Gysin map on cycles of a trivial normal bundle descends

Let `X` be locally of finite type over the base, `L` an invertible `𝒪_X`-module, `s ∈ Γ(X, L)`
and `i : D → X` the zero scheme of `s`, and assume `L|_D ≅ 𝒪_D`. Stacks 0B6Z attaches to these
data a map on cycles `i^* : Z_{k+1}(X) ⟶ Z_k(D)`
(`Stacks.Chow.gysinCycleMap`): the fundamental cycle of `W ∩ D` on an integral `W ⊄ D`, and `0`
on an integral `W ⊆ D`. This file proves that this map represents the Gysin homomorphism of
Stacks 02T8 on Chow groups. Consequently, by Stacks 02TO, `i^*` carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero.

## Main results

* `Stacks.Chow.firstChernComponentClass_eq_zero_of_isTrivial` — `c₁(L|_W) ∩ [W] = 0` when the
  restriction of `L` to the integral closed subscheme `W` is trivial.
* `Stacks.Chow.mk_gysinCycleMap` — the class of `i^* α` is the Gysin image of `α`.
* `Stacks.Chow.gysinCycleMap_mem_rationalEquivalences` — `i^*` preserves rational equivalence to
  zero.

## References

* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Stacks.Divisors

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **Stacks 02SP for a trivial restriction.** If the restriction of `L` to an integral closed
subscheme `W` of delta-dimension `k + 1` is trivial, then `c₁(L|_W) ∩ [W] = 0` in `A_k(W)`. -/
theorem firstChernComponentClass_eq_zero_of_isTrivial (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hL : AlgebraicGeometry.SheafOfModules.IsTrivial W.subscheme.sheaf.obj
      W.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback W.subschemeι).obj L)) :
    firstChernComponentClass C p k L W hW hDim = 0 := by
  have _ : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  set M : W.subscheme.Modules := (Scheme.Modules.pullback W.subschemeι).obj L
  set U : W.subscheme.Modules := SheafOfModules.unit W.subscheme.ringCatSheaf
  obtain ⟨e⟩ := hL
  let φ : U ⟶ M := e.inv
  have : IsIso φ := ⟨⟨e.hom, e.inv_hom_id, e.hom_inv_id⟩⟩
  let t : Γ(M, ⊤) := φ.val.app (op ⊤) (show Γ(U, ⊤) from (1 : Γ(W.subscheme, ⊤)))
  have ht : ∀ (y : W.subscheme) (hy : y ∈ (⊤ : W.subscheme.Opens)),
      IsStalkBasis M y (M.presheaf.germ ⊤ y hy t) := by
    intro y hy
    rw [← stalkLinearMap_germ U M φ ⊤ y hy]
    exact (isStalkBasis_germ_one (X := W.subscheme) ⊤ y trivial).mapStalkLinearMap U M φ y
  have hLt : ∀ x : W.subscheme, IsTrivializedNear M x := fun x ↦
    have := isInvertible_presheaf_modulePullback L W.subschemeι
    isTrivializedNear_of_isInvertible _ x
  have hne : M.presheaf.germ ⊤ (genericPoint W.subscheme) trivial t ≠ 0 := by
    intro h0
    have hb := ht (genericPoint W.subscheme) trivial
    rw [h0] at hb
    exact one_ne_zero (hb.injective
      (a₁ := (1 : W.subscheme.presheaf.stalk (genericPoint W.subscheme))) (a₂ := 0) (by simp))
  rw [firstChernComponentClass_eq_mk_of_ne_zero C p k L W hDim hne]
  have hzero : chernComponentCycle C (W.subschemeι ≫ p) hDim hLt
      (M.presheaf.germ ⊤ (genericPoint W.subscheme) trivial t) = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    change weilDivisorAlgebraicCycle (weilDivisorOfMeromorphicSection hLt _) z = 0
    rw [weilDivisorOfMeromorphicSection_eq_zero_of_isStalkBasis_germ hLt (U := ⊤)
      (fun _ ↦ trivial) ht]
    simp [weilDivisorAlgebraicCycle_apply, weilDivisorCoeff]
  rw [hzero]
  rfl

variable (s : Γ(L, ⊤))
  (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))

/-- **Stacks 0B6Z compared with Stacks 02T8.** When `L` is trivial on the zero scheme `D` of `s`,
the class of the Gysin map on cycles of Stacks 0B6Z is the Gysin homomorphism of Stacks 02T8. -/
theorem mk_gysinCycleMap (α : CycleGroup C p (k + 1)) :
    (QuotientAddGroup.mk (gysinCycleMap C p k L s htriv α) :
        chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k) =
      gysinHomomorphismOfInvertible C p k L s α := by
  classical
  set D := Stacks.Divisors.zeroScheme X L s
  set W : cycleSupportIndex α → X.IdealSheafData := fun x ↦ integralComponentAt x.1
  have hW : ∀ j, IsIntegral (W j).subscheme := fun x ↦ isIntegral_integralComponentAt x.1
  have hDim := schemeDeltaDimension_cycleSupportIndex α
  have hLocal := locallyFinite_support_integralComponentAt α
  obtain ⟨γ, hγ, hγval⟩ := isGysinHomomorphism_gysinHomomorphismOfInvertible C p k L s W hW
    hDim hLocal (fun x ↦ α.1 x.1) α (cycle_eq_finsum_primeCycles α)
  rw [hγ, eq_comm, ← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
  have hφval := isGysinCycleMap_gysinCycleMap C p k L s htriv W hW hDim hLocal
    (fun x ↦ α.1 x.1) α (cycle_eq_finsum_primeCycles α)
  set E : cycleSupportIndex α → Set D.subscheme :=
    fun j ↦ D.subschemeι.base ⁻¹' ((W j).support : Set X) with hE
  have hEloc : LocallyFinite E := hLocal.preimage_continuous D.subschemeι.continuous
  set u : cycleSupportIndex α → CycleGroup C (D.subschemeι ≫ p) k := fun j ↦
    α.1 j.1 • gysinComponentCycle C p k L s (firstChernComponentClass C p k L) (W j) (hW j)
      (hDim j) with hu
  set v : cycleSupportIndex α → CycleGroup C (D.subschemeι ≫ p) k := fun j ↦
    α.1 j.1 • gysinCycleMapComponent C p k L s (W j) (hW j) (hDim j) with hv
  have hsu : ∀ j, Function.support (u j).1 ⊆ E j := fun j ↦
    (Function.support_const_smul_subset _ _).trans
      (support_gysinComponentCycle_subset C p k L s (firstChernComponentClass C p k L) (W j)
        (hW j) (hDim j))
  have hsv : ∀ j, Function.support (v j).1 ⊆ E j := fun j ↦
    (Function.support_const_smul_subset _ _).trans
      (support_gysinCycleMapComponent_subset C p k L s (W j) (hW j) (hDim j))
  have hD' : ∀ j, IsRationallyEquivalentToZeroWithin C (D.subschemeι ≫ p) k (u j - v j)
      (E j) := by
    intro j
    by_cases hle : D ≤ W j
    · have htrivW : AlgebraicGeometry.SheafOfModules.IsTrivial (W j).subscheme.sheaf.obj
          (W j).subscheme.ringCatSheaf.property
          ((Scheme.Modules.pullback (W j).subschemeι).obj L) :=
        AlgebraicGeometry.SheafOfModules.isTrivial_modulePullback_scheme_of_comp
          (Scheme.IdealSheafData.inclusion hle) D.subschemeι (W j).subschemeι
          (Scheme.IdealSheafData.inclusion_subschemeι hle) htriv
      have hzero := firstChernComponentClass_eq_zero_of_isTrivial C p k L (W j) (hW j) (hDim j)
        htrivW
      have hout : Quotient.out (firstChernComponentClass C p k L (W j) (hW j) (hDim j)) ∈
          rationalEquivalences C ((W j).subschemeι ≫ p) k := by
        rwa [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
      have hpush := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
        ((W j).subschemeι ≫ p) (D.subschemeι ≫ p) (Scheme.IdealSheafData.inclusion hle)
        (by simp) k hout
      have hrange : Set.range (Scheme.IdealSheafData.inclusion hle).base ⊆ E j := by
        rintro y ⟨w, rfl⟩
        have hcomp : (Scheme.IdealSheafData.inclusion hle ≫ D.subschemeι).base w =
            (W j).subschemeι.base w := by rw [Scheme.IdealSheafData.inclusion_subschemeι]
        simp only [hE, Set.mem_preimage]
        rw [← Scheme.Hom.comp_apply, hcomp, ← (W j).range_subschemeι]
        exact ⟨w, rfl⟩
      refine isRationallyEquivalentToZeroWithin_zsmul C (D.subschemeι ≫ p) k
        (hpush.mono hrange) (α.1 j.1) fun y ↦ ?_
      simp only [hu, hv]
      rw [gysinComponentCycle_of_le C p k L s _ (W j) (hW j) (hDim j) hle,
        gysinCycleMapComponent_of_le C p k L s (W j) (hW j) (hDim j) hle]
      simp only [smul_zero, sub_zero]
      rfl
    · have h0 : u j - v j = 0 := by
        simp only [hu, hv]
        rw [gysinComponentCycle_of_not_le C p k L s _ (W j) (hW j) (hDim j) hle,
          gysinCycleMapComponent_of_not_le C p k L s (W j) (hW j) (hDim j) hle, sub_self]
      rw [h0]
      exact isRationallyEquivalentToZeroWithin_zero C (D.subschemeι ≫ p) k (E j)
  exact (isRationallyEquivalentToZeroWithin_sub_of_finsum C (D.subschemeι ≫ p) k E hEloc
    γ (gysinCycleMap C p k L s htriv α) u v hsu hsv (fun y ↦ by rw [hγval y]; rfl)
    (fun y ↦ by rw [hφval y]; rfl) hD').isRationallyEquivalentToZero

/-- **The Gysin map on cycles of a trivial normal bundle preserves rational equivalence.** If `L`
is trivial on the zero scheme of `s`, the Gysin map on cycles of Stacks 0B6Z carries a cycle
rationally equivalent to zero to a cycle rationally equivalent to zero. -/
theorem gysinCycleMap_mem_rationalEquivalences {α : CycleGroup C p (k + 1)}
    (hα : α ∈ rationalEquivalences C p (k + 1)) :
    gysinCycleMap C p k L s htriv α ∈
      rationalEquivalences C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k := by
  rw [← QuotientAddGroup.eq_zero_iff, mk_gysinCycleMap C p k L s htriv]
  exact gysinOfInvertibleFactorsThroughRationalEquivalence C p k L s α hα

end Stacks.Chow
