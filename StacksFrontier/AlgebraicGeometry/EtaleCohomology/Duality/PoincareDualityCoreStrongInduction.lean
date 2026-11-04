module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityCoreDimZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyPointClassProof

/-!
# Poincaré duality on a dense open, by strong induction on the dimension

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`.
`Stacks.EtaleCohomology.PoincareDualityCore ℓ k` is duality at `j_! Λ_{W₀}` on some dense open
`W₀` of every smooth irreducible `W` of every relative dimension `e`, for good traces; write
`Stacks.EtaleCohomology.PoincareDualityCoreAt ℓ k e` for the statement in one dimension `e`.
The induction on the dimension
(`Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTraceAux`) turns the statements in
the dimensions `≤ d` into Poincaré duality at `j_! Λ_W` itself, for every smooth irreducible `W`
of dimension `≤ d` and every injective trace
(`Stacks.EtaleCohomology.unitPoincareDualityUpTo_of_poincareDualityCoreAt`): the induction only
passes to strata of smaller dimension, and every injective trace is good
(`Stacks.EtaleCohomology.isGoodTraceAux_of_injective`, from local purity and the computation of
the top cohomology `Stacks.EtaleCohomology.topCohomologyPointClass`).

So `PoincareDualityCore ℓ k` follows from its case `e = 0`
(`Stacks.EtaleCohomology.exists_dense_isDualityPerfect_of_smoothOfRelativeDimension_zero`) and
from the *fibration step* `Stacks.EtaleCohomology.PoincareDualityFibrationStep ℓ k`: Poincaré
duality at `Λ` in all dimensions `≤ d` gives the dense-open statement in dimension `d + 1`
(in the proof, on an elementary fibration over a smooth variety of dimension `d`). This is
`Stacks.EtaleCohomology.poincareDualityCore_of_fibrationStep`, part of the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.PoincareDualityCoreAt`.
* `Stacks.EtaleCohomology.UnitPoincareDualityUpTo`.
* `Stacks.EtaleCohomology.PoincareDualityFibrationStep`.

## Main results

* `Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTraceAux_of_le`.
* `Stacks.EtaleCohomology.unitPoincareDualityUpTo_of_poincareDualityCoreAt`.
* `Stacks.EtaleCohomology.poincareDualityCore_of_fibrationStep`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize isClosedImmersion_restrictOpen_closedSpaceι
  preservesFiniteColimits_restrictOpen_closedSpaceι

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]

/-- **Poincaré duality on a dense open, in relative dimension `e`**: the statement of
`Stacks.EtaleCohomology.PoincareDualityCore` for one relative dimension `e`. For every smooth
irreducible `W` of relative dimension `e` over `k` with noetherian underlying space, every
compactification `j : W → X̄` of dimension at most `e` and every good trace `t` on
`H^{2e}_c(W, ℤ/ℓ)`, duality holds at `j_! Λ` of the constant sheaf on some dense open `W₀ ⊆ W`,
with `Ext^q_X̄(j_! Λ_{W₀}, j_! Λ_W) = 0` for `q > 2e`. -/
def PoincareDualityCoreAt (e : ℕ) : Prop :=
  ∀ (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
    ∀ (m : ℕ) (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ), e ≤ m → IsGoodTraceAux ℓ k m e f jc t →
    ∃ W₀ : W.Opens, Dense (W₀ : Set W) ∧
      Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
            (unitSheaf (X := W) ℓ))) ∧
      ∀ q, 2 * e < q → Subsingleton (Ext ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
        jc.immersion).obj ((etaleModuleExtensionByZeroOfRestriction.{u, 0} (ZMod ℓ) W₀.ι).obj
          (unitSheaf (X := W) ℓ)))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) q)

/-- `PoincareDualityCore` is `PoincareDualityCoreAt` in every relative dimension. -/
theorem poincareDualityCore_iff : PoincareDualityCore ℓ k ↔ ∀ e, PoincareDualityCoreAt ℓ k e :=
  Iff.rfl

/-- **Poincaré duality at `Λ` in relative dimensions at most `d`, for injective traces**: for
every smooth irreducible `W` of relative dimension `e ≤ d` over `k` with noetherian underlying
space, every compactification `j : W → X̄` of dimension at most `e` and every injective trace `t`
on `H^{2e}_c(W, ℤ/ℓ)`, duality holds at `j_! Λ_W` for `D = j_! Λ_W` and `t`, and
`Ext^q_X̄(j_! Λ_W, j_! Λ_W) = H^q(W, Λ) = 0` for `q > 2e`. -/
def UnitPoincareDualityUpTo (d : ℕ) : Prop :=
  ∀ (e : ℕ), e ≤ d → ∀ (W : Scheme.{u}) (f : W ⟶ Spec (.of k)) [SmoothOfRelativeDimension e f]
    [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
    (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
    ∀ (t : Ext (unitSheaf (X := jc.space) ℓ)
      ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) →+ ZMod ℓ), Function.Injective t →
    Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) ∧
      ∀ q, 2 * e < q → Subsingleton (Ext
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
          (unitSheaf (X := W) ℓ)) q)

/-- **The fibration step of Poincaré duality**: Poincaré duality at `Λ` in all relative
dimensions `≤ d` (`Stacks.EtaleCohomology.UnitPoincareDualityUpTo`) gives duality on a dense open
in relative dimension `d + 1` (`Stacks.EtaleCohomology.PoincareDualityCoreAt`). In the proof the
dense open is an elementary fibration over a smooth variety of dimension `d`. -/
def PoincareDualityFibrationStep : Prop :=
  ∀ d : ℕ, UnitPoincareDualityUpTo ℓ k d → PoincareDualityCoreAt ℓ k (d + 1)

variable {k} [IsAlgClosed k]

/-- **Poincaré duality on smooth varieties by induction on the dimension, in dimensions at most
`E`**: the induction `Stacks.EtaleCohomology.isDualityPerfect_unitSheaf_of_isGoodTraceAux` uses
the dense-open statement only in the dimension of `W` and below, so the dense-open statements in
the dimensions `≤ E` give duality at `j_! Λ_W` for every `W` of dimension `≤ E`, for good traces
with fuel `m ≥ e`. -/
theorem isDualityPerfect_unitSheaf_of_isGoodTraceAux_of_le (hpurity : LocalPurity ℓ k) (E : ℕ)
    (hcore : ∀ e, e ≤ E → PoincareDualityCoreAt ℓ k e) :
    ∀ (m e : ℕ), e ≤ E → ∀ (W : Scheme.{u}) (f : W ⟶ Spec (.of k))
      [SmoothOfRelativeDimension e f] [TopologicalSpace.NoetherianSpace W] [IrreducibleSpace W]
      (jc : CompactificationOf (Over.mk f)), topologicalKrullDim jc.space ≤ e →
      ∀ (t : Ext (unitSheaf (X := jc.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) →+ ZMod ℓ), e ≤ m → IsGoodTraceAux ℓ k m e f jc t →
      Ext.IsDualityPerfect (unitSheaf (X := jc.space) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          (2 * e) t ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) ∧
        ∀ q, 2 * e < q → Subsingleton (Ext
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj (unitSheaf (X := W) ℓ))
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jc.immersion).obj
            (unitSheaf (X := W) ℓ)) q) := by
  intro m
  refine Nat.rec ?_ (fun m ih => ?_) m
  all_goals
    intro e heE W f _ _ _ jc hdim t hem ht
    obtain ⟨W₀, hW₀, h₀⟩ := hcore e heE W f jc hdim _ t hem ht
    refine isDualityPerfect_of_dense_open_of_smooth f jc (unitSheaf ℓ) t W₀ hW₀ hpurity
      (fun M => subsingleton_ext_unitSheaf_of_proper jc.toBase e hdim _ _ (by omega)) h₀ ?_
    intro N T n _ i _ _ e' c hc hc0
  · change e ≤ 0 at hem
    omega
  intro _ _ γ hγ
  have : TopologicalSpace.NoetherianSpace T := (i ≫ n).isEmbedding.isInducing.noetherianSpace
  have hdimT := topologicalKrullDim_restrictClosed_space_le f jc n i e'
  have hgood := ht.2 N T n i e' c hc hc0 γ hγ
  obtain ⟨hPD, hCD⟩ := ih e' (by omega) T (i ≫ n ≫ f) ((jc.restrictOpen n).restrictClosed i)
    hdimT _ (by omega) hgood
  let uS := etaleModuleExtensionByZero.{u, 0} (ZMod ℓ)
    ((jc.restrictOpen n).closedImmersion i).toImage
  let eG := uS.mapIso (unitSheafRestrictionIdInverseImageIso ℓ (i ≫ n))
  exact ⟨fun q hq => subsingleton_ext_unitSheaf_of_proper
      ((jc.restrictOpen n).restrictClosed i).toBase e' hdimT _ q hq,
    Ext.isDualityPerfect_of_iso eG.symm hPD,
    fun q hq => Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source eG.symm q (hCD q hq)⟩

/-- **Poincaré duality at `Λ` in dimensions at most `d` from the dense-open statements**: for
`ℓ` invertible in `k`, the dense-open statements `PoincareDualityCoreAt ℓ k e` for `e ≤ d` give
Poincaré duality at `j_! Λ_W` for every smooth irreducible `W` of dimension `≤ d` and every
injective trace, since every injective trace is good
(`Stacks.EtaleCohomology.isGoodTraceAux_of_injective`). -/
theorem unitPoincareDualityUpTo_of_poincareDualityCoreAt (hℓ : IsUnit (ℓ : k)) (d : ℕ)
    (hcore : ∀ e, e ≤ d → PoincareDualityCoreAt ℓ k e) : UnitPoincareDualityUpTo ℓ k d := by
  intro e he W f _ _ _ jc hdim t ht
  exact isDualityPerfect_unitSheaf_of_isGoodTraceAux_of_le ℓ (Purity.localPurity (k := k) ℓ hℓ) d
    hcore e e he W f jc hdim t le_rfl
    (isGoodTraceAux_of_injective hℓ (topCohomologyPointClass ℓ k hℓ) e e W f jc t ht)

/-- **Duality on a dense open in relative dimension zero, for good traces**: the case `e = 0` of
`Stacks.EtaleCohomology.PoincareDualityCore`
(`Stacks.EtaleCohomology.exists_dense_isDualityPerfect_of_smoothOfRelativeDimension_zero`; a good
trace is injective). -/
theorem poincareDualityCoreAt_zero : PoincareDualityCoreAt ℓ k 0 := by
  intro W f _ _ _ jc _ m t _ ht
  refine exists_dense_isDualityPerfect_of_smoothOfRelativeDimension_zero ℓ f jc t ?_
  cases m with
  | zero => exact ht
  | succ m => exact ht.1

/-- **Poincaré duality on a dense open, from the fibration step**: for `ℓ` invertible in `k`,
`Stacks.EtaleCohomology.PoincareDualityCore ℓ k` holds as soon as the fibration step
`Stacks.EtaleCohomology.PoincareDualityFibrationStep ℓ k` does, by strong induction on the
dimension: the case `e = 0` is `Stacks.EtaleCohomology.poincareDualityCoreAt_zero`, and in
dimension `d + 1` the dense-open statements in the dimensions `≤ d` give Poincaré duality at `Λ`
there (`Stacks.EtaleCohomology.unitPoincareDualityUpTo_of_poincareDualityCoreAt`), the input of
the step. -/
theorem poincareDualityCore_of_fibrationStep (hℓ : IsUnit (ℓ : k))
    (hstep : PoincareDualityFibrationStep ℓ k) : PoincareDualityCore ℓ k := by
  have h : ∀ n e, e ≤ n → PoincareDualityCoreAt ℓ k e := by
    intro n
    induction n with
    | zero =>
      intro e he
      obtain rfl : e = 0 := by omega
      exact poincareDualityCoreAt_zero ℓ
    | succ n ih =>
      intro e he
      rcases Nat.lt_or_ge e (n + 1) with h | h
      · exact ih e (by omega)
      · obtain rfl : e = n + 1 := by omega
        exact hstep n (unitPoincareDualityUpTo_of_poincareDualityCoreAt ℓ hℓ n ih)
  exact (poincareDualityCore_iff ℓ k).2 fun e => h e e le_rfl

end Stacks.EtaleCohomology

end
