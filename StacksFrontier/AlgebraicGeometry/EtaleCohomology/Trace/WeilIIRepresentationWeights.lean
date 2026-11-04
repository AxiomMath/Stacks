module

public import Mathlib.Analysis.Complex.Cardinality
public import Mathlib.SetTheory.Cardinal.Continuum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDevissage

/-!
# The weight bound of Tag 03VH from the weight bound for lisse sheaves

[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) bounds the weights of `π_X^*` on
`Hⁱ_c(X_k̄, ℱ_ρ)` for a representation `ρ` satisfying the conclusions of Deligne's conjecture:
every eigenvalue `α` is algebraic with `|α| = q ^ (w / 2)` for an integer `w ≤ i`, for every
embedding of `ℚ̄_ℓ` into `ℂ`.  The sheaf `ℱ_ρ` is lisse, pointwise `ι`-mixed of weights `≤ 0`
(its Frobenius eigenvalues have absolute value `1`) and `ι`-realizable (with witness the sheaf of
the contragredient `ρ^∨`), for every `ι`; so the weight bound for lisse sheaves
(`Stacks.EtaleCohomology.LAdicSheaf.SatisfiesWeightBound`) for every `ι` gives the bound of 03VH
for every `ι`, and the bound for all `ι` together makes the eigenvalues algebraic
(`Stacks.EtaleCohomology.isCharpolyMixedOfWeightLE_of_forall_isCharpolyNormMixedOfWeightLE`,
which needs `#ℚ_ℓ ≤ #ℂ`).

## Main results

* `Stacks.EtaleCohomology.mk_padic_le_mk_complex`: `#ℚ_ℓ ≤ #ℂ`.
* `LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_satisfiesWeightBound`: if `X`
  satisfies the weight bound for lisse sheaves for every `ι`, the eigenvalues of `π_X^*` on
  `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` are algebraic of absolute value `q ^ (w / 2)` with `w ≤ i` along `ι`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

/-- **`ℚ_ℓ` has at most the cardinality of the continuum**: it is a quotient of a set of
sequences of rationals. -/
theorem mk_padic_le_mk_complex (ℓ : ℕ) [Fact ℓ.Prime] : Cardinal.mk ℚ_[ℓ] ≤ Cardinal.mk ℂ := by
  calc Cardinal.mk ℚ_[ℓ] ≤ Cardinal.mk (PadicSeq ℓ) :=
        Cardinal.mk_le_of_surjective (f := Padic.mk) fun x =>
          Quotient.inductionOn x fun s => ⟨s, rfl⟩
    _ ≤ Cardinal.mk (ℕ → ℚ) := Cardinal.mk_le_of_injective Subtype.val_injective
    _ = Cardinal.mk ℂ := by
      rw [← Cardinal.power_def, Cardinal.mk_complex, Cardinal.mk_eq_aleph0 ℚ,
        Cardinal.mk_eq_aleph0 ℕ, Cardinal.aleph0_power_aleph0]

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
  {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q}

/-- **The weight bound of Tag 03VH from the weight bound for lisse sheaves.**  Let `X` be
connected, separated of finite type over `k` with `q = p ^ n` elements, and `ρ` a continuous
representation of `π₁(X, x̄)` satisfying the conclusions of Deligne's conjecture for every
`ι`.  If `X` satisfies the weight bound for lisse sheaves for every `ι`, then for every `i` and
every `ι` the eigenvalues of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` are algebraic, and of absolute
value `q ^ (w / 2)` with `w ≤ i` along `ι`. -/
theorem LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_satisfiesWeightBound
    (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ)
    (hS : ∀ ι : ℚ_[ℓ] →+* ℂ, LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i)] (ι : ℚ_[ℓ] →+* ℂ) :
    IsCharpolyMixedOfWeightLE (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom := by
  refine isCharpolyMixedOfWeightLE_of_forall_isCharpolyNormMixedOfWeightLE
    (mk_padic_le_mk_complex ℓ) (Nat.one_le_iff_ne_zero.2
      (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)) (fun ι' => ?_) ι
  have h := hS ι' j (LAdicSheaf.representationSheaf B X x ρ hρ) 0
    (LAdicSheaf.representationSheaf_isLisse B X x ρ hρ)
    (LAdicSheaf.isPointwiseMixedOfWeightLE_representationSheaf_of_hasDeligneConclusions B X ℓ f x ρ
      hρ (p ^ q) (hD ι'))
    (LAdicSheaf.isIotaRealizable_representationSheaf B X ℓ f x ρ hρ
      ((hD ι').isIotaRealizable hρ)) i
  rwa [zero_add] at h

end Stacks.EtaleCohomology
