module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIDimensionOneGoodOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.WeilIIRepresentationWeights
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension

/-!
# The induction on the dimension in the weight bound of Weil II

The weight bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne,
Weil II 3.3.1) is proved by induction on the dimension: the statement `S(n)`
(`Stacks.EtaleCohomology.LAdicSheaf.WeightBoundInDimension`) asserts the weight bound for every
scheme of dimension at most `n` over every finite field. It holds for `n = 1`
(`Stacks.EtaleCohomology.LAdicSheaf.weightBoundInDimension_one`, from the curve case on opens of
the affine line). A scheme of finite type over a field has finite dimension, so the step
`S(n) → S(n + 1)` for `n ≥ 1` (fibration by curves and the Leray spectral sequence) gives the
weight bound on every scheme
(`Stacks.EtaleCohomology.LAdicSheaf.satisfiesWeightBound_of_weightBoundInDimension_succ`), and so
the bound of Tag 03VH for the sheaves `ℱ_ρ` (in the namespace `Stacks.EtaleCohomology`,
`LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_weightBoundInDimension_succ`).

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.WeightBoundInDimension`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
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

/-- **The weight bound of Weil II in dimension at most `n`** (`S(n)`): for every finite field
`k` with `q = p ^ m` elements, `p ≠ ℓ`, every algebraic closure `k̄` of `k`, every
`ι : ℚ_ℓ →+* ℂ` and every scheme `X` of dimension at most `n`, separated of finite type over `k`,
the weight bound `Stacks.EtaleCohomology.LAdicSheaf.SatisfiesWeightBound` holds on `X`. -/
def LAdicSheaf.WeightBoundInDimension (n : ℕ) : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q),
    ℓ ≠ p → ∀ (ι : ℚ_[ℓ] →+* ℂ) (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
      [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f], topologicalKrullDim X.1 ≤ n →
      LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f

variable {B ℓ}

/-- **`S(1)`**: the weight bound in dimension at most one, from the curve case on opens of the
affine line. -/
theorem LAdicSheaf.weightBoundInDimension_one (hcurve : WeilIICurveBoundOpenAffineLine.{u}) :
    LAdicSheaf.WeightBoundInDimension B ℓ 1 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hℓ _ X _ f _ _ _ hdim =>
    LAdicSheaf.satisfiesWeightBound_of_topologicalKrullDim_le_one hcurve hℓ X f hdim

/-- **The weight bound on every scheme from the induction step.**  Given `S(n) → S(n + 1)` for
every `n ≥ 1`, the weight bound holds on every scheme separated of finite type over a finite
field, which has finite dimension. -/
theorem LAdicSheaf.satisfiesWeightBound_of_weightBoundInDimension_succ
    (hcurve : WeilIICurveBoundOpenAffineLine.{u})
    (hstep : ∀ n : ℕ, 1 ≤ n → LAdicSheaf.WeightBoundInDimension B ℓ n →
      LAdicSheaf.WeightBoundInDimension B ℓ (n + 1))
    {k : Type u} [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
    (hℓ : ℓ ≠ p) (ι : ℚ_[ℓ] →+* ℂ) (X : B.Scheme) [IsNoetherian X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] :
    LAdicSheaf.SatisfiesWeightBound B ℓ kbar p q hcard ι X f := by
  have hS : ∀ m : ℕ, LAdicSheaf.WeightBoundInDimension B ℓ (m + 1) := by
    intro m
    induction m with
    | zero => exact LAdicSheaf.weightBoundInDimension_one hcurve
    | succ m ih => exact hstep (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) ih
  have : CompactSpace X.1 := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨n, hn⟩ :=
    exists_natCast_le_of_ne_top (topologicalKrullDim_ne_top_of_locallyOfFiniteType k f)
  exact hS n k kbar p q hcard hℓ ι X f (hn.trans (by exact_mod_cast Nat.le_succ n))

/-- **Tag 03VH from the induction step.**  For `X` connected, separated of finite type over `k`
with `q = p ^ m` elements, `ℓ ≠ p`, and `ρ` a continuous representation of `π₁(X, x̄)` satisfying
the conclusions of Deligne's conjecture, the eigenvalues of `π_X^*` on `Hⁱ_c(X_k̄, ℱ_ρ ⊗ ℚ_ℓ)` are
algebraic numbers of absolute value `q ^ (w / 2)` with `w ≤ i` along every `ι`, given the curve
case on opens of the affine line and the induction step `S(n) → S(n + 1)`. -/
theorem LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_weightBoundInDimension_succ
    (hcurve : WeilIICurveBoundOpenAffineLine.{u})
    (hstep : ∀ n : ℕ, 1 ≤ n → LAdicSheaf.WeightBoundInDimension B ℓ n →
      LAdicSheaf.WeightBoundInDimension B ℓ (n + 1))
    {k : Type u} [Field k] [Fintype k] {kbar : Type u} [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] {p q : ℕ} [Fact p.Prime] [CharP k p] {hcard : Fintype.card k = p ^ q}
    (hℓ : ℓ ≠ p) (X : B.Scheme) [IsNoetherian X.1] [ConnectedSpace X.1] (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (x : GeometricPoint X.1) {r : ℕ} (ρ : EtaleFundamentalGroup X.1 x →* GL (Fin r) ℚ_[ℓ])
    (hρ : Continuous ρ)
    (hD : ∀ ι : ℚ_[ℓ] →+* ℂ, HasDeligneConclusions (geometricFrobeniusFamily f x) p ι ρ) (i : ℤ)
    [FiniteDimensional ℚ_[ℓ] (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j
      kbar (LAdicSheaf.representationSheaf B X x ρ hρ) i)] (ι : ℚ_[ℓ] →+* ℂ) :
    IsCharpolyMixedOfWeightLE (p ^ q) ι i
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard
        (LAdicSheaf.representationSheaf B X x ρ hρ) i).hom :=
  LAdicSheaf.isCharpolyMixedOfWeightLE_representationSheaf_of_satisfiesWeightBound X f j x ρ hρ hD
    (fun ι' => LAdicSheaf.satisfiesWeightBound_of_weightBoundInDimension_succ hcurve hstep kbar p q
      hcard hℓ ι' X f) i ι

end Stacks.EtaleCohomology
