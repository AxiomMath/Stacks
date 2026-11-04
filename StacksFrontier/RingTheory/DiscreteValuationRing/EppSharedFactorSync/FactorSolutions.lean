module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppDegreePrimeBridge
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionSquare
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppFactorPackage
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppKuhlmannCompleteCase
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppPerfectResidueComplete
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppWildFamilyPreparation

/-!
# Per-factor packages and the per-factor obligation over one shared base extension

The `hfactors` payload with `S i = integralClosure B (E i)`, the factor-level square, the
per-factor obligation `FactorSolutions` and its tame, carried and mixed discharges, and the
route `isWeakSolution_of_forall_factorSolutions`.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe uA uB uK uL

section Sync

variable (A : Type uA) (B : Type uB) (L : Type uL) (K₁ K₂ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra B L] [Algebra K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [Module.Finite K₁ K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    [IsDiscreteValuationRing.IsExtension A R]
    {n : ℕ} (E : Fin n → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, Algebra B (E i)] [∀ i, Algebra R (E i)] [∀ i, Algebra A (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, IsScalarTower R K₁ (E i)]
    [∀ i, IsScalarTower A B (E i)] [∀ i, IsScalarTower A R (E i)]
    [∀ i, FiniteDimensional L (E i)] [∀ i, FaithfulSMul R (E i)]

include A L in
/-- **The combiner's `hfactors` payload, with the per-factor ring chosen canonically.**

Taking `S i = integralClosure B (E i)`, every one of the thirteen instances and both squares that
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages` quantifies over is
supplied here; the hypothesis is the per-factor weak solutions alone, over a `K₂` fixed before the
factors are examined.

The five instances that are not immediate come from `EppFactorPackage`:
`isDiscreteValuationRing_integralClosure_factor` (henselianness),
`isFractionRing_integralClosure_factor`, `algebraIntegralClosureBase`,
`isScalarTower_base_integralClosure_factor` and `isExtension_base_integralClosure_factor`, the
last of which is the only non-formal one. -/
theorem exists_reducedFactorPackages :
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
      isFractionRing_integralClosure_factor B L (E i)
    letI : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
      isScalarTower_base_integralClosure_factor A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    (∀ i, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL uK, uK,
      max uL uK, uK, max uL uK}
        R (integralClosure B (E i)) K₁ (E i) K₂, D.IsWeakSolution) →
    ∃ (S : Fin n → Type (max uL uK)) (_ : ∀ i, CommRing (S i)) (_ : ∀ i, IsDomain (S i))
      (_ : ∀ i, IsDiscreteValuationRing (S i)) (_ : ∀ i, Algebra R (S i))
      (_ : ∀ i, IsDiscreteValuationRing.IsExtension R (S i))
      (_ : ∀ i, Algebra B (S i)) (_ : ∀ i, Algebra.IsIntegral B (S i))
      (_ : ∀ i, Algebra R (E i)) (_ : ∀ i, Algebra (S i) (E i))
      (_ : ∀ i, IsFractionRing (S i) (E i))
      (_ : ∀ i, IsScalarTower R (S i) (E i)) (_ : ∀ i, IsScalarTower R K₁ (E i)),
      (∀ i b, algebraMap L (E i) (algebraMap B L b) =
          algebraMap (S i) (E i) (algebraMap B (S i) b)) ∧
        (∀ i a, algebraMap B (S i) (algebraMap A B a) =
          algebraMap R (S i) (algebraMap A R a)) ∧
        ∀ i, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL uK,
          uK, max uL uK, uK, max uL uK}
          R (S i) K₁ (E i) K₂, D.IsWeakSolution := by
  intro hsol
  exact ⟨fun i => integralClosure B (E i), fun _ => inferInstance, fun _ => inferInstance,
    fun i => isDiscreteValuationRing_integralClosure_factor B L (E i),
    fun i => algebraIntegralClosureBase A B R (E i),
    fun i => isExtension_base_integralClosure_factor A B R L (E i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    fun i => isFractionRing_integralClosure_factor B L (E i),
    fun i => isScalarTower_base_integralClosure_factor A B R (E i),
    fun _ => inferInstance,
    fun i b => algebraMap_integralClosure_factor_eq_of_tower B L (E i) b,
    fun i a => algebraMap_integralClosureBase_eq A B R (E i) a,
    hsol⟩

end Sync

/-! ### The factor-level square -/

section FactorSquare

variable (A : Type uA) (K : Type uK) (L : Type uL) (K₁ : Type uK) [CommRing A] [Field K] [Field L]
  [Field K₁]
    [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra K L] [Algebra K K₁]
    [IsScalarTower A K L] [IsScalarTower A K K₁]
    {n : ℕ} (E : Fin n → Type (max uL uK)) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]

include K in
/-- **The two routes from `A` into a conjugate factor agree.**

`A → L → E i` and `A → K₁ → E i` are the same map.  Both `L` and `K₁` reach the factor through
the decomposition, and in the tensor product the images of `A` under the two inclusions already
agree, because `includeLeft` and `includeRight` are `K`-algebra maps and `A` acts through `K` on
both sides.  Projecting along `decomp` at the index `i` and using the two compatibility equations
turns that into the displayed equality.

This is the factor-level analogue of the `hA` hypothesis that
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages` takes at `K₂`, and it is
what `exists_reducedFactorPackages` needs in order to be fed the combiner's own data: of the
structures over `A`, `B` and `R` that its hypotheses use, every other one is a composite of what
`hfactors` supplies. -/
theorem algebraMap_reducedFactor_base_eq
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i = algebraMap K₁ (E i) x)
    (i : Fin n) (a : A) :
    algebraMap L (E i) (algebraMap A L a) = algebraMap K₁ (E i) (algebraMap A K₁ a) := by
  have hxy : (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁))
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁)
          (algebraMap K L (algebraMap A K a)))) =
      (Ideal.Quotient.mk (nilradical (L ⊗[K] K₁))
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁)
          (algebraMap K K₁ (algebraMap A K a)))) := by
    congr 1
    rw [AlgHom.commutes, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply A K L a, IsScalarTower.algebraMap_apply A K K₁ a,
    ← hleft i _, ← hright i _, hxy]

end FactorSquare

section FactorSquareTower

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ : Type uK) [CommRing A]
  [CommRing B] [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    {n : ℕ} (E : Fin n → Type (max uL uK)) [∀ i, Field (E i)] [∀ i, Algebra K (E i)]
    [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)]

include K L in
/-- **The same square, read through `B`.**

`A → B → E i` and `A → K₁ → E i` agree.  This is the form `exists_reducedFactorPackages` consumes
— its `IsScalarTower A R (E i)` hypothesis is exactly this equality once the structure maps
`A → E i` and `R → E i` are taken to be the composites through `B` and through `K₁` — and it
follows from `algebraMap_reducedFactor_base_eq` by pushing `A → B → L` down to `A → L`. -/
theorem algebraMap_reducedFactor_base_eq_of_tower
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i = algebraMap K₁ (E i) x)
    (i : Fin n) (a : A) :
    algebraMap B (E i) (algebraMap A B a) = algebraMap K₁ (E i) (algebraMap A K₁ a) := by
  rw [IsScalarTower.algebraMap_apply B L (E i), ← IsScalarTower.algebraMap_apply A B L]
  exact algebraMap_reducedFactor_base_eq A K L K₁ E decomp hleft hright i a

/-- The two routes `A → B → E i` and `A → K₁ → E i` agreeing makes `E i` a scalar tower over
`A → R`. -/
private theorem isScalarTower_of_reducedFactor_square
    (R : Type uK) [CommRing R] [Algebra A R] [Algebra R K₁] [IsScalarTower A R K₁]
    [∀ i, Algebra A (E i)] [∀ i, IsScalarTower A B (E i)] [∀ i, Algebra R (E i)]
    [∀ i, IsScalarTower R K₁ (E i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x)
    (i : Fin n) : IsScalarTower A R (E i) :=
  .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A B (E i),
      algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a,
      IsScalarTower.algebraMap_apply R K₁ (E i), ← IsScalarTower.algebraMap_apply A R K₁]

end FactorSquareTower

/-! ### The per-factor obligation, in the context the combiner's data determines -/

section Obligation

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ K₂ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁] [Field K₂]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra K₁ K₂]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [Module.Finite K₁ K₂]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra R K₂] [IsScalarTower R K₁ K₂]
    [IsScalarTower A R K₁]
    {n : ℕ} (E : Fin n → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra K₁ (E i)]
    [∀ i, Module.Finite L (E i)]

/-- **The per-factor weak-solution obligation of the all-factor route.**

Given a decomposition of `(L ⊗[K] K₁) ⧸ nilradical` into conjugate factors, this is the
proposition that every factor's integral closure over `B` admits a weak solution over one shared
`K₂` — the thing a caller must produce to run
`IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages`, and the only thing left
after `exists_reducedFactorPackages`.

It is packaged as a definition because stating it requires fixing eight structures that the
combiner's own data determines but does not hand over: the composites `B → L → E i`,
`A → B → E i` and `R → K₁ → E i` with their three towers, the faithfulness of `R` on the factor,
and `IsScalarTower A R (E i)`, which is the factor-level square
`algebraMap_reducedFactor_base_eq_of_tower`.  Writing those out at each use would bury the
mathematical content; naming them once does not.

No factor is distinguished: the quantifier runs over every index. -/
def FactorSolutions
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x) : Prop :=
  letI : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, FaithfulSMul R (E i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
      ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
  letI : ∀ i, IsScalarTower A R (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
        (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
  letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  letI : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  letI : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  ∀ i, ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK, max uL uK, uK,
    max uL uK, uK, max uL uK}
    R (integralClosure B (E i)) K₁ (E i) K₂, D.IsWeakSolution

/-- **The per-factor obligation when the complete perfect-residue combiner is available.**

Unlike `FactorSolutions`, the extension field is allowed to depend on the factor.  This is sound
precisely in the setting where the base ring `R` is complete with perfect residue field: the
factorwise weak solutions can then be embedded into one finite overfield and remain weak
solutions, by
`IsDiscreteValuationRing.exists_finite_extension_forall_isWeakSolution_of_perfect_residueField`.

Naming this version prevents the equal-characteristic proof from imposing an unnecessary and
substantially stronger synchronization requirement on its constant and nonconstant Laurent
branches.  The all-conjugates requirement is unchanged: every factor still has to be solved. -/
def IndividualFactorSolutions
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x) : Prop :=
  letI : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  letI : ∀ i, FaithfulSMul R (E i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
      ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
  letI : ∀ i, IsScalarTower A R (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
        (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
  letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  letI : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  letI : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  ∀ i, ∃ (F : Type uK) (_ : Field F) (_ : Algebra K₁ F) (_ : Algebra R F)
      (_ : IsScalarTower R K₁ F) (_ : Module.Finite K₁ F),
    ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uK, max uL uK, uK,
        max uL uK, uK, max uL uK, uK, max uL uK}
      R (integralClosure B (E i)) K₁ (E i) F, D.IsWeakSolution

include A B K L K₁ K₂ R in
/-- **The tame case of the per-factor obligation, over the prescribed `K₂`.**

If every factor's extension `R → integralClosure B (E i)` is tamely ramified and the prescribed
`K₂` has local ramification index over `R` divisible by each factor's, then `FactorSolutions`
holds.

This is a *re-derivation* at each factor, not a transport:
`isWeakSolution_of_tame_of_ramificationIndex_dvd` establishes the weak-solution property over
whatever extension it is handed, so one `K₂` fixed in advance serves every factor at once.
Taking `K₂ = K₁(π₁^{1/e})` with `e` the least common multiple of the factors' ramification
indices makes the divisibility hypothesis automatic, which is how a caller discharges it.

Completeness of `R` and of `B` is what makes each factor's integral closure a complete discrete
valuation ring with `E i` as its fraction field (`integralClosure_isCompleteDVR`), which is what
Abhyankar's lemma consumes.

This does **not** settle `FactorSolutions`: the wild case — residue characteristic `p` dividing a
factor's ramification index — is exactly what Epp's theorem is for, and the degree-`p` endgame
would have to be re-derived against a prescribed `K₂` in the same way Abhyankar's lemma now is.
That is the open problem. -/
theorem factorSolutions_of_tame
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x) :
    letI : ∀ i, Algebra B (E i) := fun i =>
      ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
    letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra A (E i) := fun i =>
      ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
    letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra R (E i) := fun i =>
      ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
    letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, FaithfulSMul R (E i) := fun i =>
      (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
        ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
    letI : ∀ i, IsScalarTower A R (E i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    (∀ i, (ringChar (IsLocalRing.ResidueField R) = 0 ∨
        Nat.Coprime (ringChar (IsLocalRing.ResidueField R))
            (IsDiscreteValuationRing.ramificationIndex R (integralClosure B (E i))) ∧
          Algebra.IsSeparableExtension (IsLocalRing.ResidueField R)
            (IsLocalRing.ResidueField (integralClosure B (E i)))) ∧
        ∀ q : Ideal (integralClosure R K₂), q.IsMaximal →
          IsDiscreteValuationRing.ramificationIndex R (integralClosure B (E i)) ∣
            q.ramificationIdx R) →
    FactorSolutions A B K L K₁ K₂ R E decomp hleft hright := by
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (E i) := fun i => FaithfulSMul.trans R K₁ (E i)
  let : ∀ i, IsScalarTower A R (E i) := fun i =>
    isScalarTower_of_reducedFactor_square A B K L K₁ E R decomp hleft hright i
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  let : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  let : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  let : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  intro htame
  refine fun i => ?_
  obtain ⟨hdvrS, hextS, hfinS, hcompS, hfracS⟩ :=
    IsDiscreteValuationRing.integralClosure_isCompleteDVR B L (E i)
  let := hdvrS
  let := hcompS
  let := hfracS
  obtain ⟨D⟩ := IsDiscreteValuationRing.nonempty_integralClosureBaseChange R
    (integralClosure B (E i)) K₁ (E i) K₂
  exact ⟨D, IsDiscreteValuationRing.isWeakSolution_of_tame_of_ramificationIndex_dvd R
    (integralClosure B (E i)) K₁ (E i) K₂ (htame i).1 D (htame i).2⟩

include A B K L K₁ K₂ R in
/-- **The carried case of the per-factor obligation, over the prescribed `K₂`.**

If the prescribed `K₂ / K₁` is totally ramified with respect to `R` and separable, then every
factor whose extension `R → integralClosure B (E i)` is *already* weakly unramified is solved by
that same `K₂`.

This is the step that lets a layer recursion **carry** its already-terminal members instead of
solving them separately, which is what keeps one `K₂` serving the whole conjugate family.  The
distinction matters: a recursion that partitions the family into the members it still has to split
and the members it has already finished, solves the two parts independently, and then reconciles
the two extensions, is performing exactly the amalgamation the all-factor route forbids — weak
solutions do not survive arbitrary finite enlargement of the base, and a common overfield of
totally ramified extensions may not be assumed to preserve total ramification.  Here nothing is
reconciled: `htot` is a property of `K₂ / K₁` alone, checked once and not per factor, and `hunram`
is a *check* of each factor against that fixed datum rather than a choice made for it.

The engine is
`IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`,
the package-level form of Tag 09ER, which takes the extension as input.  Note what is absent
relative to `factorSolutions_of_tame`: **no completeness**.  That theorem needs
`IsAdicComplete` on `R` and on `B` to make each factor's integral closure a complete discrete
valuation ring for Abhyankar's lemma; total ramification is what makes the tensor product a field
and preserves ramification index one here, so henselianness of `B` — already in the ambient
context, and all that `isDiscreteValuationRing_integralClosure_factor` needs — suffices.

Together with `factorSolutions_of_tame` this fixes the pattern every case of `FactorSolutions`
should follow: take `K₂` as given and state a condition on it.  Stated that way the cases compose
over one `K₂` with nothing to merge, which is why the remaining wild case must be stated
prescribed-extension too. -/
theorem factorSolutions_of_isWeaklyUnramified
    [Algebra.IsSeparable K₁ K₂]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x)
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo R K₁ K₂) :
    letI : ∀ i, Algebra B (E i) := fun i =>
      ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
    letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra A (E i) := fun i =>
      ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
    letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra R (E i) := fun i =>
      ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
    letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, FaithfulSMul R (E i) := fun i =>
      (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
        ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
    letI : ∀ i, IsScalarTower A R (E i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    (∀ i, IsDiscreteValuationRing.IsWeaklyUnramified R (integralClosure B (E i))) →
    FactorSolutions A B K L K₁ K₂ R E decomp hleft hright := by
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (E i) := fun i => FaithfulSMul.trans R K₁ (E i)
  let : ∀ i, IsScalarTower A R (E i) := fun i =>
    isScalarTower_of_reducedFactor_square A B K L K₁ E R decomp hleft hright i
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  let : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  let : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  let : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  intro hunram
  refine fun i => ?_
  exact IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified
    R (integralClosure B (E i)) K₁ (E i) K₂ (hunram i) htot

include A B K L K₁ K₂ R in
/-- **A mixed family, carried and solved over one prescribed `K₂`.**

Each conjugate factor is required to be *either* already weakly unramified over `R` *or* tamely
ramified with `K₂`'s local ramification index divisible by its own — chosen per factor, in any
combination — and one prescribed `K₂` then discharges `FactorSolutions` for all of them together.

This is the first genuine instance of the discipline the layer recursion needs, so it is worth
saying exactly what it does and does not do.

**What it does.** A recursion over the layers of a finite extension meets, at every level, a
family in which some members are finished and some are not.  The tempting move is to solve the
finished ones over one extension, the unfinished ones over another, and reconcile; that
reconciliation is the amalgamation the all-factor route forbids, since weak solutions do not
survive arbitrary finite enlargement of the base and a common overfield of totally ramified
extensions may not be assumed to preserve total ramification.  Here nothing is reconciled.  `K₂`
is a parameter; `htot` constrains `K₂ / K₁` alone and is checked once; the per-factor hypothesis is
a *check* of each factor against that fixed `K₂`, and the two branches consume the same `K₂`
through two different prescribed-extension engines — Tag 09ER in package form
(`IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`) for a
carried factor, Abhyankar's lemma in prescribed form
(`IsDiscreteValuationRing.isWeakSolution_of_tame_of_ramificationIndex_dvd`) for a tame one.  The
disjunction is resolved inside the `∀ i`, which is what makes mixing free: no factor is
distinguished and no two branches ever have to be combined.

**What it does not do.** It does not close layer assembly.  The wild case — residue characteristic
`p` dividing a factor's ramification index, which is what Epp's theorem is for — is in neither
branch, and the degree-`p` layer that would supply it
`IsDiscreteValuationRing.exists_isGalois_totallyRamified_isWeakSolution_of_charP_of_perfectCore_le`
still *produces* its extension instead of accepting a prescribed one, so it yields a pointwise
statement that cannot be mixed in this way.  Restating it prescribed-extension is the open
obligation.

Completeness appears only because of the tame branch: Abhyankar's lemma wants each factor's
integral closure to be a complete discrete valuation ring.  The carried branch needs none, which
is why `factorSolutions_of_isWeaklyUnramified` is stated separately and without it. -/
theorem factorSolutions_of_forall_isWeaklyUnramified_or_tame
    [Algebra.IsSeparable K₁ K₂]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x)
    (htot : IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo R K₁ K₂) :
    letI : ∀ i, Algebra B (E i) := fun i =>
      ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
    letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra A (E i) := fun i =>
      ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
    letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra R (E i) := fun i =>
      ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
    letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, FaithfulSMul R (E i) := fun i =>
      (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
        ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
    letI : ∀ i, IsScalarTower A R (E i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    (∀ i, IsDiscreteValuationRing.IsWeaklyUnramified R (integralClosure B (E i)) ∨
        ((ringChar (IsLocalRing.ResidueField R) = 0 ∨
            Nat.Coprime (ringChar (IsLocalRing.ResidueField R))
                (IsDiscreteValuationRing.ramificationIndex R (integralClosure B (E i))) ∧
              Algebra.IsSeparableExtension (IsLocalRing.ResidueField R)
                (IsLocalRing.ResidueField (integralClosure B (E i)))) ∧
          ∀ q : Ideal (integralClosure R K₂), q.IsMaximal →
            IsDiscreteValuationRing.ramificationIndex R (integralClosure B (E i)) ∣
              q.ramificationIdx R)) →
    FactorSolutions A B K L K₁ K₂ R E decomp hleft hright := by
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (E i) := fun i => FaithfulSMul.trans R K₁ (E i)
  let : ∀ i, IsScalarTower A R (E i) := fun i =>
    isScalarTower_of_reducedFactor_square A B K L K₁ E R decomp hleft hright i
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  let : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  let : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  let : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  intro hcase
  refine fun i => ?_
  rcases hcase i with hunram | htame
  · exact IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified
      R (integralClosure B (E i)) K₁ (E i) K₂ hunram htot
  obtain ⟨hdvrS, hextS, hfinS, hcompS, hfracS⟩ :=
    IsDiscreteValuationRing.integralClosure_isCompleteDVR B L (E i)
  let := hdvrS
  let := hcompS
  let := hfracS
  obtain ⟨D⟩ := IsDiscreteValuationRing.nonempty_integralClosureBaseChange R
    (integralClosure B (E i)) K₁ (E i) K₂
  exact ⟨D, IsDiscreteValuationRing.isWeakSolution_of_tame_of_ramificationIndex_dvd R
    (integralClosure B (E i)) K₁ (E i) K₂ htame.1 D htame.2⟩

include A B K L K₁ K₂ R in
/-- **The all-factor route, end to end, modulo the synchronization.**

If every conjugate factor of every decomposition of `(L ⊗[K] K₁) ⧸ nilradical` admits a weak
solution over one shared `K₂` — that is, if `FactorSolutions` holds — then the caller's own base
change `D₂` over `K₂` is a weak solution for `A → B`.

This is `IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages` with its
`hfactors` hypothesis discharged: `exists_reducedFactorPackages` supplies the thirteen instances
and two squares, the eight structures the combiner determines but does not hand over are built
here, and the one of those that is not a composite — `IsScalarTower A R (E i)` — is the factor
square `algebraMap_reducedFactor_base_eq_of_tower`.

So the entire all-factor route now reduces to `FactorSolutions`, and nothing else. Producing it
is the remaining mathematics: the degree-`p` layer applied at every factor, with the absorbing
base changes of
`Stacks.EppTheorem.EppCondition.exists_finiteEtale_forall_exists_pow_eq_algebraMap` synchronized
  onto a
single `K₂` and iterated against Kuhlmann's decreasing wild-support measure. That is *not* proved
here, and until it is there is no unconditional Tag 09F9 and nothing in this file is tagged. -/
theorem isWeakSolution_of_forall_factorSolutions
    [Algebra K K₂] [Algebra A K₂] [IsScalarTower K K₁ K₂] [IsScalarTower A K K₂]
    [Module.Finite K K₁] [Module.Finite K K₂] [IsFractionRing A K]
    (D₂ : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK, max uL uK, uK, max
      uL uK} A B K L K₂)
    (hA : ∀ a : A, algebraMap A K₂ a = algebraMap R K₂ (algebraMap A R a))
    (hsol : ∀ (m : ℕ) (F : Fin m → Type (max uL uK)) (_ : ∀ i, Field (F i))
      (_ : ∀ i, Algebra K (F i)) (_ : ∀ i, Algebra L (F i)) (_ : ∀ i, Algebra K₁ (F i))
      (_ : ∀ i, IsScalarTower K L (F i)) (_ : ∀ i, IsScalarTower K K₁ (F i))
      (_ : ∀ i, Module.Finite L (F i))
      (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, F i)
      (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i = algebraMap L (F i) l)
      (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
        algebraMap K₁ (F i) x),
      FactorSolutions A B K L K₁ K₂ R F decomp hleft hright) :
    D₂.IsWeakSolution := by
  refine IsDiscreteValuationRing.isWeakSolution_of_forall_reducedFactorPackages
    A B K L K₁ K₂ R D₂ hA ?_
  intro m F instFieldF instKF instLF instK₁F instKLF instKK₁F instFinF decomp hleft hright
  let := instFieldF
  let := instKF
  let := instLF
  let := instK₁F
  let := instKLF
  let := instKK₁F
  let := instFinF
  let : ∀ i, Algebra B (F i) := fun i =>
    ((algebraMap L (F i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (F i) := fun i =>
    ((algebraMap B (F i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (F i) := fun i =>
    ((algebraMap K₁ (F i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (F i) := fun i => FaithfulSMul.trans R K₁ (F i)
  let : ∀ i, IsScalarTower A R (F i) := fun i =>
    isScalarTower_of_reducedFactor_square A B K L K₁ F R decomp hleft hright i
  exact exists_reducedFactorPackages A B L K₁ K₂ R F
    (hsol m F instFieldF instKF instLF instK₁F instKLF instKK₁F instFinF decomp hleft hright)

include A B K L K₁ R in
/-- **The all-factor route with factorwise extension fields.**

When `R` and the factor rings are complete and `ResidueField R` is perfect, every conjugate
factor may first be solved over its own finite extension of `K₁`.  The perfect-residue combiner
then replaces those fields by one finite common overfield while preserving all weak solutions.

This is the appropriate interface for the complete case of Epp's theorem.  It retains the sound
all-conjugates correction to Tag 09ET, but avoids asking the two Laurent branches to manufacture
the same extension before their solutions have been constructed. -/
theorem exists_finite_extension_isWeakSolution_of_forall_individualFactorSolutions
    [Module.Finite K K₁] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [PerfectField (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (hA : ∀ a : A, algebraMap K K₁ (algebraMap A K a) =
      algebraMap R K₁ (algebraMap A R a))
    (hsol : ∀ (m : ℕ) (F : Fin m → Type (max uL uK)) (_ : ∀ i, Field (F i))
      (_ : ∀ i, Algebra K (F i)) (_ : ∀ i, Algebra L (F i))
      (_ : ∀ i, Algebra K₁ (F i)) (_ : ∀ i, IsScalarTower K L (F i))
      (_ : ∀ i, IsScalarTower K K₁ (F i)) (_ : ∀ i, Module.Finite L (F i))
      (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, F i)
      (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
        algebraMap L (F i) l)
      (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
          ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
        algebraMap K₁ (F i) x),
      IndividualFactorSolutions A B K L K₁ R F decomp hleft hright) :
    ∃ (F : Type uK) (_ : Field F) (_ : Algebra K F) (_ : Algebra A F)
      (_ : IsScalarTower A K F) (_ : Module.Finite K F),
      ∃ D : IsDiscreteValuationRing.IntegralClosureBaseChange.{uA, uB, uK, uL, uK,
          max uL uK, uK, max uL uK} A B K L F,
        D.IsWeakSolution := by
  refine
    IsDiscreteValuationRing.exists_finite_extension_isWeakSolution_of_forall_reducedFactorSolutions
    A B K L K₁ R hA ?_
  intro m F instFieldF instKF instLF instK₁F instKLF instKK₁F instFinF decomp hleft hright
  let := instFieldF
  let := instKF
  let := instLF
  let := instK₁F
  let := instKLF
  let := instKK₁F
  let := instFinF
  let : ∀ i, Algebra B (F i) := fun i =>
    ((algebraMap L (F i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (F i) := fun i =>
    ((algebraMap B (F i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (F i) := fun i =>
    ((algebraMap K₁ (F i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (F i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (F i) := fun i => FaithfulSMul.trans R K₁ (F i)
  let : ∀ i, IsScalarTower A R (F i) := fun i =>
    isScalarTower_of_reducedFactor_square A B K L K₁ F R decomp hleft hright i
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (F i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (F i)
  let : ∀ i, Algebra R (integralClosure B (F i)) := fun i =>
    algebraIntegralClosureBase A B R (F i)
  let : ∀ i, IsFractionRing (integralClosure B (F i)) (F i) := fun i =>
    isFractionRing_integralClosure_factor B L (F i)
  let : ∀ i, IsScalarTower R (integralClosure B (F i)) (F i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (F i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (F i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (F i)
  have hcomplete : ∀ i, IsAdicComplete
      (IsLocalRing.maximalIdeal (integralClosure B (F i))) (integralClosure B (F i)) := by
    intro i
    obtain ⟨_, _, _, hcomp, _⟩ :=
      IsDiscreteValuationRing.integralClosure_isCompleteDVR B L (F i)
    exact hcomp
  refine ⟨fun i => integralClosure B (F i), fun _ => inferInstance, fun _ => inferInstance,
    fun i => isDiscreteValuationRing_integralClosure_factor B L (F i),
    fun i => algebraIntegralClosureBase A B R (F i),
    fun i => isExtension_base_integralClosure_factor A B R L (F i),
    fun _ => inferInstance, fun _ => inferInstance, fun _ => inferInstance,
    fun _ => inferInstance,
    fun i => isFractionRing_integralClosure_factor B L (F i),
    fun i => isScalarTower_base_integralClosure_factor A B R (F i),
    fun _ => inferInstance, hcomplete,
    fun i b => algebraMap_integralClosure_factor_eq_of_tower B L (F i) b,
    fun i a => algebraMap_integralClosureBase_eq A B R (F i) a, ?_⟩
  exact hsol m F instFieldF instKF instLF instK₁F instKLF instKK₁F instFinF
    decomp hleft hright

end Obligation

end Stacks.EppTheorem

end
