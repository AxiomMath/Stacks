module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CohomologicalInterpretationLocal
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.IdempotentCoefficientReduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LisseStratumCharSeries
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RegularDescentTraceFormulaConclusion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDctfFinal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The cohomological interpretation of the L-function with finite coefficients

Let `X` be a separated scheme of finite type over a finite field `k`, `Λ` a finite commutative ring
of order prime to the characteristic of `k`, and `F` a constructible flat sheaf of `Λ`-modules on
`X_étale`. Then `X` has a compactification, and for every compactification, `RΓ_c(X_k̄, F)` is
perfect and

`L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹` in `Λ⟦T⟧`

([Stacks, Tag 03UZ]).

## Main results

* `Stacks.EtaleCohomology.lFunctionCharSeriesIdentity_of_regularDescentTraceFormula`: the identity
  of Tag 03UZ from the trace formula for the regular descent sheaves of Galois coverings.
* `Stacks.EtaleCohomology.lFunction_eq_inv_charSeries_compactSupport_of_traceFormula`: the full
  statement of Tag 03UZ (existence of a compactification, and the identity for every
  compactification) from the conclusion of the trace formula of Tag 03V3 for those sheaves.
* `Stacks.EtaleCohomology.lFunction_eq_inv_charSeries_compactSupport_of_isCtf_traceFormula`: the
  same from the trace formula of Tag 03V3 for `D_ctf` with the coefficients `ℤ/ℓ^M[H]`.
* `Stacks.EtaleCohomology.groupRingCtfTraceFormula`: the trace formula of Tag 03V3 with the
  coefficients `ℤ/ℓ^M[H]`.
* `Stacks.EtaleCohomology.lFunction_eq_inv_charSeries_compactSupport`: [Stacks, Tag 03UZ].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] [Fintype k]
  (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]

/-- **The identity of [Stacks, Tag 03UZ] from the trace formula for the regular descent sheaves.**
If the trace formula holds for the regular descent sheaf of every Galois covering of every
separated scheme of finite type over `k` with coefficients `ℤ/ℓ^M[H]`, then for every finite
commutative coefficient ring `Λ` of order invertible in `k`, every constructible flat `F` and every
compactification `j`, `RΓ_c(X_k̄, F)` is perfect and
`L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹`. -/
theorem lFunctionCharSeriesIdentity_of_regularDescentTraceFormula
    (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q)
    (h03 : ∀ (Z : Scheme.{u}) (_ : B.Contains Z) (fZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType fZ]
      [QuasiCompact fZ] [IsSeparated fZ] (J : CompactificationOf (Over.mk fZ)) (H : Type) [Group H]
      [Fintype H] (C : EtaleGaloisCovering Z H) (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ), ((ℓ : ℕ) : k) ≠ 0 →
      haveI : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
      RegularDescentTraceFormula fZ J kbar p q C ℓ M)
    (Λ : Type) [CommRing Λ] [Finite Λ]
    [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
    (hΛ : ((Nat.card Λ : ℕ) : k) ≠ 0)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    LFunctionCharSeriesIdentity B X Λ f kbar F hF j p q hcard := by
  refine lFunctionCharSeriesIdentity_of_isLocalRing B X f kbar j p q hcard
    (fun Λ' _ _ _ _ _ _ _ hΛ' F' hF' => ?_) Λ hΛ F hF
  refine lFunctionCharSeriesIdentity_of_lisse B X Λ' f kbar F' p q hcard hF'
    (fun Z g _ _ _ H _ _ C N _ _ ρ hNf hNp _ _ _ _ e hfin hproj J => ?_) j
  have := hNf
  have := hNp
  exact compactSupportCharSeriesInverts_of_galoisCovering B Z Λ' (smallEtalePullObj B g F') hfin
    hproj (B.inclusion.map g ≫ f) kbar p q hcard C N ρ e hΛ'
    (fun J' ℓ _ M hℓ => h03 Z.obj Z.property (B.inclusion.map g ≫ f) J' H C ℓ M hℓ) J

/-- **[Stacks, Tag 03UZ] from the trace formula.** Let `Λ` be a finite commutative ring of order
prime to the characteristic of `k` and `F` a constructible flat `Λ`-module on `X_étale`. Given the
conclusion of the trace formula of [Stacks, Tag 03V3] for the inverse images of the regular descent
sheaves of Galois coverings to the base changes `Z ×_k k'` (the hypothesis `htf`), `X` has a
compactification, and for every compactification `j` and every presentation `#k = p ^ q`,
`RΓ_c(X_k̄, F)` is perfect and `L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹` in `Λ⟦T⟧`. -/
theorem lFunction_eq_inv_charSeries_compactSupport_of_traceFormula
    (Λ : Type) [CommRing Λ] [Finite Λ]
    [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
    (hΛ : ((Nat.card Λ : ℕ) : k) ≠ 0)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F)
    (htf : ∀ (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p] (Z : Scheme.{u})
      (_ : B.Contains Z) (fZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType fZ] [QuasiCompact fZ]
      [IsSeparated fZ] (J : CompactificationOf (Over.mk fZ)) (H : Type) [Group H] [Fintype H]
      (C : EtaleGaloisCovering Z H) (ℓ : ℕ) [Fact ℓ.Prime] (M : ℕ), ((ℓ : ℕ) : k) ≠ 0 →
      RegularDescentTraceFormulaConclusion fZ J kbar p q C ℓ M) :
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
        (hcard : Fintype.card k = p ^ q),
        LFunctionCharSeriesIdentity B X Λ f kbar F hF j p q hcard := by
  refine ⟨nonempty_compactificationOf B X f, fun j p q _ _ hcard => ?_⟩
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  exact lFunctionCharSeriesIdentity_of_regularDescentTraceFormula B X f kbar j p q hcard
    (fun Z hZ fZ _ _ _ J H _ _ C ℓ _ M hℓ => regularDescentTraceFormula_of_traceFormula fZ J kbar p
      q C ℓ M (htf p q Z hZ fZ J H C ℓ M hℓ))
    Λ hΛ F hF

/-- **[Stacks, Tag 03UZ] from the trace formula for `D_ctf`.** The hypothesis `hTF` is the trace
formula of [Stacks, Tag 03V3] with the finite coefficient rings `ℤ/ℓ^M[H]` of order invertible in
the base field, over every finite field `k' ⊆ k̄`, for bounded below complexes in `D_ctf` on
separated schemes of finite type contained in `B`. -/
theorem lFunction_eq_inv_charSeries_compactSupport_of_isCtf_traceFormula
    [Algebra.IsAlgebraic k kbar] (Λ : Type) [CommRing Λ] [Finite Λ]
    [HasColimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ)]
    [∀ (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} Λ) (SmallEtale.topology B S.obj S.property)
        (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
    [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
      HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{u + 1} Λ)]
    (hΛ : ((Nat.card Λ : ℕ) : k) ≠ 0)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F)
    (hTF : ∀ (p : ℕ) [Fact p.Prime] [CharP kbar p] (ℓ M : ℕ) [Fact ℓ.Prime] (H : Type) [Group H]
      [Fintype H], GroupRingCtfTraceFormula B kbar p ℓ M H) :
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
        (hcard : Fintype.card k = p ^ q),
        LFunctionCharSeriesIdentity B X Λ f kbar F hF j p q hcard :=
  lFunction_eq_inv_charSeries_compactSupport_of_traceFormula B X f kbar Λ hΛ F hF
    (fun p q _ _ _ _ hZ fZ _ _ _ J H _ _ C ℓ _ M hℓ =>
      regularDescentTraceFormulaConclusion_of_isCtf B hZ fZ J kbar p q C ℓ M hℓ (hTF p ℓ M H))

/-- **The trace formula of [Stacks, Tag 03V3] with coefficients `ℤ/ℓ^M[H]`.** This is
`perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated` at the finite
ring `ℤ/ℓ^M[H]`, over every finite field `k' ⊆ k̄`. -/
theorem groupRingCtfTraceFormula (B : BigEtaleSite.{u}) (kbar : Type u) [Field kbar]
    [IsAlgClosed kbar] (p : ℕ) [Fact p.Prime] [CharP kbar p] (ℓ M : ℕ) [Fact ℓ.Prime] (H : Type)
    [Group H] [Fintype H] : GroupRingCtfTraceFormula B kbar p ℓ M H := by
  intro k' _ _ _ _ _ q' hcard hΛ X f _ _ _ _ J K hX hK
  exact perfectDerivedTrace_canonicalCompactSupportFrobenius_eq_sum_of_isCtf_of_isSeparated
    (Λ := MonoidAlgebra (ZMod (ℓ ^ M)) H) (kbar := kbar) (p := p) (q := q') (hcard := hcard)
    (B := B) hΛ f J K hX hK

attribute [local instance] SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **The cohomological interpretation of the L-function with finite coefficients.** Let `X` be a
separated scheme of finite type over a finite field `k`, `k̄` an algebraic closure of `k`, `Λ` a
finite commutative ring of order prime to the characteristic of `k`, and `F` a constructible flat
`Λ`-module on `X_étale`. Then `X` has a compactification, and for every compactification `j`
(through which `RΓ_c(X_k̄, -)` and `π_X^*` are computed) and every presentation `#k = p ^ q`,
`RΓ_c(X_k̄, F)` is perfect and `L(X, F) = det(1 - π_X^* T | RΓ_c(X_k̄, F))⁻¹` in `Λ⟦T⟧`. -/
@[stacks 03UZ, sga "4½ Fonctions_L 2.2" "Theorem 2.2 case a)"]
theorem lFunction_eq_inv_charSeries_compactSupport
    [Algebra.IsAlgebraic k kbar] (Λ : Type) [CommRing Λ] [Finite Λ]
    (hΛ : ((Nat.card Λ : ℕ) : k) ≠ 0)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ (j : CompactificationOf (Over.mk f)) (p q : ℕ) [Fact p.Prime] [CharP k p]
        (hcard : Fintype.card k = p ^ q),
        LFunctionCharSeriesIdentity B X Λ f kbar F hF j p q hcard :=
  lFunction_eq_inv_charSeries_compactSupport_of_isCtf_traceFormula B X f kbar Λ hΛ F hF
    (fun p _ _ ℓ M _ H _ _ => groupRingCtfTraceFormula B kbar p ℓ M H)

end Stacks.EtaleCohomology
