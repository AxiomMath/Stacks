module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaIsCtf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveLAdicLevelTraceFormula

/-!
# The trace formula at the finite levels of an ℓ-adic sheaf

Let `X` be a separated scheme of finite type over a finite field `k` and `F` an ℓ-adic sheaf on
`X`, with torsion-free model `F'`, for a prime `ℓ ≠ p = char k`. The levels `F'ₙ` are
constructible flat sheaves of `ℤ/ℓⁿ⁺¹`-modules, so the complexes `F'ₙ[0]` lie in
`D_ctf(X, ℤ/ℓⁿ⁺¹)` and the trace formula of [Stacks, Tag 03V3]
(`perfectDerivedTrace_compactSupportFrobenius_eq_sum_of_isCtf_of_properDirectImageCtfInput`)
applies: `Kₙ = RΓ_c(X_k̄, F'ₙ)` is perfect (item (1) of the proof of [Stacks, Tag 03V2]) and
`Tr(π_X^* | Kₙ) = ∑_{x ∈ X(k)} Tr(π_x | (F'ₙ)_x̄)` (item (3)), in the shape consumed by
`Stacks.EtaleCohomology.LAdicSheaf.traceFormula_of_levelTraceFormula`.

That `R π_*` preserves `D_ctf` along proper morphisms is the hypothesis `hctf`
(`Stacks.EtaleCohomology.ProperDirectImageCtfInput`, at the rings `ℤ/ℓⁿ⁺¹`).

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.isCtf_levelComplex_torsionFreeModel`.
* `Stacks.EtaleCohomology.LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex`.
* `Stacks.EtaleCohomology.LAdicSheaf.levelTraceFormula`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem CategoryTheory.FilteredDerived Stacks.Trace

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)
variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

local notation "model" F => LAdicSheaf.torsionFreeModel F (LAdicSheaf.torsionBound F)

/-- **The levels of the torsion-free model lie in `D_ctf`**: `F'ₙ[0]` is a bounded complex of
constructible flat sheaves of `ℤ/ℓⁿ⁺¹`-modules. -/
theorem LAdicSheaf.isCtf_levelComplex_torsionFreeModel (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (n : ℕ) :
    IsCtf B X (ZMod (ℓ ^ (n + 1)))
      (DerivedCategory.Q.obj (LAdicSheaf.levelComplex B X ℓ (model F) n).obj) := by
  let G := LAdicSheaf.etaleLevel B X ℓ (model F) n
  refine IsRepresentedByConstructibleFlatEtaleComplex.isCtf B (ZMod (ℓ ^ (n + 1)))
    ⟨(CochainComplex.singleFunctor _ 0).obj G, 0, 0, inferInstance, inferInstance,
      fun i => ?_, ⟨Iso.refl _⟩⟩
  by_cases hi : i = 0
  · subst hi
    exact (LAdicSheaf.isConstructibleFlatEtaleModule_etaleLevel_torsionFreeModel B X ℓ F n).of_iso
      B X _ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 G).symm
  · exact isConstructibleFlatEtaleModule_of_isZero B _ X
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 G i hi)

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

omit [Fintype k] in
/-- `#(ℤ/ℓⁿ⁺¹)` is invertible in `k` for `ℓ ≠ char k`. -/
theorem natCard_zmod_pow_ne_zero_of_ne_char (hℓp : ℓ ≠ p) (n : ℕ) :
    (Nat.card (ZMod (ℓ ^ (n + 1))) : k) ≠ 0 := by
  rw [Nat.card_zmod, Nat.cast_pow]
  refine pow_ne_zero _ ?_
  rw [Ne, CharP.cast_eq_zero_iff k p]
  intro hdvd
  exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 hdvd).symm

include hcard in
/-- **The complexes `Kₙ = RΓ_c(X_k̄, F'ₙ)` are perfect** (item (1) of the proof of
[Stacks, Tag 03V2]), by [Stacks, Tag 03V3] at the levels. -/
theorem LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex
    [Algebra.IsAlgebraic k kbar] (hℓp : ℓ ≠ p)
    (hctf : ∀ n : ℕ, ProperDirectImageCtfInput B (ZMod (ℓ ^ (n + 1))))
    (F : LAdicSheaf.{u, u + 1} B X ℓ) (n : ℕ) :
    StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))) := by
  let : Fintype (rationalPoints f) := @Fintype.ofFinite _ (finite_rationalPoints f)
  exact
    (perfectDerivedTrace_compactSupportFrobenius_eq_sum_of_isCtf_of_properDirectImageCtfInput
    (kbar := kbar) (p := p) (q := q) (hcard := hcard)
    (natCard_zmod_pow_ne_zero_of_ne_char ℓ p hℓp n) (hctf n) f j _ X.property
    (LAdicSheaf.isCtf_levelComplex_torsionFreeModel B X ℓ F n)).choose_spec.choose

/-- **The trace formula at the finite levels of an ℓ-adic sheaf** (item (3) of the proof of
[Stacks, Tag 03V2], from [Stacks, Tag 03V3]): for `ℓ ≠ p`, the trace of `π_X^*` on
`Kₙ = RΓ_c(X_k̄, F'ₙ)` is the sum over the rational points of the traces of the geometric
Frobenius on the stalks of `F'ₙ`. -/
theorem LAdicSheaf.levelTraceFormula [Algebra.IsAlgebraic k kbar] (hℓp : ℓ ≠ p)
    (hctf : ∀ n : ℕ, ProperDirectImageCtfInput B (ZMod (ℓ ^ (n + 1))))
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hP : ∀ n, StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      (compactSupportFrobeniusCohomology.{u, 0} (ZMod (ℓ ^ (n + 1))) f j kbar
        (LAdicSheaf.levelComplex B X ℓ (model F) n))))
    [Fintype (rationalPoints f)] (n : ℕ) :
    traceAtLevel (LAdicSheaf.geometricPerfectTower B X ℓ f j kbar p q hcard (model F)
        (LAdicSheaf.powExact_etaleLevel_torsionFreeModel B X ℓ F le_rfl) hP) n =
      ∑ y : rationalPoints f, commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))
        (perfectDerivedTrace (ZMod (ℓ ^ (n + 1))) ⟨_,
          LAdicSheaf.isPerfect_rationalPointStalkComplex_torsionFreeModel B X ℓ f kbar F n y⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} (ZMod (ℓ ^ (n + 1))) kbar p
            q hcard y.1 (LAdicSheaf.levelComplex B X ℓ (model F) n)))) := by
  obtain ⟨hKs, hperf, htr⟩ :=
    perfectDerivedTrace_compactSupportFrobenius_eq_sum_of_isCtf_of_properDirectImageCtfInput
      (kbar := kbar) (p := p) (q := q) (hcard := hcard)
      (natCard_zmod_pow_ne_zero_of_ne_char ℓ p hℓp n) (hctf n) f j _ X.property
      (LAdicSheaf.isCtf_levelComplex_torsionFreeModel B X ℓ F n)
  exact (congrArg (commutativeAdditiveCommutatorQuotientEval (ZMod (ℓ ^ (n + 1)))) htr).trans
    (map_sum _ _ _)

end Stacks.EtaleCohomology

end
