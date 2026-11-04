module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicLevelTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicLFunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The trace formula and the L-function of a `ℚ_ℓ`-sheaf in every dimension

Let `X` be a separated scheme of finite type over a finite field `k` with `p ^ q` elements, `k̄`
an algebraic closure of `k`, `ℓ ≠ p` a prime and `F` a `ℚ_ℓ`-sheaf on `X`.

* [Stacks, Tag 03V2]: the groups `Hⁱ_c(X_k̄, F)` are finite dimensional over `ℚ_ℓ`, nonzero only
  for `0 ≤ i ≤ 2 dim X`, and
  `∑_{x ∈ X(k)} Tr(π_x | F_x̄) = ∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ_c(X_k̄, F))`.
* [Stacks, Tag 03V0]: `L(X, F) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}`.

In both, `ℓ ≠ p` is the standing convention of the chapter ("`Λ` is killed by a power of a prime
`ℓ` and `ℓ ∈ k^*`", in Step 3 of the proof of Tag 03UG), and the statements are false for
`ℓ = p`: for `X = 𝔸¹_k` and `F = ℚ_p`, `Hⁱ_c(𝔸¹_k̄, ℤ/pⁿ) = 0` for every `i` (Artin–Schreier), so
the right hand side of the trace formula is `0` while the left hand side is `#𝔸¹(k) = q`, and
`L(𝔸¹, ℚ_p) = 1/(1 - qT)` while the alternating product is `1`.

This file states them with the input `hctf` (that `R π_*` preserves `D_ctf` along proper
morphisms, `Stacks.EtaleCohomology.ProperDirectImageCtfInput`) of the trace formula of Tag 03V3.

## Main results

* `LAdicSheaf.traceFormula_of_properDirectImageCtfInput`: the trace formula of Tag 03V2.
* `LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_properDirectImageCtfInput`: the
  cohomological expression of `L(X, F)` of Tag 03V0.

## References

* [Stacks Project, Tag 03V2](https://stacks.math.columbia.edu/tag/03V2)
* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Stacks.InverseSystem CategoryTheory.FilteredDerived Stacks.Trace

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

section TraceFormula

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

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

/-- **[Stacks, Tag 03V2] from the input `hctf` of Tag 03V3.** For `ℓ ≠ p`, an ℓ-adic sheaf `F`
on a separated scheme `X` of finite type over a finite field `k` and an algebraic closure `k̄` of
`k`, the groups `Hⁱ_c(X_k̄, F)` are finite dimensional over `ℚ_ℓ`, nonzero only for
`0 ≤ i ≤ 2 dim X`, and the alternating sum of the traces of `π_X^*` on them is the sum over the
rational points of the traces of the geometric Frobenius on the stalks, granted (`hctf`) that
`R π_*` preserves `D_ctf` along proper morphisms for the rings `ℤ/ℓⁿ⁺¹`. -/
@[sga "4½ Rapport 4.13" "special case"]
theorem LAdicSheaf.traceFormula_of_properDirectImageCtfInput [Algebra.IsAlgebraic k kbar]
    (hℓp : ℓ ≠ p) (hctf : ∀ n : ℕ, ProperDirectImageCtfInput B (ZMod (ℓ ^ (n + 1))))
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    (∀ i : ℤ, Module.Finite ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)) ∧
    (∀ i : ℤ, Nontrivial
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i) →
      0 ≤ i ∧ ∃ d : ℕ, topologicalKrullDim X.1 = d ∧ i ≤ 2 * (d : ℤ)) ∧
    ∑ᶠ (x : closedPoints X.1) (_ : residueDegree f x.1 = 1),
        LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)) =
      ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) *
        LinearMap.trace ℚ_[ℓ]
          (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q hcard F
            i).hom := by
  let : Fintype (rationalPoints f) := @Fintype.ofFinite _ (finite_rationalPoints f)
  exact LAdicSheaf.traceFormula_of_levelTraceFormula B X ℓ f j kbar p q hcard
    (properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement) F
    (LAdicSheaf.isPerfect_compactSupportFrobeniusCohomology_levelComplex B X ℓ f j kbar p q hcard
      hℓp hctf F)
    (LAdicSheaf.levelTraceFormula B X ℓ f j kbar p q hcard hℓp hctf F _)

end TraceFormula

section LFunction

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f]
  [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

/-- **[Stacks, Tag 03V0] from the input `hctf` of Tag 03V3.** For `ℓ ≠ p`, an ℓ-adic sheaf `F`
on a separated scheme `X` of finite type over a finite field `k` and an algebraic closure `k̄` of
`k`, `L(X, F) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}`, granted (`hctf`) that `R π_*`
preserves `D_ctf` along proper morphisms for the rings `ℤ/ℓⁿ⁺¹`. -/
theorem LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_properDirectImageCtfInput
    [Algebra.IsAlgebraic k kbar] (hℓp : ℓ ≠ p)
    (hctf : ∀ n : ℕ, ProperDirectImageCtfInput B (ZMod (ℓ ^ (n + 1))))
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.rationalLFunction B X ℓ F f =
      gradedCharSeries
        (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
        (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
          hcard F i).hom) := by
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  obtain ⟨hfd, hdeg, -⟩ :=
    LAdicSheaf.traceFormula_of_properDirectImageCtfInput B X ℓ f j kbar p q hcard hℓp hctf F
  obtain ⟨D, hD⟩ : ∃ D : ℕ, topologicalKrullDim X.1 ≤ D := by
    have hne := topologicalKrullDim_ne_top_of_locallyOfFiniteType k f
    generalize topologicalKrullDim X.1 = t at hne ⊢
    induction t using WithBot.recBotCoe with
    | bot => exact ⟨0, bot_le⟩
    | coe t =>
      induction t using ENat.recTopCoe with
      | top => exact absurd rfl hne
      | coe n => exact ⟨n, le_rfl⟩
  have hfin : {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)}.Finite := by
    refine (Set.finite_Icc (0 : ℤ) (2 * D)).subset fun i hi => ?_
    obtain ⟨h0, d, hd, hi2⟩ := hdeg i hi
    have hdD : d ≤ D := by
      have h : ((d : ℕ) : WithBot ℕ∞) ≤ ((D : ℕ) : WithBot ℕ∞) := hd ▸ hD
      exact_mod_cast h
    exact ⟨h0, hi2.trans (by omega)⟩
  refine LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_traceFormula B X ℓ f j kbar p q
    hcard F hfd hfin fun k' _ _ _ _ _ _ _ _ q' hcard' => ?_
  have : Algebra.IsAlgebraic k' kbar := Algebra.IsAlgebraic.tower_top (K := k) k'
  exact (LAdicSheaf.traceFormula_of_properDirectImageCtfInput B (fieldExtensionScheme B X f k') ℓ
    (pullback.snd f (specAlgebraMap k k')) (compactificationFieldBaseChange f j k') kbar p q'
    hcard' hℓp hctf (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F)).2.2

end LFunction

end Stacks.EtaleCohomology

end
