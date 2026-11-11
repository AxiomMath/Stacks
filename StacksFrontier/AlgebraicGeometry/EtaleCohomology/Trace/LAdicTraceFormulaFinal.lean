module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.TraceFormulaDctfFinal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 03V2] and [Stacks, Tag 03V0]: the trace formula and the L-function of a `ℚ_ℓ`-sheaf

Let `X` be a separated scheme of finite type over a finite field `k` with `p ^ q` elements, `k̄`
an algebraic closure of `k`, `ℓ ≠ p` a prime and `F` a `ℚ_ℓ`-sheaf on `X`.

* [Stacks, Tag 03V2]: the groups `Hⁱ_c(X_k̄, F)` are finite dimensional over `ℚ_ℓ`, nonzero only
  for `0 ≤ i ≤ 2 dim X`, and
  `∑_{x ∈ X(k)} Tr(π_x | F_x̄) = ∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ_c(X_k̄, F))`.
* [Stacks, Tag 03V0]: `L(X, F) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}` in `ℚ_ℓ[[T]]`.

`ℓ ≠ p` is the standing convention of the chapter ("`Λ` is killed by a power of a prime `ℓ` and
`ℓ ∈ k^*`", in Step 3 of the proof of Tag 03UG), and both statements are false for `ℓ = p`: for
`X = 𝔸¹_k` and `F = ℚ_p`, `Hⁱ_c(𝔸¹_k̄, ℤ/pⁿ) = 0` for every `i` (Artin–Schreier), so the right hand
side of the trace formula is `0` while the left hand side is `#𝔸¹(k) = p ^ q`, and
`L(𝔸¹, ℚ_p) = 1/(1 - p ^ q T)` while the alternating product is `1`.

`X` is separated because `Hⁱ_c` is defined for separated schemes of finite type only
(Definition 03UT), and Noetherian because a `ℤ_ℓ`-sheaf is only defined on a Noetherian scheme
(Remark before Definition 03UT); the latter is implied by finite type over `k`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.traceFormula`: [Stacks, Tag 03V2].
* [Stacks, Tag 03V0]:
  `LAdicSheaf.nonempty_compactificationOf_and_rationalLFunction_eq_gradedCharSeries`,
  from the identity for a given compactification,
  `LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius`.

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
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosure k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The trace formula for a `ℚ_ℓ`-sheaf.** Let `X` be a separated scheme of finite type over a
finite field `k` with `p ^ q` elements, `k̄` an algebraic closure of `k`, `ℓ` a prime with `ℓ ≠ p`
and `F` a `ℚ_ℓ`-sheaf on `X` (an ℓ-adic sheaf, tensored with `ℚ_ℓ`). Then
* `Hⁱ_c(X_k̄, F)` is a finite dimensional `ℚ_ℓ`-vector space for every `i`,
* it is nonzero only for `0 ≤ i ≤ 2 dim X`, and
* `∑_{x ∈ X(k)} Tr(π_x | F_x̄) = ∑ᵢ (-1)ⁱ Tr(π_X^* | Hⁱ_c(X_k̄, F))`, the rational points being the
  closed points of residue degree one.

`ℓ ≠ p` is the chapter's standing convention; the statement is false for `ℓ = p`
(`X = 𝔸¹_k`, `F = ℚ_p`: the right hand side is `0`, the left hand side `p ^ q`). -/
@[stacks 03V2 "finiteness, the degree bounds 0 <= i <= 2 dim X and the trace formula",
  sga "4½ Rapport 2.10" "special case",
  sga "7 I 0.1.1" "Q_ℓ clause of case 0.1.1"]
theorem LAdicSheaf.traceFormula (hℓp : ℓ ≠ p) (F : LAdicSheaf.{u, u + 1} B X ℓ) :
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
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  exact LAdicSheaf.traceFormula_of_properDirectImageCtfInput B X ℓ f j kbar p q hcard hℓp
    (fun _ => properDirectImageCtfInput B _) F

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
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

/-- **The L-function of a `ℚ_ℓ`-sheaf.** Let `X` be a separated scheme of finite type over a
finite field `k` with `p ^ q` elements, `k̄` an algebraic closure of `k`, `ℓ` a prime with `ℓ ≠ p`
and `F` a `ℚ_ℓ`-sheaf on `X`. Then
`L(X, F) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}` in `ℚ_ℓ[[T]]`.

`X` is separated because `Hⁱ_c` is defined for separated schemes only (Definition 03UT).
`ℓ ≠ p` is the chapter's standing convention; the statement is false for `ℓ = p`
(`L(𝔸¹_k, ℚ_p) = 1/(1 - p ^ q T)` while the alternating product is `1`).

This is the identity for a given compactification `j`; that one exists is Nagata's theorem, and
[Stacks, Tag 03V0] with it is
`LAdicSheaf.nonempty_compactificationOf_and_rationalLFunction_eq_gradedCharSeries`. -/
theorem LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius (hℓp : ℓ ≠ p)
    (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    LAdicSheaf.rationalLFunction B X ℓ F f =
      gradedCharSeries
        (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
        (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
          hcard F i).hom) := by
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed k
  exact LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_properDirectImageCtfInput B X ℓ f j
    kbar p q hcard hℓp (fun _ => properDirectImageCtfInput B _) F

end LFunction

section LFunctionNagata

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
  [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosure k kbar]
  (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)
  [IsNoetherian X.1]

/-- **[Stacks, Tag 03V0]: the L-function of a `ℚ_ℓ`-sheaf.** Let `X` be a separated scheme of
finite type over a finite field `k` with `p ^ q` elements, `k̄` an algebraic closure of `k`, `ℓ` a
prime with `ℓ ≠ p` and `F` a `ℚ_ℓ`-sheaf on `X`. Then `X` has a compactification over `k`, and
for every compactification `j : X ⟶ X̄`, through which `Hⁱ_c(X_k̄, F)` is defined,
`L(X, F) = ∏ᵢ det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}` in `ℚ_ℓ[[T]]`.

A compactification exists by Nagata's theorem
(`AlgebraicGeometry.hasCompactification_of_compactSpace_quasiSeparatedSpace`, Tag 0F41), since
`Spec k` is quasi-compact and quasi-separated. The library compares compactly supported
cohomology computed through two compactifications at a finite level
(`Stacks.EtaleCohomology.compactSupportSheafCohomologyCompactificationIso`); the identity here
is proved for every compactification, so it does not depend on that comparison.

`X` is separated because `Hⁱ_c` is defined for separated schemes only (Definition 03UT).
`ℓ ≠ p` is the chapter's standing convention; the statement is false for `ℓ = p`
(`L(𝔸¹_k, ℚ_p) = 1/(1 - p ^ q T)` while the alternating product is `1`). -/
@[stacks 03V0 "for a Q_l-sheaf with l invertible in k, X separated (where H^i_c is defined); \
H^i_c through any compactification of X over k (one exists by 0F41)"]
theorem LAdicSheaf.nonempty_compactificationOf_and_rationalLFunction_eq_gradedCharSeries
    (hℓp : ℓ ≠ p) (F : LAdicSheaf.{u, u + 1} B X ℓ) :
    Nonempty (CompactificationOf (Over.mk f)) ∧
      ∀ j : CompactificationOf (Over.mk f),
        LAdicSheaf.rationalLFunction B X ℓ F f =
          gradedCharSeries
            (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
            (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
              hcard F i).hom) := by
  refine ⟨?_, fun j => ?_⟩
  · obtain ⟨j, -⟩ := hasCompactification_of_compactSpace_quasiSeparatedSpace f
    exact ⟨j⟩
  · exact LAdicSheaf.rationalLFunction_eq_gradedCharSeries_compactSupportFrobenius B X ℓ f j kbar
      p q hcard hℓp F

end LFunctionNagata

end Stacks.EtaleCohomology

end
