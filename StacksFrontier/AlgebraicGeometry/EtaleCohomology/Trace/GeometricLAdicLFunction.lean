module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FieldExtensionPointTrace
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LFunctionTraceCriterion
public import Mathlib.FieldTheory.Finite.Extension

/-!
# The L-function of a `ℚ_ℓ`-sheaf from the trace formula over the finite extensions

Let `X` be a separated scheme of finite type over a finite field `k` with `q = p ^ f` elements,
`F` an ℓ-adic sheaf on `X` and `k̄` an algebraic closure of `k`.  The proof of
[Stacks, Tag 03V0] reduces the identity
`L(X, F) = ∏_i det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}`
to the trace identities
`∑_{d ∣ n} d ∑_{deg x = d} Tr(π_x ^ (n / d) | F_x̄) = ∑_i (-1)^i Tr((π_X^*) ^ n | Hⁱ_c(X_k̄, F))`
for `n ≥ 1`, and each of these to the trace formula of Tag 03V2 for `X_n = X ×_k k_n` over the
subfield `k_n ⊆ k̄` of degree `n` over `k`:

* the left hand side is `∑_{y ∈ X_n(k_n)} Tr(π_y | (F|_{X_n})_ȳ)`
  (`LAdicSheaf.finsum_rationalStalkFrobenius_fieldExtension`);
* `Hⁱ_c((X_n)_k̄, F|_{X_n}) = Hⁱ_c(X_k̄, F)` with `π_{X_n}^* = (π_X^*) ^ n`
  (`LAdicSheaf.trace_rationalGeometricCompactlySupportedFrobenius_fieldExtension`).

This file carries out that reduction:
`LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_traceFormula` takes the trace formula of Tag
03V2 over every finite extension of `k` inside `k̄`, with the finiteness of the groups
`Hⁱ_c(X_k̄, F)`, and returns the identity of Tag 03V0.

## References

* [Stacks Project, Tag 03V0](https://stacks.math.columbia.edu/tag/03V0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### The subfield of degree `n` of an algebraic closure -/

section Subfield

variable (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p : ℕ) [Fact p.Prime] [CharP k p]

omit [Fintype k] in
include p in
/-- There is an intermediate field `k ⊆ k_n ⊆ k̄` of degree `n ≥ 1` over `k`. -/
lemma exists_intermediateField_finrank_eq [Finite k] (n : ℕ) [NeZero n] :
    ∃ K : IntermediateField k kbar, FiniteDimensional k K ∧ Module.finrank k K = n := by
  let ι : FiniteField.Extension k p n →ₐ[k] kbar := IsAlgClosed.lift
  let e := AlgEquiv.ofInjectiveField ι
  have : FiniteDimensional k ι.fieldRange := Module.Finite.equiv e.toLinearEquiv
  exact ⟨ι.fieldRange, inferInstance,
    e.toLinearEquiv.finrank_eq.symm.trans (FiniteField.finrank_extension k p n)⟩

end Subfield

/-! ### The reduction -/

section Reduction

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

omit [Fintype k] [IsSeparated f] [AlgebraicGeometry.IsNoetherian X.obj] in
/-- `X ×_k k'` is noetherian for a finite extension `k'` of `k`. -/
lemma isNoetherian_fieldExtensionScheme (k' : Type u) [Field k'] [Algebra k k']
    [Module.Finite k k'] : IsNoetherian (fieldExtensionScheme B X f k').1 :=
  { toIsLocallyNoetherian :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f (specAlgebraMap k k'))
    toCompactSpace :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (specAlgebraMap k k')) }

omit [IsSeparated f] in
/-- **The L-function of a `ℚ_ℓ`-sheaf from the trace formula over the finite extensions of the
base field.**  Let `F` be an ℓ-adic sheaf on a separated scheme `X` of finite type over a finite
field `k` with `p ^ q` elements, and `k̄` an algebraic closure of `k`.  Suppose the groups
`Hⁱ_c(X_k̄, F)` are finite dimensional and nonzero for finitely many `i` only (`hfd`, `hfin`), and
that for every finite extension `k ⊆ k' ⊆ k̄`, with `p ^ q'` elements, the trace formula
`∑_{y ∈ X'(k')} Tr(π_y | (g⁻¹F)_ȳ) = ∑_i (-1)^i Tr(π_{X'}^* | Hⁱ_c(X'_k̄, g⁻¹F))` holds for
`X' = X ×_k k'` and the projection `g : X' ⟶ X` (`htr`).  Then
`L(X, F) = ∏_i det(1 - π_X^* T | Hⁱ_c(X_k̄, F))^{(-1)^{i+1}}`. -/
theorem LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_traceFormula
    (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (hfd : ∀ i : ℤ, FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i))
    (hfin : {i : ℤ | Nontrivial
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)}.Finite)
    (htr : ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] [Module.Finite k k']
      [Algebra k' kbar] [IsScalarTower k k' kbar] [CharP k' p]
      [IsNoetherian (fieldExtensionScheme B X f k').1] (q' : ℕ)
      (hcard' : Fintype.card k' = p ^ q'),
      ∑ᶠ (y : closedPoints (fieldExtensionScheme B X f k').1)
          (_ : residueDegree (pullback.snd f (specAlgebraMap k k')) y.1 = 1),
          LinearMap.trace ℚ_[ℓ] _
            (LAdicSheaf.rationalStalkFrobenius B (fieldExtensionScheme B X f k') ℓ
              (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) y.1
              (finite_residueField (pullback.snd f (specAlgebraMap k k')) y.1 y.2)) =
        ∑ᶠ i : ℤ, (if Even i then (1 : ℚ_[ℓ]) else -1) * LinearMap.trace ℚ_[ℓ] _
          (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B
            (fieldExtensionScheme B X f k') ℓ (pullback.snd f (specAlgebraMap k k'))
            (compactificationFieldBaseChange f j k') kbar p q' hcard'
            (LAdicSheaf.inverseImage (fieldExtensionProj B X f k') F) i).hom) :
    LAdicSheaf.rationalLFunction B X ℓ F f =
      gradedCharSeries
        (fun i => LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F i)
        (fun i => (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ f j kbar p q
          hcard F i).hom) := by
  refine LAdicSheaf.rationalLFunction_eq_gradedCharSeries_of_finite B X ℓ F f _ _ hfin
    fun n hn => ?_
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨K, hKfin, hK⟩ := exists_intermediateField_finrank_eq k kbar p (m + 1)
  let : Fintype K := @Fintype.ofFinite _ (Module.finite_of_finite k)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  have := isNoetherian_fieldExtensionScheme B X f K
  have hcard' : Fintype.card K = p ^ (q * (m + 1)) := by
    rw [Module.card_eq_pow_finrank (K := k) (V := K), hK, hcard, pow_mul]
  rw [← LAdicSheaf.finsum_rationalStalkFrobenius_fieldExtension B X ℓ f K F (m + 1) hK hn,
    htr K (q * (m + 1)) hcard']
  refine finsum_congr fun i => ?_
  rw [neg_one_zpow_eq_ite]
  congr 1
  exact LAdicSheaf.trace_rationalGeometricCompactlySupportedFrobenius_fieldExtension B X ℓ f j K
    kbar F i p q hcard m hcard'

end Reduction

end Stacks.EtaleCohomology

end
