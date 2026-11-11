module

public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.AlgebraicEigenvalues
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.HeckePolynomial
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.CuspVanishing
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.FiniteSupport
public import StacksFrontier.NumberTheory.Adeles.GeneralLinear.Reduction.Reduction
public import StacksFrontier.NumberTheory.Drinfeld.CurveFunctionField
public import StacksFrontier.NumberTheory.TraceFormula.AutomorphicPartner
public import StacksFrontier.NumberTheory.TraceFormula.ConstantCharpoly.IntegralCongruence
public import StacksFrontier.NumberTheory.TraceFormula.FrobeniusDegree
public import StacksFrontier.NumberTheory.TraceFormula.GaitsgoryFiniteness

/-!
# Gaitsgory's theorem from the automorphic form attached to `ρ`

Let `k` be a finite field of characteristic `p`, `X` a smooth, geometrically irreducible,
projective curve over `k` with function field `K`, `ℓ ≠ p` a prime and
`ρ : π₁(X) → GL_n(F_ℓ[[t]])` continuous. Tag 03W0 says that the Conjecture (`ρ(π₁(X_k̄))` is
finite) holds for `ℓ > 2n` modulo some unproven things, citing Gaitsgory. The unproven input is
the existence of the automorphic form attached to `ρ`
(`Stacks.TraceFormula.HasCuspidalHeckeEigenforms`): unramified cuspidal Hecke eigenforms
`f_1, …, f_m` on `GL_{n_j}(A_K)` with coefficients in an extension `Λ` of `F_ℓ((t))` whose Hecke
polynomials multiply to the characteristic polynomial of `ρ(F_v)` at every place. This file
deduces the finiteness from it, as de Jong does.

1. **Harder's finiteness** (`Stacks.Adeles.GeneralLinear.finiteSupportModCenter`): a cusp form on
   `GL_n(A_K)` vanishes outside `GL_n(O) · Z(A) · S · GL_n(K)` for a finite set `S`, by reduction
   theory and the vanishing of the constant terms.
2. **Algebraicity of eigenvalues** (`Stacks.Adeles.GeneralLinear.exists_isAlgebraic_mul_pow`):
   after an unramified twist `γ^{deg det}`, which makes the central character of finite order,
   the Hecke eigenvalues `t_{v,i} γ^{i deg v}` are algebraic over `F_ℓ`.
3. **Integral congruences** (`Stacks.TraceFormula.coeff_coeff_eq_zero_of_eq_prod`): the twisting
   factors `γ^{i deg v}` are integral units over `F_ℓ[[t]]` and are `≡ 1 mod t^N` when
   `deg v` is divisible by a suitable `M`; then the characteristic polynomial of `ρ(F_v)` is
   constant modulo `t^N`, `F_ℓ` being algebraically closed in `F_ℓ[[t]]`.
4. **Chebotarev**: Frobenius elements in an open subgroup containing the geometric fundamental
   group have degree divisible by `M`
   (`Stacks.TraceFormula.exists_isOpen_subgroup_dvd_residueDegree`)
   and are dense, so the characteristic polynomials of `ρ` on `π₁(X_k̄)` have constant
   coefficients; the finiteness then follows as in
   `Stacks.TraceFormula.finite_range_of_charpoly_coeff_mem_range_C`.

## Main results

* `Stacks.Adeles.GeneralLinear.finiteSupportModCenter` — Harder's finiteness theorem.
* `Stacks.TraceFormula.charpoly_coeff_mem_range_C_of_hasCuspidalHeckeEigenforms`.
* `Stacks.TraceFormula.finite_geometricMonodromy_of_hasCuspidalHeckeEigenforms` — finiteness
  for one `ρ` with an attached automorphic form.
* `Stacks.TraceFormula.geometricMonodromyConjecture_of_gaitsgoryInput` — Tag 03W0.

## References

* [Stacks Project, Tag 03W0](https://stacks.math.columbia.edu/tag/03W0)
* [Gaitsgory]
* [dJ-conjecture]
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial Stacks.Adeles Stacks.Adeles.GlobalFunctionField
open scoped PowerSeries.WithPiTopology

universe u w

namespace Stacks.Adeles.GeneralLinear

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k in
variable (K) in
/-- **Harder's finiteness theorem**: there is a finite set `S ⊆ GL_n(A)` such that every
unramified cusp form on `GL_n(A)`, with values in any `Λ`, vanishes outside
`GL_n(O) · Z(A) · S · GL_n(K)`. -/
public theorem finiteSupportModCenter (n : ℕ) : FiniteSupportModCenter.{u, w} K n :=
  finiteSupportModCenter_of k n (reductionTheory (k := k) (K := K) n)
    (cuspVanishing (k := k) (K := K) n)

/-- **Algebraicity of the twisted Hecke eigenvalues.** For an unramified cuspidal Hecke
eigenform on `GL_n(A)`, `n > 0`, with values in a field `Λ` and eigenvalues `t`, there is a
nonzero `γ` in an algebraic closure `Λ̄` such that every `t_{v,i} γ ^ {i deg v}` is algebraic
over the prime field of `Λ̄`. -/
public theorem exists_isAlgebraic_mul_pow_algebraicClosure {n : ℕ} {Λ : Type w} [Field Λ]
    (hn : 0 < n) {f : GL (Fin n) (AdeleRing K) → Λ} (hf : IsUnramifiedCuspFormGL n f)
    {t : Place K → ℕ → Λ} (ht : IsHeckeEigenformGL f t) :
    ∃ γ : AlgebraicClosure Λ, γ ≠ 0 ∧ ∀ v i, 1 ≤ i → i ≤ n →
      IsAlgebraic (⊥ : Subfield (AlgebraicClosure Λ))
        (algebraMap Λ (AlgebraicClosure Λ) (t v i) * γ ^ (i * Stacks.Drinfeld.placeDegree k K v)) :=
  exists_isAlgebraic_mul_pow (k := k) (finiteSupportModCenter.{u, w} k K n) hn
    (hf.comp (algebraMap Λ (AlgebraicClosure Λ)).toAddMonoidHom
      (algebraMap Λ (AlgebraicClosure Λ)).injective)
    (ht.comp (algebraMap Λ (AlgebraicClosure Λ)) (algebraMap Λ (AlgebraicClosure Λ)).injective)

end Stacks.Adeles.GeneralLinear

namespace Stacks.TraceFormula

/-- An integral scheme is connected; pinned, since the general search for `ConnectedSpace X` runs
out of heartbeats with the imports of this file. -/
local instance (priority := 3000) connectedSpace_of_isIntegral_scheme' {X : Scheme.{u}}
    [IsIntegral X] : ConnectedSpace X :=
  inferInstance

/-- The geometric curve of a geometrically irreducible scheme is connected; pinned, since the
general search runs out of heartbeats with the imports of this file. -/
local instance (priority := 3000) connectedSpace_geometricBaseChange_of_isCurve'
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [GeometricallyIrreducible f] : ConnectedSpace (geometricBaseChange k K f) :=
  have := geometricallyConnected_of_geometricallyIrreducible f
  connectedSpace_fieldBaseChange f K

variable (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [GeometricallyIrreducible f] {n ℓ : ℕ}

/-- The constant coefficient of the characteristic polynomial of an invertible matrix is a
unit. -/
theorem isUnit_charpoly_coeff_zero {R : Type*} [CommRing R] (g : GL (Fin n) R) :
    IsUnit ((g : Matrix (Fin n) (Fin n) R).charpoly.coeff 0) := by
  have h := Matrix.det_eq_sign_charpoly_coeff (g : Matrix (Fin n) (Fin n) R)
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) R).det := (Matrix.isUnit_iff_isUnit_det _).1
    g.isUnit
  have hs : IsUnit ((-1 : R) ^ Fintype.card (Fin n)) := (isUnit_one.neg).pow _
  rw [h] at hdet
  exact isUnit_of_mul_isUnit_right hdet

/-- **Constant characteristic polynomials on the geometric fundamental group.** If `ρ` has an
attached automorphic form, then for every `g ∈ π₁(X_K)` the characteristic polynomial of `ρ(g)`
has constant coefficients. -/
public theorem charpoly_coeff_mem_range_C_of_hasCuspidalHeckeEigenforms [Finite k]
    [IsAlgClosure k K] [Smooth f] [IsProper f] [Fact ℓ.Prime]
    (x : GeometricPoint (geometricBaseChange k K f))
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (hρ : HasCuspidalHeckeEigenforms (x.map (geometricProjection k K f)) ρ)
    (g : EtaleFundamentalGroup (geometricBaseChange k K f) x) (i : ℕ) :
    (geometricRestriction k K f x ρ g :
      Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i ∈
      Set.range (PowerSeries.C (R := ZMod ℓ)) := by
  classical
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  obtain ⟨_, _, _, _⟩ := Stacks.Drinfeld.exists_functionField_of_isCurve f
  obtain ⟨Λ, _, ι, m, d, F, t, hι, -, hd, hF, ht, hmatch⟩ := hρ
  set φ := algebraMap Λ (AlgebraicClosure Λ)
  have hγ := fun j => Stacks.Adeles.GeneralLinear.exists_isAlgebraic_mul_pow_algebraicClosure
    (k := k) (hd j) (hF j) (ht j)
  choose γ hγ0 hγalg using hγ
  let V := {q : Place X.functionField ×
      EtaleFundamentalGroup X (x.map (geometricProjection k K f)) //
    IsGeometricFrobeniusAt (x.map (geometricProjection k K f)) q.1 q.2}
  let deg : V → ℕ := fun q => Stacks.Drinfeld.placeDegree k X.functionField q.1.1
  let P : V → Polynomial (PowerSeries (ZMod ℓ)) := fun q =>
    (ρ q.1.2 : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly
  let B : Fin m → V → Polynomial (AlgebraicClosure Λ) := fun j q =>
    heckePolynomial (d j) q.1.1.residueCard (fun i => φ (t j q.1.1 i))
  have hfac : ∀ q : V, (P q).map (φ.comp ι) = ∏ j, B j q := by
    intro q
    change ((ρ q.1.2 : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly).map (φ.comp ι) = _
    rw [← Polynomial.map_map, hmatch q.1.1 q.1.2 q.2, Polynomial.map_prod]
    exact Finset.prod_congr rfl fun j _ => map_heckePolynomial _ _ _ φ
  have hz : ∀ z : ℤ, IsAlgebraic (⊥ : Subfield (AlgebraicClosure Λ)) (z : AlgebraicClosure Λ) :=
    fun z => by
      simpa using isAlgebraic_algebraMap (R := (⊥ : Subfield (AlgebraicClosure Λ)))
        (A := AlgebraicClosure Λ) (z : (⊥ : Subfield (AlgebraicClosure Λ)))
  have halg : ∀ j q i, i ≤ d j → IsAlgebraic (⊥ : Subfield (AlgebraicClosure Λ))
      ((B j q).coeff (d j - i) * γ j ^ (i * deg q)) := by
    intro j q i hi
    simp only [B]
    rw [coeff_heckePolynomial_sub _ _ _ hi]
    rcases Nat.eq_zero_or_pos i with rfl | hi1
    · simpa using isAlgebraic_one
    · simp only [hi1.ne', ↓reduceIte]
      rw [mul_assoc]
      have h1 := hz ((-1) ^ i * (q.1.1.residueCard : ℤ) ^ (i * (i - 1) / 2))
      push_cast at h1
      exact h1.mul (hγalg j q.1.1 i hi1 hi)
  obtain ⟨v₀⟩ := nonempty_place k (K := X.functionField)
  obtain ⟨F₀, hF₀⟩ := exists_isGeometricFrobeniusAt f (x.map (geometricProjection k K f)) v₀
  have hdeg₀ : 0 < deg ⟨(v₀, F₀), hF₀⟩ := by
    have h1 := one_lt_resCard k v₀
    rw [Stacks.Drinfeld.resCard_eq_pow_placeDegree k v₀] at h1
    rcases Nat.eq_zero_or_pos (Stacks.Drinfeld.placeDegree k X.functionField v₀) with h | h
    · rw [h, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h
  have hk : 1 < Nat.card k := Finite.one_lt_card
  refine ⟨PowerSeries.constantCoeff
    ((geometricRestriction k K f x ρ g :
      Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i), ?_⟩
  ext c
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp [PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [PowerSeries.coeff_C, hc.ne', ↓reduceIte]
  obtain ⟨M, hM0, hM⟩ := coeff_coeff_eq_zero_of_eq_prod (φ.comp ι) (φ.injective.comp hι) deg P
    (fun q => Matrix.charpoly_monic _) (fun q => isUnit_charpoly_coeff_zero _) d B
    (fun j q => monic_heckePolynomial _ _ _) (fun j q => natDegree_heckePolynomial _ _ _) hfac
    γ hγ0 halg ⟨(v₀, F₀), hF₀⟩ hdeg₀ (c + 1)
  obtain ⟨U, hUo, hUg, hUdeg⟩ := exists_isOpen_subgroup_dvd_residueDegree k K f x M hM0
  set h := etaleFundamentalGroupMap (geometricProjection k K f) x g
  let O : Set (EtaleFundamentalGroup X (x.map (geometricProjection k K f))) :=
    {g' | PowerSeries.coeff c
    ((ρ g'⁻¹ : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i) =
      PowerSeries.coeff c ((ρ h : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i)}
  have hcont : Continuous fun g' : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) =>
      PowerSeries.coeff c
      ((ρ g'⁻¹ : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i) :=
    (PowerSeries.WithPiTopology.continuous_coeff _ c).comp ((continuous_charpoly_coeff i).comp
      (Units.continuous_val.comp (ρ.continuous_toFun.comp continuous_inv)))
  have hO : IsOpen O := hcont.isOpen_preimage {(PowerSeries.coeff c
    ((ρ h : Matrix (Fin n) (Fin n) (PowerSeries (ZMod ℓ))).charpoly.coeff i))} (isOpen_discrete _)
  have hdense : Dense
      (frobeniusElements (x.map (geometricProjection k K f)) (∅ : Set (closedPoints X))ᶜ) :=
    dense_frobeniusElements_compl f (x.map (geometricProjection k K f)) Set.finite_empty
  obtain ⟨g', ⟨hgO, hgU⟩, y, -, c', rfl⟩ := hdense.inter_open_nonempty (O ∩ U) (hO.inter hUo)
    ⟨h⁻¹, by simp [O], U.inv_mem (hUg g)⟩
  have hdvd := hUdeg y c' hgU
  obtain ⟨v, hcen, hgeo⟩ := exists_isCentreOf_isGeometricFrobeniusAt_inv f y c'
  have hdegv : Stacks.Drinfeld.placeDegree k X.functionField v =
      Stacks.EtaleCohomology.residueDegree f y.1 := by
    have h1 := Stacks.Drinfeld.resCard_eq_pow_placeDegree k v
    rw [resCard_eq_natCard_residueField_of_isCentreOf hcen,
      natCard_residueField_eq_pow_residueDegree f y] at h1
    exact (Nat.pow_right_injective hk h1).symm
  have := hM ⟨(v, c'.element⁻¹), hgeo⟩ (by simpa [deg, hdegv] using hdvd) i c hc
    (Nat.lt_succ_self c)
  simp only [O, Set.mem_ofPred_eq] at hgO
  have hh : geometricRestriction k K f x ρ g = ρ h := rfl
  rw [hh, ← hgO, this]

/-- **Finite geometric monodromy from the attached automorphic form.** Let `k` be a finite field of
characteristic `p`, `X` a smooth, geometrically irreducible, projective curve over `k`, `ℓ ≠ p` a
prime with `2n < ℓ`, and `ρ : π₁(X) → GL_n(F_ℓ[[t]])` continuous. If `ρ` has an attached
automorphic form (cuspidal Hecke eigenforms on `GL_{n_j}(A)`, `∑ n_j = n`, with coefficients in an
extension of `F_ℓ((t))`, whose Hecke polynomials multiply to the characteristic polynomial of `ρ`
at every geometric Frobenius element), then `ρ(π₁(X_k̄))` is finite. -/
public theorem finite_geometricMonodromy_of_hasCuspidalHeckeEigenforms [Finite k]
    [IsAlgClosure k K] [Smooth f] (p : ℕ) [CharP k p] [Fact ℓ.Prime]
    (x : GeometricPoint (geometricBaseChange k K f))
    (ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
      Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)))
    (hproj : IsProjective f) (hℓp : ℓ ≠ p) (hn : 2 * n < ℓ)
    (hρ : 2 * n < ℓ → HasCuspidalHeckeEigenforms (x.map (geometricProjection k K f)) ρ) :
    Finite (geometricMonodromy k K f x ρ) := by
  have : IsProper f := hproj.isProper
  have hp : p.Prime := CharP.char_is_prime k p
  have hℓ : (ℓ : k) ≠ 0 := fun h => hℓp <| by
    have hdvd := (CharP.cast_eq_zero_iff k p ℓ).mp h
    exact ((Nat.prime_dvd_prime_iff_eq hp (Fact.out : ℓ.Prime)).mp hdvd).symm
  have := compactSpace_etaleFundamentalGroup (geometricBaseChange k K f) x
  have hfin := finite_range_of_charpoly_coeff_mem_range_C (geometricRestriction k K f x ρ)
    (fun g i => charpoly_coeff_mem_range_C_of_hasCuspidalHeckeEigenforms k K f x ρ (hρ hn) g i)
    (fun V hV => finite_continuous_monoidHom_multiplicative_zmod_of_isOpen k K f hℓ x V hV)
  exact hfin.to_subtype

variable (n ℓ) in
/-- The Conjecture of the section on automorphic forms and sheaves for `X`, `n` and `ℓ`: for every
continuous `ρ : π₁(X) → GL_n(F_ℓ[[t]])` the geometric monodromy group `ρ(π₁(X_k̄))` is finite
(here `k̄ = K` is an algebraic closure of `k` and the base point comes from `X_K`). -/
public def GeometricMonodromyConjecture (x : GeometricPoint (geometricBaseChange k K f)) : Prop :=
  ∀ ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
    Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)), Finite (geometricMonodromy k K f x ρ)

variable (n ℓ) in
/-- The input of Gaitsgory's theorem for `X`, `n` and `ℓ`: every continuous
`ρ : π₁(X) → GL_n(F_ℓ[[t]])` has an attached automorphic form
(`Stacks.TraceFormula.HasCuspidalHeckeEigenforms`). Gaitsgory constructs it, for `ℓ > 2n`, from a
Hecke eigensheaf with `F_ℓ((t))`-coefficients, through a theory of sheaves with such coefficients
which is not worked out in the literature. -/
public def GaitsgoryInput (x : GeometricPoint (geometricBaseChange k K f)) : Prop :=
  ∀ ρ : EtaleFundamentalGroup X (x.map (geometricProjection k K f)) →ₜ*
    Matrix.GeneralLinearGroup (Fin n) (PowerSeries (ZMod ℓ)),
    HasCuspidalHeckeEigenforms (x.map (geometricProjection k K f)) ρ

/-- **Stacks Project, Tag 03W0 (Gaitsgory).** *The Conjecture holds if `ℓ > 2n`, modulo some
unproven things.* Let `k` be a finite field of characteristic `p`, `X` a smooth, geometrically
irreducible, projective curve over `k`, `k̄` an algebraic closure of `k`, and `ℓ ≠ p` a prime with
`2n < ℓ`. Then the unproven input of Gaitsgory's construction (`GaitsgoryInput`: every continuous
`ρ : π₁(X) → GL_n(F_ℓ[[t]])` has an attached automorphic form) implies the Conjecture for `X`, `n`
and `ℓ` (`GeometricMonodromyConjecture`: every such `ρ` has finite geometric monodromy
`ρ(π₁(X_k̄))`). -/
@[stacks 03W0 "Gaitsgory's theorem: for l > 2n, the input the source leaves unproven \
(GaitsgoryInput: every rho has an attached automorphic form, cuspidal Hecke eigenforms on GL_{n_j} \
whose Hecke polynomials multiply to the characteristic polynomials of Frobenius) implies the \
Conjecture (GeometricMonodromyConjecture)"]
public theorem geometricMonodromyConjecture_of_gaitsgoryInput [Finite k] [IsAlgClosure k K]
    [Smooth f] (p : ℕ) [CharP k p] [Fact ℓ.Prime]
    (x : GeometricPoint (geometricBaseChange k K f)) (hproj : IsProjective f) (hℓp : ℓ ≠ p)
    (hn : 2 * n < ℓ) :
    GaitsgoryInput k K f n ℓ x → GeometricMonodromyConjecture k K f n ℓ x :=
  fun h ρ => finite_geometricMonodromy_of_hasCuspidalHeckeEigenforms k K f p x ρ hproj hℓp hn
    fun _ => h ρ

end Stacks.TraceFormula

end
