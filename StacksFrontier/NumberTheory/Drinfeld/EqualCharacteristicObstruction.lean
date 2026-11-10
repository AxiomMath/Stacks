module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.GaloisSide
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Instances.Matrix

/-!
# No `p`-adic Galois representation matches eigenvalues with `u_v` a `p`-adic unit

Let `X` be a smooth proper curve over a finite field `k` of characteristic `p` and let
`ρ : π₁(X) → GL₂(E)` be continuous, with `E` a finite extension of `ℚ_p`. Since `π₁(X)` is
compact, the determinants `det ρ(g)` form a compact subgroup of `Eˣ`, so `det ρ(F_v)` and its
inverse are integral over `ℤ_p`. The residue cardinality `q_v` is a power of `p`, so
`q_v⁻¹ det ρ(F_v)` is never integral over `ℤ_p`. Hence the equality `u_v = q_v⁻¹ det ρ(F_v)` of
Stacks Theorem 03VT cannot hold at a place where `u_v` is a unit of `Z̄_p`: in the case `ℓ = p`
the conclusion of Theorem 03VT fails for every eigenform satisfying its hypothesis.

## Main results

* `Stacks.Drinfeld.exists_fg_submodule_of_isCompact` — a compact subset of a finite extension `E`
  of `ℚ_p` (with its module topology) lies in a finitely generated `ℤ_p`-submodule.
* `Stacks.Drinfeld.isIntegral_of_pow_mem_of_isCompact` — an element of `E` all of whose powers
  lie in a compact set is integral over `ℤ_p`.
* `Stacks.Drinfeld.ringChar_dvd_residueCard` — `p ∣ q_v` for every place `v` of `k(X)`.
* `Stacks.Drinfeld.not_isFrobeniusCompatible_of_eq_ringChar` — the obstruction for `ℓ = p`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Adeles Stacks.Adeles.GlobalFunctionField

universe u

namespace Stacks.Drinfeld

section Compact

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Field E] [Algebra ℚ_[p] E]
  [FiniteDimensional ℚ_[p] E] [TopologicalSpace E] [IsModuleTopology ℚ_[p] E]
  [Algebra ℤ_[p] E] [IsScalarTower ℤ_[p] ℚ_[p] E]

/-- A compact subset of a finite extension `E` of `ℚ_p`, with its module topology, lies in a
finitely generated `ℤ_p`-submodule of `E`. -/
public theorem exists_fg_submodule_of_isCompact {C : Set E} (hC : IsCompact C) :
    ∃ M : Submodule ℤ_[p] E, M.FG ∧ C ⊆ M := by
  let b := Module.finBasis ℚ_[p] E
  let e := b.equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1 (hC.image he).isBounded
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt R
    (show (1 : ℝ) < p by exact_mod_cast (Fact.out : p.Prime).one_lt)
  refine ⟨Submodule.span ℤ_[p] (Set.range fun i => ((p : ℚ_[p]) ^ m)⁻¹ • b i),
    Submodule.fg_span (Set.finite_range _), fun x hx => ?_⟩
  have hcoord : ∀ i, ‖(p : ℚ_[p]) ^ m * e x i‖ ≤ 1 := by
    intro i
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow]
    calc ((p : ℝ) ^ m)⁻¹ * ‖e x i‖ ≤ ((p : ℝ) ^ m)⁻¹ * (p : ℝ) ^ m := by
          gcongr
          exact (norm_le_pi_norm (e x) i).trans ((hR _ ⟨x, hx, rfl⟩).trans hm.le)
      _ = 1 := inv_mul_cancel₀ (pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero))
  have hp0 : ((p : ℚ_[p]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let c : Fin (Module.finrank ℚ_[p] E) → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ m * e x i, hcoord i⟩
  have hx' : x = ∑ i, c i • (((p : ℚ_[p]) ^ m)⁻¹ • b i) := by
    conv_lhs => rw [← b.sum_equivFun x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul ℚ_[p] (c i), smul_smul]
    congr 1
    change e x i = ((p : ℚ_[p]) ^ m * e x i) * ((p : ℚ_[p]) ^ m)⁻¹
    field_simp
  rw [hx']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- An element of a finite extension of `ℚ_p` all of whose powers lie in a compact set is
integral over `ℤ_p`. -/
public theorem isIntegral_of_pow_mem_of_isCompact {C : Set E} (hC : IsCompact C) {a : E}
    (ha : ∀ n : ℕ, a ^ n ∈ C) : IsIntegral ℤ_[p] a := by
  obtain ⟨M, hM, hCM⟩ := exists_fg_submodule_of_isCompact (p := p) hC
  have := isNoetherian_of_fg_of_noetherian M hM
  refine isIntegral_of_submodule_noetherian (Algebra.adjoin ℤ_[p] {a}) ?_ a
    (Algebra.self_mem_adjoin_singleton ℤ_[p] a)
  have hle : Subalgebra.toSubmodule (Algebra.adjoin ℤ_[p] {a}) ≤ M := by
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    rintro _ hy
    obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 hy
    exact hCM (ha n)
  exact isNoetherian_of_le hle

end Compact

section Curve

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}} [IsIntegral X]
  (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [IsProper f]

omit [Finite k] [IsCurve k f] [Smooth f] [IsProper f] in
include f in
/-- The characteristic of `k` vanishes in the residue field `κ_v` of every completion. -/
public theorem natCast_ringChar_residueField (v : Place X.functionField) :
    ((ringChar k : ℕ) : IsLocalRing.ResidueField v.integers) = 0 := by
  have h0 : ((ringChar k : ℕ) : X.functionField) = 0 := by
    rw [← map_natCast (fieldToStalk f (genericPoint X)).hom, ringChar.Nat.cast_ringChar,
      map_zero]
  have h1 : ((ringChar k : ℕ) : v.completion) = 0 := by
    rw [← map_natCast v.coeRingHom, h0, map_zero]
  have h2 : ((ringChar k : ℕ) : v.integers) = 0 := Subtype.ext (by simpa using h1)
  rw [← map_natCast (IsLocalRing.residue v.integers), h2, map_zero]

omit [IsCurve k f] [Smooth f] [IsProper f] in
include f in
/-- **The residue cardinalities are divisible by the characteristic**: `p ∣ q_v`. -/
public theorem ringChar_dvd_residueCard (v : Place X.functionField) :
    ringChar k ∣ Place.residueCard v := by
  by_cases h : Place.residueCard v = 0
  · simp [h]
  have : Finite (IsLocalRing.ResidueField v.integers) := Nat.finite_of_card_ne_zero h
  let := Fintype.ofFinite (IsLocalRing.ResidueField v.integers)
  have hp : (ringChar k).Prime := CharP.char_is_prime k (ringChar k)
  have : CharP (IsLocalRing.ResidueField v.integers) (ringChar k) :=
    (CharP.charP_iff_prime_eq_zero hp).2 (natCast_ringChar_residueField f v)
  obtain ⟨n, -, hn⟩ := FiniteField.card (IsLocalRing.ResidueField v.integers) (ringChar k)
  rw [Place.residueCard, Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self _ n.ne_zero

include f in
/-- **No `p`-adic representation matches a `p`-adic unit `u_v`.** Let `ℓ = p` be the
characteristic of `k`, `E` a finite extension of `ℚ_p`, `j : E → Ω` a `ℚ_p`-embedding into a
field `Ω` over `ℚ_p`, and `ρ : π₁(X) → GL₂(E)` continuous. If `u_v` is a unit of the integral
closure of `ℤ_p` in `Ω` at one place `v`, then `u_v ≠ q_v⁻¹ det ρ(F_v)`, so `ρ` is not compatible
with `(t, u)`. In particular, for `ℓ = p` the conclusion of Stacks Theorem 03VT fails for every
eigenform satisfying its hypothesis `u_v ∈ Z̄_p^*`. -/
public theorem not_isFrobeniusCompatible_of_eq_ringChar [ConnectedSpace X]
    (base : GeometricPoint X) {ℓ : ℕ} [Fact ℓ.Prime] (hℓ : ℓ = ringChar k)
    {Ω : Type*} [Field Ω] [Algebra ℚ_[ℓ] Ω] [Algebra ℤ_[ℓ] Ω] [IsScalarTower ℤ_[ℓ] ℚ_[ℓ] Ω]
    (E : TopologicalFieldExtension ℚ_[ℓ]) (j : E.carrier →ₐ[ℚ_[ℓ]] Ω)
    (ρ : EtaleFundamentalGroup X base →* GL (Fin 2) E.carrier)
    (hρ : Continuous fun g => (ρ g : Matrix (Fin 2) (Fin 2) E.carrier))
    (t u : Place X.functionField → Ω) (v : Place X.functionField)
    (hu : ∃ w : (integralClosure ℤ_[ℓ] Ω)ˣ, ((w : integralClosure ℤ_[ℓ] Ω) : Ω) = u v) :
    ¬ IsFrobeniusCompatible base ρ j.toRingHom t u := by
  intro hc
  obtain ⟨F, hF⟩ := exists_isGeometricFrobeniusAt f base v
  obtain ⟨-, hdet⟩ := hc v F hF
  obtain ⟨w, hw⟩ := hu
  let : Algebra ℤ_[ℓ] E.carrier := Algebra.compHom _ (algebraMap ℤ_[ℓ] ℚ_[ℓ])
  have : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] E.carrier := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := compactSpace_etaleFundamentalGroup X base
  have : IsTopologicalRing E.carrier := IsModuleTopology.isTopologicalRing ℚ_[ℓ] E.carrier
  let D := Matrix.GeneralLinearGroup.det.comp ρ
  have hD : ∀ g, ((D g : E.carrierˣ) : E.carrier) =
      Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E.carrier) := fun g =>
    Matrix.GeneralLinearGroup.val_det_apply _
  let C := Set.range fun g => Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E.carrier)
  have hC : IsCompact C := isCompact_range hρ.matrix_det
  have hdet_int : ∀ g, IsIntegral ℤ_[ℓ] (Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E.carrier)) :=
    fun g => isIntegral_of_pow_mem_of_isCompact hC fun n =>
      ⟨g ^ n, by beta_reduce; rw [← hD, ← hD, map_pow, Units.val_pow_eq_pow_val]⟩
  set a := Matrix.det (ρ F : Matrix (Fin 2) (Fin 2) E.carrier) with ha_def
  have hainv : IsIntegral ℤ_[ℓ] a⁻¹ := by
    have h := hdet_int F⁻¹
    rwa [← hD, map_inv, Units.val_inv_eq_inv_val, hD] at h
  have ha0 : a ≠ 0 := by rw [ha_def, ← hD]; exact (D F).ne_zero
  have hja : IsIntegral ℤ_[ℓ] (j a⁻¹) := hainv.map (j.restrictScalars ℤ_[ℓ])
  have huint : IsIntegral ℤ_[ℓ] (u v) := hw ▸ (w : integralClosure ℤ_[ℓ] Ω).2
  have hu0 : u v ≠ 0 := by
    rw [← hw]
    exact fun h => w.ne_zero (Subtype.ext h)
  set q := Place.residueCard v
  have hq0 : q ≠ 0 := by
    rintro hq
    apply hu0
    rw [hdet, hq, Nat.cast_zero, inv_zero, zero_mul]
  have hqinv : ((q : Ω))⁻¹ = u v * j a⁻¹ := by
    have hja0 : j a ≠ 0 := (map_ne_zero j).2 ha0
    rw [map_inv₀, hdet]
    change (q : Ω)⁻¹ = (q : Ω)⁻¹ * j a * (j a)⁻¹
    rw [mul_assoc, mul_inv_cancel₀ hja0, mul_one]
  have hint : IsIntegral ℤ_[ℓ] (algebraMap ℚ_[ℓ] Ω ((q : ℚ_[ℓ]))⁻¹) := by
    rw [map_inv₀, map_natCast, hqinv]
    exact huint.mul hja
  have hint' : IsIntegral ℤ_[ℓ] ((q : ℚ_[ℓ]))⁻¹ :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ_[ℓ] Ω).restrictScalars ℤ_[ℓ])
      (algebraMap ℚ_[ℓ] Ω).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  have hle : ‖((q : ℚ_[ℓ]))⁻¹‖ ≤ 1 := hy ▸ y.norm_le_one
  have hlt : ‖(q : ℚ_[ℓ])‖ < 1 :=
    Padic.norm_natCast_lt_one_iff.2 (hℓ ▸ ringChar_dvd_residueCard f v)
  have hqne : (q : ℚ_[ℓ]) ≠ 0 := by exact_mod_cast hq0
  rw [norm_inv] at hle
  exact absurd (one_lt_inv₀ (norm_pos_iff.2 hqne) |>.2 hlt) (not_lt.2 hle)

end Curve

end Stacks.Drinfeld

end
