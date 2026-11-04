module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFibreCharpoly

/-!
# Purity of the Fourier family from equal absolute values and duality

Laumon's purity (in absolute value) of the fibres `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))`,
`Stacks.EtaleCohomology.LaumonFibrePurityInput` (Kedlaya, *Fourier
transforms and p-adic Weil II*, Theorem 6.4 "fourpur"), splits into two statements about the
Frobenius roots `z` (along `ι'`) of a fibre over `k'`, `#k' = q`:

* **equal absolute values** (`Stacks.EtaleCohomology.LaumonFibreEquinorm`): all roots have the
  same absolute value. For `a ≠ 0` the family in `c` is the Fourier transform of
  `ℱ_σ ⊗ L_ψ(a xⁿ)`, absolutely irreducible on its lisse locus, and `ι'`-real together with
  the transform of the dual; by Weil II 1.5.1 it is pure of some weight there. This holds off a
  curve `D = 0` containing `a = 0` and the complement of the lisse locus
  (`Stacks.EtaleCohomology.LaumonFourierEquinormInput`).
* **duality with complex conjugation** (`Stacks.EtaleCohomology.LaumonFibreReciprocal`): the
  roots are nonzero and `z ↦ q ^ (β + 1) / z̄` permutes them. Poincaré duality pairs the fibre
  with the fibre of `σ^∨ ⊗ L_ψ(-(a xⁿ + c x))` into `ℚ_ℓ(-1)` (no local terms at `∞`, so
  `H¹_c = H¹`), whose roots are `q ^ (-β) z̄` by the trace formula and the `ι'`-purity of `σ`.
  This holds for `a ≠ 0` (`Stacks.EtaleCohomology.LaumonFibreReciprocityInput`).

Together they force `‖z‖ ^ 2 = q ^ (β + 1)`
(`Stacks.EtaleCohomology.norm_eq_rpow_of_forall_isRoot_div_conj`), which gives
`Stacks.EtaleCohomology.laumonFibrePurityInput_of_equinorm_reciprocity` with
`D = a · D₁`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFibreEquinorm`, `Stacks.EtaleCohomology.LaumonFibreReciprocal`.
* `Stacks.EtaleCohomology.LaumonFourierEquinormInput`,
  `Stacks.EtaleCohomology.LaumonFibreReciprocityInput`.

## Main results

* `Stacks.EtaleCohomology.norm_eq_rpow_of_forall_isRoot_div_conj`.
* `Stacks.EtaleCohomology.laumonFibrePure_of_equinorm_of_reciprocal`.
* `Stacks.EtaleCohomology.laumonFibrePurityInput_of_equinorm_reciprocity`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix

universe u

namespace Stacks.EtaleCohomology

/-- **Equal absolute values and the symmetry `z ↦ Q / z̄` force `‖z‖ = √Q`**: if all roots of
`P` have the same absolute value, and for every root `z` of `P` we have `z ≠ 0` and
`q ^ w / z̄` is a root, then every root has absolute value `q ^ (w / 2)`. -/
public theorem norm_eq_rpow_of_forall_isRoot_div_conj {P : Polynomial ℂ} {q : ℕ} {w : ℤ}
    (hR : ∃ R : ℝ, ∀ z : ℂ, P.IsRoot z → ‖z‖ = R)
    (hrec : ∀ z : ℂ, P.IsRoot z → z ≠ 0 ∧ P.IsRoot ((q : ℂ) ^ w / starRingEnd ℂ z))
    (z : ℂ) (hz : P.IsRoot z) : ‖z‖ = (q : ℝ) ^ ((w : ℝ) / 2) := by
  obtain ⟨R, hR⟩ := hR
  obtain ⟨hz0, hz'⟩ := hrec z hz
  have h0 := hR z hz
  have h1 := hR _ hz'
  rw [norm_div, norm_zpow, Complex.norm_natCast, Complex.norm_conj, h0] at h1
  have hRpos : 0 < R := h0 ▸ norm_pos_iff.2 hz0
  have hsq : R * R = (q : ℝ) ^ w := ((div_eq_iff hRpos.ne').1 h1).symm
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  calc ‖z‖ = R := h0
    _ = Real.sqrt (R * R) := (Real.sqrt_mul_self hRpos.le).symm
    _ = ((q : ℝ) ^ (w : ℝ)) ^ ((1 : ℝ) / 2) := by
      rw [hsq, Real.sqrt_eq_rpow, Real.rpow_intCast]
    _ = (q : ℝ) ^ ((w : ℝ) / 2) := by
      rw [← Real.rpow_mul hq]
      ring_nf

section Fibre

open Polynomial

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [ConnectedSpace U.1]
  (k : Type u) [Field k] [Fintype k] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
  (x : GeometricPoint U.1) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (ι' : E →+* ℂ) (β : ℤ) (ψ : AddChar k E) (n : ℕ)

/-- **The fibres off `D = 0` have Frobenius roots of a single absolute value** along `ι'`
(pointwise purity of some weight). -/
public def LaumonFibreEquinorm (D : MvPolynomial (Fin 2) k) : Prop :=
  LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D fun _ P =>
    ∃ R : ℝ, ∀ z : ℂ, (P.map ι').IsRoot z → ‖z‖ = R

/-- **Duality with complex conjugation on the fibres off `D = 0`**: over `k'` with `#k' = q`,
the Frobenius roots `z` along `ι'` are nonzero and `q ^ (β + 1) / z̄` is again a root. -/
public def LaumonFibreReciprocal (D : MvPolynomial (Fin 2) k) : Prop :=
  LaumonFibreCharpoly B U ℓ k e x E b σ ψ n D fun q P =>
    ∀ z : ℂ, (P.map ι').IsRoot z →
      z ≠ 0 ∧ (P.map ι').IsRoot ((q : ℂ) ^ (β + 1) / starRingEnd ℂ z)

variable {B U ℓ k e x E b σ ι' β ψ n}

omit [Fintype k] in
/-- **Purity of the fibres off `a · D₁ = 0`** from equal absolute values off `D₁ = 0` and
duality with complex conjugation off `a = 0`. -/
public theorem laumonFibrePure_of_equinorm_of_reciprocal [Finite k] {D₁ : MvPolynomial (Fin 2) k}
    (h₁ : LaumonFibreEquinorm B U ℓ k e x E b σ ι' ψ n D₁)
    (h₂ : LaumonFibreReciprocal B U ℓ k e x E b σ ι' β ψ n (MvPolynomial.X 0)) :
    LaumonFibrePure B U ℓ k e x E b σ ι' β ψ n (MvPolynomial.X 0 * D₁) := by
  have := Fintype.ofFinite k
  exact LaumonFibreCharpoly.of_and h₁ h₂
    (fun k' _ _ a c h => by
      rw [map_mul, map_mul] at h
      exact ⟨right_ne_zero_of_mul h, left_ne_zero_of_mul h⟩)
    (fun _ _ hR hrec z hz => norm_eq_rpow_of_forall_isRoot_div_conj hR hrec z hz)

end Fibre

/-- **Equal absolute values of the Fourier family off a curve** (Laumon; Kedlaya, *Fourier
transforms and p-adic Weil II*, Theorem 6.4, first half): for `σ` as in
`Stacks.EtaleCohomology.LaumonFibrePurityInput` and `ψ ≠ 1` there is `N` such that for
`n > N` prime to `p` the fibres `H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` have Frobenius roots of a single
absolute value off a curve `D = 0`. For `a ≠ 0` the family in `c` is the Fourier transform of
`ℱ_σ ⊗ L_ψ(a xⁿ)`, absolutely irreducible on its lisse locus, and `ι'`-real together with
the transform of the dual; Weil II 1.5.1 makes it pure of some weight there. -/
public def LaumonFourierEquinormInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      ∃ D : MvPolynomial (Fin 2) k, D ≠ 0 ∧ LaumonFibreEquinorm B U ℓ k e x E b σ ι' ψ n D

/-- **Duality with complex conjugation on the Fourier family** (Kedlaya, *Fourier transforms and
p-adic Weil II*, proof of Theorem 6.4): for `σ` as in
`Stacks.EtaleCohomology.LaumonFibrePurityInput` and `ψ ≠ 1` there is `N` such that for
`n > N` prime to `p` and `a ≠ 0` the Frobenius roots `z` of the fibre
`H¹_c(𝔸¹, ℱ_σ ⊗ L_ψ(a xⁿ + c x))` over `k'` (`#k' = q`) are nonzero and `z ↦ q ^ (β + 1) / z̄`
permutes them: there are no local terms at `∞` (Artin–Schreier inertia), so Poincaré duality
pairs the fibre perfectly with that of `σ^∨ ⊗ L_ψ(-(a xⁿ + c x))`, whose roots are `q ^ (-β) z̄`
by the trace formula and the `ι'`-purity of `σ`. -/
public def LaumonFibreReciprocityInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
        (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      LaumonFibreReciprocal B U ℓ k e x E b σ ι' β ψ n (MvPolynomial.X 0)

/-- **Purity of the Fourier family from equal absolute values and duality**:
`Stacks.EtaleCohomology.LaumonFourierEquinormInput` and
`Stacks.EtaleCohomology.LaumonFibreReciprocityInput` imply
`Stacks.EtaleCohomology.LaumonFibrePurityInput`, with the curve `a · D₁ = 0`. -/
public theorem laumonFibrePurityInput_of_equinorm_reciprocity
    (hE : LaumonFourierEquinormInput.{u}) (hR : LaumonFibreReciprocityInput.{u}) :
    LaumonFibrePurityInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ he j kbar _ _ _ _ p n _ _ hcard hℓp x E _ _ _ d b
    m σ hσ K _ _ _ hirr hζ ι' β _ hpure ψ hψ
  obtain ⟨N₁, h₁⟩ := hE B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ
  obtain ⟨N₂, h₂⟩ := hR B U ℓ k f e he j kbar p n hcard hℓp x E b σ hσ K hirr hζ ι' β hpure ψ hψ
  refine ⟨max N₁ N₂, fun n' hn' hpn' => ?_⟩
  obtain ⟨D, hD, hDe⟩ := h₁ n' (lt_of_le_of_lt (le_max_left _ _) hn') hpn'
  exact ⟨MvPolynomial.X 0 * D, mul_ne_zero (MvPolynomial.X_ne_zero _) hD,
    laumonFibrePure_of_equinorm_of_reciprocal hDe
      (h₂ n' (lt_of_le_of_lt (le_max_right _ _) hn') hpn')⟩

end Stacks.EtaleCohomology

end
