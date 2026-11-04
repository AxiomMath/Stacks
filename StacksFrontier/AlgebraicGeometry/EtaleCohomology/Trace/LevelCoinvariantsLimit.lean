module

public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RankinTraceFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.IntegralModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationLevels
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Coinvariants of the levels of an integral representation

Let `ρ : Γ → GL_r(ℤ_ℓ)` be a representation, `H ⊆ Γ` a normal subgroup and
`N = (ℤ_ℓ^r)_H` the module of `H`-coinvariants. This file relates `N` to the coinvariants
`C_k = ((ℤ/ℓ^k)^r)_H` of the reductions of `ρ` and to the coinvariants of `ρ ⊗ ℚ_ℓ`:

* reduction `N → C_k` is surjective with kernel `ℓ^k N`;
* `N → (ℚ_ℓ^r)_H` is a base change along `ℤ_ℓ → ℚ_ℓ`;
* all these maps intertwine the action of an element `φ` of `Γ`.

An `ℓ`-adically complete module `M` is the limit of its quotient tower `n ↦ M ⧸ ℓ^{n+1} M`, and a
tower whose levels are isomorphic to those of the quotient tower of a finite `ℤ_ℓ`-module,
compatibly with endomorphisms, is isomorphic to that quotient tower. Consequently a tower `S` of
this kind over `N` has `ℚ_ℓ ⊗ lim S ≅ (ℚ_ℓ^r)_H`, compatibly with the action of `φ`.

## Main definitions

All names are in the namespace `Stacks.EtaleCohomology`.

* `integralCoinvariantsReduction`: the reduction `(ℤ_ℓ^r)_H → ((ℤ/ℓ^k)^r)_H`.
* `integralCoinvariantsRationalization`: the map `(ℤ_ℓ^r)_H → (ℚ_ℓ^r)_H`.
* `rationalCoinvariantsConjEquiv`: conjugation by `P` identifies the coinvariants of `P⁻¹ τ P`
  with those of `τ`.
* `padicQuotientTower`: the tower `n ↦ M ⧸ ℓ^{n+1} M`.
* `isLimitPadicQuotientCone`: an `ℓ`-adically complete module is the limit of its quotient tower.

## Main results

* `surjective_integralCoinvariantsReduction`, `ker_integralCoinvariantsReduction`: reduction of
  coinvariants is surjective with kernel `ℓ^k N`.
* `isBaseChange_integralCoinvariantsRationalization`: `(ℚ_ℓ^r)_H` is the base change of
  `(ℤ_ℓ^r)_H` along `ℤ_ℓ → ℚ_ℓ`.
* `exists_iso_padicQuotientTower_of_levels`: a tower whose levels are compatibly isomorphic to
  those of the quotient tower of a finite `ℤ_ℓ`-module is isomorphic to that quotient tower.
* `exists_extendScalars_limit_linearEquiv_coinvariants`: `ℚ_ℓ ⊗ lim S ≅ (ℚ_ℓ^r)_H`, compatibly
  with the action of `φ`.

## References

* [Stacks Project, Tag 03VL](https://stacks.math.columbia.edu/tag/03VL)
-/

@[expose] public noncomputable section

open Representation Matrix CategoryTheory CategoryTheory.Limits

namespace Stacks.EtaleCohomology

variable {Γ : Type*} [Group Γ] (H : Subgroup Γ) {ℓ : ℕ} [Fact ℓ.Prime] {r : ℕ}
  (ρ : Γ →* GL (Fin r) ℤ_[ℓ])

/-! ### Reduction modulo `ℓ ^ k` -/

/-- The coordinatewise reduction `ℤ_ℓ^r → (ℤ/ℓ^k)^r`, semilinear over `ℤ_ℓ → ℤ/ℓ^k`. -/
def padicVecReduction (k : ℕ) :
    (Fin r → ℤ_[ℓ]) →ₛₗ[PadicInt.toZModPow (p := ℓ) k] (Fin r → ZMod (ℓ ^ k)) where
  toFun v i := PadicInt.toZModPow k (v i)
  map_add' _ _ := funext fun _ => map_add _ _ _
  map_smul' _ _ := funext fun _ => map_mul _ _ _

/-- The coordinates of `padicVecReduction k v` are the reductions of those of `v`. -/
theorem padicVecReduction_apply (k : ℕ) (v : Fin r → ℤ_[ℓ]) (i : Fin r) :
    padicVecReduction (ℓ := ℓ) k v i = PadicInt.toZModPow k (v i) :=
  rfl

/-- The reduction `ℤ_ℓ^r → (ℤ/ℓ^k)^r` is surjective. -/
theorem surjective_padicVecReduction (k : ℕ) :
    Function.Surjective (padicVecReduction (ℓ := ℓ) (r := r) k) := fun w =>
  ⟨fun i => (ZMod.ringHom_surjective (PadicInt.toZModPow k) (w i)).choose,
    funext fun i => (ZMod.ringHom_surjective (PadicInt.toZModPow k) (w i)).choose_spec⟩

/-- Reduction modulo `ℓ ^ k` intertwines `ρ` with its reduction `levelRepresentation ρ k`. -/
theorem padicVecReduction_matrixRepresentation (k : ℕ) (g : Γ) (v : Fin r → ℤ_[ℓ]) :
    padicVecReduction k (matrixRepresentation ρ g v) =
      levelRepresentation ρ k g (padicVecReduction k v) := by
  funext i
  simp only [padicVecReduction_apply, matrixRepresentation_apply, levelRepresentation_apply,
    Matrix.mulVec, dotProduct, map_sum, map_mul]
  rfl

/-- The `H`-coinvariants `(ℤ_ℓ^r)_H` of an integral representation. -/
abbrev integralCoinvariants := Coinvariants ((matrixRepresentation ρ).comp H.subtype)

/-- The `H`-coinvariants `((ℤ/ℓ^k)^r)_H` of the reduction of an integral representation. -/
abbrev levelCoinvariants (k : ℕ) := Coinvariants ((levelRepresentation ρ k).comp H.subtype)

/-- Reduction modulo `ℓ ^ k` maps the integral coinvariant kernel into the level one. -/
theorem coinvariantsKer_le_comap_padicVecReduction (k : ℕ) :
    Coinvariants.ker ((matrixRepresentation ρ).comp H.subtype) ≤
      (Coinvariants.ker ((levelRepresentation ρ k).comp H.subtype)).comap
        (padicVecReduction k) := by
  rw [Coinvariants.ker, Submodule.span_le]
  rintro _ ⟨⟨h, v⟩, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap]
  show padicVecReduction k (matrixRepresentation ρ (h : Γ) v - v) ∈
    Coinvariants.ker ((levelRepresentation ρ k).comp H.subtype)
  rw [map_sub, padicVecReduction_matrixRepresentation]
  exact Coinvariants.sub_mem_ker (ρ := (levelRepresentation ρ k).comp H.subtype) h _

/-- **Reduction of coinvariants** `(ℤ_ℓ^r)_H → ((ℤ/ℓ^k)^r)_H`. -/
def integralCoinvariantsReduction (k : ℕ) :
    integralCoinvariants H ρ →ₛₗ[PadicInt.toZModPow (p := ℓ) k] levelCoinvariants H ρ k :=
  Submodule.mapQ _ _ (padicVecReduction k) (coinvariantsKer_le_comap_padicVecReduction H ρ k)

/-- Reduction of coinvariants on the class of `v` is the class of the reduction of `v`. -/
theorem integralCoinvariantsReduction_mk (k : ℕ) (v : Fin r → ℤ_[ℓ]) :
    integralCoinvariantsReduction H ρ k (Coinvariants.mk _ v) =
      Coinvariants.mk _ (padicVecReduction k v) :=
  rfl

/-- **Reduction of coinvariants is surjective.** -/
theorem surjective_integralCoinvariantsReduction (k : ℕ) :
    Function.Surjective (integralCoinvariantsReduction H ρ k) := by
  intro y
  obtain ⟨w, rfl⟩ := Coinvariants.mk_surjective _ y
  obtain ⟨v, rfl⟩ := surjective_padicVecReduction (ℓ := ℓ) (r := r) k w
  exact ⟨Coinvariants.mk _ v, rfl⟩

/-- Every element of the level coinvariant kernel lifts to the integral one. -/
theorem exists_mem_coinvariantsKer_padicVecReduction_eq (k : ℕ) {y : Fin r → ZMod (ℓ ^ k)}
    (hy : y ∈ Coinvariants.ker ((levelRepresentation ρ k).comp H.subtype)) :
    ∃ u ∈ Coinvariants.ker ((matrixRepresentation ρ).comp H.subtype),
      padicVecReduction k u = y := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨⟨h, w⟩, rfl⟩ := hx
      obtain ⟨w', rfl⟩ := surjective_padicVecReduction (ℓ := ℓ) (r := r) k w
      refine ⟨matrixRepresentation ρ h w' - w',
        Coinvariants.sub_mem_ker (ρ := (matrixRepresentation ρ).comp H.subtype) h w', ?_⟩
      rw [map_sub, padicVecReduction_matrixRepresentation]
      rfl
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add x y _ _ hx hy =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨u', hu', rfl⟩ := hy
      exact ⟨u + u', Submodule.add_mem _ hu hu', map_add _ _ _⟩
  | smul c x _ hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨c', rfl⟩ := ZMod.ringHom_surjective (PadicInt.toZModPow (p := ℓ) k) c
      exact ⟨c' • u, Submodule.smul_mem _ c' hu, map_smulₛₗ _ _ _⟩

open Pointwise in
/-- **The kernel of reduction of coinvariants is `ℓ^k N`.** -/
theorem ker_integralCoinvariantsReduction (k : ℕ) :
    LinearMap.ker (integralCoinvariantsReduction H ρ k) =
      ((ℓ : ℤ_[ℓ]) ^ k) • (⊤ : Submodule ℤ_[ℓ] (integralCoinvariants H ρ)) := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · intro hx
    obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
    rw [integralCoinvariantsReduction_mk, Coinvariants.mk_eq_zero] at hx
    obtain ⟨u, hu, huv⟩ := exists_mem_coinvariantsKer_padicVecReduction_eq H ρ k hx
    have hd : ∀ i, (v - u) i ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ k} := fun i => by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, Pi.sub_apply, map_sub]
      have h1 := congrFun huv i
      rw [padicVecReduction_apply, padicVecReduction_apply] at h1
      rw [h1, sub_self]
    choose t ht using fun i => Ideal.mem_span_singleton'.1 (hd i)
    refine ⟨Coinvariants.mk _ t, Submodule.mem_top, ?_⟩
    rw [← map_smul]
    refine (Coinvariants.mk_eq_iff _).mpr ?_
    have hneg : (ℓ : ℤ_[ℓ]) ^ k • t - v = -u := by
      funext i
      have h := ht i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.neg_apply] at h ⊢
      rw [mul_comm, h]
      ring
    rw [hneg]
    exact Submodule.neg_mem _ hu
  · rintro ⟨y, -, rfl⟩
    rw [map_smulₛₗ, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_smul]

/-! ### Rationalization -/

/-- An integral representation read over `ℚ_ℓ`. -/
abbrev rationalGL : Γ →* GL (Fin r) ℚ_[ℓ] :=
  (Matrix.GeneralLinearGroup.map (PadicInt.Coe.ringHom (p := ℓ))).comp ρ

/-- The `H`-coinvariants `(ℚ_ℓ^r)_H` of an integral representation read over `ℚ_ℓ`. -/
abbrev rationalCoinvariants := Coinvariants ((matrixRepresentation (rationalGL ρ)).comp H.subtype)

/-- The `ℤ_ℓ`-module structure of `(ℚ_ℓ^r)_H` by restriction of scalars. -/
instance instModulePadicIntRationalCoinvariants : Module ℤ_[ℓ] (rationalCoinvariants H ρ) :=
  inferInstanceAs (Module ℤ_[ℓ] ((Fin r → ℚ_[ℓ]) ⧸
    Coinvariants.ker ((matrixRepresentation (rationalGL ρ)).comp H.subtype)))

/-- The `ℤ_ℓ`- and `ℚ_ℓ`-actions on `(ℚ_ℓ^r)_H` form a scalar tower. -/
instance instIsScalarTowerPadicIntRationalCoinvariants :
    IsScalarTower ℤ_[ℓ] ℚ_[ℓ] (rationalCoinvariants H ρ) :=
  inferInstanceAs (IsScalarTower ℤ_[ℓ] ℚ_[ℓ] ((Fin r → ℚ_[ℓ]) ⧸
    Coinvariants.ker ((matrixRepresentation (rationalGL ρ)).comp H.subtype)))

/-- The inclusion `ℤ_ℓ^r → ℚ_ℓ^r`. -/
abbrev padicVecInclusion : (Fin r → ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] (Fin r → ℚ_[ℓ]) :=
  (Algebra.linearMap ℤ_[ℓ] ℚ_[ℓ]).compLeft (Fin r)

/-- The inclusion `ℤ_ℓ^r → ℚ_ℓ^r` intertwines `ρ` with `rationalGL ρ`. -/
theorem padicVecInclusion_matrixRepresentation (g : Γ) (v : Fin r → ℤ_[ℓ]) :
    padicVecInclusion (matrixRepresentation ρ g v) =
      matrixRepresentation (rationalGL ρ) g (padicVecInclusion v) := by
  funext i
  simp only [padicVecInclusion, LinearMap.compLeft_apply, Function.comp_apply,
    Algebra.linearMap_apply, matrixRepresentation_apply, Matrix.mulVec, dotProduct, map_sum,
    map_mul]
  rfl

/-- **Rationalization of coinvariants** `(ℤ_ℓ^r)_H → (ℚ_ℓ^r)_H`. -/
def integralCoinvariantsRationalization :
    integralCoinvariants H ρ →ₗ[ℤ_[ℓ]] rationalCoinvariants H ρ :=
  Coinvariants.lift _ (((Coinvariants.mk _).restrictScalars ℤ_[ℓ]) ∘ₗ padicVecInclusion)
    fun h => LinearMap.ext fun v => by
      change Coinvariants.mk _ (padicVecInclusion (matrixRepresentation ρ (h : Γ) v)) =
        Coinvariants.mk _ (padicVecInclusion v)
      rw [padicVecInclusion_matrixRepresentation]
      exact Coinvariants.mk_self_apply ((matrixRepresentation (rationalGL ρ)).comp H.subtype) h _

/-- Rationalization of coinvariants on the class of `v` is the class of the image of `v`. -/
theorem integralCoinvariantsRationalization_mk (v : Fin r → ℤ_[ℓ]) :
    integralCoinvariantsRationalization H ρ (Coinvariants.mk _ v) =
      Coinvariants.mk _ (padicVecInclusion v) :=
  rfl

/-- The generators `ρ(h) v - v` of the coinvariant kernel, indexed by `H × ℤ_ℓ^r`. -/
abbrev integralCoinvariantsGenerators : (H × (Fin r → ℤ_[ℓ]) →₀ ℤ_[ℓ]) →ₗ[ℤ_[ℓ]] (Fin r → ℤ_[ℓ]) :=
  Finsupp.linearCombination ℤ_[ℓ] fun hv => matrixRepresentation ρ (hv.1 : Γ) hv.2 - hv.2

/-- The same generators over `ℚ_ℓ`, still indexed by `H × ℤ_ℓ^r`. -/
abbrev rationalCoinvariantsGenerators : (H × (Fin r → ℤ_[ℓ]) →₀ ℚ_[ℓ]) →ₗ[ℚ_[ℓ]] (Fin r → ℚ_[ℓ]) :=
  Finsupp.linearCombination ℚ_[ℓ] fun hv =>
    matrixRepresentation (rationalGL ρ) (hv.1 : Γ) (padicVecInclusion hv.2) - padicVecInclusion hv.2

/-- The rational generators span the coinvariant kernel of `rationalGL ρ`. -/
theorem range_rationalCoinvariantsGenerators :
    LinearMap.range (rationalCoinvariantsGenerators H ρ) =
      Coinvariants.ker ((matrixRepresentation (rationalGL ρ)).comp H.subtype) := by
  rw [Finsupp.range_linearCombination, Coinvariants.ker]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨h, v⟩, rfl⟩
    exact Submodule.subset_span ⟨(h, padicVecInclusion v), rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨h, w⟩, rfl⟩
    obtain ⟨⟨b, hb⟩, hw⟩ := IsLocalization.exist_integer_multiples_of_finite
      (nonZeroDivisors ℤ_[ℓ]) w
    choose v hv using hw
    have hb0 : (algebraMap ℤ_[ℓ] ℚ_[ℓ] b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hwv : w = (algebraMap ℤ_[ℓ] ℚ_[ℓ] b)⁻¹ • padicVecInclusion v := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, padicVecInclusion, LinearMap.compLeft_apply,
        Function.comp_apply, Algebra.linearMap_apply, hv i, Algebra.smul_def]
      field_simp
    rw [hwv]
    show matrixRepresentation (rationalGL ρ) (h : Γ)
        ((algebraMap ℤ_[ℓ] ℚ_[ℓ] b)⁻¹ • padicVecInclusion v) -
      (algebraMap ℤ_[ℓ] ℚ_[ℓ] b)⁻¹ • padicVecInclusion v ∈ _
    rw [map_smul, ← smul_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(h, v), rfl⟩)

/-- The integral generators span the coinvariant kernel of `ρ`. -/
theorem range_integralCoinvariantsGenerators :
    LinearMap.range (integralCoinvariantsGenerators H ρ) =
      Coinvariants.ker ((matrixRepresentation ρ).comp H.subtype) := by
  rw [Finsupp.range_linearCombination, Coinvariants.ker]
  rfl

/-- **`(ℚ_ℓ^r)_H` is the base change of `(ℤ_ℓ^r)_H` along `ℤ_ℓ → ℚ_ℓ`.** -/
theorem isBaseChange_integralCoinvariantsRationalization :
    IsBaseChange ℚ_[ℓ] (integralCoinvariantsRationalization H ρ) := by
  classical
  refine IsBaseChange.of_right_exact ℚ_[ℓ]
    (Finsupp.mapRange.linearMap (α := H × (Fin r → ℤ_[ℓ])) (Algebra.linearMap ℤ_[ℓ] ℚ_[ℓ]))
    padicVecInclusion (integralCoinvariantsRationalization H ρ)
    (f := integralCoinvariantsGenerators H ρ) (g := Coinvariants.mk _)
    (f' := rationalCoinvariantsGenerators H ρ) (g' := Coinvariants.mk _) ?_ ?_
    (IsBaseChange.finsuppPow _ (IsBaseChange.linearMap ℤ_[ℓ] ℚ_[ℓ]))
    (IsBaseChange.finitePow (Fin r) (IsBaseChange.linearMap ℤ_[ℓ] ℚ_[ℓ])) ?_
    (Coinvariants.mk_surjective _) ?_ (Coinvariants.mk_surjective _)
  · refine Finsupp.lhom_ext fun hv c => ?_
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single, map_smul,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, map_sub, padicVecInclusion_matrixRepresentation]
    rw [algebra_compatible_smul ℚ_[ℓ] c]
  · exact LinearMap.ext fun v => rfl
  · intro y
    rw [Coinvariants.mk_eq_zero, ← range_integralCoinvariantsGenerators]
    exact Iff.rfl
  · intro y
    rw [Coinvariants.mk_eq_zero, ← range_rationalCoinvariantsGenerators]
    exact Iff.rfl

/-! ### The action of an element of `Γ` -/

variable [H.Normal] (φ : Γ)

/-- The action of `φ` on the level coinvariants `((ℤ/ℓ^k)^r)_H`. -/
abbrev levelCoinvariantsFrobenius (k : ℕ) : Module.End (ZMod (ℓ ^ k)) (levelCoinvariants H ρ k) :=
  coinvariantsFrobenius H (levelMatrixRepresentation ρ k) φ

/-- Reduction of coinvariants intertwines the actions of `φ`. -/
theorem integralCoinvariantsReduction_coinvariantsFrobenius (k : ℕ) (x : integralCoinvariants H ρ) :
    integralCoinvariantsReduction H ρ k (coinvariantsFrobenius H ρ φ x) =
      levelCoinvariantsFrobenius H ρ φ k (integralCoinvariantsReduction H ρ k x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  show Coinvariants.mk _ (padicVecReduction k (matrixRepresentation ρ φ v)) =
    Coinvariants.mk _ (levelRepresentation ρ k φ (padicVecReduction k v))
  rw [padicVecReduction_matrixRepresentation]

/-- Rationalization of coinvariants intertwines the actions of `φ`. -/
theorem integralCoinvariantsRationalization_coinvariantsFrobenius (x : integralCoinvariants H ρ) :
    integralCoinvariantsRationalization H ρ (coinvariantsFrobenius H ρ φ x) =
      coinvariantsFrobenius H (rationalGL ρ) φ (integralCoinvariantsRationalization H ρ x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  show Coinvariants.mk _ (padicVecInclusion (matrixRepresentation ρ φ v)) =
    Coinvariants.mk _ (matrixRepresentation (rationalGL ρ) φ (padicVecInclusion v))
  rw [padicVecInclusion_matrixRepresentation]

/-! ### Conjugation -/

section Conj

variable {ρ} (τ : Γ →* GL (Fin r) ℚ_[ℓ]) (P : GL (Fin r) ℚ_[ℓ])
  (hP : ∀ g, rationalGL ρ g = P⁻¹ * τ g * P)

include hP

/-- Multiplication by `P` intertwines `rationalGL ρ` with `τ`. -/
theorem mulVec_matrixRepresentation_rationalGL (g : Γ) (v : Fin r → ℚ_[ℓ]) :
    (P : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ matrixRepresentation (rationalGL ρ) g v =
      matrixRepresentation τ g ((P : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ v) := by
  rw [matrixRepresentation_apply, matrixRepresentation_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hP g, Units.val_mul, Units.val_mul, ← mul_assoc, ← mul_assoc,
    Units.mul_inv, one_mul]

/-- Multiplication by `P⁻¹` intertwines `τ` with `rationalGL ρ`. -/
theorem inv_mulVec_matrixRepresentation (g : Γ) (v : Fin r → ℚ_[ℓ]) :
    ((P⁻¹ : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ matrixRepresentation τ g v =
      matrixRepresentation (rationalGL ρ) g
        (((P⁻¹ : GL (Fin r) ℚ_[ℓ]) : Matrix (Fin r) (Fin r) ℚ_[ℓ]) *ᵥ v) := by
  rw [matrixRepresentation_apply, matrixRepresentation_apply, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hP g]
  simp only [Units.val_mul, mul_assoc, Units.mul_inv, mul_one]

/-- **Conjugation by `P` identifies the coinvariants of `P⁻¹ τ P` with those of `τ`.** -/
def rationalCoinvariantsConjEquiv :
    rationalCoinvariants H ρ ≃ₗ[ℚ_[ℓ]] Coinvariants ((matrixRepresentation τ).comp H.subtype) :=
  LinearEquiv.ofLinear
    (Coinvariants.lift _ (Coinvariants.mk _ ∘ₗ Matrix.mulVecLin P.val)
      fun h => LinearMap.ext fun v => by
        change Coinvariants.mk _ (P.val *ᵥ matrixRepresentation (rationalGL ρ) h v) =
          Coinvariants.mk _ (P.val *ᵥ v)
        rw [mulVec_matrixRepresentation_rationalGL τ P hP]
        exact Coinvariants.mk_self_apply ((matrixRepresentation τ).comp H.subtype) h _)
    (Coinvariants.lift _ (Coinvariants.mk _ ∘ₗ
        Matrix.mulVecLin (P⁻¹).val)
      fun h => LinearMap.ext fun v => by
        change Coinvariants.mk _ ((P⁻¹).val *ᵥ
            matrixRepresentation τ h v) =
          Coinvariants.mk _ ((P⁻¹).val *ᵥ v)
        rw [inv_mulVec_matrixRepresentation τ P hP]
        exact Coinvariants.mk_self_apply ((matrixRepresentation (rationalGL ρ)).comp H.subtype) h _)
    (Coinvariants.hom_ext (LinearMap.ext fun v => by
      change Coinvariants.mk _ (P.val *ᵥ ((P⁻¹).val *ᵥ v)) =
        Coinvariants.mk _ v
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]))
    (Coinvariants.hom_ext (LinearMap.ext fun v => by
      change Coinvariants.mk _ ((P⁻¹).val *ᵥ (P.val *ᵥ v)) =
        Coinvariants.mk _ v
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]))

/-- Conjugation by `P` intertwines the actions of `φ` on the two coinvariant modules. -/
theorem rationalCoinvariantsConjEquiv_coinvariantsFrobenius (x : rationalCoinvariants H ρ) :
    rationalCoinvariantsConjEquiv H τ P hP (coinvariantsFrobenius H (rationalGL ρ) φ x) =
      coinvariantsFrobenius H τ φ (rationalCoinvariantsConjEquiv H τ P hP x) := by
  obtain ⟨v, rfl⟩ := Coinvariants.mk_surjective _ x
  show Coinvariants.mk _ (P.val *ᵥ matrixRepresentation (rationalGL ρ) φ v) =
    Coinvariants.mk _ (matrixRepresentation τ φ (P.val *ᵥ v))
  rw [mulVec_matrixRepresentation_rationalGL τ P hP]

end Conj

/-! ### Limits of the quotient towers of an `ℓ`-adically complete module -/

section Limit

universe v

variable (ℓ) in
/-- The ideal `(ℓ)` of `ℤ_ℓ`. -/
abbrev padicIdeal : Ideal ℤ_[ℓ] := Ideal.span {(ℓ : ℤ_[ℓ])}

omit [H.Normal] in
open Pointwise in
/-- The kernel of reduction of coinvariants is `(ℓ)^k N`. -/
theorem ker_integralCoinvariantsReduction' (k : ℕ) :
    LinearMap.ker (integralCoinvariantsReduction H ρ k) =
      padicIdeal ℓ ^ k • (⊤ : Submodule ℤ_[ℓ] (integralCoinvariants H ρ)) := by
  rw [ker_integralCoinvariantsReduction, Ideal.span_singleton_pow,
    Submodule.ideal_span_singleton_smul]

variable (M : ModuleCat.{v} ℤ_[ℓ])

/-- The transition `M ⧸ (ℓ)^{n+2} M → M ⧸ (ℓ)^{n+1} M`. -/
def padicQuotientTransition (n : ℕ) :
    ModuleCat.of ℤ_[ℓ] (M ⧸ (padicIdeal ℓ ^ (n + 1 + 1) • (⊤ : Submodule ℤ_[ℓ] M))) ⟶
      ModuleCat.of ℤ_[ℓ] (M ⧸ (padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M))) :=
  ModuleCat.ofHom (Submodule.factor
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))))

/-- **The tower `n ↦ M ⧸ ℓ^{n+1} M`.** -/
abbrev padicQuotientTower : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ] :=
  Functor.ofOpSequence (X := fun n =>
    ModuleCat.of ℤ_[ℓ] (M ⧸ (padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M))))
    (padicQuotientTransition M)

/-- The cone of quotient maps on the tower `n ↦ M ⧸ ℓ^{n+1} M`. -/
abbrev padicQuotientCone : Cone (padicQuotientTower M) where
  pt := M
  π := NatTrans.ofOpSequence (F := (Functor.const ℕᵒᵖ).obj M)
    (fun n => ModuleCat.ofHom (Submodule.mkQ _)) fun n => by
      ext x
      simp only [padicQuotientTower, Functor.ofOpSequence_map_homOfLE_succ]
      rfl

/-- The transition maps of the quotient tower send the class of `x` to the class of `x`. -/
theorem padicQuotientTower_map_apply {m n : ℕ} (h : m ≤ n) (x : M) :
    ((padicQuotientTower M).map (homOfLE h).op).hom (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk x :=
  congrArg (fun f => f.hom x) ((padicQuotientCone M).w (homOfLE h).op)

/-- **An `ℓ`-adically complete module is the limit of its quotient tower.** -/
def isLimitPadicQuotientCone [IsAdicComplete (padicIdeal ℓ) M] :
    IsLimit (padicQuotientCone M) := by
  refine isLimitOfReflects (forget (ModuleCat.{v} ℤ_[ℓ]))
    ((Types.isLimit_iff_bijective_sectionOfCone _).2 ⟨?_, ?_⟩).some
  · intro x y hxy
    change (M : Type v) at x y
    have h : ∀ n, x - y ≡ 0 [SMOD (padicIdeal ℓ ^ n • (⊤ : Submodule ℤ_[ℓ] M))] := by
      intro n
      have hn : (Submodule.Quotient.mk x :
          M ⧸ (padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M))) = Submodule.Quotient.mk y :=
        congrArg (fun s => s.1 (Opposite.op n)) hxy
      rw [Submodule.Quotient.eq] at hn
      rw [SModEq.sub_mem, sub_zero]
      exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) hn
    have hxy' : x = y := sub_eq_zero.1 (IsHausdorff.haus (I := padicIdeal ℓ) (M := M)
      IsAdicComplete.toIsHausdorff (x - y) h)
    exact hxy'
  · intro s
    let f : ℕ → M := fun n => (Submodule.Quotient.mk_surjective _ (s.1 (Opposite.op n))).choose
    have hf : ∀ n, (Submodule.Quotient.mk (f n) :
        M ⧸ (padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M))) = s.1 (Opposite.op n) := fun n =>
      (Submodule.Quotient.mk_surjective _ (s.1 (Opposite.op n))).choose_spec
    have hcompat : ∀ {m n : ℕ}, m ≤ n →
        f m ≡ f n [SMOD (padicIdeal ℓ ^ (m + 1) • (⊤ : Submodule ℤ_[ℓ] M))] := by
      intro m n hmn
      change (Submodule.Quotient.mk (f m) : M ⧸ _) = Submodule.Quotient.mk (f n)
      rw [hf m, ← s.2 (homOfLE hmn).op, ← hf n]
      exact padicQuotientTower_map_apply M hmn (f n)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := padicIdeal ℓ)
      (M := M)) (f := f) fun {m n} hmn => (hcompat hmn).mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ m)))
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    obtain ⟨n⟩ := n
    change (Submodule.Quotient.mk L : M ⧸ (padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M))) =
      s.1 (Opposite.op n)
    rw [← hf n]
    exact ((hcompat (Nat.le_succ n)).trans (hL (n + 1))).symm

/-- `ℤ_ℓ` is `(ℓ)`-adically complete. -/
theorem isAdicComplete_padicIdeal : IsAdicComplete (padicIdeal ℓ) ℤ_[ℓ] := by
  simpa [padicIdeal, PadicInt.maximalIdeal_eq_span_p] using
    (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal ℤ_[ℓ]) ℤ_[ℓ])

omit [H.Normal] in
/-- **`(ℤ_ℓ^r)_H` is `ℓ`-adically complete.** -/
theorem isAdicComplete_integralCoinvariants :
    IsAdicComplete (padicIdeal ℓ) (integralCoinvariants H ρ) := by
  have := isAdicComplete_padicIdeal (ℓ := ℓ)
  exact AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing _ _

variable {M} in
/-- The map of quotient towers induced by a linear map. -/
def padicQuotientTowerMap {M' : ModuleCat.{v} ℤ_[ℓ]} (ψ : M ⟶ M') :
    padicQuotientTower M ⟶ padicQuotientTower M' :=
  NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (Submodule.mapQ _ _ ψ.hom
      (Submodule.smul_top_le_comap_smul_top _ ψ.hom))) fun n => by
    ext x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [padicQuotientTower, Functor.ofOpSequence_map_homOfLE_succ]
    rfl

/-- The quotient maps intertwine a linear map with the induced map of quotient towers. -/
theorem padicQuotientCone_π_comp_padicQuotientTowerMap {M' : ModuleCat.{v} ℤ_[ℓ]} (ψ : M ⟶ M')
    (n : ℕᵒᵖ) :
    (padicQuotientCone M).π.app n ≫ (padicQuotientTowerMap ψ).app n =
      ψ ≫ (padicQuotientCone M').π.app n := by
  ext x
  rfl

/-! ### Compatible isomorphisms of levels (Kőnig) -/

section Koenig

variable {M}

open Pointwise in
/-- The kernel of `M ⧸ ℓ^{n+2} M → M ⧸ ℓ^{n+1} M` is `ℓ^{n+1} (M ⧸ ℓ^{n+2} M)`. -/
theorem ker_padicQuotientTransition (n : ℕ) :
    LinearMap.ker (padicQuotientTransition M n).hom =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (M ⧸ (padicIdeal ℓ ^ (n + 1 + 1) •
        (⊤ : Submodule ℤ_[ℓ] M)))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hy : y ∈ padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] M) :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    exact Submodule.smul_top_le_comap_smul_top (padicIdeal ℓ ^ (n + 1))
      (Submodule.mkQ (padicIdeal ℓ ^ (n + 1 + 1) • (⊤ : Submodule ℤ_[ℓ] M))) hy
  · rw [Submodule.smul_le]
    intro a ha x _
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (a • y) ∈ _
    rw [LinearMap.mem_ker]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)

/-- The levels of the quotient tower of a finite module are finite. -/
theorem finite_padicQuotientTower_obj [Module.Finite ℤ_[ℓ] M] (n : ℕ) :
    Finite ((padicQuotientTower M).obj (Opposite.op n)) := by
  let I := padicIdeal ℓ ^ (n + 1)
  have hI : I = RingHom.ker (PadicInt.toZModPow (p := ℓ) (n + 1)) := by
    rw [PadicInt.ker_toZModPow]
    exact Ideal.span_singleton_pow _ _
  have : Finite (ℤ_[ℓ] ⧸ I) := by
    rw [hI]
    exact Finite.of_equiv _ (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := ℓ) (n + 1)))).symm.toEquiv
  show Finite (M ⧸ I • (⊤ : Submodule ℤ_[ℓ] M))
  have : Module.Finite (ℤ_[ℓ] ⧸ I) (M ⧸ I • (⊤ : Submodule ℤ_[ℓ] M)) :=
    Module.Finite.of_restrictScalars_finite ℤ_[ℓ] _ _
  exact Module.finite_of_finite (ℤ_[ℓ] ⧸ I)

variable (M) in
/-- The isomorphisms of a level of `S` with a level of the quotient tower intertwining the
endomorphisms. -/
abbrev levelIsoSet (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (σ : S ⟶ S) (ψ : M ⟶ M) (n : ℕ) : Type v :=
  {e : S.obj (Opposite.op n) ≃ₗ[ℤ_[ℓ]] (padicQuotientTower M).obj (Opposite.op n) //
    ∀ x, e ((σ.app (Opposite.op n)).hom x) =
      ((padicQuotientTowerMap ψ).app (Opposite.op n)).hom (e x)}

open Pointwise in
/-- **Kőnig's lemma for the levels**: a tower `S` whose transitions are surjective with kernel
`ℓ^{n+1}`, with an endomorphism `σ`, all of whose levels are isomorphic to those of the quotient
tower of a finite `ℤ_ℓ`-module `M` compatibly with `σ` and `ψ`, is isomorphic to that quotient
tower compatibly with `σ` and `ψ`. -/
theorem exists_iso_padicQuotientTower_of_levels [Module.Finite ℤ_[ℓ] M] (ψ : M ⟶ M)
    (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ]) (σ : S ⟶ S)
    (hsurj : ∀ n, Function.Surjective (S.map (homOfLE (Nat.le_add_right n 1)).op).hom)
    (hker : ∀ n, LinearMap.ker (S.map (homOfLE (Nat.le_add_right n 1)).op).hom =
      padicIdeal ℓ ^ (n + 1) • (⊤ : Submodule ℤ_[ℓ] (S.obj (Opposite.op (n + 1)))))
    (hlev : ∀ n, Nonempty (levelIsoSet M S σ ψ n)) :
    ∃ E : S ≅ padicQuotientTower M, σ ≫ E.hom = E.hom ≫ padicQuotientTowerMap ψ := by
  classical
  let tS := fun n => (S.map (homOfLE (Nat.le_add_right n 1)).op).hom
  let tQ := fun n => (padicQuotientTransition M n).hom
  have htQ : ∀ n, (padicQuotientTower M).map (homOfLE (Nat.le_add_right n 1)).op =
      padicQuotientTransition M n := fun n => Functor.ofOpSequence_map_homOfLE_succ _ n
  have hσS : ∀ n x, tS n ((σ.app (Opposite.op (n + 1))).hom x) =
      (σ.app (Opposite.op n)).hom (tS n x) := fun n x =>
    congrArg (fun t => t.hom x) (σ.naturality (homOfLE (Nat.le_add_right n 1)).op).symm
  have hψQ : ∀ n x, tQ n (((padicQuotientTowerMap ψ).app (Opposite.op (n + 1))).hom x) =
      ((padicQuotientTowerMap ψ).app (Opposite.op n)).hom (tQ n x) := fun n x => by
    have := congrArg (fun t => t.hom x)
      ((padicQuotientTowerMap ψ).naturality (homOfLE (Nat.le_add_right n 1)).op)
    simp only [htQ] at this
    exact this.symm
  have hkerQ : ∀ n (y : (padicQuotientTower M).obj (Opposite.op (n + 1))),
      tQ n y = 0 ↔ y ∈ padicIdeal ℓ ^ (n + 1) •
        (⊤ : Submodule ℤ_[ℓ] ((padicQuotientTower M).obj (Opposite.op (n + 1)))) := fun n y =>
    SetLike.ext_iff.1 (ker_padicQuotientTransition (M := M) n) y
  have hsurjQ : ∀ n, Function.Surjective (tQ n) := fun n x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hres : ∀ n (e : levelIsoSet M S σ ψ (n + 1)), ∃ e' : levelIsoSet M S σ ψ n,
      ∀ x, e'.1 (tS n x) = tQ n (e.1 x) := by
    intro n e
    let g : S.obj (Opposite.op (n + 1)) →ₗ[ℤ_[ℓ]] (padicQuotientTower M).obj (Opposite.op n) :=
      tQ n ∘ₗ e.1.toLinearMap
    have hker' : LinearMap.ker (tS n) ≤ LinearMap.ker g := by
      intro x hx
      rw [hker] at hx
      rw [LinearMap.mem_ker]
      have hx' := Submodule.smul_top_le_comap_smul_top (padicIdeal ℓ ^ (n + 1)) e.1.toLinearMap hx
      change e.1 x ∈ padicIdeal ℓ ^ (n + 1) •
        (⊤ : Submodule ℤ_[ℓ] ((padicQuotientTower M).obj (Opposite.op (n + 1)))) at hx'
      exact (hkerQ n _).2 hx'
    let q := (LinearMap.quotKerEquivOfSurjective (tS n) (hsurj n)).symm.toLinearMap
    let g' := (LinearMap.ker (tS n)).liftQ g hker' ∘ₗ q
    have hg' : ∀ x, g' (tS n x) = tQ n (e.1 x) := fun x => by
      show (LinearMap.ker (tS n)).liftQ g hker'
        ((LinearMap.quotKerEquivOfSurjective (tS n) (hsurj n)).symm (tS n x)) = _
      have : (LinearMap.quotKerEquivOfSurjective (tS n) (hsurj n)).symm (tS n x) =
          Submodule.Quotient.mk x := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      rw [this]
      rfl
    have hbij : Function.Bijective g' := by
      constructor
      · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro y hy
        obtain ⟨x, rfl⟩ := hsurj n y
        rw [LinearMap.mem_ker, hg'] at hy
        have hx : e.1 x ∈ padicIdeal ℓ ^ (n + 1) •
            (⊤ : Submodule ℤ_[ℓ] ((padicQuotientTower M).obj (Opposite.op (n + 1)))) :=
          (hkerQ n _).1 hy
        have hx' := Submodule.smul_top_le_comap_smul_top (padicIdeal ℓ ^ (n + 1))
          e.1.symm.toLinearMap hx
        rw [Submodule.mem_comap, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ← hker] at hx'
        exact (LinearMap.mem_ker.1 hx').symm ▸ Submodule.zero_mem _
      · intro z
        obtain ⟨w, rfl⟩ := hsurjQ n z
        obtain ⟨x, rfl⟩ := e.1.surjective w
        exact ⟨tS n x, hg' x⟩
    refine ⟨⟨LinearEquiv.ofBijective g' hbij, fun y => ?_⟩, hg'⟩
    obtain ⟨x, rfl⟩ := hsurj n y
    show g' ((σ.app (Opposite.op n)).hom (tS n x)) = _
    show _ = ((padicQuotientTowerMap ψ).app (Opposite.op n)).hom (g' (tS n x))
    rw [← hσS, hg', hg', e.2, hψQ]
  choose res hres using hres
  let F : ℕᵒᵖ ⥤ Type v := Functor.ofOpSequence (C := Type v) (X := fun n => levelIsoSet M S σ ψ n)
    (fun n => TypeCat.ofHom (res n))
  have : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => by
    have := finite_padicQuotientTower_obj (M := M) j.unop
    obtain ⟨e₀⟩ := hlev j.unop
    have : Finite (S.obj (Opposite.op j.unop)) := Finite.of_equiv _ e₀.1.symm.toEquiv
    show Finite (levelIsoSet M S σ ψ j.unop)
    exact Finite.of_injective (fun e => (e.1 : S.obj (Opposite.op j.unop) →
      (padicQuotientTower M).obj (Opposite.op j.unop))) fun a b h =>
        Subtype.ext (LinearEquiv.coe_injective h)
  have : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => hlev j.unop
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  have hcompat : ∀ n x, (sec (Opposite.op n)).1 (tS n x) =
      tQ n ((sec (Opposite.op (n + 1))).1 x) := fun n x => by
    have h := hsec (homOfLE (Nat.le_add_right n 1)).op
    have hF : F.map (homOfLE (Nat.le_add_right n 1)).op = TypeCat.ofHom (res n) :=
      Functor.ofOpSequence_map_homOfLE_succ _ n
    rw [hF] at h
    rw [← h]
    exact hres n _ x
  let Ehom : S ⟶ padicQuotientTower M := NatTrans.ofOpSequence
    (fun n => ModuleCat.ofHom (sec (Opposite.op n)).1.toLinearMap) fun n => by
      ext x
      rw [htQ]
      exact hcompat n x
  have : ∀ n, IsIso (Ehom.app n) := fun n =>
    (ConcreteCategory.isIso_iff_bijective _).2 (sec n).1.bijective
  have : IsIso Ehom := NatIso.isIso_of_isIso_app _
  refine ⟨asIso Ehom, ?_⟩
  ext n x
  exact (sec n).2 x

end Koenig

variable [IsAdicComplete (padicIdeal ℓ) M]

/-- **The limit of a tower isomorphic to the quotient tower of a complete module is the
module.** -/
def limitIsoOfIsoPadicQuotientTower (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (E : S ≅ padicQuotientTower M) : limit S ≅ M :=
  HasLimit.isoOfNatIso E ≪≫ limit.isoLimitCone ⟨_, isLimitPadicQuotientCone M⟩

/-- The identification of the limit carries the limit of an endomorphism of the tower to the
endomorphism of the module it lies over. -/
theorem limMap_comp_limitIsoOfIsoPadicQuotientTower_hom (S : ℕᵒᵖ ⥤ ModuleCat.{v} ℤ_[ℓ])
    (E : S ≅ padicQuotientTower M) (σ : S ⟶ S) (ψ : M ⟶ M)
    (hσ : σ ≫ E.hom = E.hom ≫ padicQuotientTowerMap ψ) :
    limMap σ ≫ (limitIsoOfIsoPadicQuotientTower M S E).hom =
      (limitIsoOfIsoPadicQuotientTower M S E).hom ≫ ψ := by
  refine (isLimitPadicQuotientCone M).hom_ext fun n => ?_
  have key : (limitIsoOfIsoPadicQuotientTower M S E).hom ≫ (padicQuotientCone M).π.app n =
      limit.π S n ≫ E.hom.app n := by
    rw [limitIsoOfIsoPadicQuotientTower, Iso.trans_hom, Category.assoc,
      limit.isoLimitCone_hom_π, HasLimit.isoOfNatIso_hom_π]
  have hσn : σ.app n ≫ E.hom.app n = E.hom.app n ≫ (padicQuotientTowerMap ψ).app n := by
    simpa only [NatTrans.comp_app] using congrArg (fun t => t.app n) hσ
  rw [Category.assoc, key, limMap_π_assoc, hσn, Category.assoc,
    ← padicQuotientCone_π_comp_padicQuotientTowerMap, reassoc_of% key]


end Limit

/-! ### Assembly: from a tower of level coinvariants to `(ℚ_ℓ^r)_H` -/

section Assembly

universe w

/-- `(ℤ_ℓ^r)_H`, lifted to the universe `w` of the cohomology modules. -/
abbrev integralCoinvariantsModule : ModuleCat.{w} ℤ_[ℓ] :=
  ModuleCat.of ℤ_[ℓ] (ULift.{w} (integralCoinvariants H ρ))

/-- Linear maps preserve congruences modulo `I ^ n • ⊤`. -/
private theorem sModEq_pow_smul_top_map {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (I : Ideal R) (n : ℕ) (f : M →ₗ[R] N) {x y : M}
    (h : x ≡ y [SMOD I ^ n • (⊤ : Submodule R M)]) :
    f x ≡ f y [SMOD I ^ n • (⊤ : Submodule R N)] := by
  rw [SModEq.sub_mem] at h ⊢
  simpa using Submodule.smul_top_le_comap_smul_top (I ^ n) f h

omit [H.Normal] in
/-- The lifted coinvariants `(ℤ_ℓ^r)_H` are `ℓ`-adically complete. -/
theorem isAdicComplete_integralCoinvariantsModule :
    IsAdicComplete (padicIdeal ℓ) (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) := by
  have := isAdicComplete_integralCoinvariants H ρ
  let e : ULift.{w} (integralCoinvariants H ρ) ≃ₗ[ℤ_[ℓ]] integralCoinvariants H ρ :=
    ULift.moduleEquiv
  have hH : IsHausdorff (padicIdeal ℓ)
      (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) := ⟨fun x hx => e.injective (by
    rw [map_zero]
    exact IsHausdorff.haus (I := padicIdeal ℓ) IsAdicComplete.toIsHausdorff _ fun n => by
      simpa using sModEq_pow_smul_top_map _ n e.toLinearMap (hx n))⟩
  have hP : IsPrecomplete (padicIdeal ℓ)
      (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) := ⟨fun f hf => by
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := padicIdeal ℓ))
      (f := fun n => e (f n)) fun {m n} hmn => by
        simpa using sModEq_pow_smul_top_map _ m e.toLinearMap (hf hmn)
    exact ⟨e.symm L, fun n => by
      simpa using sModEq_pow_smul_top_map _ n e.symm.toLinearMap (hL n)⟩⟩
  exact {}

end Assembly

section AssemblyFrobenius

universe w

open scoped ChangeOfRings

variable (τ : Γ →* GL (Fin r) ℚ_[ℓ]) (P : GL (Fin r) ℚ_[ℓ])
  (hP : ∀ g, rationalGL ρ g = P⁻¹ * τ g * P) (c : ℤ_[ℓ])

/-- `c · ρ(φ)` on the lifted coinvariants `(ℤ_ℓ^r)_H`. -/
def integralCoinvariantsModuleEnd :
    (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) ⟶ integralCoinvariantsModule H ρ :=
  ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ (c • coinvariantsFrobenius H ρ φ) ∘ₗ
    ULift.moduleEquiv.toLinearMap)

/-- `integralCoinvariantsModuleEnd` acts as `c · ρ(φ)` on the underlying coinvariants. -/
theorem integralCoinvariantsModuleEnd_apply (x : integralCoinvariantsModule H ρ) :
    (integralCoinvariantsModuleEnd.{w} H ρ φ c).hom x =
      ULift.up (c • coinvariantsFrobenius H ρ φ (ULift.down x)) :=
  rfl

include hP in
/-- A tower `S` of `ℤ_ℓ`-modules isomorphic to the quotient tower of `(ℤ_ℓ^r)_H`, with an
endomorphism lying over `c · ρ(φ)`, has `ℚ_ℓ ⊗ lim S ≅ (ℚ_ℓ^r)_H` for `τ = P ρ P⁻¹`, carrying the
limit endomorphism to `c · τ(φ)`. -/
theorem exists_extendScalars_limit_linearEquiv_coinvariants (S : ℕᵒᵖ ⥤ ModuleCat.{w} ℤ_[ℓ])
    (E : S ≅ padicQuotientTower (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]))
    (σ : S ⟶ S)
    (hσ : σ ≫ E.hom = E.hom ≫ padicQuotientTowerMap (integralCoinvariantsModuleEnd H ρ φ c)) :
    ∃ e : (ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj (limit S) ≃ₗ[ℚ_[ℓ]]
        Coinvariants ((matrixRepresentation τ).comp H.subtype),
      ∀ x, e (((ModuleCat.extendScalars.{0, 0, w} (algebraMap ℤ_[ℓ] ℚ_[ℓ])).map
          (limMap σ)).hom x) =
        algebraMap ℤ_[ℓ] ℚ_[ℓ] c • coinvariantsFrobenius H τ φ (e x) := by
  have : IsAdicComplete (padicIdeal ℓ) (integralCoinvariantsModule H ρ : ModuleCat.{w} ℤ_[ℓ]) :=
    isAdicComplete_integralCoinvariantsModule H ρ
  let M : ModuleCat.{w} ℤ_[ℓ] := integralCoinvariantsModule H ρ
  let I := limitIsoOfIsoPadicQuotientTower M S E
  let f := algebraMap ℤ_[ℓ] ℚ_[ℓ]
  let X := (ModuleCat.restrictScalars f).obj (ModuleCat.of ℚ_[ℓ] ℚ_[ℓ])
  let : IsScalarTower ℤ_[ℓ] ℚ_[ℓ] X := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₂ : ((ModuleCat.extendScalars f).obj M : Type w) ≃ₗ[ℚ_[ℓ]]
      TensorProduct ℤ_[ℓ] ℚ_[ℓ] (integralCoinvariants H ρ) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl ℚ_[ℓ] ℚ_[ℓ]) ULift.moduleEquiv
  let e₃ := (isBaseChange_integralCoinvariantsRationalization H ρ).equiv
  let e₄ := rationalCoinvariantsConjEquiv H τ P hP
  let e := ((ModuleCat.extendScalars f).mapIso I).toLinearEquiv ≪≫ₗ e₂ ≪≫ₗ e₃ ≪≫ₗ e₄
  have he : ∀ m : ((limit S : ModuleCat.{w} ℤ_[ℓ]) : Type w), e ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] m) =
      e₄ (integralCoinvariantsRationalization H ρ (ULift.down (I.hom.hom m))) := by
    intro m
    show e₄ (e₃ (e₂ ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] I.hom.hom m))) = _
    congr 1
    show e₃ ((1 : ℚ_[ℓ]) ⊗ₜ ULift.down (I.hom.hom m)) = _
    rw [IsBaseChange.equiv_tmul, one_smul]
  have hI : ∀ m : ((limit S : ModuleCat.{w} ℤ_[ℓ]) : Type w), I.hom.hom ((limMap σ).hom m) =
      (integralCoinvariantsModuleEnd H ρ φ c).hom (I.hom.hom m) := fun m =>
    congrArg (fun t => t.hom m) (limMap_comp_limitIsoOfIsoPadicQuotientTower_hom M S E σ _ hσ)
  refine ⟨e, fun x => ?_⟩
  let α : (ModuleCat.extendScalars f).obj (limit S) ⟶
      ModuleCat.of ℚ_[ℓ] (ULift.{w} (Coinvariants ((matrixRepresentation τ).comp H.subtype))) :=
    (ModuleCat.extendScalars f).map (limMap σ) ≫
      ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ e.toLinearMap)
  let β : (ModuleCat.extendScalars f).obj (limit S) ⟶
      ModuleCat.of ℚ_[ℓ] (ULift.{w} (Coinvariants ((matrixRepresentation τ).comp H.subtype))) :=
    ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap ∘ₗ
      (f c • coinvariantsFrobenius H τ φ) ∘ₗ e.toLinearMap)
  have hαβ : α = β := by
    refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
    show ULift.up (e (((ModuleCat.extendScalars f).map (limMap σ)).hom
        ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] m))) =
      ULift.up (f c • coinvariantsFrobenius H τ φ (e ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], f] m)))
    congr 1
    refine (he ((limMap σ).hom m)).trans ?_
    rw [he m, hI, integralCoinvariantsModuleEnd_apply, map_smul,
      integralCoinvariantsRationalization_coinvariantsFrobenius, ← algebraMap_smul ℚ_[ℓ] c,
      map_smul, rationalCoinvariantsConjEquiv_coinvariantsFrobenius]
  exact congrArg (fun t => ULift.down (t.hom x)) hαβ

end AssemblyFrobenius

end Stacks.EtaleCohomology

end
