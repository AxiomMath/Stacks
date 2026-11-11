module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic.LinearCombination
public import StacksFrontier.RingTheory.DifferentialOperator.Defs

/-!
# Differential operators of order one

Fix a ring map `R → S` and an `S`-module `N`, viewed as an `R`-module by restriction of scalars.
A differential operator of order `≤ 1` from `S` to `N` is an `R`-linear map `D : S → N` such that
for every `g ∈ S` the map `h ↦ D(g h) - g · D(h)` is `S`-linear. Every such `D` decomposes as
`D = σ_D + λ_{D 1}`, where `σ_D g = D g - g · D 1` is an `R`-derivation and `λ_x g = g · x`; this
gives an isomorphism `Diff¹(S, N) ≅ Der_R(S, N) ⊕ N`, natural in `N`. Combined with the universal
property of `Ω[S⁄R]` it gives the natural isomorphism `Diff¹(S, N) ≅ Hom_S(Ω[S⁄R] ⊕ S, N)`, the
representable form of `P¹_{S/R} ≅ Ω_{S/R} ⊕ S`.

For a ring map `A → B`, the de Rham differentials `d : Ωⁱ_{B/A} → Ωⁱ⁺¹_{B/A}` are differential
operators of order one.

## Main definitions

* `diff1Submodule`, `Diff1`: the `S`-module `Diff¹(S, N)` of differential operators of order
  `≤ 1`.
* `elementSmulMap`: the map `λ_x : g ↦ g · x`.
* `sigmaDerivation`: the derivation `σ_D` attached to `D ∈ Diff¹(S, N)`.
* `diff1EquivDerProd`: the isomorphism `Diff¹(S, N) ≃ₗ[S] Der_R(S, N) × N`.
* `diff1Map`: the functoriality of `Diff¹(S, -)` in `N`.
* `principalPartsEquiv`: the isomorphism `Diff¹(S, N) ≃ₗ[S] ((Ω[S⁄R] × S) →ₗ[S] N)`.
* `kaehlerDProdId`: the map `S → Ω[S⁄R] × S`, `b ↦ (d b, b)`.
* `deRhamGen`, `deRhamTop`: the forms `b₀ · db₁ ∧ ⋯ ∧ dbᵢ` and `db₀ ∧ db₁ ∧ ⋯ ∧ dbᵢ`.

## Main results

* `diff1EquivDerProd_naturality`, `principalPartsEquiv_naturality`: naturality in `N`.
* `isUniversalDifferentialOperatorOfOrderLE_kaehlerDProdId`: `Ω[S⁄R] × S` with `b ↦ (d b, b)` is
  the module of principal parts `P¹_{S/R}` (Example 09CM, second claim).
* `principalPartsOne_equiv_kaehler_prod`: every module of principal parts of order `1` of `S` is
  `S`-linearly isomorphic to `Ω[S⁄R] × S`, compatibly with the universal operators.
* `deRham_isDiffOpOfOrder_one`: the de Rham differential is a differential operator of order
  one.

## References

* [Stacks Project, Tag 09CI](https://stacks.math.columbia.edu/tag/09CI)
* [Stacks Project, Tag 09CM](https://stacks.math.columbia.edu/tag/09CM)
* [Stacks Project, Tag 0G34](https://stacks.math.columbia.edu/tag/0G34)
-/

@[expose] public section
variable {R S N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The `S`-submodule of `S →ₗ[R] N` consisting of differential operators of order `≤ 1`
([Stacks, Tag 09CI], with source module `S`): the `R`-linear maps `D : S → N` such that for every
`g ∈ S` the map `h ↦ D(g h) - g · D(h)` is `S`-linear, that is,
`D (g (s h)) - g · D (s h) = s · (D (g h) - g · D h)` for all `g, s, h`. The `S`-module structure
is `(s · D) g = s · D g`. -/
def diff1Submodule : Submodule S (S →ₗ[R] N) where
  carrier := {D | ∀ g s h : S, D (g * (s * h)) - g • D (s * h) = s • (D (g * h) - g • D h)}
  add_mem' := by
    intro a b ha hb g s h
    simp only [LinearMap.add_apply, smul_add]
    rw [show a (g * (s * h)) + b (g * (s * h)) - (g • a (s * h) + g • b (s * h))
          = (a (g * (s * h)) - g • a (s * h)) + (b (g * (s * h)) - g • b (s * h)) by abel,
        ha g s h, hb g s h, ← smul_add]
    congr 1; abel
  zero_mem' := by intro g s h; simp
  smul_mem' := by
    intro c a ha g s h
    simp only [LinearMap.smul_apply]
    rw [show c • a (g * (s * h)) - g • c • a (s * h)
          = c • (a (g * (s * h)) - g • a (s * h)) by rw [smul_sub, smul_comm g c],
        ha g s h, smul_comm c s]
    congr 1; rw [smul_sub, smul_comm g c]

/-- `Diff¹(S, N)`: differential operators `S → N` of order `≤ 1`, as an
`S`-module. -/
@[ega "IV 16.8.1" "n = 1",
  ega "IV 16.8.5" "special case",
  sga "3 VIIA 1.1.1" "partial",
  sga "3 VIIA 1.4" "special case"]
abbrev Diff1 (R S N : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N] :=
  diff1Submodule (R := R) (S := S) (N := N)

/-- For `x ∈ N`, the `R`-linear map `λ_x : S → N`, `g ↦ g · x`. -/
def elementSmulMap (x : N) : S →ₗ[R] N := (LinearMap.toSpanSingleton S N x).restrictScalars R

/-- The map `λ_x` sends `g` to `g · x`. -/
@[simp] theorem elementSmulMap_apply (x : N) (g : S) : elementSmulMap (R := R) x g = g • x := by
  simp [elementSmulMap, LinearMap.toSpanSingleton]

/-- The Leibniz defect of an operator of order `≤ 1`: for `D ∈ Diff¹`,
`D (g*s) = g • D s + s • D g - (s*g) • D 1`. -/
@[ega "IV 16.11.1" "special case", sga "3 VIIA 1.3.1" "(b), special case"]
theorem diff1_key (D : S →ₗ[R] N) (hD : D ∈ diff1Submodule (R := R)) (g s : S) :
    D (g * s) = g • D s + s • D g - (s * g) • D 1 := by
  have := hD g s 1
  simp only [mul_one] at this
  rw [smul_sub, smul_smul, sub_eq_iff_eq_add] at this
  rw [this]; abel

/-- The map `λ_x` lies in `Diff¹(S, N)`. -/
theorem elementSmulMap_mem (x : N) : elementSmulMap (R := R) (S := S) x ∈ diff1Submodule := by
  intro g s h
  simp only [elementSmulMap_apply, mul_smul]; simp [smul_smul]

/-- Every `R`-derivation `σ : S → N` lies in `Diff¹(S, N)`. -/
@[sga "3 VIIA 1.2.0" "partial", sga "3 VIIA 1.3.1" "partial"]
theorem derivation_mem (σ : Derivation R S N) :
    (σ.toLinearMap : S →ₗ[R] N) ∈ diff1Submodule := by
  intro g s h
  change σ (g * (s * h)) - g • σ (s * h) = s • (σ (g * h) - g • σ h)
  rw [σ.leibniz g (s*h), σ.leibniz s h, σ.leibniz g h]
  simp only [smul_add, smul_sub, smul_smul]
  rw [mul_comm s g]; abel

/-- For an `R`-linear `D : S → N`, the map `σ_D : S → N`,
`σ_D g := D g - g · D 1`, as an `R`-linear map. -/
def sigmaMap (D : S →ₗ[R] N) : S →ₗ[R] N := D - elementSmulMap (D 1)

/-- The map `σ_D` sends `g` to `D g - g · D 1`. -/
@[simp] theorem sigmaMap_apply (D : S →ₗ[R] N) (g : S) : sigmaMap D g = D g - g • D 1 := by
  simp [sigmaMap]

/-- For `D ∈ Diff¹(S, N)`, the map `σ_D := D - λ_{D 1}` is an `R`-derivation `S → N`; its
underlying map is `sigmaMap D.val`. -/
def sigmaDerivation (D : Diff1 R S N) : Derivation R S N :=
  Derivation.mk' (sigmaMap D.val) (by
    intro a b
    simp only [sigmaMap_apply]
    rw [diff1_key D.val D.property a b, smul_sub, smul_sub, smul_smul, smul_smul, mul_comm b a]
    abel)

/-- The derivation `σ_D` sends `g` to `D g - g · D 1`. -/
@[simp] theorem sigmaDerivation_apply (D : Diff1 R S N) (g : S) :
    sigmaDerivation D g = D.1 g - g • D.1 1 := by
  simp [sigmaDerivation]

/-- The forward `S`-linear map of the decomposition: `D ↦ (σ_D, D 1)`. -/
def diff1ToDerProd : Diff1 R S N →ₗ[S] (Derivation R S N × N) where
  toFun D := (sigmaDerivation D, D.val 1)
  map_add' D D' := by
    ext g
    · simp [sigmaDerivation_apply]; abel
    · simp
  map_smul' c D := by
    ext g
    · simp [sigmaDerivation_apply, smul_sub, smul_smul, mul_comm]
    · simp

/-- The first-order differential operator associated to a derivation and a constant term. -/
def derProdToDiff1 (p : Derivation R S N × N) : Diff1 R S N :=
  ⟨p.fst.toLinearMap + elementSmulMap p.snd,
    diff1Submodule.add_mem (derivation_mem p.fst) (elementSmulMap_mem p.snd)⟩

/-- The operator associated to `(σ, x)` sends `g` to `σ g + g · x`. -/
@[simp] theorem derProdToDiff1_apply (p : Derivation R S N × N) (g : S) :
    (derProdToDiff1 p).1 g = p.1 g + g • p.2 := by
  simp [derProdToDiff1]

/-- The inverse `S`-linear map of the decomposition: `(σ, x) ↦ σ + λ_x`. -/
def derProdToDiff1Linear : (Derivation R S N × N) →ₗ[S] Diff1 R S N where
  toFun := derProdToDiff1
  map_add' p q := by
    ext g
    simp only [derProdToDiff1_apply, Submodule.coe_add, LinearMap.add_apply, Prod.fst_add,
      Prod.snd_add, Derivation.add_apply, smul_add]; abel
  map_smul' c p := by
    ext g
    simp only [derProdToDiff1_apply, SetLike.val_smul, LinearMap.smul_apply, Prod.smul_fst,
      Prod.smul_snd, Derivation.smul_apply, RingHom.id_apply, smul_add, smul_smul, mul_comm]

/-- The `S`-module isomorphism `Diff¹(S, N) ≃ₗ[S] Der_R(S, N) × N` given by `D ↦ (σ_D, D 1)`, where
`σ_D g = D g - g · D 1`, with inverse `(σ, x) ↦ σ + λ_x`. -/
@[stacks 09CM "First claim, `Diff¹(S, N) = Der_R(S, N) ⊕ N`, via `D ↦ (σ_D, D 1)`. The second
claim, `P¹_{S/R} = Ω_{S/R} ⊕ S`, is `isUniversalDifferentialOperatorOfOrderLE_kaehlerDProdId`.",
  sga "3 VIIA 1.3.1" "Dev≤1 ≃ O_S ⊕ Der_S"]
def diff1EquivDerProd : Diff1 R S N ≃ₗ[S] (Derivation R S N × N) :=
  LinearEquiv.ofLinearMap diff1ToDerProd derProdToDiff1Linear
    (by
      apply LinearMap.ext; intro p
      apply Prod.ext
      · apply Derivation.ext; intro g
        simp only [LinearMap.coe_comp, Function.comp_apply, diff1ToDerProd, derProdToDiff1Linear,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, sigmaDerivation_apply,
          derProdToDiff1_apply]
        rw [p.fst.map_one_eq_zero]; module
      · simp only [LinearMap.coe_comp, Function.comp_apply, diff1ToDerProd, derProdToDiff1Linear,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, derProdToDiff1_apply]
        simp)
    (by
      apply LinearMap.ext; intro D
      apply Subtype.ext; apply LinearMap.ext; intro g
      simp only [LinearMap.coe_comp, Function.comp_apply, diff1ToDerProd, derProdToDiff1Linear,
        LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_coe, id_eq, derProdToDiff1_apply,
        sigmaDerivation_apply]
      abel)

/-- The forward map of the decomposition is `D ↦ (σ_D, D 1)`. -/
@[simp] theorem diff1EquivDerProd_apply (D : Diff1 R S N) :
    diff1EquivDerProd D = (sigmaDerivation D, D.1 1) := rfl

/-- The inverse map of the decomposition is `(σ, x) ↦ σ + λ_x`. -/
@[simp] theorem diff1EquivDerProd_symm_apply (p : Derivation R S N × N) :
    ((diff1EquivDerProd.symm p : Diff1 R S N) : S →ₗ[R] N)
      = p.1.toLinearMap + elementSmulMap p.2 := rfl

/-- Functoriality of `Diff¹(S, -)`: postcomposition by an `S`-linear `f : N →ₗ[S] N'`
gives an `S`-linear map `Diff¹(S, N) → Diff¹(S, N')`. -/
def diff1Map {N' : Type*} [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] (f : N →ₗ[S] N') :
    Diff1 R S N →ₗ[S] Diff1 R S N' where
  toFun D := ⟨(f.restrictScalars R).comp D.val, fun g s h => by
    simpa [map_smul] using congrArg f (D.property g s h)⟩
  map_add' D D' := by ext g; simp
  map_smul' c D := by ext g; simp

/-- The operator `diff1Map f D` sends `g` to `f (D g)`. -/
@[simp] theorem diff1Map_apply {N' : Type*} [AddCommGroup N'] [Module S N'] [Module R N']
    [IsScalarTower R S N'] (f : N →ₗ[S] N') (D : Diff1 R S N)
    (g : S) : (diff1Map f D).1 g = f (D.1 g) := rfl

/-- The derivation `σ_D` is compatible with postcomposition by an `S`-linear map. -/
private theorem sigmaDerivation_diff1Map {N' : Type*} [AddCommGroup N'] [Module S N']
    [Module R N'] [IsScalarTower R S N'] (f : N →ₗ[S] N') (D : Diff1 R S N) (g : S) :
    sigmaDerivation (diff1Map f D) g = f (sigmaDerivation D g) := by
  rw [sigmaDerivation_apply, sigmaDerivation_apply, diff1Map_apply, diff1Map_apply,
    map_sub, map_smul]

/-- Naturality of the decomposition in the `S`-module `N`: for an `S`-linear map
`f : N →ₗ[S] N'`, `(f.compDer × f) ∘ diff1EquivDerProd = diff1EquivDerProd ∘ diff1Map f`. -/
theorem diff1EquivDerProd_naturality {N' : Type*} [AddCommGroup N'] [Module S N']
    [Module R N'] [IsScalarTower R S N'] (f : N →ₗ[S] N')
    (D : Diff1 R S N) :
    diff1EquivDerProd (diff1Map f D)
      = (f.compDer (sigmaDerivation D), f (D.1 1)) := by
  apply Prod.ext
  · exact Derivation.ext (sigmaDerivation_diff1Map f D)
  · simp [diff1Map]

/-- The `S`-module isomorphism `Diff¹(S, N) ≃ₗ[S] ((Ω[S⁄R] × S) →ₗ[S] N)`, the composite of
`diff1EquivDerProd`, the universal property `Der_R(S, N) ≃ Hom_S(Ω[S⁄R], N)` of Kähler
differentials and `N ≃ Hom_S(S, N)`. As `N` varies it is the representable form of
`P¹_{S/R} ≅ Ω_{S/R} ⊕ S` ([Stacks, Tag 09CM]). -/
@[ega "IV 16.8.3" "special case",
  sga "3 VIIA 1.3.1" "special case",
  sga "3 VIIA 1.4.2" "d'' clause, special case"]
noncomputable def principalPartsEquiv (N : Type*) [AddCommGroup N] [Module S N]
    [Module R N] [IsScalarTower R S N] :
    Diff1 R S N ≃ₗ[S] ((Ω[S⁄R] × S) →ₗ[S] N) :=
  diff1EquivDerProd.trans
    (((KaehlerDifferential.linearMapEquivDerivation R S (M := N)).symm.prodCongr
        (LinearMap.ringLmapEquivSelf S S N).symm).trans
      (LinearMap.coprodEquiv (R := S) S))

/-- Naturality of `principalPartsEquiv` in `N`: for an `S`-linear `f : N →ₗ[S] N'`,
postcomposition by `f` on `Hom_S(Ω[S⁄R] × S, -)` corresponds to `diff1Map f` on
`Diff¹(S, -)`. -/
theorem principalPartsEquiv_naturality {N' : Type*} [AddCommGroup N'] [Module S N']
    [Module R N'] [IsScalarTower R S N'] (f : N →ₗ[S] N')
    (D : Diff1 R S N) :
    principalPartsEquiv N' (diff1Map f D)
      = f.comp (principalPartsEquiv N D) := by
  ext x
  · simp only [principalPartsEquiv, LinearEquiv.trans_apply]
    simp only [LinearMap.coprodEquiv, diff1EquivDerProd, LinearEquiv.coe_ofLinearMap,
      LinearEquiv.prodCongr_apply, KaehlerDifferential.linearMapEquivDerivation_symm_apply,
      LinearMap.ringLmapEquivSelf_symm_apply, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coprod_inl, Derivation.coe_comp, LinearMap.coe_comp, LinearMap.coe_restrictScalars,
      Derivation.coeFn_coe, Function.comp_apply, Derivation.liftKaehlerDifferential_comp_D,
      LinearMap.restrictScalars_comp, LinearMap.coe_inl, LinearMap.coprod_apply,
      LinearMap.coe_smulRight, Module.End.one_apply, zero_smul, add_zero]
    exact sigmaDerivation_diff1Map f D x
  · simp only [principalPartsEquiv, LinearEquiv.trans_apply]
    simp only [LinearMap.coprodEquiv, LinearMap.ringLmapEquivSelf, LinearEquiv.symm_mk,
      LinearMap.coe_mk, AddHom.coe_mk, diff1EquivDerProd, LinearEquiv.coe_ofLinearMap,
      LinearEquiv.prodCongr_apply, KaehlerDifferential.linearMapEquivDerivation_symm_apply,
      LinearEquiv.coe_mk, LinearMap.coprod_inr, LinearMap.coe_smulRight, Module.End.one_apply,
      one_smul, LinearMap.coe_comp, LinearMap.coe_inr, Function.comp_apply, LinearMap.coprod_apply,
      map_zero, zero_add]
    change (diff1Map f D).val 1 = f (D.val 1)
    rw [diff1Map_apply]

/-- The value of `principalPartsEquiv N D` at `(η, s)` is `σ̃_D η + s · D 1`, where
`σ̃_D : Ω[S⁄R] → N` is the `S`-linear map induced by the derivation `σ_D`. -/
theorem principalPartsEquiv_apply (D : Diff1 R S N) (η : Ω[S⁄R]) (s : S) :
    principalPartsEquiv N D (η, s) = (sigmaDerivation D).liftKaehlerDifferential η + s • D.1 1 :=
  rfl

/-- An `R`-linear map `E : S → N` is a differential operator of order at most `1` in the sense of
`LinearMap.IsDifferentialOperatorOfOrderLE` exactly when it lies in `Diff¹(S, N)`. -/
theorem isDifferentialOperatorOfOrderLE_one_iff_mem_diff1Submodule (E : S →ₗ[R] N) :
    E.IsDifferentialOperatorOfOrderLE S 1 ↔ E ∈ diff1Submodule (R := R) :=
  Iff.rfl

variable (R S) in
/-- The `R`-linear map `S → Ω[S⁄R] × S`, `b ↦ (d b, b)`: the universal differential operator of
order `≤ 1` on `S` (Example 09CM). -/
noncomputable def kaehlerDProdId : S →ₗ[R] Ω[S⁄R] × S :=
  (KaehlerDifferential.D R S).toLinearMap.prod LinearMap.id

/-- The map `kaehlerDProdId R S` sends `b` to `(d b, b)`. -/
@[simp] theorem kaehlerDProdId_apply (b : S) :
    kaehlerDProdId R S b = (KaehlerDifferential.D R S b, b) := rfl

/-- The map `b ↦ (d b, b)` is a differential operator of order `≤ 1` from `S` to
`Ω[S⁄R] × S`. -/
theorem isDifferentialOperatorOfOrderLE_one_kaehlerDProdId :
    (kaehlerDProdId R S).IsDifferentialOperatorOfOrderLE S 1 := by
  rw [isDifferentialOperatorOfOrderLE_one_iff_mem_diff1Submodule]
  have h : kaehlerDProdId R S =
      (((LinearMap.inl S (Ω[S⁄R]) S).compDer (KaehlerDifferential.D R S) :
          Derivation R S (Ω[S⁄R] × S)) : S →ₗ[R] Ω[S⁄R] × S) +
        elementSmulMap ((0 : Ω[S⁄R]), (1 : S)) := by
    ext b <;> simp
  rw [h]
  exact diff1Submodule.add_mem (derivation_mem _) (elementSmulMap_mem _)

/-- Every differential operator `E : S → N` of order `≤ 1`, with `N` an `S`-module in any
universe, factors as `E = α ∘ (b ↦ (d b, b))` for a unique `S`-linear `α : Ω[S⁄R] × S → N`,
namely `principalPartsEquiv N E`. -/
theorem existsUnique_comp_kaehlerDProdId (E : S →ₗ[R] N)
    (hE : E.IsDifferentialOperatorOfOrderLE S 1) :
    ∃! α : (Ω[S⁄R] × S) →ₗ[S] N, ∀ b : S, α (kaehlerDProdId R S b) = E b := by
  have hE' := (isDifferentialOperatorOfOrderLE_one_iff_mem_diff1Submodule E).mp hE
  set α := principalPartsEquiv N (⟨E, hE'⟩ : Diff1 R S N)
  have hα : ∀ b : S, α (kaehlerDProdId R S b) = E b := fun b => by
    rw [kaehlerDProdId_apply, principalPartsEquiv_apply,
      Derivation.liftKaehlerDifferential_comp_D, sigmaDerivation_apply, sub_add_cancel]
  have hinr : ∀ γ : (Ω[S⁄R] × S) →ₗ[S] N, (∀ b, γ (kaehlerDProdId R S b) = E b) →
      ∀ s : S, γ (0, s) = s • E 1 := fun γ hγ s => by
    have h1 := hγ 1
    rw [kaehlerDProdId_apply, (KaehlerDifferential.D R S).map_one_eq_zero] at h1
    rw [show ((0 : Ω[S⁄R]), s) = s • ((0 : Ω[S⁄R]), (1 : S)) by simp, map_smul, h1]
  have hinl : ∀ γ : (Ω[S⁄R] × S) →ₗ[S] N, (∀ b, γ (kaehlerDProdId R S b) = E b) →
      ∀ b : S, γ (KaehlerDifferential.D R S b, 0) = E b - b • E 1 := fun γ hγ b => by
    rw [← hinr γ hγ b, ← hγ b, kaehlerDProdId_apply, ← map_sub]
    simp
  refine ⟨α, hα, fun β hβ => LinearMap.prod_ext ?_ ?_⟩
  · refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun b => ?_)
    change β (KaehlerDifferential.D R S b, 0) = α (KaehlerDifferential.D R S b, 0)
    rw [hinl β hβ b, hinl α hα b]
  · refine LinearMap.ext_ring ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.inr_apply]
    rw [hinr β hβ 1, hinr α hα 1]

/-- **Stacks 09CM, second claim.** Let `R → S` be a ring map. Then `Ω[S⁄R] × S`, together with
`b ↦ (d b, b)`, is the module of principal parts of order `1` of `S`: the map `b ↦ (d b, b)` is a
differential operator of order `≤ 1` and every differential operator `E : S → N` of order `≤ 1`
into an `S`-module factors as `α ∘ (b ↦ (d b, b))` for a unique `S`-linear `α`. That is,
`P¹_{S/R} = Ω_{S/R} ⊕ S`. -/
@[stacks 09CM "Second claim, `P¹_{S/R} = Ω_{S/R} ⊕ S`, in the form of Definition 09CL: the pair
`(Ω[S⁄R] × S, b ↦ (d b, b))` is a module of principal parts of order `1` of `S`. The isomorphism
with any other module of principal parts is `principalPartsOne_equiv_kaehler_prod`."]
theorem isUniversalDifferentialOperatorOfOrderLE_kaehlerDProdId :
    (kaehlerDProdId R S).IsUniversalDifferentialOperatorOfOrderLE S 1 :=
  ⟨isDifferentialOperatorOfOrderLE_one_kaehlerDProdId,
    fun _ _ _ _ _ E hE => existsUnique_comp_kaehlerDProdId E hE⟩

/-- **Stacks 09CM, second claim, as an isomorphism.** Let `R → S` be a ring map and let
`D : S → P` be a universal differential operator of order `≤ 1` on `S`, so that `P` is the module
of principal parts `P¹_{S/R}` (Definition 09CL). Then there is an `S`-linear isomorphism
`P ≃ₗ[S] Ω[S⁄R] × S` sending `D b` to `(d b, b)`. -/
@[stacks 09CM "Second claim, `P¹_{S/R} = Ω_{S/R} ⊕ S`, as an `S`-linear isomorphism out of an
arbitrary module of principal parts `(P, D)` of order `1` of `S` (Definition 09CL), matching `D`
with `b ↦ (d b, b)`."]
theorem principalPartsOne_equiv_kaehler_prod {P : Type*} [AddCommGroup P] [Module R P]
    [Module S P] [IsScalarTower R S P] {D : S →ₗ[R] P}
    (hD : D.IsUniversalDifferentialOperatorOfOrderLE S 1) :
    ∃ e : P ≃ₗ[S] Ω[S⁄R] × S, ∀ b : S, e (D b) = (KaehlerDifferential.D R S b, b) := by
  obtain ⟨α, hα, -⟩ := existsUnique_comp_kaehlerDProdId D hD.1
  obtain ⟨β₀, hβ₀, -⟩ := hD.2 (N := ULift (Ω[S⁄R] × S))
    ((ULift.moduleEquiv (R := S)).symm.toLinearMap.restrictScalars R ∘ₗ kaehlerDProdId R S)
    (LinearMap.isDifferentialOperatorOfOrderLE_postcomp _
      isDifferentialOperatorOfOrderLE_one_kaehlerDProdId)
  set β : P →ₗ[S] Ω[S⁄R] × S := (ULift.moduleEquiv (R := S)).toLinearMap ∘ₗ β₀
  have hβ : ∀ b : S, β (D b) = kaehlerDProdId R S b := fun b => by
    simp [β, hβ₀ b]
  have hβα : β ∘ₗ α = LinearMap.id := by
    obtain ⟨_, -, huniq⟩ := existsUnique_comp_kaehlerDProdId (kaehlerDProdId R S)
      isDifferentialOperatorOfOrderLE_one_kaehlerDProdId
    exact (huniq _ fun b => by rw [LinearMap.comp_apply, hα b, hβ b]).trans
      (huniq _ fun b => rfl).symm
  have hαβ : α ∘ₗ β = LinearMap.id := by
    set u : P →ₗ[S] ULift P := (ULift.moduleEquiv (R := S)).symm.toLinearMap
    obtain ⟨_, -, huniq⟩ := hD.2 (N := ULift P) (u.restrictScalars R ∘ₗ D)
      (LinearMap.isDifferentialOperatorOfOrderLE_postcomp _ hD.1)
    have h := (huniq (u ∘ₗ α ∘ₗ β) fun b => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hβ b, hα b]; rfl).trans
      (huniq u fun b => rfl).symm
    ext p
    exact ULift.moduleEquiv.symm.injective (LinearMap.congr_fun h p)
  exact ⟨LinearEquiv.ofLinearMap β α hβα hαβ, fun b => by
    rw [LinearEquiv.coe_ofLinearMap, hβ b, kaehlerDProdId_apply]⟩

/-!
## The de Rham differentials

Fix a ring map `A → B` and write `Ωⁱ_{B/A} = ⋀ⁱ_B Ω[B⁄A]`. An `A`-linear map
`d : Ωⁱ → Ωⁱ⁺¹` with `d (b₀ · db₁ ∧ ⋯ ∧ dbᵢ) = db₀ ∧ db₁ ∧ ⋯ ∧ dbᵢ` is a differential operator of
order `1` relative to `A → B`.
-/

@[expose] public section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The element `b₀ · db₁ ∧ ⋯ ∧ dbᵢ` of `Ωⁱ_{B/A} = ⋀ⁱ_B Ω[B⁄A]`, for an `(i+1)`-tuple
`b : Fin (i+1) → B`, where `d` is the universal derivation `KaehlerDifferential.D A B`. -/
noncomputable def deRhamGen (i : ℕ) (b : Fin (i + 1) → B) : ⋀[B]^i (Ω[B⁄A]) :=
  (b 0) • exteriorPower.ιMulti B i (fun j : Fin i => KaehlerDifferential.D A B (b j.succ))

/-- The element `db₀ ∧ db₁ ∧ ⋯ ∧ dbᵢ` of `Ωⁱ⁺¹_{B/A} = ⋀ⁱ⁺¹_B Ω[B⁄A]`, for an
`(i+1)`-tuple `b : Fin (i+1) → B`: the value of the de Rham differential on `deRhamGen i b`. -/
noncomputable def deRhamTop (i : ℕ) (b : Fin (i + 1) → B) : ⋀[B]^(i+1) (Ω[B⁄A]) :=
  exteriorPower.ιMulti B (i+1) (fun j : Fin (i+1) => KaehlerDifferential.D A B (b j))

/-- Let `A → B` be a ring map and `i ≥ 0`. The de Rham differential `d : Ωⁱ_{B/A} → Ωⁱ⁺¹_{B/A}`,
an additive map that is `A`-linear (`hAlin`) and satisfies
`d (b₀ · db₁ ∧ ⋯ ∧ dbᵢ) = db₀ ∧ db₁ ∧ ⋯ ∧ dbᵢ` (`hChar`), is a differential operator of order `1`
relative to `A → B`: for every `b ∈ B` the map `ω ↦ d (b · ω) - b · d ω` is `B`-linear. -/
@[stacks 0G34]
theorem deRham_isDiffOpOfOrder_one (i : ℕ)
    (d : (⋀[B]^i (Ω[B⁄A])) →+ (⋀[B]^(i + 1) (Ω[B⁄A])))
    (hAlin : IsALinear A B d)
    (hChar : ∀ b : Fin (i+1) → B, d (deRhamGen i b) = deRhamTop i b) :
    IsDiffOpLE A B 1 d := by
  refine ⟨hAlin, fun g => ?_⟩
  change ∀ (h : B) (m : ⋀[B]^i (Ω[B⁄A])), diffOpComm g d (h • m) = h • diffOpComm g d m
  intro h m
  simp only [diffOpComm_apply]
  set P : (⋀[B]^i (Ω[B⁄A])) → Prop :=
    fun z => ∀ c : B,
      d (g • h • (c • z)) - g • d (h • (c • z))
        = h • (d (g • (c • z)) - g • d (c • z))
  have hmem : m ∈ Submodule.span B
        ((exteriorPower.ιMulti B i) ''
          {a : Fin i → Ω[B⁄A] | Set.range a ⊆ Set.range (KaehlerDifferential.D A B)}) := by
    rw [exteriorPower.ιMulti_span_of_span B i (Ω[B⁄A])
      (KaehlerDifferential.span_range_derivation A B)]
    exact Submodule.mem_top
  have key : P m := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨v, hv, rfl⟩
      choose b hb using fun j : Fin i => (hv ⟨j, rfl⟩ : ∃ bj, KaehlerDifferential.D A B bj = v j)
      set w : Fin i → Ω[B⁄A] := fun j => KaehlerDifferential.D A B (b j) with hw
      obtain rfl : v = w := funext fun j => (hb j).symm
      have hF : ∀ s : B,
          d (s • (exteriorPower.ιMulti B i) w)
            = (exteriorPower.ιMulti B (i+1)) (Fin.cons (KaehlerDifferential.D A B s) w) := by
        intro s
        have hgen : s • (exteriorPower.ιMulti B i) w = deRhamGen i (Fin.cons s b) := by
          simp only [deRhamGen, Fin.cons_zero, Fin.cons_succ, hw]
        rw [hgen, hChar, deRhamTop]
        congr 1
        funext j
        refine Fin.cases ?_ (fun k => ?_) j <;> simp [hw]
      intro c
      have hLeib : ∀ s t : B,
          d ((s * t) • (exteriorPower.ιMulti B i) w)
            = s • d (t • (exteriorPower.ιMulti B i) w)
              + t • d (s • (exteriorPower.ιMulti B i) w) := by
        intro s t
        rw [hF, hF, hF, Derivation.leibniz]
        change (exteriorPower.ιMulti B (i+1)).toMultilinearMap _ = _
        rw [MultilinearMap.cons_add, MultilinearMap.cons_smul, MultilinearMap.cons_smul]
        rfl
      rw [smul_smul, smul_smul, smul_smul, smul_smul, show g * h * c = g * (h * c) by ring,
        hLeib g (h * c), hLeib g c]
      module
    · intro c; simp
    · intro x y hx hy Px Py c
      simp only [smul_add, map_add]
      linear_combination (norm := module) Px c + Py c
    · intro a x hx Px c
      rw [smul_smul c a x]
      exact Px (c * a)
  simpa only [one_smul] using key 1
