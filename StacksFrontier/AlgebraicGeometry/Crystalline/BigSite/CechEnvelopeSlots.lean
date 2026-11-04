module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeProducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.SectionsDividedPowerRing
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Envelope

/-!
# The slot projections of the differentials of a product of smooth-lift objects

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `p` nilpotent on `S` and
`X` separated, affine opens `U_0, …, U_n` of `X` and smooth lifts `L_k` of them, with objects
`D_k` of `CRIS(X/S)` (`CechEnvelope.SmoothLift.object`).  Their product `D_s = D_0 × ⋯ × D_n` is
the divided power envelope `D` of `K = ker(B_0 ⊗_A ⋯ ⊗_A B_n → Γ(U_0 ∩ ⋯ ∩ U_n))`
(`CechEnvelope.isLimitFan`).  This file shows that the divided power differentials
`Ω_{Γ(D_s)} = Ω_{Γ(D_s)/A,δ}` split along the factors: there are `Γ(D_s)`-linear projections
`π_0, …, π_n` with

`π_k(d q_{k'}(b)) = d q_{k'}(b)` if `k = k'`, and `0` otherwise,

where `q_k : Γ(D_k) → Γ(D_s)` is the map of the `k`-th projection, the `d q_k(b)` span
`Ω_{Γ(D_s)}` and `∑ π_k = 1`; the same holds for any product `T` of the `D_k`
(`CechEnvelope.slotProjOfIsLimit`), and the sums `π_Z = ∑_{k ∈ Z} π_k` are natural:
`π_Z ∘ Ω_g = Ω_g ∘ π'_{h⁻¹ Z}` for a morphism of products `g` covering a map of index sets `h`
(`CechEnvelope.slotSum_oneFormsMap`).  These are the support projections of the cosimplicial
module of differential forms of the Čech nerve ([Stacks, Tag 07LA]); note that the projections
are *not* compatible with the codegeneracies in the naive sense `Ω_f ∘ π_e = π_{f(e)} ∘ Ω_f`,
but only in the summed form above.

The construction goes in three steps.

1. On `P = B_0 ⊗_A ⋯ ⊗_A B_n`, the slot derivation
   `δ_k(b_0 ⊗ ⋯ ⊗ b_n) = (∏_{j ≠ k} b_j) · d b_k` (`CechEnvelope.slotDerivation`) gives a
   `P`-linear endomorphism `π_k` of `Ω_{P/A}` (`CechEnvelope.kaehlerSlotProj`) with
   `π_k(d ι_{k'}(b)) = [k = k'] d ι_{k'}(b)`; the `d ι_k(b)` span `Ω_{P/A}`.
2. Through `Ω_{D/A,δ} ≅ D ⊗_P Ω_{P/A}` ([Stacks, Tag 07HW]) the `1 ⊗ π_k` are projections of
   `Ω_{D/A,δ}` (`CechEnvelope.exists_isSlotFamily_envelope`).
3. They are transported along the divided power isomorphisms `D ≅ Γ(Spec D, ⊤) = Γ(D_s)` and
   `Γ(D_s) ≅ Γ(T)` (`CechEnvelope.IsSlotFamily.transport`).

The properties are packaged as `CechEnvelope.IsSlotFamily`; it determines the projections
(`CechEnvelope.IsSlotFamily.unique`), so the choice made in `CechEnvelope.slotProjOfIsLimit` is
canonical.

## Main definitions

* `CechEnvelope.IsSlotFamily` — projections of `Ω_B` along maps `g_k : R_k → B`.
* `CechEnvelope.slotSum` — `π_Z = ∑_{k ∈ Z} π_k`.
* `CechEnvelope.slotProjOfIsLimit` — the slot projections of a product of the `D_k`;
  `CechEnvelope.slotProj` those of the envelope object.

## Main results

* `CechEnvelope.slotProj_d`, `CechEnvelope.span_dividedPowerDifferential_proj`,
  `CechEnvelope.sum_slotProj` — the projections of `Ω_{Γ(D_s)}`.
* `CechEnvelope.slotProjOfIsLimit_d`, `CechEnvelope.span_dividedPowerDifferential_of_isLimit`,
  `CechEnvelope.sum_slotProjOfIsLimit` — the same for any product.
* `CechEnvelope.slotSum_oneFormsMap` — naturality of `π_Z`.

## References

* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

/-- Semilinear maps agreeing on a spanning family of vectors are equal. -/
private theorem linearMap_ext_of_span_iUnion_range {ι : Type*} {X : ι → Type*} {M N R R' : Type*}
    [Semiring R] [Semiring R'] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R' N]
    {σ : R →+* R'} (v : ∀ k, X k → M) (hv : Submodule.span R (⋃ k, Set.range (v k)) = ⊤)
    {f g : M →ₛₗ[σ] N} (h : ∀ k b, f (v k b) = g (v k b)) : f = g :=
  LinearMap.ext_on hv fun ω hω ↦ by
    obtain ⟨k, b, rfl⟩ := Set.mem_iUnion.mp hω
    exact h k b

/-- Projections picking out the vectors of their own slot sum to the identity. -/
private theorem sum_eq_id_of_span_iUnion_range {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} {M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (v : ∀ k, X k → M)
    (hv : Submodule.span R (⋃ k, Set.range (v k)) = ⊤) {π : ι → M →ₗ[R] M}
    (h : ∀ k k' (b : X k'), π k (v k' b) = if k = k' then v k' b else 0) :
    ∑ k, π k = LinearMap.id :=
  linearMap_ext_of_span_iUnion_range v hv fun k' b ↦ by
    simp only [LinearMap.sum_apply, h, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      LinearMap.id_apply]

/-! ### The slot derivations of a finite tensor product -/

section Kaehler

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ι → Type*}
  [∀ k, CommRing (R k)] [∀ k, Algebra A (R k)] {P : Type*} [CommRing P] [Algebra A P]
  (e : (⨂[A] k, R k) ≃ₐ[A] P)

/-- The inclusion of the `k`-th factor `R_k → ⨂_A R_j ≅ P`. -/
abbrev slotIncl (k : ι) : R k →ₐ[A] P :=
  e.toAlgHom.comp (PiTensorProduct.singleAlgHom k)

/-- A pure tensor is the product of the inclusions of its factors. -/
theorem tprod_eq_prod_slotIncl (b : ∀ k, R k) :
    e (PiTensorProduct.tprod A b) = ∏ k, slotIncl e k (b k) := by
  have h : PiTensorProduct.tprod A b =
      ∏ k, PiTensorProduct.singleAlgHom (R := A) (A := R) k (b k) := by
    simp only [PiTensorProduct.singleAlgHom_apply, ← PiTensorProduct.tprod_prod]
    congr 1
    exact (Finset.univ_prod_mulSingle b).symm
  rw [h, map_prod]
  rfl

/-- The product of the inclusions of all factors but the `k`-th. -/
theorem prod_update_slotIncl_of_ne (k : ι) {i : ι} (hi : i ≠ k)
    (b : ∀ j, R j) (x : R i) :
    ∏ j ∈ Finset.univ.erase k, slotIncl e j (Function.update b i x j) =
      slotIncl e i x * ∏ j ∈ (Finset.univ.erase k).erase i, slotIncl e j (b j) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩),
    Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun j hj ↦ ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The product of the inclusions of all factors but the `k`-th does not see the `k`-th. -/
theorem prod_update_slotIncl_self (k : ι) (b : ∀ j, R j) (x : R k) :
    ∏ j ∈ Finset.univ.erase k, slotIncl e j (Function.update b k x j) =
      ∏ j ∈ Finset.univ.erase k, slotIncl e j (b j) :=
  Finset.prod_congr rfl fun j hj ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The multilinear map `b ↦ (∏_{j ≠ k} b_j) · d b_k`. -/
def slotMultilinear (k : ι) : MultilinearMap A R Ω[P⁄A] :=
  MultilinearMap.mk' (fun b ↦ (∏ j ∈ Finset.univ.erase k, slotIncl e j (b j)) •
    KaehlerDifferential.D A P (slotIncl e k (b k)))
  (fun b i x y ↦ by
    by_cases hi : i = k
    · subst hi
      simp only [prod_update_slotIncl_self, Function.update_self, map_add, smul_add]
    · simp only [prod_update_slotIncl_of_ne e k hi, Function.update_of_ne (Ne.symm hi), map_add,
        add_mul, add_smul])
  (fun b i c x ↦ by
    by_cases hi : i = k
    · subst hi
      simp only [prod_update_slotIncl_self, Function.update_self, map_smul, Derivation.map_smul,
        smul_comm _ c]
    · simp only [prod_update_slotIncl_of_ne e k hi, Function.update_of_ne (Ne.symm hi), map_smul,
        smul_mul_assoc, smul_assoc])

/-- The value of `slotMultilinear`. -/
theorem slotMultilinear_apply (k : ι) (b : ∀ j, R j) :
    slotMultilinear e k b = (∏ j ∈ Finset.univ.erase k, slotIncl e j (b j)) •
      KaehlerDifferential.D A P (slotIncl e k (b k)) := rfl

/-- The Leibniz rule for `slotMultilinear` on pure tensors. -/
theorem slotMultilinear_mul (k : ι) (b c : ∀ j, R j) :
    slotMultilinear e k (b * c) = e (PiTensorProduct.tprod A b) • slotMultilinear e k c +
      e (PiTensorProduct.tprod A c) • slotMultilinear e k b := by
  simp only [slotMultilinear_apply, tprod_eq_prod_slotIncl, Pi.mul_apply, map_mul,
    Finset.prod_mul_distrib, Derivation.leibniz]
  rw [← Finset.mul_prod_erase _ (fun j ↦ slotIncl e j (b j)) (Finset.mem_univ k),
    ← Finset.mul_prod_erase _ (fun j ↦ slotIncl e j (c j)) (Finset.mem_univ k)]
  module

/-- The `A`-linear map `⨂ R_j → Ω_{P/A}` lifting `slotMultilinear`. -/
def slotLin (k : ι) : (⨂[A] j, R j) →ₗ[A] Ω[P⁄A] :=
  PiTensorProduct.lift (slotMultilinear e k)

/-- The Leibniz rule for `slotLin`. -/
theorem slotLin_mul (k : ι) (y z : ⨂[A] j, R j) :
    slotLin e k (y * z) = e y • slotLin e k z + e z • slotLin e k y := by
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r b =>
    induction z using PiTensorProduct.induction_on with
    | smul_tprod s c =>
      rw [PiTensorProduct.smul_tprod_mul_smul_tprod]
      simp only [slotLin, map_smul, PiTensorProduct.lift.tprod, slotMultilinear_mul]
      simp only [← algebraMap_smul P r, ← algebraMap_smul P s, ← algebraMap_smul P (r * s),
        Algebra.smul_def, map_mul]
      module
    | add z₁ z₂ h₁ h₂ =>
      simp only [mul_add, map_add, h₁, h₂, smul_add, add_smul]
      abel
  | add y₁ y₂ h₁ h₂ =>
    simp only [add_mul, map_add, h₁, h₂, smul_add, add_smul]
    abel

/-- **The `k`-th slot derivation** `δ_k` of `P ≅ ⨂_A R_j`:
`δ_k(b_0 ⊗ ⋯ ⊗ b_n) = (∏_{j ≠ k} b_j) · d b_k`. -/
def slotDerivation (k : ι) : Derivation A P Ω[P⁄A] :=
  Derivation.mk' ((slotLin e k).comp e.symm.toLinearMap) fun x y ↦ by
    simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_mul, slotLin_mul,
      AlgEquiv.apply_symm_apply]

/-- `δ_k` on the inclusion of a factor. -/
theorem slotDerivation_slotIncl (k k' : ι) (b : R k') :
    slotDerivation e k (slotIncl e k' b) =
      if k = k' then KaehlerDifferential.D A P (slotIncl e k' b) else 0 := by
  show slotLin e k (e.symm (e (PiTensorProduct.singleAlgHom k' b))) = _
  rw [AlgEquiv.symm_apply_apply, PiTensorProduct.singleAlgHom_apply, slotLin,
    PiTensorProduct.lift.tprod, slotMultilinear_apply]
  split_ifs with h
  · subst h
    rw [Finset.prod_eq_one fun j hj ↦ ?_, one_smul, MonoidHom.mulSingle_apply,
      Pi.mulSingle_eq_same]
    rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne (Finset.ne_of_mem_erase hj), map_one]
  · rw [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, map_one, Derivation.map_one_eq_zero,
      smul_zero]

/-- **The `k`-th slot projection** `π_k` of `Ω_{P/A}` for `P ≅ ⨂_A R_j`: the `P`-linear
endomorphism with `π_k(d b) = δ_k(b)`. -/
def kaehlerSlotProj (k : ι) : Ω[P⁄A] →ₗ[P] Ω[P⁄A] :=
  (slotDerivation e k).liftKaehlerDifferential

/-- `π_k` on the differential of the inclusion of a factor. -/
theorem kaehlerSlotProj_D (k k' : ι) (b : R k') :
    kaehlerSlotProj e k (KaehlerDifferential.D A P (slotIncl e k' b)) =
      if k = k' then KaehlerDifferential.D A P (slotIncl e k' b) else 0 := by
  rw [kaehlerSlotProj, Derivation.liftKaehlerDifferential_comp_D, slotDerivation_slotIncl]

/-- **`Ω_{P/A}` is spanned by the differentials of the factors.** -/
theorem span_kaehler_slotIncl :
    Submodule.span P (⋃ k, Set.range fun b : R k ↦ KaehlerDifferential.D A P (slotIncl e k b)) =
      ⊤ := by
  set N := Submodule.span P
    (⋃ k, Set.range fun b : R k ↦ KaehlerDifferential.D A P (slotIncl e k b))
  let S₀ : Subalgebra A P :=
    { carrier := {x | KaehlerDifferential.D A P x ∈ N}
      mul_mem' := fun {x y} hx hy ↦ by
        show KaehlerDifferential.D A P (x * y) ∈ N
        rw [Derivation.leibniz]
        exact N.add_mem (N.smul_mem x hy) (N.smul_mem y hx)
      add_mem' := fun {x y} hx hy ↦ by
        show KaehlerDifferential.D A P (x + y) ∈ N
        rw [map_add]
        exact N.add_mem hx hy
      algebraMap_mem' := fun a ↦ by
        show KaehlerDifferential.D A P (algebraMap A P a) ∈ N
        rw [Derivation.map_algebraMap]
        exact N.zero_mem }
  have hS : ∀ x : P, x ∈ S₀ := fun x ↦ by
    rw [← e.apply_symm_apply x]
    induction e.symm x using PiTensorProduct.induction_on with
    | smul_tprod r b =>
      rw [map_smul, tprod_eq_prod_slotIncl]
      refine S₀.smul_mem (Subalgebra.prod_mem _ fun k _ ↦ ?_) r
      exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, b k, rfl⟩)
    | add y z hy hz =>
      rw [map_add]
      exact S₀.add_mem hy hz
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  exact hS x

/-- The slot projections sum to the identity. -/
theorem sum_kaehlerSlotProj : ∑ k, kaehlerSlotProj e k = LinearMap.id := by
  exact sum_eq_id_of_span_iUnion_range _ (span_kaehler_slotIncl e) (kaehlerSlotProj_D e)

end Kaehler

/-! ### Slot families on divided power differentials -/

section Family

open DeRhamPair DividedPowers

variable {A : Type u} [CommRing A] {B : DividedPowerRing.{u}} [Algebra A B] {ι : Type*}
  [Fintype ι] [DecidableEq ι] {R : ι → Type*}

/-- **A slot family** on `Ω_B = Ω_{B/A,δ}` along maps `g_k : R_k → B`: `B`-linear endomorphisms
`π_k` with `π_k(d g_{k'}(b)) = d g_{k'}(b)` if `k = k'` and `0` otherwise, the differentials
`d g_k(b)` spanning `Ω_B`. -/
structure IsSlotFamily (g : ∀ k, R k → B)
    (π : ι → dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) : Prop where
  /-- `π_k` keeps the differentials of the `k`-th slot and kills those of the others. -/
  map_d : ∀ k k' (b : R k'), π k (dividedPowerDifferential (A := A) B.dividedPowers (g k' b)) =
    if k = k' then dividedPowerDifferential (A := A) B.dividedPowers (g k' b) else 0
  /-- The differentials of the slots span. -/
  span : Submodule.span (B : Type u)
    (⋃ k, Set.range fun b : R k ↦ dividedPowerDifferential (A := A) B.dividedPowers (g k b)) = ⊤

variable {g : ∀ k, R k → B}
  {π : ι → dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
    dividedPowerDifferentials (A := A) B.dividedPowers}

/-- The sum of the projections of a slot family over a set of slots. -/
def slotSum (π : ι → dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
    dividedPowerDifferentials (A := A) B.dividedPowers) (Z : Set ι) :
    dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers :=
  open scoped Classical in ∑ k ∈ Finset.univ.filter (· ∈ Z), π k

/-- `slotSum` on the differential of a slot. -/
theorem IsSlotFamily.slotSum_d (h : IsSlotFamily g π) (Z : Set ι) (k' : ι) (b : R k') :
    open scoped Classical in
    slotSum π Z (dividedPowerDifferential (A := A) B.dividedPowers (g k' b)) =
      if k' ∈ Z then dividedPowerDifferential (A := A) B.dividedPowers (g k' b) else 0 := by
  classical
  rw [slotSum, LinearMap.sum_apply]
  simp only [h.map_d]
  rw [Finset.sum_ite_eq']
  by_cases hk : k' ∈ Z <;> simp [hk]

omit [Fintype ι] in
/-- Two slot families along the same maps agree. -/
theorem IsSlotFamily.unique (h : IsSlotFamily g π)
    {π' : ι → dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers} (h' : IsSlotFamily g π') :
    π = π' := by
  funext k
  exact linearMap_ext_of_span_iUnion_range _ h.span fun k' b ↦ by rw [h.map_d, h'.map_d]

/-- **The projections of a slot family sum to the identity.** -/
theorem IsSlotFamily.sum_eq_id (h : IsSlotFamily g π) : ∑ k, π k = LinearMap.id := by
  exact sum_eq_id_of_span_iUnion_range _ h.span h.map_d

/-- The sum over all slots is the identity. -/
theorem IsSlotFamily.slotSum_univ (h : IsSlotFamily g π) : slotSum π Set.univ = LinearMap.id := by
  classical
  rw [← h.sum_eq_id, slotSum]
  congr 1
  ext k
  simp

omit [DecidableEq ι] in
/-- The sum over no slot is zero. -/
theorem slotSum_empty : slotSum π ∅ = 0 := by
  classical
  simp [slotSum]

omit [Fintype ι] in
/-- A slot family stays one when the slots are reparametrized by surjections. -/
theorem IsSlotFamily.reparam (h : IsSlotFamily g π) {R' : ι → Type*} (r : ∀ k, R' k → R k)
    (hr : ∀ k, Function.Surjective (r k)) {g' : ∀ k, R' k → B}
    (hg : ∀ k b, g' k b = g k (r k b)) : IsSlotFamily g' π where
  map_d k k' b := by rw [hg, h.map_d]
  span := by
    rw [← h.span]
    congr 1
    refine Set.iUnion_congr fun k ↦ ?_
    ext ω
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨r k b, by simp only [hg]⟩
    · rintro ⟨b, rfl⟩
      obtain ⟨b', rfl⟩ := hr k b
      exact ⟨b', by simp only [hg]⟩

/-- The value of `oneFormsMap` on a universal differential. -/
theorem oneFormsMap_dividedPowerDifferential {C : DividedPowerRing.{u}} [Algebra A C]
    (f : (B : Type u) →ₐ[A] C)
    (hf : IsDPMorphism B.dividedPowers C.dividedPowers f.toRingHom) (b : B) :
    oneFormsMap f hf (dividedPowerDifferential (A := A) B.dividedPowers b) =
      dividedPowerDifferential (A := A) C.dividedPowers (f b) :=
  mapDifferentialsOfDPMorphism_d (A := A) (J := B.ideal) (delta := B.dividedPowers)
    C.dividedPowers f hf b

variable {B' : DividedPowerRing.{u}} [Algebra A B']

/-- The conjugate of an endomorphism of `Ω_B` by a divided power isomorphism `B ≅ B'`. -/
def transportSlot (φ : (B : Type u) →ₐ[A] B')
    (hφ : IsDPMorphism B.dividedPowers B'.dividedPowers φ.toRingHom)
    (ψ : (B' : Type u) →ₐ[A] B) (hψ : IsDPMorphism B'.dividedPowers B.dividedPowers ψ.toRingHom)
    (hφψ : ∀ y, φ (ψ y) = y)
    (ε : dividedPowerDifferentials (A := A) B.dividedPowers →ₗ[(B : Type u)]
      dividedPowerDifferentials (A := A) B.dividedPowers) :
    dividedPowerDifferentials (A := A) B'.dividedPowers →ₗ[(B' : Type u)]
      dividedPowerDifferentials (A := A) B'.dividedPowers where
  toFun ω := oneFormsMap φ hφ (ε (oneFormsMap ψ hψ ω))
  map_add' x y := by simp only [map_add]
  map_smul' b ω := by
    rw [map_smulₛₗ (oneFormsMap ψ hψ), LinearMap.map_smul, map_smulₛₗ (oneFormsMap φ hφ)]
    exact congrArg (· • _) (hφψ b)

omit [Fintype ι] in
/-- **A slot family transported along a divided power isomorphism.** -/
theorem IsSlotFamily.transport (h : IsSlotFamily g π) (φ : (B : Type u) →ₐ[A] B')
    (hφ : IsDPMorphism B.dividedPowers B'.dividedPowers φ.toRingHom)
    (ψ : (B' : Type u) →ₐ[A] B) (hψ : IsDPMorphism B'.dividedPowers B.dividedPowers ψ.toRingHom)
    (hφψ : ∀ y, φ (ψ y) = y) (hψφ : ∀ x, ψ (φ x) = x) :
    IsSlotFamily (fun k b ↦ φ (g k b)) fun k ↦ transportSlot φ hφ ψ hψ hφψ (π k) where
  map_d k k' b := by
    show oneFormsMap φ hφ (π k (oneFormsMap ψ hψ _)) = _
    rw [oneFormsMap_dividedPowerDifferential, hψφ, h.map_d]
    split_ifs
    · exact oneFormsMap_dividedPowerDifferential φ hφ _
    · exact map_zero _
  span := by
    rw [eq_top_iff]
    intro ω _
    have hω : oneFormsMap ψ hψ ω ∈ Submodule.span (B : Type u)
        (⋃ k, Set.range fun b : R k ↦ dividedPowerDifferential (A := A) B.dividedPowers
          (g k b)) := h.span ▸ Submodule.mem_top
    have key : ∀ x ∈ Submodule.span (B : Type u)
        (⋃ k, Set.range fun b : R k ↦ dividedPowerDifferential (A := A) B.dividedPowers
          (g k b)),
        oneFormsMap φ hφ x ∈ Submodule.span (B' : Type u)
          (⋃ k, Set.range fun b : R k ↦ dividedPowerDifferential (A := A) B'.dividedPowers
            (φ (g k b))) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, b, rfl⟩ := Set.mem_iUnion.mp hy
        rw [oneFormsMap_dividedPowerDifferential]
        exact Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, b, rfl⟩)
      | zero =>
        rw [map_zero]
        exact Submodule.zero_mem _
      | add y z _ _ hy hz =>
        rw [map_add]
        exact Submodule.add_mem _ hy hz
      | smul c y _ hy =>
        rw [map_smulₛₗ]
        exact Submodule.smul_mem _ _ hy
    have h3 : oneFormsMap φ hφ (oneFormsMap ψ hψ ω) = ω := by
      have hc : (oneFormsMap φ hφ).toAddMonoidHom.comp (oneFormsMap ψ hψ).toAddMonoidHom =
          AddMonoidHom.id _ := by
        show (mapDifferentialsOfDPMorphism (A := A) (J := B.ideal) (delta := B.dividedPowers)
          B'.dividedPowers φ hφ).comp (mapDifferentialsOfDPMorphism (A := A) (J := B'.ideal)
            (delta := B'.dividedPowers) B.dividedPowers ψ hψ) = _
        rw [mapDifferentialsOfDPMorphism_comp]
        have he : φ.comp ψ = AlgHom.id A B' := AlgHom.ext hφψ
        simpa only [he] using mapDifferentialsOfDPMorphism_id (A := A) (J := B'.ideal)
          (delta := B'.dividedPowers)
      exact DFunLike.congr_fun hc ω
    simpa only [h3] using key _ hω

/-- **Naturality of slot sums**: for a divided power morphism `f : B' → B` carrying the `j`-th
slot of `B'` to the `h(j)`-th slot of `B`, `π_Z ∘ Ω_f = Ω_f ∘ π'_{h⁻¹ Z}`. -/
theorem IsSlotFamily.slotSum_oneFormsMap (hπ : IsSlotFamily g π) {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] (h : ι' → ι) {g' : ∀ j, R (h j) → B'}
    {π' : ι' → dividedPowerDifferentials (A := A) B'.dividedPowers →ₗ[(B' : Type u)]
      dividedPowerDifferentials (A := A) B'.dividedPowers} (hπ' : IsSlotFamily g' π')
    (f : (B' : Type u) →ₐ[A] B) (hf : IsDPMorphism B'.dividedPowers B.dividedPowers f.toRingHom)
    (hfg : ∀ j b, f (g' j b) = g (h j) b) (Z : Set ι) (ω) :
    slotSum π Z (oneFormsMap f hf ω) = oneFormsMap f hf (slotSum π' (h ⁻¹' Z) ω) := by
  classical
  have hcomp : (slotSum π Z).comp (oneFormsMap f hf) =
      (oneFormsMap f hf).comp (slotSum π' (h ⁻¹' Z)) := by
    refine linearMap_ext_of_span_iUnion_range _ hπ'.span fun j b ↦ ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, oneFormsMap_dividedPowerDifferential, hfg,
      hπ.slotSum_d, hπ'.slotSum_d]
    simp only [Set.mem_preimage]
    split_ifs
    · rw [oneFormsMap_dividedPowerDifferential, hfg]
    · rw [map_zero]
  exact DFunLike.congr_fun hcomp ω

end Family

/-! ### Slot families on the differentials of a divided power envelope -/

section Envelope

variable (A : DividedPowerRing.{u}) {B : Type u} [CommRing B] (f : A →+* B) (J : Ideal B)
  (hJ : A.ideal.map f ≤ J) (E : DividedPowerEnvelope A f J hJ) {ι : Type*} [Fintype ι]
  [DecidableEq ι] {R : ι → Type*} (g : ∀ k, R k → B)

omit [Fintype ι] in
/-- **Slot projections of the Kähler differentials extend to the divided power differentials of
the envelope**, through `Ω_{D/A,δ} ≅ D ⊗_B Ω_{B/A}` ([Stacks, Tag 07HW]): `π_k ↦ 1 ⊗ π_k`. -/
theorem exists_isSlotFamily_envelope :
    letI : Algebra A B := f.toAlgebra
    letI : Algebra A E.object := E.structureMap.toRingHom.toAlgebra
    ∀ π : ι → Ω[B⁄A] →ₗ[B] Ω[B⁄A],
      (∀ k k' (b : R k'), π k (KaehlerDifferential.D A B (g k' b)) =
        if k = k' then KaehlerDifferential.D A B (g k' b) else 0) →
      Submodule.span B (⋃ k, Set.range fun b : R k ↦ KaehlerDifferential.D A B (g k b)) = ⊤ →
      ∃ π' : ι → dividedPowerDifferentials (A := A) E.object.dividedPowers →ₗ[(E.object : Type u)]
          dividedPowerDifferentials (A := A) E.object.dividedPowers,
        IsSlotFamily (A := A) (B := E.object) (fun k b ↦ E.algebraMap.toRingHom (g k b)) π' := by
  let : Algebra A B := f.toAlgebra
  let : Algebra A E.object := E.structureMap.toRingHom.toAlgebra
  let : Algebra B E.object := E.algebraMap.toRingHom.toAlgebra
  intro π hπ hspan
  obtain ⟨eqv, heqv⟩ := dividedPowerEnvelopeDifferentialsEquiv A f J hJ E
  have hsymm : ∀ b : B, eqv.symm ((1 : E.object) ⊗ₜ[B] KaehlerDifferential.D A B b) =
      dividedPowerDifferential (A := A) E.object.dividedPowers (E.algebraMap.toRingHom b) :=
    fun b ↦ (LinearEquiv.symm_apply_eq _).mpr (heqv b).symm
  refine ⟨fun k ↦ eqv.symm.toLinearMap ∘ₗ (π k).baseChange E.object ∘ₗ eqv.toLinearMap,
    ⟨fun k k' b ↦ ?_, ?_⟩⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, heqv, LinearMap.baseChange_tmul, hπ]
    split_ifs
    · exact hsymm _
    · rw [TensorProduct.tmul_zero, map_zero]
  · have hX : Submodule.span (E.object : Type u) (TensorProduct.mk B E.object Ω[B⁄A] 1 ''
        ⋃ k, Set.range fun b : R k ↦ KaehlerDifferential.D A B (g k b)) = ⊤ := by
      rw [← Submodule.baseChange_span, hspan, Submodule.baseChange_top]
    have h1 : (Submodule.span (E.object : Type u) (TensorProduct.mk B E.object Ω[B⁄A] 1 ''
        ⋃ k, Set.range fun b : R k ↦ KaehlerDifferential.D A B (g k b))).map
          eqv.symm.toLinearMap ≤ Submodule.span (E.object : Type u)
          (⋃ k, Set.range fun b : R k ↦ dividedPowerDifferential (A := A) E.object.dividedPowers
            (E.algebraMap.toRingHom (g k b))) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨_, hm, rfl⟩, rfl⟩
      obtain ⟨k, b, rfl⟩ := Set.mem_iUnion.mp hm
      refine Submodule.subset_span (Set.mem_iUnion.mpr ⟨k, b, ?_⟩)
      exact (hsymm _).symm
    rw [hX, Submodule.map_top, LinearEquiv.range] at h1
    exact top_le_iff.mp h1

end Envelope

/-! ### The slot projections of a product of smooth-lift objects -/

section Crystalline

open DeRhamPair DividedPowers

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) {n : ℕ} {U : Fin (n + 1) → S.X.Opens}
  [∀ k, IsAffine (U k)] [S.X.IsSeparated] (L : ∀ k, SmoothLift S (U k).ι)

omit [IsAffine S.S.scheme] [S.X.IsSeparated] in
/-- The map on global sections of the structure morphism, read through `appTop`. -/
private theorem crysBaseAppLE_apply_eq_appTop (T : Thickening S) (a : Γ(S.S.scheme, ⊤)) :
    crysBaseAppLE S T a = T.toBase.hom.appTop.hom a :=
  congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_eq_app T.toBase.hom)

/-- **The slot family of the envelope object**: projections of `Ω_{Γ(D_s)}` onto the parts spanned
by the differentials of the factors `Γ(D_k)`. -/
theorem exists_isSlotFamily_envelopeObject :
    ∃ π : Fin (n + 1) → dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (envelopeObject hp L)).dividedPowers →ₗ[(sectionsDPRing S
          (envelopeObject hp L) : Type u)] dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (envelopeObject hp L)).dividedPowers,
      IsSlotFamily (fun k (b : sectionsDPRing S ((L k).object hp)) ↦
        sectionsDPRingMap (proj hp L k) b) π := by
  let e : @AlgEquiv (baseSectionsRing S) (⨂[baseSectionsRing S] k, (L k).ring) (tensorRing L)
      _ _ _ _ (algebraMap (baseSectionsRing S) (tensorRing L)).toAlgebra :=
    @AlgEquiv.ofRingEquiv _ _ _ _ _ _ _
      (algebraMap (baseSectionsRing S) (tensorRing L)).toAlgebra (RingEquiv.refl _)
      fun _ ↦ rfl
  let inst : Algebra (baseSectionsRing S) (tensorRing L) :=
    (algebraMap (baseSectionsRing S) (tensorRing L)).toAlgebra
  obtain ⟨π₀, h₀⟩ := exists_isSlotFamily_envelope (baseSectionsRing S) _ _ _ (envelope L)
    (fun k ↦ slotIncl e k) (kaehlerSlotProj e) (kaehlerSlotProj_D e)
    (span_kaehler_slotIncl e)
  let : Algebra Γ(S.S.scheme, ⊤) (envelope L).object :=
    (envelope L).structureMap.toRingHom.toAlgebra
  let φ : ((envelope L).object : Type u) →ₐ[Γ(S.S.scheme, ⊤)]
      sectionsDPRing S (envelopeObject hp L) :=
    { toRingHom := (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
      commutes' := fun a ↦
        ((crysBaseAppLE_apply_eq_appTop _ a).trans (envelopeObject_toBase_appTop hp L a)).symm }
  let ψ : (sectionsDPRing S (envelopeObject hp L) : Type u) →ₐ[Γ(S.S.scheme, ⊤)]
      (envelope L).object :=
    { toRingHom := (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).hom.hom
      commutes' := fun a ↦
        (congrArg (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).hom.hom
          ((crysBaseAppLE_apply_eq_appTop _ a).trans (envelopeObject_toBase_appTop hp L a))).trans
          (DividedPowerScheme.ΓSpecIso_hom_inv_apply _ _) }
  have hφ : IsDPMorphism (envelope L).object.dividedPowers
      (sectionsDPRing S (envelopeObject hp L)).dividedPowers φ.toRingHom :=
    (DividedPowerScheme.specSectionsRingIso (envelope L).object).hom.isDPMorphism
  have hψ : IsDPMorphism (sectionsDPRing S (envelopeObject hp L)).dividedPowers
      (envelope L).object.dividedPowers ψ.toRingHom :=
    (DividedPowerScheme.specSectionsRingIso (envelope L).object).inv.isDPMorphism
  have h₁ := @IsSlotFamily.transport Γ(S.S.scheme, ⊤) _ (envelope L).object this _ _ _ _ π₀ _ _
    h₀ φ hφ ψ hψ (ΓSpecIso_inv_hom_apply _)
    (fun x ↦ DividedPowerScheme.ΓSpecIso_hom_inv_apply (CommRingCat.of (envelope L).object) x)
  exact ⟨_, h₁.reparam (fun k ↦ (Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).hom.hom)
    (fun k b ↦ ⟨(Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom b,
      DividedPowerScheme.ΓSpecIso_hom_inv_apply (CommRingCat.of (L k).dividedPowerRing) b⟩)
    fun k b ↦ proj_targetHom_appTop hp L k b⟩

/-- **The slot family of any product of the smooth-lift objects**, transported from the envelope
object along the identification of the two products. -/
theorem exists_isSlotFamily_of_isLimit {T : Thickening S} {p : ∀ k, T ⟶ (L k).object hp}
    (hT : IsLimit (Fan.mk T p : Fan fun k ↦ (L k).object hp)) :
    ∃ π : Fin (n + 1) → dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S T).dividedPowers →ₗ[(sectionsDPRing S T : Type u)]
        dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T).dividedPowers,
      IsSlotFamily (fun k (b : sectionsDPRing S ((L k).object hp)) ↦ sectionsDPRingMap (p k) b)
        π := by
  obtain ⟨π, h⟩ := exists_isSlotFamily_envelopeObject hp L
  let i := hT.conePointUniqueUpToIso (isLimitFan hp L)
  have hi : ∀ k, i.hom ≫ proj hp L k = p k := fun k ↦
    hT.conePointUniqueUpToIso_hom_comp (isLimitFan hp L) ⟨k⟩
  refine ⟨_, (h.transport (sectionsDPRingMap i.hom) (isDPMorphism_sectionsDPRingMap _)
    (sectionsDPRingMap i.inv) (isDPMorphism_sectionsDPRingMap _) (fun y ↦ ?_) (fun x ↦ ?_)).reparam
    (fun _ ↦ id) (fun _ ↦ Function.surjective_id) (fun k b ↦ ?_)⟩
  · rw [← AlgHom.comp_apply, ← sectionsDPRingMap_comp, i.hom_inv_id]
    exact DFunLike.congr_fun (sectionsDPRingMap_id _) y
  · rw [← AlgHom.comp_apply, ← sectionsDPRingMap_comp, i.inv_hom_id]
    exact DFunLike.congr_fun (sectionsDPRingMap_id _) x
  · rw [← AlgHom.comp_apply, ← sectionsDPRingMap_comp, hi]
    rfl

variable {T : Thickening S} {p : ∀ k, T ⟶ (L k).object hp}
  (hT : IsLimit (Fan.mk T p : Fan fun k ↦ (L k).object hp))

/-- **The `k`-th slot projection of `Ω_{Γ(T)}` for a product `T = ∏ D_j` of the smooth-lift
objects**: the `Γ(T, 𝒪_T)`-linear endomorphism of the divided power differentials which keeps the
differentials of sections coming from the `k`-th factor and kills those coming from the
others. -/
def slotProjOfIsLimit (k : Fin (n + 1)) :
    dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T).dividedPowers
      →ₗ[(sectionsDPRing S T : Type u)]
      dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T).dividedPowers :=
  Classical.choose (exists_isSlotFamily_of_isLimit hp L hT) k

/-- The slot projections of a product form a slot family. -/
theorem isSlotFamily_slotProjOfIsLimit :
    IsSlotFamily (fun k (b : sectionsDPRing S ((L k).object hp)) ↦ sectionsDPRingMap (p k) b)
      (slotProjOfIsLimit hp L hT) :=
  Classical.choose_spec (exists_isSlotFamily_of_isLimit hp L hT)

/-- **The slot projections on the differentials of the factors**:
`π_k(d q_{k'}(b)) = d q_{k'}(b)` if `k = k'`, and `0` otherwise. -/
theorem slotProjOfIsLimit_d (k k' : Fin (n + 1)) (b : sectionsDPRing S ((L k').object hp)) :
    slotProjOfIsLimit hp L hT k (dividedPowerDifferential (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S T).dividedPowers (sectionsDPRingMap (p k') b)) =
      if k = k' then dividedPowerDifferential (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S T).dividedPowers (sectionsDPRingMap (p k') b) else 0 :=
  (isSlotFamily_slotProjOfIsLimit hp L hT).map_d k k' b

include hT in
/-- **The differentials of the sections coming from the factors span `Ω_{Γ(T)}`.** -/
theorem span_dividedPowerDifferential_of_isLimit :
    Submodule.span (sectionsDPRing S T : Type u)
        (⋃ k, Set.range fun b : sectionsDPRing S ((L k).object hp) ↦
          dividedPowerDifferential (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T).dividedPowers
            (sectionsDPRingMap (p k) b)) = ⊤ :=
  (isSlotFamily_slotProjOfIsLimit hp L hT).span

/-- **The slot projections of a product sum to the identity.** -/
theorem sum_slotProjOfIsLimit : ∑ k, slotProjOfIsLimit hp L hT k = LinearMap.id :=
  (isSlotFamily_slotProjOfIsLimit hp L hT).sum_eq_id

/-- **The `k`-th slot projection of `Ω_{Γ(D_s)}`** for the envelope object
`D_s = D_0 × ⋯ × D_n`. -/
abbrev slotProj (k : Fin (n + 1)) :
    dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (envelopeObject hp L)).dividedPowers
      →ₗ[(sectionsDPRing S (envelopeObject hp L) : Type u)]
      dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (envelopeObject hp L)).dividedPowers :=
  slotProjOfIsLimit hp L (isLimitFan hp L) k

/-- **The slot projections of the envelope object on the differentials of the factors**:
`π_k(d q_{k'}(b)) = d q_{k'}(b)` if `k = k'`, and `0` otherwise, where
`q_k : Γ(D_k) → Γ(D_s)` is the map of the `k`-th projection. -/
theorem slotProj_d (k k' : Fin (n + 1)) (b : sectionsDPRing S ((L k').object hp)) :
    slotProj hp L k (dividedPowerDifferential (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (envelopeObject hp L)).dividedPowers
        (sectionsDPRingMap (proj hp L k') b)) =
      if k = k' then dividedPowerDifferential (A := Γ(S.S.scheme, ⊤))
        (sectionsDPRing S (envelopeObject hp L)).dividedPowers
        (sectionsDPRingMap (proj hp L k') b) else 0 :=
  slotProjOfIsLimit_d hp L (isLimitFan hp L) k k' b

/-- **`Ω_{Γ(D_s)}` is spanned by the differentials of the sections coming from the factors.** -/
theorem span_dividedPowerDifferential_proj :
    Submodule.span (sectionsDPRing S (envelopeObject hp L) : Type u)
        (⋃ k, Set.range fun b : sectionsDPRing S ((L k).object hp) ↦
          dividedPowerDifferential (A := Γ(S.S.scheme, ⊤))
            (sectionsDPRing S (envelopeObject hp L)).dividedPowers
            (sectionsDPRingMap (proj hp L k) b)) = ⊤ :=
  span_dividedPowerDifferential_of_isLimit hp L (isLimitFan hp L)

/-- **The slot projections of the envelope object sum to the identity.** -/
theorem sum_slotProj : ∑ k, slotProj hp L k = LinearMap.id :=
  sum_slotProjOfIsLimit hp L (isLimitFan hp L)

/-- **Naturality of the slot projections on the support of a set of slots**: for products
`T = ∏_{k ≤ n} D_k` and `T' = ∏_{j ≤ m} D_{h(j)}` and a morphism `g : T ⟶ T'` with
`g ≫ p'_j = p_{h(j)}`, `π_Z ∘ Ω_g = Ω_g ∘ π'_{h⁻¹ Z}`, where `π_Z = ∑_{k ∈ Z} π_k`. -/
theorem slotSum_oneFormsMap {m : ℕ} (h : Fin (m + 1) → Fin (n + 1)) {T' : Thickening S}
    {p' : ∀ j, T' ⟶ (L (h j)).object hp}
    (hT' : IsLimit (Fan.mk T' p' : Fan fun j ↦ (L (h j)).object hp)) (g : T ⟶ T')
    (hg : ∀ j, g ≫ p' j = p (h j)) (Z : Set (Fin (n + 1)))
    (ω : dividedPowerDifferentials (A := Γ(S.S.scheme, ⊤)) (sectionsDPRing S T').dividedPowers) :
    slotSum (slotProjOfIsLimit hp L hT) Z
        (oneFormsMap (sectionsDPRingMap g) (isDPMorphism_sectionsDPRingMap g) ω) =
      oneFormsMap (sectionsDPRingMap g) (isDPMorphism_sectionsDPRingMap g)
        (slotSum (slotProjOfIsLimit hp (fun j ↦ L (h j)) hT') (h ⁻¹' Z) ω) :=
  (isSlotFamily_slotProjOfIsLimit hp L hT).slotSum_oneFormsMap h
    (isSlotFamily_slotProjOfIsLimit hp (fun j ↦ L (h j)) hT') _ _
    (fun j b ↦ by rw [← AlgHom.comp_apply, ← sectionsDPRingMap_comp, hg]) Z ω

end Crystalline

end Crystalline.GlobalCrystallineSituation.CechEnvelope
