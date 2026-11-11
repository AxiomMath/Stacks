module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.CuspFormsFinite

/-!
# Base change of cusp forms

Let `K` be a global function field of characteristic `p` and `Λ` a field in which `p` is
invertible, containing a field `F`. The base change map `Λ ⊗_F C(F) → C(Λ)` on cusp forms with
central character is an isomorphism; for `F` the prime subfield this is the identification
`C(Λ) = C(F) ⊗_F Λ` of the second clause of Stacks 03VW.

When `p` is invertible, the cusp condition, which quantifies over every open subgroup `U` leaving
the integrand invariant, is equivalent to the same condition for the single subgroup `U_x`
attached to `x` (the `y` with `x (1, y; 0, 1) x⁻¹ ∈ GL₂(O)`): the sums over the transversals of
two such subgroups differ by an index, which is a power of `p`. The latter condition is linear,
so `C(Λ)` is cut out by linear conditions with coefficients in `F`, and the coordinates of an
element of `C(Λ)` in an `F`-basis of `Λ` lie in `C(F)`.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.stabSubgroup`: the subgroup `U_x`.
* `Stacks.Adeles.GlobalFunctionField.StarCusp`: the cusp condition for the subgroups `U_x`.
* `Stacks.Adeles.GlobalFunctionField.cuspFormsBaseChange`: the base change map
  `Λ ⊗_F C(F) → C(Λ)`.

## Main results

* `Stacks.Adeles.GlobalFunctionField.sum_transversal_eq`: sums over transversals.
* `Stacks.Adeles.GlobalFunctionField.exists_adeleLattice_le_of_isOpen`: an open subgroup of `A`
  contains some `A(E)`.
* `Stacks.Adeles.GlobalFunctionField.isUnramifiedCuspForm_of_starCusp`: when `p` is invertible,
  the cusp condition for the subgroups `U_x` implies the cusp condition.
* `Stacks.Adeles.GlobalFunctionField.cuspFormsBaseChange_injective` and
  `Stacks.Adeles.GlobalFunctionField.cuspFormsBaseChange_surjective`: the base change map is
  bijective, the latter when `p` is invertible in `Λ`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

section Transversals

/-- Sums over transversals: if `φ` is invariant under `N' ⊇ N`, then the sum of `φ` over a
transversal of `G ⧸ N` is `[N' : N]` times its sum over a transversal of `G ⧸ N'`. -/
public theorem sum_transversal_eq {G : Type*} [AddCommGroup G] {M : Type*} [AddCommMonoid M]
    {N N' : AddSubgroup G} (hNN' : N ≤ N') (φ : G → M) (hφ : ∀ z, ∀ y ∈ N', φ (z + y) = φ z)
    {s s' : Finset G} (hs : ∀ a, ∃! z ∈ s, a - z ∈ N') (hs' : ∀ a, ∃! z ∈ s', a - z ∈ N) :
    ∑ z ∈ s', φ z = N.relIndex N' • ∑ z ∈ s, φ z := by
  classical
  choose π hπs hπ using fun a => (hs a).exists
  have hφπ : ∀ a, φ a = φ (π a) := by
    intro a
    have := hφ (π a) (a - π a) (hπ a)
    rwa [add_sub_cancel] at this
  have hπeq : ∀ a z, z ∈ s → a - z ∈ N' → π a = z := fun a z hz haz => by
    obtain ⟨_, -, huniq⟩ := hs a
    rw [huniq (π a) ⟨hπs a, hπ a⟩, huniq z ⟨hz, haz⟩]
  rw [← Finset.sum_fiberwise_of_maps_to (s := s') (t := s) (g := π) (fun a _ => hπs a),
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hfib : ∀ a ∈ s'.filter (fun a => π a = z), φ a = φ z := by
    intro a ha
    rw [hφπ a, (Finset.mem_filter.1 ha).2]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const]
  congr 1
  -- the fibre over `z` is in bijection with `N' ⧸ N`
  let e : (s'.filter fun a => π a = z) → N' ⧸ N.addSubgroupOf N' := fun a =>
    QuotientAddGroup.mk ⟨(a : G) - z, by
      have h1 := hπ a
      rw [(Finset.mem_filter.1 a.2).2] at h1
      exact h1⟩
  have he : Function.Bijective e := by
    refine ⟨fun a b hab => ?_, fun q => ?_⟩
    · have h := QuotientAddGroup.eq.1 hab
      rw [AddSubgroup.mem_addSubgroupOf] at h
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, neg_sub] at h
      have hab' : (a : G) - b ∈ N := by
        have := N.neg_mem h
        convert this using 1; abel
      obtain ⟨z', -, huniq⟩ := hs' a
      apply Subtype.ext
      rw [huniq a ⟨(Finset.mem_filter.1 a.2).1, by simp⟩,
        huniq b ⟨(Finset.mem_filter.1 b.2).1, hab'⟩]
    · obtain ⟨n, rfl⟩ := QuotientAddGroup.mk_surjective q
      obtain ⟨z', ⟨hzs', hz'⟩, -⟩ := hs' (z + n)
      have hz'N' : z' - z ∈ N' := by
        have : z' - z = (n : G) - (z + n - z') := by abel
        rw [this]
        exact N'.sub_mem n.2 (hNN' hz')
      refine ⟨⟨z', Finset.mem_filter.2 ⟨hzs', hπeq z' z hz hz'N'⟩⟩, ?_⟩
      apply QuotientAddGroup.eq.2
      rw [AddSubgroup.mem_addSubgroupOf]
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
      have : -(z' - z) + (n : G) = z + n - z' := by abel
      rw [this]
      exact hz'
  rw [← Nat.card_eq_finsetCard, Nat.card_congr (Equiv.ofBijective e he)]
  rfl

/-- In an abelian group of exponent `p` a finite index is a power of `p`. -/
public theorem relIndex_eq_pow_of_nsmul_eq_zero {G : Type*} [AddCommGroup G] {p : ℕ}
    [hp : Fact p.Prime] (hG : ∀ g : G, p • g = 0) (N N' : AddSubgroup G)
    (hfin : N.relIndex N' ≠ 0) :
    ∃ n : ℕ, N.relIndex N' = p ^ n := by
  set Q := N' ⧸ N.addSubgroupOf N'
  have hQ : ∀ q : Q, p • q = 0 := by
    intro q
    obtain ⟨n, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_nsmul]
    have : p • n = 0 := Subtype.ext (hG n)
    rw [this, QuotientAddGroup.mk_zero]
  let := AddCommGroup.zmodModule hQ
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : Finite Q := Nat.finite_of_card_ne_zero hfin
  have : Module.Finite (ZMod p) Q := Module.Finite.of_finite (R := ZMod p) (M := Q)
  have h := @Module.natCard_eq_pow_finrank (ZMod p) Q _ _ (AddCommGroup.zmodModule hQ) this
  exact ⟨_, show Nat.card Q = p ^ Module.finrank (ZMod p) Q by rw [h, Nat.card_zmod]⟩

/-- A subgroup of finite index has a finite transversal. -/
public theorem exists_transversal {G : Type*} [AddCommGroup G] (N : AddSubgroup G)
    (hN : N.index ≠ 0) : ∃ s : Finset G, ∀ a, ∃! z ∈ s, a - z ∈ N := by
  classical
  have : Finite (G ⧸ N) := Nat.finite_of_card_ne_zero hN
  let := Fintype.ofFinite (G ⧸ N)
  refine ⟨(Finset.univ : Finset (G ⧸ N)).image Quotient.out, fun a => ?_⟩
  have hmem : ∀ z : G, a - z ∈ N ↔ (QuotientAddGroup.mk z : G ⧸ N) = QuotientAddGroup.mk a := by
    intro z
    rw [QuotientAddGroup.eq, ← neg_add_eq_sub, add_comm]
  refine ⟨Quotient.out (QuotientAddGroup.mk a : G ⧸ N),
    ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hmem _).2 (Quotient.out_eq _)⟩, ?_⟩
  rintro z ⟨hz, hzN⟩
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz
  have := (hmem _).1 hzN
  rw [show (QuotientAddGroup.mk (Quotient.out q) : G ⧸ N) = q from Quotient.out_eq q] at this
  rw [this]

end Transversals

section Star

variable {K : Type u} [Field K]

/-- The nilpotent matrix `E₁₂ = (0, 1; 0, 0)`. -/
public abbrev eOneTwo (R : Type*) [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 0, 0]

/-- `E₁₂² = 0`. -/
public theorem eOneTwo_mul_self (R : Type*) [CommRing R] : eOneTwo R * eOneTwo R = 0 := by
  rw [mul_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The matrix of `(1, y; 0, 1)` is `1 + y E₁₂`. -/
public theorem coe_upperRightHom (R : Type*) [CommRing R] (y : R) :
    ((GeneralLinearGroup.upperRightHom y : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) =
      1 + y • eOneTwo R := by
  rw [GeneralLinearGroup.upperRightHom_apply, one_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

variable (K) in
/-- `x E₁₂ x⁻¹`. -/
public def conjE (x : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K) :=
  (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)) * eOneTwo (AdeleRing K) *
    ((x⁻¹ : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K))

/-- `(x E₁₂ x⁻¹)² = 0`. -/
public theorem conjE_mul_self (x : GL (Fin 2) (AdeleRing K)) : conjE K x * conjE K x = 0 := by
  simp only [conjE, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc _ (x : Matrix (Fin 2) (Fin 2) (AdeleRing K)), Units.inv_mul,
    Matrix.one_mul, ← Matrix.mul_assoc (eOneTwo _), eOneTwo_mul_self, Matrix.zero_mul,
    Matrix.mul_zero]

variable (K) in
/-- The subgroup `U_x = {y | x (1, y; 0, 1) x⁻¹ ∈ GL₂(O)}`. -/
public def stabSubgroup (x : GL (Fin 2) (AdeleRing K)) : AddSubgroup (AdeleRing K) where
  carrier := {y | ∀ i j, y * conjE K x i j ∈ integralAdeles K}
  zero_mem' i j := by simp
  add_mem' ha hb i j := by rw [add_mul]; exact (integralAdeles K).add_mem (ha i j) (hb i j)
  neg_mem' ha i j := by rw [neg_mul]; exact (integralAdeles K).neg_mem (ha i j)

/-- For `y ∈ U_x` and `c = ±y`, the entries of `1 + c x E₁₂ x⁻¹` are integral adeles. -/
public theorem one_add_smul_conjE_mem {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K}
    (hy : y ∈ stabSubgroup K x) (c : AdeleRing K) (hc : c = y ∨ c = -y) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing K)) + c • conjE K x) i j ∈ integralAdeles K := by
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  refine (integralAdeles K).add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact (integralAdeles K).one_mem
    · exact (integralAdeles K).zero_mem
  · rcases hc with rfl | rfl
    · exact hy i j
    · rw [neg_mul]; exact (integralAdeles K).neg_mem (hy i j)

/-- The matrix `1 + y x E₁₂ x⁻¹` with integral entries, for `y ∈ U_x`. -/
public def stabMat {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K} (hy : y ∈ stabSubgroup K x)
    (c : AdeleRing K) (hc : c = y ∨ c = -y) : Matrix (Fin 2) (Fin 2) (integralAdeles K) :=
  Matrix.of fun i j => ⟨_, one_add_smul_conjE_mem hy c hc i j⟩

/-- The matrix `stabMat hy c hc`, read with adelic entries, is `1 + c x E₁₂ x⁻¹`. -/
public theorem mapMatrix_stabMat {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K}
    (hy : y ∈ stabSubgroup K x) (c : AdeleRing K) (hc : c = y ∨ c = -y) :
    (integralAdeles K).subtype.mapMatrix (stabMat hy c hc) = 1 + c • conjE K x := by
  ext i j; rfl

/-- `(1 + y x E₁₂ x⁻¹)(1 - y x E₁₂ x⁻¹) = 1` over the integral adeles. -/
public theorem stabMat_mul {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K}
    (hy : y ∈ stabSubgroup K x) :
    stabMat hy y (Or.inl rfl) * stabMat hy (-y) (Or.inr rfl) = 1 := by
  have hinj : Function.Injective ((integralAdeles K).subtype.mapMatrix :
      Matrix (Fin 2) (Fin 2) (integralAdeles K) →+* Matrix (Fin 2) (Fin 2) (AdeleRing K)) := by
    intro M N h
    ext i j v
    exact congrArg (fun a : AdeleRing K => a v) (congrFun (congrFun h i) j)
  apply hinj
  rw [map_mul, map_one, mapMatrix_stabMat, mapMatrix_stabMat, add_mul, mul_add, mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, smul_mul_smul_comm, conjE_mul_self,
    smul_zero, add_zero, add_assoc, ← add_smul]
  simp

/-- The element `x (1, y; 0, 1) x⁻¹ ∈ GL₂(O)` for `y ∈ U_x`. -/
public def stabUnit {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K} (hy : y ∈ stabSubgroup K x) :
    GL (Fin 2) (integralAdeles K) :=
  ⟨stabMat hy y (Or.inl rfl), stabMat hy (-y) (Or.inr rfl), stabMat_mul hy,
    mul_eq_one_comm.1 (stabMat_mul hy)⟩

/-- The image of `stabUnit hy` in `GL₂(A)` is `1 + y x E₁₂ x⁻¹`. -/
public theorem coe_mapO_stabUnit {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K}
    (hy : y ∈ stabSubgroup K x) :
    ((mapO (stabUnit hy) : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) =
      1 + y • conjE K x := by
  rw [← mapMatrix_stabMat hy y (Or.inl rfl)]
  ext i j; rfl

/-- For `y ∈ U_x`, `x (1, y; 0, 1) = κ x` with `κ ∈ GL₂(O)`. -/
public theorem exists_mapO_of_mem_stabSubgroup {x : GL (Fin 2) (AdeleRing K)} {y : AdeleRing K}
    (hy : y ∈ stabSubgroup K x) :
    ∃ κ : GL (Fin 2) (integralAdeles K), x * GeneralLinearGroup.upperRightHom y = mapO κ * x := by
  refine ⟨stabUnit hy, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul, coe_mapO_stabUnit,
    coe_upperRightHom, add_mul, Matrix.one_mul, mul_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.smul_mul]
  congr 2
  simp only [conjE, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

/-- `U_x` is open. -/
public theorem isOpen_stabSubgroup (x : GL (Fin 2) (AdeleRing K)) :
    IsOpen (stabSubgroup K x : Set (AdeleRing K)) := by
  have : Fact (∀ v : Place K, IsOpen (v.integers : Set v.completion)) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  have hO : IsOpen (integralAdeles K : Set (AdeleRing K)) :=
    RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _
  have : (stabSubgroup K x : Set (AdeleRing K)) =
      ⋂ i, ⋂ j, (fun y => y * conjE K x i j) ⁻¹' (integralAdeles K : Set (AdeleRing K)) := by
    ext y; simp [stabSubgroup]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hO.preimage (continuous_id.mul continuous_const)

/-- A left `GL₂(O)`-invariant function has integrand `z ↦ f(x (1, z; 0, 1))` invariant under
`U_x`. -/
public theorem left_inv_upperRight_add {Λ : Type*} {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : ∀ κ x, f (mapO κ * x) = f x) (x : GL (Fin 2) (AdeleRing K)) (z : AdeleRing K)
    {y : AdeleRing K} (hy : y ∈ stabSubgroup K x) :
    f (x * GeneralLinearGroup.upperRightHom (z + y)) =
      f (x * GeneralLinearGroup.upperRightHom z) := by
  obtain ⟨κ, hκ⟩ := exists_mapO_of_mem_stabSubgroup hy
  rw [add_comm, AddChar.map_add_eq_mul, ← mul_assoc, hκ, mul_assoc, hf]


variable (K) in
/-- The linear form of the cusp condition: for every `x`, the sum of `z ↦ f(x (1, z; 0, 1))` over
a transversal of `A ⧸ (K + U_x)` vanishes. -/
public def StarCusp (Λ : Type w) [CommRing Λ] (f : GL (Fin 2) (AdeleRing K) → Λ) : Prop :=
  ∀ (x : GL (Fin 2) (AdeleRing K)) (s : Finset (AdeleRing K)),
    (∀ a, ∃! z ∈ s, a - z ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x) →
      ∑ z ∈ s, f (x * GeneralLinearGroup.upperRightHom z) = 0

/-- An unramified cusp form satisfies the cusp condition for the subgroups `U_x`. -/
public theorem IsUnramifiedCuspForm.starCusp {Λ : Type w} [CommRing Λ]
    {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspForm f) : StarCusp K Λ f := by
  intro x s hs
  exact hf.vanishing_constant_term x _ (isOpen_stabSubgroup x)
    (fun z y hy => left_inv_upperRight_add (fun κ x => hf.left_invariant x κ) x z hy) s hs

end Star

section KFreeBaseChange

variable {K : Type u} [Field K]

section BaseChange

variable (Λ : Type w) [CommRing Λ]

variable (K) in
/-- The `Λ`-module of functions satisfying the star cusp condition. -/
public def starForms : Submodule Λ (GL (Fin 2) (AdeleRing K) → Λ) where
  carrier := {f | StarCusp K Λ f}
  zero_mem' x s _ := by simp
  add_mem' {f g} hf hg x s hs := by
    simp only [Pi.add_apply, Finset.sum_add_distrib, hf x s hs, hg x s hs, add_zero]
  smul_mem' c f hf x s hs := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hf x s hs, mul_zero]

/-- `C(Λ)` with central character `φ` satisfies the star cusp condition. -/
public theorem cuspFormsWithChar_le_starForms (φ : Place K → Λ) :
    cuspFormsWithChar K Λ φ ≤ starForms K Λ :=
  Submodule.span_le.2 fun _ hf => IsUnramifiedCuspForm.starCusp hf.1

/-- `C(Λ)` satisfies the star cusp condition. -/
public theorem cuspFormsCentralChar_le_starForms : cuspFormsCentralChar K Λ ≤ starForms K Λ :=
  cuspFormsWithChar_le_starForms Λ _

variable {Λ}

/-- Postcomposition with an injective ring map `ι` sends cusp forms with central character `φ`
to cusp forms with central character `ψ`, when `ψ_v = ι(φ_v)`. -/
public theorem IsCuspFormWithChar.mapCoeffs {Λ' : Type*} [CommRing Λ'] {ι : Λ →+* Λ'}
    (hι : Function.Injective ι) {φ : Place K → Λ} {ψ : Place K → Λ'}
    (hψ : ∀ v, ι (φ v) = ψ v) {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsCuspFormWithChar Λ φ f) : IsCuspFormWithChar Λ' ψ (mapCoeffs ι f) := by
  refine ⟨⟨fun x γ => by simp [Stacks.Adeles.mapCoeffs, hf.1.right_invariant x γ],
    fun x u => by simp [Stacks.Adeles.mapCoeffs, hf.1.left_invariant x u],
    fun x U hU hinv s hs => ?_⟩, fun v a ha x => ?_⟩
  · have hinv' : ∀ z, ∀ y ∈ U, f (x * GeneralLinearGroup.upperRightHom (z + y)) =
        f (x * GeneralLinearGroup.upperRightHom z) := fun z y hy => hι (hinv z y hy)
    have := hf.1.vanishing_constant_term x U hU hinv' s hs
    simp only [Stacks.Adeles.mapCoeffs, ← map_sum, this, map_zero]
  · rw [← hψ v]
    change ι _ * ι (f (a * x)) = ι (f x)
    rw [← map_mul]
    exact congrArg ι (hf.2 v a ha x)

/-- Postcomposition with an injective ring map preserves cusp forms with central character. -/
public theorem IsCuspFormCentralChar.mapCoeffs {Λ' : Type*} [CommRing Λ'] {ι : Λ →+* Λ'}
    (hι : Function.Injective ι) {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsCuspFormCentralChar Λ f) : IsCuspFormCentralChar Λ' (mapCoeffs ι f) :=
  IsCuspFormWithChar.mapCoeffs hι (fun _ => map_natCast ι _) hf

end BaseChange

section BaseChangeMap

variable (F Λ : Type w) [Field F] [Field Λ] [Algebra F Λ]

section WithChar

variable {F Λ} {φ : Place K → F} {ψ : Place K → Λ}

/-- Composing an element of `C(F)` with central character `φ` with `F → Λ` gives an element of
`C(Λ)` with central character `ψ`, when `ψ_v` is the image of `φ_v`. -/
public theorem mapCoeffs_mem_cuspFormsWithChar (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v)
    {f : GL (Fin 2) (AdeleRing K) → F} (hf : f ∈ cuspFormsWithChar K F φ) :
    mapCoeffs (algebraMap F Λ) f ∈ cuspFormsWithChar K Λ ψ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    exact mem_cuspFormsWithChar (IsCuspFormWithChar.mapCoeffs (algebraMap F Λ).injective hψ hf)
  | zero =>
    have : mapCoeffs (algebraMap F Λ) (0 : GL (Fin 2) (AdeleRing K) → F) = 0 := by
      funext x; simp [Stacks.Adeles.mapCoeffs]
    rw [this]; exact (cuspFormsWithChar K Λ ψ).zero_mem
  | add f g _ _ hf hg =>
    have : mapCoeffs (algebraMap F Λ) (f + g) =
        mapCoeffs (algebraMap F Λ) f + mapCoeffs (algebraMap F Λ) g := by
      funext x; simp [Stacks.Adeles.mapCoeffs]
    rw [this]; exact add_mem hf hg
  | smul c f _ hf =>
    have : mapCoeffs (algebraMap F Λ) (c • f) =
        algebraMap F Λ c • mapCoeffs (algebraMap F Λ) f := by
      funext x; simp [Stacks.Adeles.mapCoeffs]
    rw [this]; exact Submodule.smul_mem _ _ hf

variable (K F Λ) in
/-- The `F`-linear map `C(F) → C(Λ)`, `f ↦ ι ∘ f`, between the modules with central characters
`φ` and `ψ`, when `ψ_v` is the image of `φ_v`. -/
public def cuspFormsMapWithChar (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v) :
    cuspFormsWithChar K F φ →ₗ[F] cuspFormsWithChar K Λ ψ where
  toFun f := ⟨mapCoeffs (algebraMap F Λ) f, mapCoeffs_mem_cuspFormsWithChar hψ f.2⟩
  map_add' f g := Subtype.ext (funext fun x => by simp [Stacks.Adeles.mapCoeffs])
  map_smul' c f := Subtype.ext (funext fun x => by
    simp [Stacks.Adeles.mapCoeffs, Algebra.smul_def])

/-- The function underlying `cuspFormsMapWithChar K F Λ hψ f` is `ι ∘ f`. -/
@[simp]
public theorem coe_cuspFormsMapWithChar (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v)
    (f : cuspFormsWithChar K F φ) :
    ((cuspFormsMapWithChar K F Λ hψ f : cuspFormsWithChar K Λ ψ) :
      GL (Fin 2) (AdeleRing K) → Λ) = mapCoeffs (algebraMap F Λ) f := rfl

variable (K F Λ) in
/-- The base change map `Λ ⊗_F C(F) → C(Λ)`, `c ⊗ f ↦ c · (ι ∘ f)`, for the central characters
`φ` and `ψ`, when `ψ_v` is the image of `φ_v`. -/
public def cuspFormsBaseChangeWithChar (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v) :
    TensorProduct F Λ (cuspFormsWithChar K F φ) →ₗ[Λ] cuspFormsWithChar K Λ ψ :=
  LinearMap.liftBaseChange Λ (cuspFormsMapWithChar K F Λ hψ)

/-- The base change map sends `c ⊗ f` to `c · (ι ∘ f)`. -/
public theorem cuspFormsBaseChangeWithChar_tmul (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v) (c : Λ)
    (f : cuspFormsWithChar K F φ) :
    cuspFormsBaseChangeWithChar K F Λ hψ (c ⊗ₜ f) = c • cuspFormsMapWithChar K F Λ hψ f :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The images in `C(Λ)` of an `F`-basis of `C(F)` are `Λ`-linearly independent. -/
public theorem linearIndependent_cuspFormsMapWithChar (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v)
    {ι : Type*} {b : ι → cuspFormsWithChar K F φ} (hb : LinearIndependent F b) :
    LinearIndependent Λ (fun i => cuspFormsMapWithChar K F Λ hψ (b i)) := by
  classical
  set B := Module.Basis.ofVectorSpace F Λ
  rw [linearIndependent_iff']
  intro s c hc i hi
  have hcoord : ∀ j, ∀ i ∈ s, B.repr (c i) j = 0 := by
    intro j
    have hb' := linearIndependent_iff'.1 hb s (fun i => B.repr (c i) j)
    refine hb' ?_
    apply Subtype.ext
    funext x
    have h := congrArg (fun g : cuspFormsWithChar K Λ ψ => (g : GL (Fin 2) (AdeleRing K) → Λ) x)
      hc
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      coe_cuspFormsMapWithChar, Stacks.Adeles.mapCoeffs, smul_eq_mul, Submodule.coe_zero,
      Pi.zero_apply] at h
    have h2 := congrArg (fun z => B.repr z j) h
    simp only [map_sum, map_zero, Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.coe_finsetSum, Finset.sum_apply] at h2
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply]
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have : B.repr (c i) = 0 := Finsupp.ext fun j => hcoord j i hi
  simpa using this

/-- The base change map is injective. -/
public theorem cuspFormsBaseChangeWithChar_injective (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v) :
    Function.Injective (cuspFormsBaseChangeWithChar K F Λ hψ) := by
  classical
  set b := Module.Basis.ofVectorSpace F (cuspFormsWithChar K F φ)
  set b' := b.baseChange Λ
  have hli := linearIndependent_cuspFormsMapWithChar hψ b.linearIndependent
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  have hrep := b'.linearCombination_repr t
  rw [← hrep, Finsupp.apply_linearCombination] at ht
  have hcomp : (cuspFormsBaseChangeWithChar K F Λ hψ) ∘ b' =
      fun i => cuspFormsMapWithChar K F Λ hψ (b i) := by
    funext i
    simp [b', cuspFormsBaseChangeWithChar_tmul]
  rw [hcomp] at ht
  have := linearIndependent_iff.1 hli _ ht
  rw [← hrep, this, map_zero]

end WithChar


/-- Composing an element of `C(F)` with `F → Λ` gives an element of `C(Λ)`. -/
public theorem mapCoeffs_mem_cuspFormsCentralChar {f : GL (Fin 2) (AdeleRing K) → F}
    (hf : f ∈ cuspFormsCentralChar K F) :
    mapCoeffs (algebraMap F Λ) f ∈ cuspFormsCentralChar K Λ :=
  mapCoeffs_mem_cuspFormsWithChar (fun _ => map_natCast _ _) hf

variable (K) in
/-- The `F`-linear map `C(F) → C(Λ)`, `f ↦ ι ∘ f`. -/
public def cuspFormsMap : cuspFormsCentralChar K F →ₗ[F] cuspFormsCentralChar K Λ where
  toFun f :=
    ⟨mapCoeffs (algebraMap F Λ) f, mapCoeffs_mem_cuspFormsCentralChar (F := F) (Λ := Λ) f.2⟩
  map_add' f g := Subtype.ext (funext fun x => by simp [Stacks.Adeles.mapCoeffs])
  map_smul' c f := Subtype.ext (funext fun x => by
    simp [Stacks.Adeles.mapCoeffs, Algebra.smul_def])

/-- The function underlying `cuspFormsMap K F Λ f` is `ι ∘ f`. -/
@[simp]
public theorem coe_cuspFormsMap (f : cuspFormsCentralChar K F) :
    ((cuspFormsMap K F Λ f : cuspFormsCentralChar K Λ) : GL (Fin 2) (AdeleRing K) → Λ) =
      mapCoeffs (algebraMap F Λ) f := rfl

variable (K) in
/-- The base change map `Λ ⊗_F C(F) → C(Λ)`, `c ⊗ f ↦ c · (ι ∘ f)`. -/
public def cuspFormsBaseChange :
    TensorProduct F Λ (cuspFormsCentralChar K F) →ₗ[Λ] cuspFormsCentralChar K Λ :=
  LinearMap.liftBaseChange Λ (cuspFormsMap K F Λ)

/-- The base change map sends `c ⊗ f` to `c · (ι ∘ f)`. -/
public theorem cuspFormsBaseChange_tmul (c : Λ) (f : cuspFormsCentralChar K F) :
    cuspFormsBaseChange K F Λ (c ⊗ₜ f) = c • cuspFormsMap K F Λ f :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The images in `C(Λ)` of an `F`-basis of `C(F)` are `Λ`-linearly independent. -/
public theorem linearIndependent_cuspFormsMap {ι : Type*} {b : ι → cuspFormsCentralChar K F}
    (hb : LinearIndependent F b) : LinearIndependent Λ (fun i => cuspFormsMap K F Λ (b i)) :=
  linearIndependent_cuspFormsMapWithChar (fun _ => map_natCast _ _) hb

/-- The base change map is injective. -/
public theorem cuspFormsBaseChange_injective :
    Function.Injective (cuspFormsBaseChange K F Λ) :=
  cuspFormsBaseChangeWithChar_injective (fun _ => map_natCast _ _)

end BaseChangeMap

end KFreeBaseChange

include k

/-- An open subgroup of the adeles contains some `A(E)`. -/
public theorem exists_adeleLattice_le_of_isOpen {U : AddSubgroup (AdeleRing K)}
    (hU : IsOpen (U : Set (AdeleRing K))) : ∃ E : Place K →₀ ℤ, adeleLattice K E ≤ U := by
  classical
  have hBopen : ∀ v : Place K, IsOpen (v.integers : Set v.completion) :=
    fun v => Valued.isOpen_valuationSubring _
  have h0 : (U : Set (AdeleRing K)) ∈ nhds (0 : AdeleRing K) := hU.mem_nhds U.zero_mem
  have h1 : (U : Set (AdeleRing K)) ∈ nhds (RestrictedProduct.structureMap _
      (fun v : Place K => (v.integers : Set v.completion)) Filter.cofinite 0) := h0
  rw [RestrictedProduct.nhds_zero_eq_map_structureMap (R := Place.completion)
    (B := fun v : Place K => v.integers) hBopen, Filter.mem_map, nhds_pi, Filter.mem_pi] at h1
  obtain ⟨I, hI, t, ht, hsub⟩ := h1
  have hball : ∀ v : Place K, ∃ m : ℕ, ∀ y : (v.integers : Set v.completion),
      (y : v.completion) ∈ v.ball m → y ∈ t v := by
    intro v
    have := ht v
    rw [nhds_subtype, Filter.mem_comap] at this
    obtain ⟨s, hs, hst⟩ := this
    obtain ⟨m, hm⟩ := Place.exists_ball_subset (isDiscrete k v) hs
    exact ⟨m.toNat, fun y hy => hst (hm (Place.ball_anti (isDiscrete k v)
      (Int.self_le_toNat m) hy))⟩
  choose m hm using hball
  set E : Place K →₀ ℤ := -(∑ v ∈ hI.toFinset, Finsupp.single v (m v : ℤ))
  have hE : ∀ v, -E v = if v ∈ I then (m v : ℤ) else 0 := by
    intro v
    simp only [E, Finsupp.coe_neg, Pi.neg_apply, neg_neg, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.single_apply]
    rw [Finset.sum_ite_eq']
    simp
  refine ⟨E, fun a ha => ?_⟩
  have hint : ∀ v, a v ∈ (v.integers : Set v.completion) := by
    intro v
    have := ha v
    rw [hE v] at this
    split_ifs at this
    · exact Place.mem_ball_zero_iff.1 (Place.ball_anti (isDiscrete k v) (by omega) this)
    · exact Place.mem_ball_zero_iff.1 this
  let a' : ∀ v : Place K, (v.integers : Set v.completion) := fun v => ⟨a v, hint v⟩
  have ha' : a = RestrictedProduct.structureMap _ _ Filter.cofinite a' := rfl
  have : a' ∈ I.pi t := by
    intro v hv
    refine hm v (a' v) ?_
    have := ha v
    rw [hE v] at this
    simpa only [hv, ↓reduceIte] using this
  rw [ha']
  exact hsub this


/-- The adeles are killed by the characteristic `p`. -/
public theorem ringChar_nsmul_adele (g : AdeleRing K) : ringChar k • g = 0 := by
  have h0 : ((ringChar k : ℕ) : AdeleRing K) = 0 := by
    rw [← map_natCast (diag k K), ← map_natCast (algebraMap k K), CharP.cast_eq_zero, map_zero,
      map_zero]
  rw [nsmul_eq_mul, h0, zero_mul]

/-- The principal adeles, as an additive subgroup, are `principal k K`. -/
public theorem principalAdeles_toAddSubgroup :
    (principalAdeles K).toAddSubgroup = principal k K := by
  rw [principal, range_diag]

/-- If `φ` is invariant under `W ⊇ N` and `W₀ ⊇ N`, `N` of finite index in a group of exponent
`p`, and the sums of `φ` over the transversals of `W₀` vanish, then so do its sums over the
transversals of `W`, provided `p` is invertible. -/
public theorem sum_eq_zero_of_finer {G : Type*} [AddCommGroup G] {Λ : Type*} [CommRing Λ]
    {p : ℕ} [Fact p.Prime] (hG : ∀ g : G, p • g = 0) (hp : IsUnit (p : Λ)) {φ : G → Λ}
    {N W W₀ : AddSubgroup G} (hNW : N ≤ W) (hNW₀ : N ≤ W₀) (hN : N.index ≠ 0)
    (hφW : ∀ z, ∀ y ∈ W, φ (z + y) = φ z) (hφW₀ : ∀ z, ∀ y ∈ W₀, φ (z + y) = φ z)
    (hzero : ∀ s₀ : Finset G, (∀ a, ∃! z ∈ s₀, a - z ∈ W₀) → ∑ z ∈ s₀, φ z = 0)
    {s : Finset G} (hs : ∀ a, ∃! z ∈ s, a - z ∈ W) : ∑ z ∈ s, φ z = 0 := by
  have hidx : W₀.index ≠ 0 := ne_zero_of_dvd_ne_zero hN (AddSubgroup.index_dvd_of_le hNW₀)
  obtain ⟨s', hs'⟩ := exists_transversal N hN
  obtain ⟨s₀, hs₀⟩ := exists_transversal W₀ hidx
  have e1 := sum_transversal_eq hNW φ hφW hs hs'
  have e2 := sum_transversal_eq hNW₀ φ hφW₀ hs₀ hs'
  rw [hzero s₀ hs₀, smul_zero] at e2
  rw [e2] at e1
  obtain ⟨n, hn⟩ := relIndex_eq_pow_of_nsmul_eq_zero hG N W
    (ne_zero_of_dvd_ne_zero hN (AddSubgroup.relIndex_dvd_index_of_le hNW))
  rw [hn, nsmul_eq_mul, Nat.cast_pow] at e1
  exact ((hp.pow n).mul_right_eq_zero).1 e1.symm

/-- The integrand of a right `GL₂(K)`-invariant function, invariant under `W`, is invariant under
`K + W`. -/
public theorem integrand_add_mem_sup {Λ : Type*} {f : GL (Fin 2) (AdeleRing K) → Λ}
    (h2 : ∀ γ x, f (x * mapK γ) = f x) (x : GL (Fin 2) (AdeleRing K))
    {W : AddSubgroup (AdeleRing K)}
    (hW : ∀ z, ∀ y ∈ W, f (x * GeneralLinearGroup.upperRightHom (z + y)) =
      f (x * GeneralLinearGroup.upperRightHom z)) (z : AdeleRing K) {y : AdeleRing K}
    (hy : y ∈ (principalAdeles K).toAddSubgroup ⊔ W) :
    f (x * GeneralLinearGroup.upperRightHom (z + y)) =
      f (x * GeneralLinearGroup.upperRightHom z) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hy
  rw [show z + (a + b) = (z + b) + a by abel, AddChar.map_add_eq_mul, ← mul_assoc, ← hW z b hb]
  have := h2 (GeneralLinearGroup.upperRightHom ⟨a, ha⟩)
    (x * GeneralLinearGroup.upperRightHom (z + b))
  change f (_ * GeneralLinearGroup.map (principalAdeles K).subtype _) = _ at this
  rwa [mapK_upperRightHom] at this

/-- When `p` is invertible in `Λ`, the star cusp condition, with left `GL₂(O)`- and right
`GL₂(K)`-invariance, gives the cusp condition. -/
public theorem isUnramifiedCuspForm_of_starCusp {Λ : Type w} [CommRing Λ]
    (hp : IsUnit (ringChar k : Λ)) {f : GL (Fin 2) (AdeleRing K) → Λ}
    (h1 : ∀ κ x, f (mapO κ * x) = f x) (h2 : ∀ γ x, f (x * mapK γ) = f x)
    (hs : StarCusp K Λ f) : IsUnramifiedCuspForm f := by
  refine ⟨fun x γ => h2 γ x, fun x u => h1 u x, fun x U hU hinv s hsU => ?_⟩
  obtain ⟨E, hE⟩ := exists_adeleLattice_le_of_isOpen k (U := U ⊓ stabSubgroup K x)
    (hU.inter (isOpen_stabSubgroup x))
  have hN : ((principalAdeles K).toAddSubgroup ⊔ (U ⊓ stabSubgroup K x)).index ≠ 0 := by
    intro h0
    have hle : (principalAdeles K).toAddSubgroup ⊔ adeleLattice K E ≤
        (principalAdeles K).toAddSubgroup ⊔ (U ⊓ stabSubgroup K x) := sup_le_sup_left hE _
    have := zero_dvd_iff.1 (h0 ▸ AddSubgroup.index_dvd_of_le hle)
    rw [principalAdeles_toAddSubgroup k] at this
    exact hOne_ne_zero k E this
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  have hA : ∀ z, ∀ y ∈ (principalAdeles K).toAddSubgroup ⊔ U,
      f (x * GeneralLinearGroup.upperRightHom (z + y)) =
        f (x * GeneralLinearGroup.upperRightHom z) :=
    fun z y hy => integrand_add_mem_sup k h2 x hinv z hy
  have hB : ∀ z, ∀ y ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x,
      f (x * GeneralLinearGroup.upperRightHom (z + y)) =
        f (x * GeneralLinearGroup.upperRightHom z) :=
    fun z y hy => integrand_add_mem_sup k h2 x
      (fun z' y' hy' => left_inv_upperRight_add h1 x z' hy') z hy
  have hZ : ∀ s₀ : Finset (AdeleRing K), (∀ a, ∃! z ∈ s₀,
      a - z ∈ (principalAdeles K).toAddSubgroup ⊔ stabSubgroup K x) →
      ∑ z ∈ s₀, f (x * GeneralLinearGroup.upperRightHom z) = 0 :=
    fun s₀ hs₀ => hs x s₀ hs₀
  have hG := ringChar_nsmul_adele k (K := K)
  exact sum_eq_zero_of_finer k hG hp (sup_le_sup_left inf_le_left _)
    (sup_le_sup_left inf_le_right _) hN hA hB hZ hsU


section Surjective

variable {F Λ : Type w} [Field F] [Field Λ] [Algebra F Λ]

omit [Finite k] in
/-- If `p` is invertible in `Λ`, it is invertible in `F`. -/
public theorem isUnit_ringChar_of_algebra (hp : IsUnit (ringChar k : Λ)) :
    IsUnit (ringChar k : F) := by
  rw [isUnit_iff_ne_zero]
  intro h
  have : ((ringChar k : ℕ) : Λ) = 0 := by rw [← map_natCast (algebraMap F Λ), h, map_zero]
  exact hp.ne_zero this

section WithChar

variable {φ : Place K → F} {ψ : Place K → Λ}

/-- The coordinates of an element of `C(Λ)` with central character `ψ` in an `F`-basis of `Λ`
lie in `C(F)` with central character `φ`, when `ψ_v` is the image of `φ_v`. -/
public theorem coord_mem_cuspFormsWithChar (hp : IsUnit (ringChar k : Λ))
    (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v)
    {g : GL (Fin 2) (AdeleRing K) → Λ} (hg : g ∈ cuspFormsWithChar K Λ ψ)
    (j : Module.Basis.ofVectorSpaceIndex F Λ) :
    (fun x => (Module.Basis.ofVectorSpace F Λ).repr (g x) j) ∈ cuspFormsWithChar K F φ := by
  set B := Module.Basis.ofVectorSpace F Λ
  have hW := cuspFormsWithChar_le_reducedFormsWithChar k Λ ψ hg
  have hS := cuspFormsWithChar_le_starForms Λ ψ hg
  refine mem_cuspFormsWithChar ⟨isUnramifiedCuspForm_of_starCusp k
    (isUnit_ringChar_of_algebra k hp) (fun κ x => by simp only [hW.1 κ x])
    (fun γ x => by simp only [hW.2.1 γ x]) (fun x s hs => ?_), fun v a ha x => ?_⟩
  · have := hS x s hs
    have h2 := congrArg (fun z => B.repr z j) this
    simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.coe_zero, Pi.zero_apply] at h2
    exact h2
  · have h := congrArg (fun z => B.repr z j) (hW.2.2.1 v a ha x)
    change φ v * B.repr (g (a * x)) j = B.repr (g x) j
    rw [← h, ← hψ v, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- Only finitely many coordinates of an element of `C(Λ)` with central character `ψ` are
nonzero, when `ψ_v` is the image of a unit `φ_v` of `F`. -/
public theorem exists_finset_coord_withChar (hp : IsUnit (ringChar k : Λ))
    (hφ : ∀ v, IsUnit (φ v)) (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v)
    {g : GL (Fin 2) (AdeleRing K) → Λ} (hg : g ∈ cuspFormsWithChar K Λ ψ) :
    ∃ J : Finset (Module.Basis.ofVectorSpaceIndex F Λ), ∀ j ∉ J, ∀ x,
      (Module.Basis.ofVectorSpace F Λ).repr (g x) j = 0 := by
  classical
  set B := Module.Basis.ofVectorSpace F Λ
  obtain ⟨P, hP⟩ := exists_finset_eval_eq_withChar k F hφ (K := K)
  refine ⟨P.biUnion fun p => (B.repr (g p)).support, fun j hj x => ?_⟩
  have hjW := cuspFormsWithChar_le_reducedFormsWithChar k F φ
    (coord_mem_cuspFormsWithChar k hp hψ hg j)
  obtain ⟨p, hpP, u, hu⟩ := hP x
  have h0 : B.repr (g p) j = 0 := by
    by_contra h
    exact hj (Finset.mem_biUnion.2 ⟨p, hpP, Finsupp.mem_support_iff.2 h⟩)
  have := hu _ hjW
  rw [this, h0, mul_zero]

/-- The base change map `Λ ⊗_F C(F) → C(Λ)` for the central characters `φ` and `ψ` is
surjective when `p` is invertible in `Λ`, every `φ_v` is a unit and `ψ_v` is the image of
`φ_v`. -/
public theorem cuspFormsBaseChangeWithChar_surjective (hp : IsUnit (ringChar k : Λ))
    (hφ : ∀ v, IsUnit (φ v)) (hψ : ∀ v, algebraMap F Λ (φ v) = ψ v) :
    Function.Surjective (cuspFormsBaseChangeWithChar K F Λ hψ) := by
  classical
  rintro ⟨g, hg⟩
  set B := Module.Basis.ofVectorSpace F Λ
  obtain ⟨J, hJ⟩ := exists_finset_coord_withChar k hp hφ hψ hg
  refine ⟨∑ j ∈ J, B j ⊗ₜ ⟨_, coord_mem_cuspFormsWithChar k hp hψ hg j⟩, ?_⟩
  apply Subtype.ext
  funext x
  simp only [map_sum, cuspFormsBaseChangeWithChar_tmul, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, coe_cuspFormsMapWithChar, Stacks.Adeles.mapCoeffs,
    smul_eq_mul]
  have hx : g x = ∑ j ∈ J, (B.repr (g x)) j • B j := by
    conv_lhs => rw [← B.linearCombination_repr (g x)]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_subset (fun j hj => ?_) (fun j _ hj => ?_)
    · by_contra hjJ
      exact (Finsupp.mem_support_iff.1 hj) (hJ j hjJ x)
    · rw [Finsupp.notMem_support_iff.1 hj, zero_smul]
  conv_rhs => rw [hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, mul_comm]

end WithChar

/-- The coordinates of an element of `C(Λ)` in an `F`-basis of `Λ` lie in `C(F)`. -/
public theorem coord_mem_cuspFormsCentralChar (hp : IsUnit (ringChar k : Λ))
    {g : GL (Fin 2) (AdeleRing K) → Λ} (hg : g ∈ cuspFormsCentralChar K Λ)
    (j : Module.Basis.ofVectorSpaceIndex F Λ) :
    (fun x => (Module.Basis.ofVectorSpace F Λ).repr (g x) j) ∈ cuspFormsCentralChar K F :=
  coord_mem_cuspFormsWithChar k hp (fun _ => map_natCast _ _) hg j

/-- Only finitely many coordinates of an element of `C(Λ)` are nonzero. -/
public theorem exists_finset_coord (hp : IsUnit (ringChar k : Λ))
    {g : GL (Fin 2) (AdeleRing K) → Λ} (hg : g ∈ cuspFormsCentralChar K Λ) :
    ∃ J : Finset (Module.Basis.ofVectorSpaceIndex F Λ), ∀ j ∉ J, ∀ x,
      (Module.Basis.ofVectorSpace F Λ).repr (g x) j = 0 :=
  exists_finset_coord_withChar k hp (isUnit_residueCard k (isUnit_ringChar_of_algebra k hp))
    (fun _ => map_natCast _ _) hg

/-- The base change map is surjective when `p` is invertible in `Λ`. -/
public theorem cuspFormsBaseChange_surjective (hp : IsUnit (ringChar k : Λ)) :
    Function.Surjective (cuspFormsBaseChange K F Λ) :=
  cuspFormsBaseChangeWithChar_surjective k hp
    (isUnit_residueCard k (isUnit_ringChar_of_algebra k hp)) (fun _ => map_natCast _ _)

end Surjective

end Stacks.Adeles.GlobalFunctionField

end
