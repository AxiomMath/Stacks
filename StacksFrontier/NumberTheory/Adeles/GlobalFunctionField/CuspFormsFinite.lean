module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.Iwasawa

/-!
# Finiteness of unramified cusp forms with prescribed central character

Let `K` be a global function field, `Λ` a ring. The unramified cusp forms on `GL₂(A)` with values
in `Λ` satisfying `q_v · U_v f = f` at every place satisfy four linear conditions: left
`GL₂(O)`-invariance, right `GL₂(K)`-invariance, the central condition, and vanishing at the
upper triangular matrices `(α, β; 0, δ)` with `A = K + (δ/α) O`. The last one is the cusp
condition evaluated with the open subgroup `(δ/α) O` and the transversal `{0}`.

We show that, when the characteristic of `K` is invertible in `Λ`, a function satisfying these
conditions is determined by its values on an explicit finite subset of `GL₂(A)`. This uses the
Iwasawa decomposition, reduction theory (a lower bound for the instability of the upper
triangular factor, from Riemann–Roch), the vanishing of `H¹` for divisors of large degree, and
the finiteness of the divisor classes of bounded degree. Hence `C(Λ)` is a finitely generated
`Λ`-module when `Λ` is Noetherian.

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.reducedForms` — the `Λ`-module of functions satisfying the
  four conditions.

## Main results

* `Stacks.Adeles.GlobalFunctionField.cuspFormsCentralChar_le_reducedForms`.
* `Stacks.Adeles.GlobalFunctionField.cuspFormsCentralChar_fg`.
-/

@[expose] public noncomputable section

open Matrix

universe u w

namespace Stacks.Adeles.GlobalFunctionField

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

section KFree

variable {K' : Type u} [Field K']

/-- `GL₂(O) → GL₂(A)`. -/
public def mapO : GL (Fin 2) (integralAdeles K') →* GL (Fin 2) (AdeleRing K') :=
  GeneralLinearGroup.map (integralAdeles K').subtype

/-- `GL₂(K) → GL₂(A)`. -/
public def mapK : GL (Fin 2) (principalAdeles K') →* GL (Fin 2) (AdeleRing K') :=
  GeneralLinearGroup.map (principalAdeles K').subtype

/-- The entries of `mapO κ` are those of `κ`, viewed in `A`. -/
public theorem coe_mapO_apply (κ : GL (Fin 2) (integralAdeles K')) (i j : Fin 2) :
    ((mapO κ : GL (Fin 2) (AdeleRing K')) : Matrix (Fin 2) (Fin 2) (AdeleRing K')) i j =
      (((κ : Matrix (Fin 2) (Fin 2) (integralAdeles K')) i j : integralAdeles K') :
        AdeleRing K') := rfl

/-- The entries of `mapK γ` are those of `γ`, viewed in `A`. -/
public theorem coe_mapK_apply (γ : GL (Fin 2) (principalAdeles K')) (i j : Fin 2) :
    ((mapK γ : GL (Fin 2) (AdeleRing K')) : Matrix (Fin 2) (Fin 2) (AdeleRing K')) i j =
      (((γ : Matrix (Fin 2) (Fin 2) (principalAdeles K')) i j : principalAdeles K') :
        AdeleRing K') := rfl

/-- `GL₂(O) → GL₂(A)` sends `(1, w; 0, 1)` to `(1, w; 0, 1)`. -/
public theorem mapO_upperRightHom (w : integralAdeles K') :
    GeneralLinearGroup.map (integralAdeles K').subtype (GeneralLinearGroup.upperRightHom w) =
      GeneralLinearGroup.upperRightHom (w : AdeleRing K') := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `GL₂(K) → GL₂(A)` sends `(1, w; 0, 1)` to `(1, w; 0, 1)`. -/
public theorem mapK_upperRightHom (w : principalAdeles K') :
    GeneralLinearGroup.map (principalAdeles K').subtype (GeneralLinearGroup.upperRightHom w) =
      GeneralLinearGroup.upperRightHom (w : AdeleRing K') := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `(α, β; 0, δ) · (1, y; 0, 1) = (1, α y δ⁻¹; 0, 1) · (α, β; 0, δ)`. -/
public theorem upperGL_mul_upperRightHom (α δ : (AdeleRing K')ˣ) (β y : AdeleRing K') :
    upperGL α δ β * GeneralLinearGroup.upperRightHom y =
      GeneralLinearGroup.upperRightHom ((α : AdeleRing K') * y * ((δ⁻¹ : (AdeleRing K')ˣ) :
        AdeleRing K')) * upperGL α δ β := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_assoc]
  ring

/-- The matrix `(w₁, -1; w₂, 0) ∈ GL₂(K)`. -/
public def gammaK {w₂ : K'} (w₁ : K') (hw : w₂ ≠ 0) : GL (Fin 2) K' where
  val := !![w₁, -1; w₂, 0]
  inv := !![0, w₂⁻¹; -1, w₁ * w₂⁻¹]
  val_inv := by
    rw [mul_fin_two, one_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hw]
  inv_val := by
    rw [mul_fin_two, one_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp [hw]

/-- The underlying matrix of `gammaK w₁ hw` is `(w₁, -1; w₂, 0)`. -/
@[simp]
public theorem coe_gammaK {w₂ : K'} (w₁ : K') (hw : w₂ ≠ 0) :
    ((gammaK w₁ hw : GL (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') = !![w₁, -1; w₂, 0] := rfl

/-- `(a, b; 0, d) (a', b'; 0, d') = (a a', a b' + b d'; 0, d d')`. -/
public theorem upperGL_mul (a d a' d' : (AdeleRing K')ˣ) (b b' : AdeleRing K') :
    upperGL a d b * upperGL a' d' b' =
      upperGL (a * a') (d * d') ((a : AdeleRing K') * b' + b * d') := by
  ext i j
  rw [Matrix.GeneralLinearGroup.coe_mul, coe_upperGL, coe_upperGL, coe_upperGL, mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp

/-- `(1, w; 0, 1)` is the upper triangular matrix `upperGL 1 1 w`. -/
public theorem upperRightHom_eq_upperGL (w : AdeleRing K') :
    GeneralLinearGroup.upperRightHom w = upperGL 1 1 w := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The diagonal matrix `(o, 0; 0, 1)` over a commutative ring. -/
public def diagGL {R : Type*} [CommRing R] (o : Rˣ) : GL (Fin 2) R where
  val := !![(o : R), 0; 0, 1]
  inv := !![((o⁻¹ : Rˣ) : R), 0; 0, 1]
  val_inv := by
    rw [mul_fin_two, one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [mul_fin_two, one_fin_two]; ext i j; fin_cases i <;> fin_cases j <;> simp

/-- A ring map sends `(o, 0; 0, 1)` to `(f o, 0; 0, 1)`. -/
public theorem map_diagGL {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (o : Rˣ) :
    GeneralLinearGroup.map f (diagGL o) = diagGL (Units.map f.toMonoidHom o) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.GeneralLinearGroup.map_apply]

/-- `(o, 0; 0, 1)` is the upper triangular matrix `upperGL o 1 0`. -/
public theorem diagGL_eq_upperGL (o : (AdeleRing K')ˣ) : diagGL o = upperGL o 1 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The scalar matrix `δ · 1` is the upper triangular matrix `upperGL δ δ 0`. -/
public theorem scalarGL_eq_upperGL (δ : (AdeleRing K')ˣ) : scalarGL δ = upperGL δ δ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end KFree

variable (Λ : Type w) [CommRing Λ]

variable (K) in
/-- The `Λ`-module of functions on `GL₂(A)` that are left `GL₂(O)`-invariant, right
`GL₂(K)`-invariant, satisfy `q_v · f(a x) = f(x)` for the central data `a` of `U_v`, and vanish at
the upper triangular `(α, β; 0, δ)` with `A = K + A(div α - div δ)`. -/
public def reducedForms : Submodule Λ (GL (Fin 2) (AdeleRing K) → Λ) where
  carrier := {f | (∀ κ x, f (mapO κ * x) = f x) ∧ (∀ γ x, f (x * mapK γ) = f x) ∧
    (∀ v a, IsCentralDataAt v a → ∀ x, (Place.residueCard v : Λ) * f (a * x) = f x) ∧
    (∀ α δ β, principal k K ⊔ adeleLattice K (idelDiv k K α - idelDiv k K δ) = ⊤ →
      f (upperGL α δ β) = 0)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => mul_zero _, fun _ _ _ _ => rfl⟩
  add_mem' {f g} hf hg := ⟨fun κ x => by simp [hf.1 κ x, hg.1 κ x],
    fun γ x => by simp [hf.2.1 γ x, hg.2.1 γ x],
    fun v a ha x => by simp [mul_add, hf.2.2.1 v a ha x, hg.2.2.1 v a ha x],
    fun α δ β h => by simp [hf.2.2.2 α δ β h, hg.2.2.2 α δ β h]⟩
  smul_mem' c f hf := ⟨fun κ x => by simp [hf.1 κ x], fun γ x => by simp [hf.2.1 γ x],
    fun v a ha x => by
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [mul_left_comm, hf.2.2.1 v a ha x],
    fun α δ β h => by simp [hf.2.2.2 α δ β h]⟩

/-- `A(0) = O`. -/
public theorem mem_adeleLattice_zero_iff {y : AdeleRing K} :
    y ∈ adeleLattice K 0 ↔ y ∈ integralAdeles K := by
  rw [mem_adeleLattice, mem_integralAdeles]
  simp [Place.mem_ball_zero_iff]

/-- An idele `c` maps `A(idelDiv c - E)` into `A(-E)`. -/
private theorem idele_mul_mem_adeleLattice_neg (c : (AdeleRing K)ˣ) {E : Place K →₀ ℤ}
    {y : AdeleRing K} (hy : y ∈ adeleLattice K (idelDiv k K c - E)) :
    (c : AdeleRing K) * y ∈ adeleLattice K (-E) := by
  have h := (idele_mul_mem_adeleLattice_iff k c).2 hy
  rwa [sub_sub_cancel_left] at h

include k in
/-- The lattice `A(D)` is open in the adele ring. -/
public theorem isOpen_adeleLattice (D : Place K →₀ ℤ) :
    IsOpen (adeleLattice K D : Set (AdeleRing K)) := by
  have : Fact (∀ v : Place K, IsOpen (v.integers : Set v.completion)) :=
    ⟨fun v => Valued.isOpen_valuationSubring _⟩
  set W : Set (AdeleRing K) := {a | ∀ v, (a : AdeleRing K) v ∈ (v.integers : Set v.completion)} ∩
    ⋂ v ∈ D.support, {a | (a : AdeleRing K) v ∈ (v.ball (-D v) : Set v.completion)}
  have hW : IsOpen W := by
    refine (RestrictedProduct.isOpen_forall_mem fun v => Valued.isOpen_valuationSubring _).inter
      (isOpen_biInter_finset fun v _ => ?_)
    exact (Place.isOpen_ball (isDiscrete k v) _).preimage (RestrictedProduct.continuous_eval v)
  have h0 : (0 : AdeleRing K) ∈ W := by
    refine ⟨fun v => v.integers.zero_mem, Set.mem_iInter₂.2 fun v _ => (v.ball _).zero_mem⟩
  have hsub : W ⊆ adeleLattice K D := by
    rintro a ⟨ha, ha'⟩ v
    by_cases hv : v ∈ D.support
    · exact Set.mem_iInter₂.1 ha' v hv
    · rw [Finsupp.notMem_support_iff.1 hv, neg_zero, Place.mem_ball_zero_iff]
      exact ha v
  exact AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hW.mem_nhds h0) hsub)

/-- An unramified cusp form vanishes at `(α, β; 0, δ)` when `A = K + A(div α - div δ)`: this is
its constant term with the open subgroup `A(div α - div δ)` and the transversal `{0}`. -/
public theorem IsUnramifiedCuspForm.eq_zero_of_sup_eq_top {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : IsUnramifiedCuspForm f) (α δ : (AdeleRing K)ˣ) (β : AdeleRing K)
    (h : principal k K ⊔ adeleLattice K (idelDiv k K α - idelDiv k K δ) = ⊤) :
    f (upperGL α δ β) = 0 := by
  set U := adeleLattice K (idelDiv k K α - idelDiv k K δ)
  have hU : IsOpen (U : Set (AdeleRing K)) := isOpen_adeleLattice k _
  have hinv : ∀ z : AdeleRing K, ∀ y ∈ U,
      f (upperGL α δ β * GeneralLinearGroup.upperRightHom (z + y)) =
        f (upperGL α δ β * GeneralLinearGroup.upperRightHom z) := by
    intro z y hy
    have hw : (α : AdeleRing K) * y * ((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) ∈
        integralAdeles K := by
      rw [← mem_adeleLattice_zero_iff]
      have h1 := idele_mul_mem_adeleLattice_neg k α hy
      have h2 := (idele_mul_mem_adeleLattice_iff k δ⁻¹ (E := -idelDiv k K δ)).2 h1
      rw [idelDiv_inv, sub_neg_eq_add, neg_add_cancel] at h2
      rwa [mul_comm] at h2
    rw [add_comm z y, AddChar.map_add_eq_mul, ← mul_assoc, upperGL_mul_upperRightHom, mul_assoc]
    have := hf.left_invariant (upperGL α δ β * GeneralLinearGroup.upperRightHom z)
      (GeneralLinearGroup.upperRightHom ⟨_, hw⟩)
    rw [mapO_upperRightHom] at this
    exact this
  have hprin : (principalAdeles K).toAddSubgroup = principal k K := by
    rw [principal, range_diag]
  have hs : ∀ a : AdeleRing K, ∃! z ∈ ({0} : Finset (AdeleRing K)),
      a - z ∈ (principalAdeles K).toAddSubgroup ⊔ U := by
    intro a
    refine ⟨0, ⟨Finset.mem_singleton_self _, ?_⟩, fun z hz => Finset.mem_singleton.1 hz.1⟩
    rw [hprin, h]
    exact AddSubgroup.mem_top _
  have := hf.vanishing_constant_term (upperGL α δ β) U hU hinv {0} hs
  rwa [Finset.sum_singleton, AddChar.map_zero_eq_one, mul_one] at this

/-- `C(Λ)` satisfies the four conditions of `reducedForms`. -/
public theorem cuspFormsCentralChar_le_reducedForms :
    cuspFormsCentralChar K Λ ≤ reducedForms k K Λ := by
  refine Submodule.span_le.2 fun f hf => ?_
  exact ⟨fun κ x => hf.1.left_invariant x κ, fun γ x => hf.1.right_invariant x γ, hf.2,
    fun α δ β h => IsUnramifiedCuspForm.eq_zero_of_sup_eq_top k Λ hf.1 α δ β h⟩

variable {Λ}

/-- When the characteristic of `k` is invertible in `Λ`, so is every `q_v`. -/
public theorem isUnit_residueCard (hp : IsUnit (ringChar k : Λ)) (v : Place K) :
    IsUnit (v.residueCard : Λ) := by
  classical
  rw [Place.residueCard_eq_resCard, Place.resCard]
  have := finite_residueField k v
  let := Fintype.ofFinite (IsLocalRing.ResidueField v.1)
  let φ : k →+* IsLocalRing.ResidueField v.1 :=
    (IsLocalRing.residue v.1).comp ((algebraMap k K).codRestrict v.1.toSubring
      (algebraMap_mem_place v))
  have : CharP k (ringChar k) := ringChar.charP k
  have : CharP (IsLocalRing.ResidueField v.1) (ringChar k) :=
    charP_of_injective_ringHom φ.injective (ringChar k)
  obtain ⟨n, -, hn⟩ := FiniteField.card (IsLocalRing.ResidueField v.1) (ringChar k)
  rw [Nat.card_eq_fintype_card, hn, Nat.cast_pow]
  exact hp.pow _

variable (Λ)

/-- The scalar matrices of `GL₂(O)` act trivially on `reducedForms`. -/
public theorem mapO_scalar (o : (integralAdeles K)ˣ) :
    mapO (Units.map (Matrix.scalar (Fin 2) : integralAdeles K →+* Matrix (Fin 2) (Fin 2)
      (integralAdeles K)).toMonoidHom o) =
      scalarGL (Units.map (integralAdeles K).subtype.toMonoidHom o) := by
  ext i j : 2
  rw [coe_mapO_apply]
  simp only [coe_scalarGL, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/-- **Central character**: every idele acts on `reducedForms` through a unit of `Λ`. -/
public theorem exists_unit_scalarGL (hp : IsUnit (ringChar k : Λ)) (c : (AdeleRing K)ˣ) :
    ∃ u : Λˣ, ∀ f ∈ reducedForms k K Λ, ∀ x, f (scalarGL c * x) = u * f x := by
  classical
  let Z : Subgroup (AdeleRing K)ˣ :=
    { carrier := {c | ∃ u : Λˣ, ∀ f ∈ reducedForms k K Λ, ∀ x, f (scalarGL c * x) = u * f x}
      one_mem' := ⟨1, fun f _ x => by simp⟩
      mul_mem' := by
        rintro a b ⟨u, hu⟩ ⟨u', hu'⟩
        refine ⟨u * u', fun f hf x => ?_⟩
        rw [map_mul, mul_assoc, hu f hf, hu' f hf, Units.val_mul, mul_assoc]
      inv_mem' := by
        rintro a ⟨u, hu⟩
        refine ⟨u⁻¹, fun f hf x => ?_⟩
        have := hu f hf (scalarGL a⁻¹ * x)
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at this
        rw [this, ← mul_assoc, Units.inv_mul, one_mul] }
  -- units of `O`
  have hO : ∀ o : (integralAdeles K)ˣ, Units.map (integralAdeles K).subtype.toMonoidHom o ∈ Z := by
    intro o
    refine ⟨1, fun f hf x => ?_⟩
    rw [← mapO_scalar, hf.1, Units.val_one, one_mul]
  -- local uniformizers
  have hU : ∀ v, unifInvIdele k v ∈ Z := by
    intro v
    refine ⟨(isUnit_residueCard k hp v).unit⁻¹, fun f hf x => ?_⟩
    have h := hf.2.2.1 v _ (isCentralDataAt_scalarGL_unifInvIdele k v) x
    rw [← h, ← mul_assoc]
    simp
  -- every idele
  set D := idelDiv k K c
  set e : (AdeleRing K)ˣ := ∏ v ∈ D.support, unifInvIdele k v ^ D v
  have he : e ∈ Z := Subgroup.prod_mem _ fun v _ => Subgroup.zpow_mem _ (hU v) _
  have hdiv : idelDiv k K (c * e) = 0 := by
    have hhom : ∀ (s : Finset (Place K)) (n : Place K → ℤ),
        idelDiv k K (∏ v ∈ s, unifInvIdele k v ^ n v) = -∑ v ∈ s, Finsupp.single v (n v) := by
      intro s n
      induction s using Finset.induction_on with
      | empty => simp [idelDiv_one]
      | insert a s ha ih =>
        rw [Finset.prod_insert ha, idelDiv_mul, ih, Finset.sum_insert ha, neg_add]
        congr 1
        have hz : ∀ m : ℤ, idelDiv k K (unifInvIdele k a ^ m) = -Finsupp.single a m := by
          intro m
          induction m using Int.induction_on with
          | zero => simp [idelDiv_one]
          | succ m ih' => rw [zpow_add_one, idelDiv_mul, ih', idelDiv_unifInvIdele,
              Finsupp.single_add]; abel
          | pred m ih' => rw [zpow_sub_one, idelDiv_mul, ih', idelDiv_inv, idelDiv_unifInvIdele,
              Finsupp.single_sub]; abel
        exact hz (n a)
    rw [idelDiv_mul, hhom, ← Finsupp.sum, Finsupp.sum_single, add_neg_cancel]
  obtain ⟨o, ho⟩ := exists_integralUnit_of_idelDiv_eq_zero k hdiv
  have hce : c * e ∈ Z := by
    have : Units.map (integralAdeles K).subtype.toMonoidHom o = c * e := Units.ext ho
    rw [← this]
    exact hO o
  have := Z.mul_mem hce (Z.inv_mem he)
  rwa [mul_inv_cancel_right] at this

section ReductionLemmas

include k

omit [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- `O · A(E) ⊆ A(E)`. -/
public theorem integral_mul_mem_adeleLattice {o y : AdeleRing K} (ho : o ∈ integralAdeles K)
    {E : Place K →₀ ℤ} (hy : y ∈ adeleLattice K E) : o * y ∈ adeleLattice K E := by
  intro v
  have hv := hy v
  rw [Place.mem_ball] at hv ⊢
  show Valued.v (o v * y v) ≤ _
  rw [map_mul]
  exact (mul_le_of_le_one_left zero_le (ho v)).trans hv

/-- `N` is monotone. -/
public theorem divNorm_mono {D D' : Place K →₀ ℤ} (h : D ≤ D') : divNorm K D ≤ divNorm K D' := by
  have h1 := one_le_divNorm k (sub_nonneg.2 h)
  have h2 : divNorm K D' = divNorm K D * divNorm K (D' - D) := by
    rw [← divNorm_add k, add_sub_cancel]
  rw [h2]
  exact le_mul_of_one_le_right (divNorm_pos k D).le h1

/-- `ℓ(D) = 1` when `N(D) < 1`. -/
public theorem ell_eq_one_of_divNorm_lt_one {D : Place K →₀ ℤ} (hD : divNorm K D < 1) :
    ell k K D = 1 := by
  have : principal k K ⊓ adeleLattice K D = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx, hx'⟩
    obtain ⟨κ, rfl⟩ := (mem_principal k).1 hx
    rw [eq_zero_of_mem_of_divNorm_lt_one k hD hx', map_zero]
    exact AddSubgroup.zero_mem _
  rw [ell, this, AddSubgroup.card_bot]

/-- If an idele lies in `A(-E)` then `E ≤ div α`. -/
private theorem le_idelDiv_of_mem_adeleLattice_neg (α : (AdeleRing K)ˣ) {E : Place K →₀ ℤ}
    (h : (α : AdeleRing K) ∈ adeleLattice K (-E)) : E ≤ idelDiv k K α := by
  intro v
  have := (Place.mem_ball_iff_ordC (isDiscrete k v)).1 (h v)
  simp only [Finsupp.coe_neg, Pi.neg_apply, neg_neg] at this
  rcases this with h0 | h
  · exact absurd h0 (idele_apply_ne_zero α v)
  · simpa using h

/-- The ideles of `GL₂(O)` have divisor `0`. -/
public theorem idelDiv_det_mapO (κ : GL (Fin 2) (integralAdeles K)) :
    idelDiv k K (GeneralLinearGroup.det (mapO κ)) = 0 := by
  have : GeneralLinearGroup.det (mapO κ) =
      Units.map (integralAdeles K).subtype.toMonoidHom (GeneralLinearGroup.det κ) := by
    ext1
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map,
      Matrix.GeneralLinearGroup.val_det_apply]
    show ((integralAdeles K).subtype.mapMatrix (κ : Matrix (Fin 2) (Fin 2) _)).det =
      (integralAdeles K).subtype (κ : Matrix (Fin 2) (Fin 2) _).det
    rw [RingHom.map_det]
  rw [this]
  have key : ∀ o : (integralAdeles K)ˣ,
      0 ≤ idelDiv k K (Units.map (integralAdeles K).subtype.toMonoidHom o) := fun o =>
    le_idelDiv_of_mem_adeleLattice_neg k _ (by
      rw [neg_zero, mem_adeleLattice_zero_iff]; exact o.1.2)
  have h2 := key (GeneralLinearGroup.det κ)⁻¹
  rw [map_inv, idelDiv_inv] at h2
  exact le_antisymm (neg_nonneg.1 h2) (key _)

omit [Field k] [Finite k] [Algebra k K] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K]
  [FunctionField k K] in
/-- `det (α, β; 0, δ) = α δ`. -/
public theorem det_upperGL (α δ : (AdeleRing K)ˣ) (β : AdeleRing K) :
    GeneralLinearGroup.det (upperGL α δ β) = α * δ := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, det_fin_two]

variable (K) in
/-- The diagonal embedding `K → principalAdeles K`. -/
public def diagP : K →+* principalAdeles K :=
  (diag k K).codRestrict (principalAdeles K) fun κ => by rw [← range_diag k]; exact ⟨κ, rfl⟩

/-- The image of `gammaK w₁ hw` in `GL₂(A)` is `(w₁, -1; w₂, 0)`, entries embedded diagonally. -/
public theorem coe_mapK_gammaK {w₂ : K} (w₁ : K) (hw : w₂ ≠ 0) :
    ((mapK (GeneralLinearGroup.map (diagP k K) (gammaK w₁ hw)) : GL (Fin 2) (AdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing K)) = !![diag k K w₁, -1; diag k K w₂, 0] := by
  ext i j : 2
  rw [coe_mapK_apply]
  fin_cases i <;> fin_cases j <;> simp [diagP, Matrix.GeneralLinearGroup.map_apply]

/-- The determinant of the image of `gammaK w₁ hw` in `GL₂(A)` is `w₂`, as an idele. -/
public theorem det_mapK_gammaK {w₂ : K} (w₁ : K) (hw : w₂ ≠ 0) :
    GeneralLinearGroup.det (mapK (GeneralLinearGroup.map (diagP k K) (gammaK w₁ hw))) =
      diagUnit k hw := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_mapK_gammaK, det_fin_two]
  simp

end ReductionLemmas

section Reduction

include k

variable (K) in
/-- A fixed place of `K`. -/
public def basePlace : Place K := (nonempty_place k (K := K)).some

variable (K) in
/-- The reduction constant `χ(0)² / q₀²`, with `q₀` the residue cardinality of `basePlace`. -/
public def redConst : ℚ :=
  ((ell k K 0 : ℚ) / hOne k K 0) ^ 2 / ((basePlace k K).resCard : ℚ) ^ 2

/-- The reduction constant is positive. -/
public theorem redConst_pos : 0 < redConst k K := by
  have := chi_zero_pos k (K := K)
  have : (0 : ℚ) < (basePlace k K).resCard := by exact_mod_cast resCard_pos k _
  unfold redConst
  positivity

/-- The exponent of the reduction step. -/
public theorem exists_reduction_exponent {Dα Dδ : Place K →₀ ℤ}
    (hcase : divNorm K (Dα - Dδ) < redConst k K) :
    ∃ j : ℕ, hOne k K (-Finsupp.single (basePlace k K) (j : ℤ)) <
        ell k K (Dδ - (Dα + Finsupp.single (basePlace k K) (j : ℤ))) ∧
      redConst k K ≤ divNorm K (Dα - Dδ) * (((basePlace k K).resCard : ℚ) ^ j) ^ 2 := by
  classical
  set v₀ := basePlace k K
  set q₀ : ℚ := (v₀.resCard : ℚ)
  set χ : ℚ := (ell k K 0 : ℚ) / hOne k K 0
  have hχ : 0 < χ := chi_zero_pos k
  have hq₀ : 1 < q₀ := by
    have := one_lt_resCard k v₀
    simp only [q₀]
    exact_mod_cast this
  have hq₀0 : 0 < q₀ := zero_lt_one.trans hq₀
  have hred : redConst k K = χ ^ 2 / q₀ ^ 2 := by unfold redConst; rfl
  have hNinv : divNorm K (Dδ - Dα) = (divNorm K (Dα - Dδ))⁻¹ := by
    rw [← divNorm_neg k, neg_sub]
  obtain ⟨X, hXdef⟩ : ∃ X, X = divNorm K (Dδ - Dα) * χ ^ 2 := ⟨_, rfl⟩
  have hX : q₀ ^ 2 < X := by
    have hpos := divNorm_pos k (Dα - Dδ)
    have h1 : divNorm K (Dα - Dδ) * q₀ ^ 2 < χ ^ 2 := by
      rwa [hred, lt_div_iff₀ (by positivity)] at hcase
    rw [hXdef, hNinv, inv_mul_eq_div, lt_div_iff₀ hpos]
    linarith
  have hex : ∃ j : ℕ, X ≤ q₀ ^ (2 * (j + 1)) := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt X hq₀
    exact ⟨n, hn.le.trans (pow_le_pow_right₀ hq₀.le (by omega))⟩
  obtain ⟨j, hjdef⟩ : ∃ j, j = Nat.find hex := ⟨_, rfl⟩
  have hjle : X ≤ q₀ ^ (2 * (j + 1)) := hjdef ▸ Nat.find_spec hex
  have hj1 : 1 ≤ j := by
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, zero_add, mul_one] at hjle
    linarith
  have hjlt : q₀ ^ (2 * j) < X := by
    have := Nat.find_min hex (show j - 1 < Nat.find hex by omega)
    push Not at this
    rwa [show j - 1 + 1 = j by omega] at this
  refine ⟨j, ?_, ?_⟩
  · have hNS : divNorm K (Finsupp.single v₀ (j : ℤ)) = q₀ ^ j := by
      rw [divNorm_single, zpow_natCast]
    have hNE₂ : divNorm K (-Finsupp.single v₀ (j : ℤ)) < 1 := by
      rw [divNorm_neg k, hNS]
      exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hq₀ (by omega))
    have hell₂ := ell_eq_one_of_divNorm_lt_one k hNE₂
    have hh₂ : (hOne k K (-Finsupp.single v₀ (j : ℤ)) : ℚ) = q₀ ^ j / χ := by
      have h := ell_div_hOne k (-Finsupp.single v₀ (j : ℤ))
      rw [hell₂, Nat.cast_one, divNorm_neg k, hNS] at h
      rw [← one_div_one_div (hOne k K (-Finsupp.single v₀ (j : ℤ)) : ℚ), h, one_div, mul_inv,
        inv_inv, div_eq_mul_inv _ χ]
    have h1 := divNorm_mul_chi_le_ell k (Dδ - (Dα + Finsupp.single v₀ (j : ℤ)))
    have hNE₁ : divNorm K (Dδ - (Dα + Finsupp.single v₀ (j : ℤ))) =
        divNorm K (Dδ - Dα) / q₀ ^ j := by
      rw [show Dδ - (Dα + Finsupp.single v₀ (j : ℤ)) = (Dδ - Dα) - Finsupp.single v₀ (j : ℤ) by
        abel, divNorm_sub k, hNS]
    have hqj : 0 < q₀ ^ j := pow_pos hq₀0 j
    have key : q₀ ^ j * q₀ ^ j < X := by rw [← pow_add, ← two_mul]; exact hjlt
    have : (hOne k K (-Finsupp.single v₀ (j : ℤ)) : ℚ) <
        ell k K (Dδ - (Dα + Finsupp.single v₀ (j : ℤ))) := by
      rw [hh₂]
      refine lt_of_lt_of_le ?_ h1
      rw [hNE₁, div_lt_iff₀ hχ]
      have heq : divNorm K (Dδ - Dα) / q₀ ^ j * χ * χ = X / q₀ ^ j := by
        rw [hXdef]; field_simp
      rw [heq, lt_div_iff₀ hqj]
      exact key
    exact_mod_cast this
  · have hXpos : 0 < X := lt_trans (by positivity) hX
    have h2 : divNorm K (Dα - Dδ) = χ ^ 2 / X := by
      rw [hXdef, hNinv]
      have := (divNorm_pos k (Dα - Dδ)).ne'
      field_simp
    rw [hred, h2, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hXpos]
    have : X ≤ q₀ ^ 2 * (q₀ ^ j) ^ 2 := by
      calc X ≤ q₀ ^ (2 * (j + 1)) := hjle
        _ = q₀ ^ 2 * (q₀ ^ j) ^ 2 := by rw [← pow_mul, ← pow_add]; ring_nf
    nlinarith [sq_nonneg χ]

/-- Pigeonhole: if `h¹(D₂) < ℓ(D₁)` then for every adele `c` there are `w₁, w₂ ∈ K`, `w₂ ≠ 0`,
with `w₂ ∈ L(D₁)` and `w₁ + c w₂ ∈ A(D₂)`. -/
public theorem exists_pigeonhole {D₁ D₂ : Place K →₀ ℤ} (c : AdeleRing K)
    (h : hOne k K D₂ < ell k K D₁) :
    ∃ w₁ w₂ : K, w₂ ≠ 0 ∧ diag k K w₂ ∈ adeleLattice K D₁ ∧
      diag k K w₁ + c * diag k K w₂ ∈ adeleLattice K D₂ := by
  classical
  have := finite_principal_inf_adeleLattice k D₁
  have := finite_quotient_principal_sup_adeleLattice k D₂
  let := Fintype.ofFinite ↥(principal k K ⊓ adeleLattice K D₁)
  let := Fintype.ofFinite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D₂))
  let φ : ↥(principal k K ⊓ adeleLattice K D₁) →
      AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D₂) :=
    fun y => QuotientAddGroup.mk (c * (y : AdeleRing K))
  obtain ⟨y, y', hyy', hφ⟩ := Fintype.exists_ne_map_eq_of_card_lt φ (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact h)
  have hz : (y : AdeleRing K) - y' ∈ principal k K ⊓ adeleLattice K D₁ := sub_mem y.2 y'.2
  have hz0 : (y : AdeleRing K) - y' ≠ 0 := fun h => hyy' (Subtype.ext (sub_eq_zero.1 h))
  have hcz : c * ((y : AdeleRing K) - y') ∈ principal k K ⊔ adeleLattice K D₂ := by
    have h1 : -(c * (y : AdeleRing K)) + c * (y' : AdeleRing K) ∈
        principal k K ⊔ adeleLattice K D₂ := QuotientAddGroup.eq.1 hφ
    have h2 := (principal k K ⊔ adeleLattice K D₂).neg_mem h1
    have heq : c * ((y : AdeleRing K) - y') =
        -(-(c * (y : AdeleRing K)) + c * (y' : AdeleRing K)) := by ring
    rw [heq]
    exact h2
  obtain ⟨w₂, hw₂⟩ := (mem_principal k).1 (AddSubgroup.mem_inf.1 hz).1
  have hw₂0 : w₂ ≠ 0 := fun h => hz0 (by rw [← hw₂, h, map_zero])
  obtain ⟨p, hp, a, ha, hpa⟩ := AddSubgroup.mem_sup.1 hcz
  obtain ⟨κ', rfl⟩ := (mem_principal k).1 hp
  refine ⟨-κ', w₂, hw₂0, hw₂ ▸ (AddSubgroup.mem_inf.1 hz).2, ?_⟩
  have : diag k K (-κ') + c * diag k K w₂ = a := by
    rw [map_neg, hw₂]
    linear_combination (-1 : AdeleRing K) * hpa
  rw [this]
  exact ha

/-- The `(0, 0)` entry of the image of `gammaK w₁ hw` in `GL₂(A)` is `w₁`. -/
public theorem mapK_gammaK_apply_zero_zero {w₂ : K} (w₁ : K) (hw : w₂ ≠ 0) :
    ((mapK (GeneralLinearGroup.map (diagP k K) (gammaK w₁ hw)) : GL (Fin 2) (AdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 0 = diag k K w₁ := by
  rw [coe_mapK_apply]; simp [diagP, Matrix.GeneralLinearGroup.map_apply]

/-- The `(1, 0)` entry of the image of `gammaK w₁ hw` in `GL₂(A)` is `w₂`. -/
public theorem mapK_gammaK_apply_one_zero {w₂ : K} (w₁ : K) (hw : w₂ ≠ 0) :
    ((mapK (GeneralLinearGroup.map (diagP k K) (gammaK w₁ hw)) : GL (Fin 2) (AdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 0 = diag k K w₂ := by
  rw [coe_mapK_apply]; simp [diagP, Matrix.GeneralLinearGroup.map_apply]

/-- The first entry of the new upper triangular factor is divisible by `α₀ ϖ^j`. -/
public theorem le_idelDiv_of_reduction {κ₀ κ₁ : GL (Fin 2) (integralAdeles K)}
    {α₀ δ₀ α₁ δ₁ : (AdeleRing K)ˣ} {β₀ β₁ : AdeleRing K} {g : GL (Fin 2) (AdeleRing K)}
    {d₁ d₂ : AdeleRing K} (hg0 : (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 0 = d₁)
    (hg1 : (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 0 = d₂) {E : Place K →₀ ℤ}
    (hd₂ : d₂ ∈ adeleLattice K (idelDiv k K δ₀ - E))
    (hd₁ : d₁ + ((α₀⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β₀ * d₂ ∈
      adeleLattice K (idelDiv k K α₀ - E))
    (hy : mapO κ₀ * upperGL α₀ δ₀ β₀ * g = mapO κ₁ * upperGL α₁ δ₁ β₁) :
    E ≤ idelDiv k K α₁ := by
  have hu₁ : upperGL α₁ δ₁ β₁ = mapO (κ₁⁻¹ * κ₀) * (upperGL α₀ δ₀ β₀ * g) := by
    rw [map_mul, map_inv, mul_assoc, ← mul_assoc (mapO κ₀), hy, inv_mul_cancel_left]
  obtain ⟨N, hNdef⟩ : ∃ N, N = mapO (κ₁⁻¹ * κ₀) := ⟨_, rfl⟩
  rw [← hNdef] at hu₁
  have hM00 : ((upperGL α₀ δ₀ β₀ * g : GL (Fin 2) (AdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 0 = (α₀ : AdeleRing K) * d₁ + β₀ * d₂ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1]
    rfl
  have hM10 : ((upperGL α₀ δ₀ β₀ * g : GL (Fin 2) (AdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (AdeleRing K)) 1 0 = (δ₀ : AdeleRing K) * d₂ := by
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1]
    show 0 * d₁ + (δ₀ : AdeleRing K) * d₂ = _
    rw [zero_mul, zero_add]
  have h00 : (α₁ : AdeleRing K) =
      (N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 0 * ((α₀ : AdeleRing K) * d₁ + β₀ * d₂) +
      (N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 1 * ((δ₀ : AdeleRing K) * d₂) := by
    have h := congrArg (fun g : GL (Fin 2) (AdeleRing K) =>
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing K)) 0 0) hu₁
    change (α₁ : AdeleRing K) = _ at h
    rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hM00, hM10] at h
    exact h
  have hN : ∀ i j, ((N : Matrix (Fin 2) (Fin 2) (AdeleRing K)) i j) ∈ integralAdeles K :=
    fun i j => by
      rw [hNdef, coe_mapO_apply]
      exact (((κ₁⁻¹ * κ₀ : GL (Fin 2) (integralAdeles K)) :
        Matrix (Fin 2) (Fin 2) (integralAdeles K)) i j).2
  have hfirst : (α₀ : AdeleRing K) * d₁ + β₀ * d₂ ∈ adeleLattice K (-E) := by
    have : (α₀ : AdeleRing K) * d₁ + β₀ * d₂ = (α₀ : AdeleRing K) *
        (d₁ + ((α₀⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β₀ * d₂) := by
      rw [mul_add, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]
    exact idele_mul_mem_adeleLattice_neg k α₀ hd₁
  have hsecond : (δ₀ : AdeleRing K) * d₂ ∈ adeleLattice K (-E) :=
    idele_mul_mem_adeleLattice_neg k δ₀ hd₂
  have hα₁ : (α₁ : AdeleRing K) ∈ adeleLattice K (-E) := by
    rw [h00]
    exact add_mem (integral_mul_mem_adeleLattice k (hN 0 0) hfirst)
      (integral_mul_mem_adeleLattice k (hN 0 1) hsecond)
  exact le_idelDiv_of_mem_adeleLattice_neg k α₁ hα₁

/-- The determinant identity of the reduction step. -/
public theorem idelDiv_add_of_reduction {κ₀ κ₁ : GL (Fin 2) (integralAdeles K)}
    {α₀ δ₀ α₁ δ₁ : (AdeleRing K)ˣ} {β₀ β₁ : AdeleRing K} {w₁ w₂ : K} (hw₂0 : w₂ ≠ 0)
    (hy : mapO κ₀ * upperGL α₀ δ₀ β₀ * mapK (GeneralLinearGroup.map (diagP k K)
      (gammaK w₁ hw₂0)) = mapO κ₁ * upperGL α₁ δ₁ β₁) :
    idelDiv k K α₁ + idelDiv k K δ₁ =
      idelDiv k K α₀ + idelDiv k K δ₀ + principalDivisor k K w₂ := by
  have h := congrArg (fun g => idelDiv k K (GeneralLinearGroup.det g)) hy
  simp only [map_mul, idelDiv_mul k, idelDiv_det_mapO k, zero_add, det_mapK_gammaK k,
    idelDiv_diagUnit k] at h
  rw [det_upperGL k, det_upperGL k, idelDiv_mul k, idelDiv_mul k] at h
  exact h.symm

/-- **Reduction theory**: every `x ∈ GL₂(A)` is `k · (α, β; 0, δ) · γ` with `k ∈ GL₂(O)`,
`γ ∈ GL₂(K)` and `N(div α - div δ) ≥ c₀`. -/
public theorem exists_reduction (x : GL (Fin 2) (AdeleRing K)) :
    ∃ (κ : GL (Fin 2) (integralAdeles K)) (γ : GL (Fin 2) (principalAdeles K))
      (α δ : (AdeleRing K)ˣ) (β : AdeleRing K), x = mapO κ * upperGL α δ β * mapK γ ∧
        redConst k K ≤ divNorm K (idelDiv k K α - idelDiv k K δ) := by
  obtain ⟨κ₀, α₀, δ₀, β₀, hx⟩ := exists_iwasawa x
  change x = mapO κ₀ * upperGL α₀ δ₀ β₀ at hx
  by_cases hcase : redConst k K ≤ divNorm K (idelDiv k K α₀ - idelDiv k K δ₀)
  · exact ⟨κ₀, 1, α₀, δ₀, β₀, by rw [map_one, mul_one]; exact hx, hcase⟩
  push Not at hcase
  obtain ⟨j, hcard, hbound⟩ := exists_reduction_exponent k hcase
  set S := Finsupp.single (basePlace k K) (j : ℤ)
  obtain ⟨w₁, w₂, hw₂0, hw₂, hw₁⟩ := exists_pigeonhole k (K := K)
    (((α₀⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β₀) hcard
  set γ := GeneralLinearGroup.map (diagP k K) (gammaK w₁ hw₂0)
  obtain ⟨κ₁, α₁, δ₁, β₁, hy₀⟩ := exists_iwasawa (x * mapK γ)
  change x * mapK γ = mapO κ₁ * upperGL α₁ δ₁ β₁ at hy₀
  rw [hx] at hy₀
  refine ⟨κ₁, γ⁻¹, α₁, δ₁, β₁, ?_, ?_⟩
  · rw [map_inv, hx, ← hy₀, mul_inv_cancel_right]
  have hw₂' : diag k K w₂ ∈ adeleLattice K (idelDiv k K δ₀ - (idelDiv k K α₀ + S)) := hw₂
  have hw₁' : diag k K w₁ + ((α₀⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β₀ * diag k K w₂ ∈
      adeleLattice K (idelDiv k K α₀ - (idelDiv k K α₀ + S)) := by
    rw [sub_add_cancel_left]; exact hw₁
  have hDa := le_idelDiv_of_reduction k (mapK_gammaK_apply_zero_zero k w₁ hw₂0)
    (mapK_gammaK_apply_one_zero k w₁ hw₂0) hw₂' hw₁' hy₀
  have hdet := idelDiv_add_of_reduction k hw₂0 hy₀
  have hsplit : idelDiv k K α₁ - idelDiv k K δ₁ =
      2 • (idelDiv k K α₁ - (idelDiv k K α₀ + S)) + (idelDiv k K α₀ - idelDiv k K δ₀) + 2 • S -
        principalDivisor k K w₂ := by
    have : idelDiv k K δ₁ = idelDiv k K α₀ + idelDiv k K δ₀ + principalDivisor k K w₂ -
        idelDiv k K α₁ := by rw [← hdet]; abel
    rw [this]; abel
  have hNS : divNorm K S = ((basePlace k K).resCard : ℚ) ^ j := by
    rw [divNorm_single, zpow_natCast]
  rw [hsplit, divNorm_sub k, divNorm_add k, divNorm_add k, divNorm_nsmul k, divNorm_nsmul k,
    divNorm_principalDivisor k hw₂0, div_one, hNS]
  have h1 : 1 ≤ divNorm K (idelDiv k K α₁ - (idelDiv k K α₀ + S)) ^ 2 :=
    one_le_pow₀ (one_le_divNorm k (sub_nonneg.2 hDa))
  have hp : 0 ≤ divNorm K (idelDiv k K α₀ - idelDiv k K δ₀) *
      (((basePlace k K).resCard : ℚ) ^ j) ^ 2 := by
    have := divNorm_pos k (idelDiv k K α₀ - idelDiv k K δ₀)
    positivity
  exact hbound.trans ((le_mul_of_one_le_left hp h1).trans_eq (mul_assoc _ _ _).symm)

end Reduction

section Support

include k

variable {Λ}

/-- The inverse of the idele `κ` is the idele `κ⁻¹`. -/
public theorem diagUnit_inv {κ : K} (hκ : κ ≠ 0) :
    (diagUnit k hκ)⁻¹ = diagUnit k (inv_ne_zero hκ) := by
  ext1
  simp [diagUnit]

/-- Invariance under `n(w)`, `w ∈ O`, on the left. -/
public theorem reducedForms_upperRight_left {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : f ∈ reducedForms k K Λ) {w : AdeleRing K} (hw : w ∈ integralAdeles K)
    (z : GL (Fin 2) (AdeleRing K)) : f (upperGL 1 1 w * z) = f z := by
  have := hf.1 (GeneralLinearGroup.upperRightHom ⟨w, hw⟩) z
  change f (GeneralLinearGroup.map (integralAdeles K).subtype
    (GeneralLinearGroup.upperRightHom ⟨w, hw⟩) * z) = f z at this
  rwa [mapO_upperRightHom, upperRightHom_eq_upperGL] at this

/-- Invariance under `n(t)`, `t ∈ K`, on the right. -/
public theorem reducedForms_upperRight_right {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : f ∈ reducedForms k K Λ) (t : K) (z : GL (Fin 2) (AdeleRing K)) :
    f (z * upperGL 1 1 (diag k K t)) = f z := by
  have := hf.2.1 (GeneralLinearGroup.upperRightHom (diagP k K t)) z
  change f (z * GeneralLinearGroup.map (principalAdeles K).subtype
    (GeneralLinearGroup.upperRightHom (diagP k K t))) = f z at this
  rwa [mapK_upperRightHom, upperRightHom_eq_upperGL] at this

/-- Invariance under `(o, 0; 0, 1)`, `o ∈ Oˣ`, on the left. -/
public theorem reducedForms_diag_left {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : f ∈ reducedForms k K Λ) (o : (integralAdeles K)ˣ) (z : GL (Fin 2) (AdeleRing K)) :
    f (upperGL (Units.map (integralAdeles K).subtype.toMonoidHom o) 1 0 * z) = f z := by
  have := hf.1 (diagGL o) z
  change f (GeneralLinearGroup.map (integralAdeles K).subtype (diagGL o) * z) = f z at this
  rwa [map_diagGL, diagGL_eq_upperGL] at this

/-- Invariance under `(κ, 0; 0, 1)`, `κ ∈ Kˣ`, on the right. -/
public theorem reducedForms_diag_right {f : GL (Fin 2) (AdeleRing K) → Λ}
    (hf : f ∈ reducedForms k K Λ) {κ : K} (hκ : κ ≠ 0) (z : GL (Fin 2) (AdeleRing K)) :
    f (z * upperGL (diagUnit k hκ) 1 0) = f z := by
  have := hf.2.1 (GeneralLinearGroup.map (diagP k K) (diagGL (Units.mk0 κ hκ))) z
  change f (z * GeneralLinearGroup.map (principalAdeles K).subtype
    (GeneralLinearGroup.map (diagP k K) (diagGL (Units.mk0 κ hκ)))) = f z at this
  rw [map_diagGL, map_diagGL, diagGL_eq_upperGL] at this
  convert this using 4
  ext1
  rfl

/-- Moving `(c, b; 0, 1)` to a representative with `c` the idele of a fixed divisor `D'`. -/
public theorem exists_rep_eval {c : (AdeleRing K)ˣ} {D' : Place K →₀ ℤ} {κ : K} (hκ : κ ≠ 0)
    (hc : idelDiv k K c = D' - principalDivisor k K κ) (b : AdeleRing K) :
    ∃ b' : AdeleRing K, ∀ f ∈ reducedForms k K Λ,
      f (upperGL c 1 b) = f (upperGL (idelOfDiv k K D') 1 b') := by
  set c' := idelOfDiv k K D'
  set o := c * c'⁻¹ * diagUnit k hκ
  have ho : idelDiv k K o = 0 := by
    simp only [o, c', idelDiv_mul, idelDiv_inv, idelDiv_idelOfDiv, idelDiv_diagUnit, hc]
    abel
  obtain ⟨o', ho'⟩ := exists_integralUnit_of_idelDiv_eq_zero k ho
  have ho'' : Units.map (integralAdeles K).subtype.toMonoidHom o' = o := Units.ext ho'
  refine ⟨((o⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * b, fun f hf => ?_⟩
  have hid : upperGL c 1 b = upperGL o 1 0 * (upperGL c' 1
      (((o⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * b) * upperGL (diagUnit k hκ)⁻¹ 1 0) := by
    rw [upperGL_mul, upperGL_mul]
    congr 1
    · simp only [o]
      rw [← mul_assoc, mul_right_comm (c * c'⁻¹) (diagUnit k hκ) c', mul_inv_cancel_right,
        inv_mul_cancel_right]
    · simp
    · simp only [mul_zero, zero_add, Units.val_one, mul_one, ← mul_assoc, Units.mul_inv, one_mul,
        add_zero]
  rw [hid, ← ho'', reducedForms_diag_left k hf, diagUnit_inv, reducedForms_diag_right k hf]

/-- Moving `(c', b; 0, 1)` to `(c', c' r; 0, 1)` with `r` in a finite set of representatives. -/
public theorem eval_eq_of_rep {D' : Place K →₀ ℤ} (b r : AdeleRing K)
    (hr : -r + ((idelOfDiv k K D')⁻¹ : (AdeleRing K)ˣ) * b ∈ principal k K ⊔ adeleLattice K D')
    {f : GL (Fin 2) (AdeleRing K) → Λ} (hf : f ∈ reducedForms k K Λ) :
    f (upperGL (idelOfDiv k K D') 1 b) =
      f (upperGL (idelOfDiv k K D') 1 ((idelOfDiv k K D' : AdeleRing K) * r)) := by
  set c' := idelOfDiv k K D'
  obtain ⟨p₀, hp₀, y, hy, hpy⟩ := AddSubgroup.mem_sup.1 hr
  obtain ⟨κ'', rfl⟩ := (mem_principal k).1 hp₀
  have hcy : (c' : AdeleRing K) * y ∈ integralAdeles K := by
    rw [← mem_adeleLattice_zero_iff]
    have h := (idele_mul_mem_adeleLattice_iff k c' (E := D')).2 hy
    rwa [idelDiv_idelOfDiv, sub_self] at h
  have hb : b = (c' : AdeleRing K) * r + ((c' : AdeleRing K) * diag k K κ'' +
      (c' : AdeleRing K) * y) := by
    have h1 : ((c'⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * b = r + (diag k K κ'' + y) := by
      linear_combination (-1 : AdeleRing K) * hpy
    rw [← mul_add, ← mul_add, ← h1, ← mul_assoc, Units.mul_inv, one_mul]
  have hid : upperGL c' 1 b = upperGL 1 1 ((c' : AdeleRing K) * y) *
      upperGL c' 1 ((c' : AdeleRing K) * r) * upperGL 1 1 (diag k K κ'') := by
    rw [upperGL_mul, upperGL_mul]
    congr 1
    · simp
    · simp
    · rw [hb]; simp only [Units.val_one, one_mul, mul_one]; ring
  rw [hid, reducedForms_upperRight_right k hf, reducedForms_upperRight_left k hf hcy]

variable (Λ)

/-- **Support**: there is a finite set `P ⊆ GL₂(A)` such that every value of an element of
`reducedForms` is a multiple, independent of the form, of its value at a point of `P`. -/
public theorem exists_finset_eval_eq (hp : IsUnit (ringChar k : Λ)) :
    ∃ P : Finset (GL (Fin 2) (AdeleRing K)), ∀ x, ∃ p ∈ P, ∃ u : Λ,
      ∀ f ∈ reducedForms k K Λ, f x = u * f p := by
  classical
  obtain ⟨M₀, hM₀⟩ := exists_sup_adeleLattice_eq_top k (K := K)
  have hc₀ := redConst_pos k (K := K)
  obtain ⟨F, hF⟩ := exists_finset_divisor_classes k (K := K) (max M₀ (redConst k K)⁻¹)
  let R : (Place K →₀ ℤ) → Finset (AdeleRing K) := fun D' =>
    have := finite_quotient_principal_sup_adeleLattice k D'
    let := Fintype.ofFinite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D'))
    (Finset.univ : Finset (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D'))).image Quotient.out
  have hR : ∀ D' (a : AdeleRing K), ∃ r ∈ R D', -r + a ∈ principal k K ⊔ adeleLattice K D' := by
    intro D' a
    have := finite_quotient_principal_sup_adeleLattice k D'
    let := Fintype.ofFinite (AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D'))
    refine ⟨Quotient.out (QuotientAddGroup.mk a :
      AdeleRing K ⧸ (principal k K ⊔ adeleLattice K D')), ?_, ?_⟩
    · simp only [R]
      convert Finset.mem_image_of_mem Quotient.out (Finset.mem_univ _)
    · exact QuotientAddGroup.eq.1 (Quotient.out_eq _)
  refine ⟨insert 1 (F.biUnion fun D' => (R D').image fun r =>
    upperGL (idelOfDiv k K D') 1 ((idelOfDiv k K D' : AdeleRing K) * r)), fun x => ?_⟩
  obtain ⟨κ, γ, α, δ, β, hx, hbound⟩ := exists_reduction k x
  have hfx : ∀ f ∈ reducedForms k K Λ, f x = f (upperGL α δ β) := fun f hf => by
    rw [hx, hf.2.1, hf.1]
  by_cases hD : M₀ ≤ divNorm K (idelDiv k K α - idelDiv k K δ)
  · refine ⟨1, Finset.mem_insert_self _ _, 0, fun f hf => ?_⟩
    rw [hfx f hf, hf.2.2.2 α δ β (hM₀ _ hD), zero_mul]
  push Not at hD
  have hlow : (max M₀ (redConst k K)⁻¹)⁻¹ ≤ divNorm K (idelDiv k K α - idelDiv k K δ) :=
    ((inv_le_comm₀ (lt_of_lt_of_le (inv_pos.2 hc₀) (le_max_right _ _)) hc₀).2
      (le_max_right _ _)).trans hbound
  obtain ⟨D', hD'F, κ', hκ', hDeq⟩ := hF _ hlow (hD.le.trans (le_max_left _ _))
  obtain ⟨u, hu⟩ := exists_unit_scalarGL k Λ hp δ
  have hcdiv : idelDiv k K (α * δ⁻¹) = D' - principalDivisor k K κ' := by
    rw [idelDiv_mul, idelDiv_inv, ← sub_eq_add_neg, hDeq]
  obtain ⟨b', hb'⟩ :=
    exists_rep_eval k (Λ := Λ) hκ' hcdiv (((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β)
  obtain ⟨r, hrR, hr⟩ := hR D' (((idelOfDiv k K D')⁻¹ : (AdeleRing K)ˣ) * b')
  refine ⟨upperGL (idelOfDiv k K D') 1 ((idelOfDiv k K D' : AdeleRing K) * r),
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨D', hD'F, Finset.mem_image_of_mem _ hrR⟩),
    u, fun f hf => ?_⟩
  have h1 : upperGL α δ β = scalarGL δ * upperGL (α * δ⁻¹) 1
      (((δ⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) * β) := by
    rw [scalarGL_eq_upperGL, upperGL_mul]
    congr 1
    · rw [mul_left_comm, mul_inv_cancel, mul_one]
    · rw [mul_one]
    · rw [zero_mul, add_zero, ← mul_assoc, Units.mul_inv, one_mul]
  rw [hfx f hf, h1, hu f hf, hb' f hf, eval_eq_of_rep k b' r hr hf]

end Support

/-- **Finite generation** (the first clause of Stacks 03VW): when the characteristic of `k` is
invertible in the Noetherian ring `Λ`, the module `C(Λ)` is finitely generated. -/
public theorem cuspFormsCentralChar_fg [IsNoetherianRing Λ] (hp : IsUnit (ringChar k : Λ)) :
    (cuspFormsCentralChar K Λ).FG := by
  classical
  obtain ⟨P, hP⟩ := exists_finset_eval_eq k Λ hp (K := K)
  let ψ : (GL (Fin 2) (AdeleRing K) → Λ) →ₗ[Λ] (P → Λ) :=
    LinearMap.pi fun p => LinearMap.proj (p : GL (Fin 2) (AdeleRing K))
  have hker : cuspFormsCentralChar K Λ ⊓ LinearMap.ker ψ = ⊥ := by
    rw [eq_bot_iff]
    rintro f ⟨hfC, hfk⟩
    have hfW := cuspFormsCentralChar_le_reducedForms k Λ hfC
    rw [Submodule.mem_bot]
    funext x
    obtain ⟨p, hpP, u, hu⟩ := hP x
    have h0 : f p = 0 := congrFun (LinearMap.mem_ker.1 hfk) ⟨p, hpP⟩
    rw [hu f hfW, h0, mul_zero, Pi.zero_apply]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker ψ (IsNoetherian.noetherian _) ?_
  rw [hker]
  exact Submodule.fg_bot

end Stacks.Adeles.GlobalFunctionField

end
