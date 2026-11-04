module

public import StacksFrontier.NumberTheory.Adeles.GlobalFunctionField.RiemannRoch

/-!
# Ideles of a global function field

For an idele `c` (a unit of the adele ring) of a global function field `K` we define its divisor
`div c = (ord_v c_v)_v`, show that multiplication by `c` maps `A(E)` onto `A(E - div c)`, that an
idele of divisor `0` is a unit of the integral adeles `O`, that every divisor is the divisor of an
idele, and we describe the central data of the Hecke operators `U_v` (the scalar matrix
`π_v⁻¹` at `v`).

## Main definitions

* `Stacks.Adeles.GlobalFunctionField.idelDiv` — the divisor of an idele.
* `Stacks.Adeles.GlobalFunctionField.idelOfDiv` — an idele with prescribed divisor.
* `Stacks.Adeles.GlobalFunctionField.scalarGL` — the scalar matrix of an idele in `GL₂(A)`.
-/

@[expose] public noncomputable section

open WithZero Matrix

universe u

namespace Stacks.Adeles.GlobalFunctionField

section KFree

variable {K : Type u} [Field K]

/-- The components of an idele and of its inverse multiply to `1` at every place. -/
public theorem idele_mul_inv_apply (c : (AdeleRing K)ˣ) (v : Place K) :
    (c : AdeleRing K) v * ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) v = 1 :=
  (congrArg (fun x : AdeleRing K => x v) c.mul_inv :)

/-- Every component of an idele is nonzero. -/
public theorem idele_apply_ne_zero (c : (AdeleRing K)ˣ) (v : Place K) :
    (c : AdeleRing K) v ≠ 0 := fun h => by
  have := idele_mul_inv_apply c v
  rw [h, zero_mul] at this
  exact zero_ne_one this

/-- The scalar matrix of an idele, as a homomorphism `Aˣ → GL₂(A)`. -/
public def scalarGL : (AdeleRing K)ˣ →* GL (Fin 2) (AdeleRing K) :=
  Units.map
    (Matrix.scalar (Fin 2) : AdeleRing K →+* Matrix (Fin 2) (Fin 2) (AdeleRing K)).toMonoidHom

/-- The underlying matrix of `scalarGL c` is the scalar matrix of `c`. -/
@[simp]
public theorem coe_scalarGL (c : (AdeleRing K)ˣ) :
    ((scalarGL c : GL (Fin 2) (AdeleRing K)) : Matrix (Fin 2) (Fin 2) (AdeleRing K)) =
      Matrix.scalar (Fin 2) (c : AdeleRing K) := rfl

/-- Scalar matrices are central. -/
public theorem scalarGL_mul_comm (c : (AdeleRing K)ˣ) (x : GL (Fin 2) (AdeleRing K)) :
    scalarGL c * x = x * scalarGL c :=
  Units.ext (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).eq

open scoped Classical in
/-- The idele with component `z ≠ 0` at `v` and `1` elsewhere. -/
public def localIdele (v : Place K) {z : v.completion} (hz : z ≠ 0) : (AdeleRing K)ˣ where
  val := ⟨Pi.mulSingle v z, (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    apply hw
    change Pi.mulSingle v z w ∈ (w.integers : Set w.completion)
    rw [Pi.mulSingle_eq_of_ne (by simpa using h)]
    exact w.integers.one_mem⟩
  inv := ⟨Pi.mulSingle v z⁻¹, (Set.finite_singleton v).subset fun w hw => by
    by_contra h
    apply hw
    change Pi.mulSingle v z⁻¹ w ∈ (w.integers : Set w.completion)
    rw [Pi.mulSingle_eq_of_ne (by simpa using h)]
    exact w.integers.one_mem⟩
  val_inv := RestrictedProduct.ext _ _ fun w => by
    change Pi.mulSingle v z w * Pi.mulSingle v z⁻¹ w = 1
    by_cases hw : w = v
    · subst hw; simp [hz]
    · simp [Pi.mulSingle_eq_of_ne hw]
  inv_val := RestrictedProduct.ext _ _ fun w => by
    change Pi.mulSingle v z⁻¹ w * Pi.mulSingle v z w = 1
    by_cases hw : w = v
    · subst hw; simp [hz]
    · simp [Pi.mulSingle_eq_of_ne hw]

open scoped Classical in
/-- The component of `localIdele v hz` at `v` is `z`. -/
public theorem localIdele_apply_self (v : Place K) {z : v.completion} (hz : z ≠ 0) :
    (localIdele v hz : AdeleRing K) v = z :=
  Pi.mulSingle_eq_same v z

open scoped Classical in
/-- The component of `localIdele v hz` at a place `w ≠ v` is `1`. -/
public theorem localIdele_apply_ne {v w : Place K} (h : w ≠ v) {z : v.completion} (hz : z ≠ 0) :
    (localIdele v hz : AdeleRing K) w = 1 :=
  Pi.mulSingle_eq_of_ne h z

end KFree

variable (k : Type u) [Field k] [Finite k] {K : Type u} [Field K] [Algebra k K]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

include k

/-- The order of `1` in a completion is `0`. -/
public theorem ordC_one (v : Place K) : v.ordC (1 : v.completion) = 0 := by
  have := Place.ordC_coeRingHom (isDiscrete k v) (one_ne_zero (α := K))
  rw [map_one] at this
  rw [this, Place.ord, map_one, log_one, neg_zero]

/-- The order of the inverse of an idele at `v` is the negative of its order. -/
public theorem ordC_inv_idele (c : (AdeleRing K)ˣ) (v : Place K) :
    v.ordC (((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) v) = -v.ordC ((c : AdeleRing K) v) := by
  have h := Place.ordC_mul (isDiscrete k v) (idele_apply_ne_zero c v) (idele_apply_ne_zero c⁻¹ v)
  rw [idele_mul_inv_apply, ordC_one k] at h
  omega

/-- An idele has order `0` at all but finitely many places. -/
public theorem finite_setOf_ordC_ne_zero (c : (AdeleRing K)ˣ) :
    {v : Place K | v.ordC ((c : AdeleRing K) v) ≠ 0}.Finite := by
  refine ((Filter.eventually_cofinite.1 (c : AdeleRing K).2).union
    (Filter.eventually_cofinite.1 ((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K).2)).subset ?_
  intro v hv
  by_contra hmem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hmem
  have h1 := (Place.mem_ball_iff_ordC (isDiscrete k v) (m := 0)).1
    (Place.mem_ball_zero_iff.2 hmem.1)
  have h2 := (Place.mem_ball_iff_ordC (isDiscrete k v) (m := 0)).1
    (Place.mem_ball_zero_iff.2 hmem.2)
  have h3 := ordC_inv_idele k c v
  rcases h1 with h1 | h1
  · exact idele_apply_ne_zero c v h1
  rcases h2 with h2 | h2
  · exact idele_apply_ne_zero c⁻¹ v h2
  have h2' : 0 ≤ v.ordC (((c⁻¹ : (AdeleRing K)ˣ) : AdeleRing K) v) := h2
  have h1' : 0 ≤ v.ordC ((c : AdeleRing K) v) := h1
  rw [h3] at h2'
  exact hv (by omega)

variable (K) in
/-- The divisor `(ord_v c_v)_v` of an idele `c`. -/
public def idelDiv (c : (AdeleRing K)ˣ) : Place K →₀ ℤ :=
  Finsupp.ofSupportFinite (fun v => v.ordC ((c : AdeleRing K) v)) (finite_setOf_ordC_ne_zero k c)

/-- The coefficient of `div c` at `v` is the order of `c_v`. -/
@[simp]
public theorem idelDiv_apply (c : (AdeleRing K)ˣ) (v : Place K) :
    idelDiv k K c v = v.ordC ((c : AdeleRing K) v) := rfl

/-- The divisor of a product of ideles is the sum of their divisors. -/
public theorem idelDiv_mul (c c' : (AdeleRing K)ˣ) :
    idelDiv k K (c * c') = idelDiv k K c + idelDiv k K c' := by
  ext v
  simp only [idelDiv_apply, Units.val_mul, Finsupp.coe_add, Pi.add_apply]
  exact Place.ordC_mul (isDiscrete k v) (idele_apply_ne_zero c v) (idele_apply_ne_zero c' v)

/-- The divisor of the inverse of an idele is the negative of its divisor. -/
public theorem idelDiv_inv (c : (AdeleRing K)ˣ) : idelDiv k K c⁻¹ = -idelDiv k K c := by
  ext v
  simp only [idelDiv_apply, Finsupp.coe_neg, Pi.neg_apply]
  exact ordC_inv_idele k c v

/-- The divisor of the unit idele is `0`. -/
public theorem idelDiv_one : idelDiv k K 1 = 0 := by
  ext v
  simp only [idelDiv_apply, Units.val_one, Finsupp.coe_zero, Pi.zero_apply]
  exact ordC_one k v

/-- Multiplication by an idele `c` maps `A(E)` onto `A(E - div c)`. -/
public theorem idele_mul_mem_adeleLattice_iff (c : (AdeleRing K)ˣ) {E : Place K →₀ ℤ}
    {y : AdeleRing K} :
    (c : AdeleRing K) * y ∈ adeleLattice K (E - idelDiv k K c) ↔ y ∈ adeleLattice K E := by
  simp only [mem_adeleLattice]
  refine forall_congr' fun v => ?_
  have : -(E - idelDiv k K c) v = -E v + v.ordC ((c : AdeleRing K) v) := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, idelDiv_apply]; ring
  rw [this]
  exact Place.mul_mem_ball_iff (isDiscrete k v) (idele_apply_ne_zero c v)

/-- The idele of `κ ∈ Kˣ`. -/
public def diagUnit {κ : K} (hκ : κ ≠ 0) : (AdeleRing K)ˣ := Units.map (diag k K) (Units.mk0 κ hκ)

/-- The underlying adele of `diagUnit k hκ` is the diagonal image of `κ`. -/
@[simp]
public theorem coe_diagUnit {κ : K} (hκ : κ ≠ 0) : (diagUnit k hκ : AdeleRing K) = diag k K κ := rfl

/-- The divisor of the idele of `κ ∈ Kˣ` is the principal divisor of `κ`. -/
public theorem idelDiv_diagUnit {κ : K} (hκ : κ ≠ 0) :
    idelDiv k K (diagUnit k hκ) = principalDivisor k K κ := by
  ext v
  simp only [idelDiv_apply, coe_diagUnit, diag_apply, principalDivisor_apply]
  exact Place.ordC_coeRingHom (isDiscrete k v) hκ

/-- An idele of divisor `0` is a unit of the integral adeles. -/
public theorem exists_integralUnit_of_idelDiv_eq_zero {c : (AdeleRing K)ˣ}
    (h : idelDiv k K c = 0) :
    ∃ o : (integralAdeles K)ˣ, ((o : integralAdeles K) : AdeleRing K) = c := by
  have hmem : ∀ d : (AdeleRing K)ˣ, idelDiv k K d = 0 → (d : AdeleRing K) ∈ integralAdeles K := by
    intro d hd v
    rw [← Place.mem_ball_zero_iff, Place.mem_ball_iff_ordC (isDiscrete k v)]
    right
    have := congrArg (fun D => D v) hd
    simp only [idelDiv_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    omega
  have h' : idelDiv k K c⁻¹ = 0 := by rw [idelDiv_inv, h, neg_zero]
  refine ⟨⟨⟨c, hmem c h⟩, ⟨_, hmem c⁻¹ h'⟩, Subtype.ext c.mul_inv, Subtype.ext c.inv_mul⟩, rfl⟩

variable (K) in
/-- An idele with divisor `D`: `ϖ_v ^ D(v)` at every place. -/
public def idelOfDiv (D : Place K →₀ ℤ) : (AdeleRing K)ˣ where
  val := ⟨fun v => v.coeRingHom (v.unif ^ D v), Filter.eventually_cofinite.2
    (D.finite_support.subset fun v hv => by
      by_contra h
      have hD : D v = 0 := Function.notMem_support.1 h
      exact hv (by simp only [hD, zpow_zero, map_one]; exact v.integers.one_mem))⟩
  inv := ⟨fun v => v.coeRingHom (v.unif ^ (-D v)), Filter.eventually_cofinite.2
    (D.finite_support.subset fun v hv => by
      by_contra h
      have hD : D v = 0 := Function.notMem_support.1 h
      exact hv (by simp only [hD, neg_zero, zpow_zero, map_one]; exact v.integers.one_mem))⟩
  val_inv := RestrictedProduct.ext _ _ fun v => by
    change v.coeRingHom _ * v.coeRingHom _ = 1
    rw [← map_mul, ← zpow_add₀ (Place.unif_ne_zero (isDiscrete k v)), add_neg_cancel, zpow_zero,
      map_one]
  inv_val := RestrictedProduct.ext _ _ fun v => by
    change v.coeRingHom _ * v.coeRingHom _ = 1
    rw [← map_mul, ← zpow_add₀ (Place.unif_ne_zero (isDiscrete k v)), neg_add_cancel, zpow_zero,
      map_one]

/-- The order of `ϖ_v ^ n` in the completion at `v` is `n`. -/
private theorem ordC_coeRingHom_unif_zpow (v : Place K) (n : ℤ) :
    v.ordC (v.coeRingHom (v.unif ^ n)) = n := by
  rw [Place.ordC_coeRingHom (isDiscrete k v) (zpow_ne_zero _ (Place.unif_ne_zero (isDiscrete k v))),
    Place.ord, map_zpow₀, Place.normVal_unif (isDiscrete k v), ← exp_zsmul, log_exp]
  simp

/-- The idele `idelOfDiv k K D` has divisor `D`. -/
public theorem idelDiv_idelOfDiv (D : Place K →₀ ℤ) : idelDiv k K (idelOfDiv k K D) = D := by
  ext v
  exact ordC_coeRingHom_unif_zpow k v (D v)

/-- The inverse uniformizer at `v`, as an idele. -/
public def unifInvIdele (v : Place K) : (AdeleRing K)ˣ :=
  localIdele v (z := (v.coeRingHom v.unif)⁻¹)
    (inv_ne_zero ((_root_.map_ne_zero _).2 (Place.unif_ne_zero (isDiscrete k v))))

/-- The inverse uniformizer at `v` has divisor `-v`. -/
public theorem idelDiv_unifInvIdele (v : Place K) :
    idelDiv k K (unifInvIdele k v) = -Finsupp.single v 1 := by
  classical
  ext w
  simp only [idelDiv_apply, Finsupp.coe_neg, Pi.neg_apply, Finsupp.single_apply]
  by_cases hw : w = v
  · subst hw
    rw [unifInvIdele, localIdele_apply_self, if_pos rfl,
      ← zpow_neg_one, ← map_zpow₀, ordC_coeRingHom_unif_zpow k w]
  · rw [unifInvIdele, localIdele_apply_ne hw, if_neg (Ne.symm hw), ordC_one k, neg_zero]

/-- The scalar matrix of the inverse uniformizer at `v` is central data for `U_v`. -/
public theorem isCentralDataAt_scalarGL_unifInvIdele (v : Place K) :
    IsCentralDataAt v (scalarGL (unifInvIdele k v)) := by
  classical
  refine ⟨_, Place.isUniformizer_unif (isDiscrete k v), fun i j => ?_, fun w hw i j => ?_⟩
  · simp only [coe_scalarGL, Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs <;> simp [unifInvIdele, localIdele_apply_self]
  · simp only [coe_scalarGL, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp [unifInvIdele, localIdele_apply_ne hw]

end Stacks.Adeles.GlobalFunctionField

end
