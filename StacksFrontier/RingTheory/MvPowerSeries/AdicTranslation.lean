module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.MvPowerSeries.Substitution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Adic lifts and translation automorphisms of power series rings

For an ideal `I` of a ring `Λ` that is `I`-adically complete, a compatible family of elements of
the quotients `Λ ⧸ I ^ N` lifts to `Λ`, and power series over `Λ` are determined by their
coefficients modulo every `I ^ N`. For `d : Fin n → Λ` with each `d i ∈ I`, this file constructs
the `Λ`-algebra endomorphism of `Λ[[x_1, …, x_n]]` sending `X i ↦ X i + C (d i)` as an `I`-adic
limit, proves the composition law for these translations, and shows they are bijective.
-/

open IsLocalRing MvPowerSeries

/-- If `g N ∈ R ⧸ I ^ N` is a family compatible under the projections
`R ⧸ I ^ (N + 1) → R ⧸ I ^ N`, then for `a ≤ b` the projection `R ⧸ I ^ b → R ⧸ I ^ a` sends
`g b` to `g a`. -/
lemma factor_g_le {R : Type*} [CommRing R] (I : Ideal R) (g : ∀ N : ℕ, R ⧸ (I ^ N))
    (hg : ∀ N, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N)) (g (N + 1)) = g N) :
    ∀ (a b : ℕ) (h : a ≤ b), Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (g b) = g a := by
  intro a b h
  induction b with
  | zero =>
    obtain rfl : a = 0 := Nat.le_zero.mp h
    simp
  | succ k ih =>
    rcases Nat.lt_or_ge a (k + 1) with hlt | hge
    · have hak : a ≤ k := Nat.lt_succ_iff.mp hlt
      calc
        Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (g (k + 1)) =
            Ideal.Quotient.factor (Ideal.pow_le_pow_right hak)
              (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k)) (g (k + 1))) := by
          induction (g (k + 1)) using Quotient.inductionOn with
          | h r => simp
        _ = Ideal.Quotient.factor (Ideal.pow_le_pow_right hak) (g k) := by rw [hg k]
        _ = g a := ih hak
    · obtain rfl : a = k + 1 := le_antisymm h hge
      simp

/-- If `R` is `I`-adically complete, every family `g N ∈ R ⧸ I ^ N` compatible under the
projections `R ⧸ I ^ (N + 1) → R ⧸ I ^ N` is the family of residues of a single `x : R`. -/
lemma adic_lift_of_compatible {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (g : ∀ N : ℕ, R ⧸ (I ^ N))
    (hg : ∀ N, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N)) (g (N + 1)) = g N) :
    ∃ x : R, ∀ N, Ideal.Quotient.mk (I ^ N) x = g N := by
  set r : ℕ → R := fun N => Quotient.out (g N)
  have hrout : ∀ N, Ideal.Quotient.mk (I ^ N) (r N) = g N := fun N => Quotient.out_eq (g N)
  have hcompat : ∀ {a b : ℕ}, a ≤ b → r a ≡ r b [SMOD I ^ a • (⊤ : Submodule R R)] := by
    intro a b h
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      hrout a, ← factor_g_le I g hg a b h, ← hrout b, Ideal.Quotient.factor_mk]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete) hcompat
  refine ⟨L, fun N => ?_⟩
  have hLN := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at hLN
  rw [← hrout N]
  exact ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr hLN).symm

/-- If `Λ` is `I`-adically complete, two power series over `Λ` whose coefficients agree modulo
`I ^ N` for every `N` are equal. -/
lemma coeff_ext_of_forall_mk {Λ : Type*} [CommRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] {n : ℕ}
    (a b : MvPowerSeries (Fin n) Λ)
    (h :
      ∀ (mm : Fin n →₀ ℕ) (N : ℕ),
        Ideal.Quotient.mk (I ^ N) (MvPowerSeries.coeff mm a) =
          Ideal.Quotient.mk (I ^ N) (MvPowerSeries.coeff mm b)) :
    a = b := by
  refine MvPowerSeries.ext fun mm => sub_eq_zero.mp ?_
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := I)) _ fun N => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, sub_zero,
    ← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact h mm N

namespace ShiftConstr

variable {Λ : Type*} [CommRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] {n : ℕ}

/-- The family of power series `X i + C (d i mod I ^ N)` over `Λ ⧸ I ^ N`. -/
noncomputable def aN (d : Fin n → Λ) (N : ℕ) : Fin n → MvPowerSeries (Fin n) (Λ ⧸ I ^ N) :=
  fun i => MvPowerSeries.X i + MvPowerSeries.C (Ideal.Quotient.mk (I ^ N) (d i))

omit [IsAdicComplete I Λ] in
/-- For `d i ∈ I`, the family `X i + C (d i mod I ^ N)` is admissible for substitution into
power series over `Λ ⧸ I ^ N`, its constant coefficients being nilpotent. -/
lemma hasSubst_aN (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (N : ℕ) :
    MvPowerSeries.HasSubst (aN I d N) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
  intro s
  refine ⟨N, ?_⟩
  have : MvPowerSeries.constantCoeff (aN I d N s) = Ideal.Quotient.mk (I ^ N) (d s) := by simp [aN]
  rw [this, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (hd s) N

omit [IsAdicComplete I Λ] in
/-- Reducing the family `aN I d (N + 1)` modulo `I ^ N` gives `aN I d N`. -/
lemma map_factor_aN (d : Fin n → Λ) (N : ℕ) (i : Fin n) :
    MvPowerSeries.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N) (I := I)))
        (aN I d (N + 1) i) =
      aN I d N i := by
  simp only [aN, map_add, MvPowerSeries.map_X, MvPowerSeries.map_C, Ideal.Quotient.factor_mk]

omit [IsAdicComplete I Λ] in
/-- Reducing modulo `I ^ N` the substitution of `aN I d (N + 1)` into `f mod I ^ (N + 1)` gives
the substitution of `aN I d N` into `f mod I ^ N`. -/
lemma factor_subst_succ (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (N : ℕ) (f : MvPowerSeries (Fin n) Λ) :
    MvPowerSeries.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N) (I := I)))
        (MvPowerSeries.subst (aN I d (N + 1))
          (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (N + 1))) f)) =
      MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  rw [MvPowerSeries.map_subst (hasSubst_aN I d hd (N + 1))]
  have hfam :
    (fun i =>
        MvPowerSeries.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N) (I := I)))
          (aN I d (N + 1) i)) =
      aN I d N := by
    funext i; exact map_factor_aN I d N i
  have hmap :
    MvPowerSeries.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N) (I := I)))
        (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (N + 1))) f) =
      MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f := by
    rw [MvPowerSeries.map_map]
    congr 1
  rw [hfam, hmap]

omit [IsAdicComplete I Λ] in
/-- The coefficients of `subst (aN I d N) (f mod I ^ N)` form a family compatible under the
projections `Λ ⧸ I ^ (N + 1) → Λ ⧸ I ^ N`. -/
lemma g_compatible (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ)
    (mm : Fin n →₀ ℕ) (N : ℕ) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ N))
        (MvPowerSeries.coeff mm
          (MvPowerSeries.subst (aN I d (N + 1))
            (MvPowerSeries.map (Ideal.Quotient.mk (I ^ (N + 1))) f))) =
      MvPowerSeries.coeff mm
        (MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f)) := by
  rw [← MvPowerSeries.coeff_map, factor_subst_succ I d hd N f]

/-- The element of `Λ` whose residue modulo every `I ^ N` is the coefficient of index `mm` of
`subst (aN I d N) (f mod I ^ N)`. -/
noncomputable def Lcoef (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ)
    (mm : Fin n →₀ ℕ) : Λ :=
  Classical.choose
    (adic_lift_of_compatible I
      (fun N =>
        MvPowerSeries.coeff mm
          (MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f)))
      (fun N => g_compatible I d hd f mm N))

/-- The residue of `Lcoef I d hd f mm` modulo `I ^ N` is the coefficient of index `mm` of
`subst (aN I d N) (f mod I ^ N)`. -/
lemma Lcoef_spec (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ)
    (mm : Fin n →₀ ℕ) (N : ℕ) :
    Ideal.Quotient.mk (I ^ N) (Lcoef I d hd f mm) =
      MvPowerSeries.coeff mm
        (MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f)) :=
  Classical.choose_spec
    (adic_lift_of_compatible I
      (fun N =>
        MvPowerSeries.coeff mm
          (MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f)))
      (fun N => g_compatible I d hd f mm N))
    N

/-- The power series whose coefficient of index `mm` is `Lcoef I d hd f mm`; it is the image of
`f` under the substitution `X i ↦ X i + C (d i)`. -/
noncomputable def shiftFun (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ) :
    MvPowerSeries (Fin n) Λ := fun mm => Lcoef I d hd f mm

/-- The coefficient of index `mm` of `shiftFun I d hd f` is `Lcoef I d hd f mm`. -/
lemma coeff_shiftFun (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ)
    (mm : Fin n →₀ ℕ) : MvPowerSeries.coeff mm (shiftFun I d hd f) = Lcoef I d hd f mm :=
  rfl

/-- Reducing `shiftFun I d hd f` modulo `I ^ N` gives `subst (aN I d N) (f mod I ^ N)`. -/
lemma map_shiftFun (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ) (N : ℕ) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (shiftFun I d hd f) =
      MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  apply MvPowerSeries.ext
  intro mm
  rw [MvPowerSeries.coeff_map, coeff_shiftFun, Lcoef_spec]

/-- Two power series over `Λ` whose reductions modulo `I ^ N` agree for every `N` are equal. -/
lemma eq_of_map_eq (a b : MvPowerSeries (Fin n) Λ)
    (h :
      ∀ N,
        MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) a =
          MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) b) :
    a = b := by
  apply coeff_ext_of_forall_mk I a b
  intro mm N
  have := congrArg (MvPowerSeries.coeff mm) (h N)
  rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at this

/-- Reducing `shiftFun I d hd f` modulo `I ^ N` is a `Λ ⧸ I ^ N`-algebra homomorphism applied to
`f mod I ^ N`. -/
private lemma map_shiftFun_eq_substAlgHom (d : Fin n → Λ) (hd : ∀ i, d i ∈ I)
    (f : MvPowerSeries (Fin n) Λ) (N : ℕ) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (shiftFun I d hd f) =
      MvPowerSeries.substAlgHom (R := Λ ⧸ I ^ N) (hasSubst_aN I d hd N)
        (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  rw [map_shiftFun, MvPowerSeries.substAlgHom_apply]

/-- `shiftFun I d hd` is additive. -/
lemma shiftFun_add (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f g : MvPowerSeries (Fin n) Λ) :
    shiftFun I d hd (f + g) = shiftFun I d hd f + shiftFun I d hd g :=
  eq_of_map_eq I _ _ fun N => by simp only [map_shiftFun_eq_substAlgHom, map_add]

/-- `shiftFun I d hd` sends `0` to `0`. -/
lemma shiftFun_zero (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) : shiftFun I d hd 0 = 0 :=
  eq_of_map_eq I _ _ fun N => by simp only [map_shiftFun_eq_substAlgHom, map_zero]

/-- `shiftFun I d hd` sends `1` to `1`. -/
lemma shiftFun_one (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) : shiftFun I d hd 1 = 1 :=
  eq_of_map_eq I _ _ fun N => by simp only [map_shiftFun_eq_substAlgHom, map_one]

/-- `shiftFun I d hd` is multiplicative. -/
lemma shiftFun_mul (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f g : MvPowerSeries (Fin n) Λ) :
    shiftFun I d hd (f * g) = shiftFun I d hd f * shiftFun I d hd g :=
  eq_of_map_eq I _ _ fun N => by simp only [map_shiftFun_eq_substAlgHom, map_mul]

/-- `shiftFun I d hd` fixes constant power series. -/
lemma shiftFun_C (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (x : Λ) :
    shiftFun I d hd (MvPowerSeries.C x) = MvPowerSeries.C x := by
  apply eq_of_map_eq I
  intro N
  rw [map_shiftFun]
  simp only [MvPowerSeries.map_C]
  rw [MvPowerSeries.subst_C]

/-- The `Λ`-algebra endomorphism of `Λ[[x_1, …, x_n]]` given by `X i ↦ X i + C (d i)`. -/
noncomputable def shiftAlgHom (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) :
    MvPowerSeries (Fin n) Λ →ₐ[Λ] MvPowerSeries (Fin n) Λ :=
  AlgHom.mk'
    { toFun := shiftFun I d hd
      map_one' := shiftFun_one I d hd
      map_mul' := shiftFun_mul I d hd
      map_zero' := shiftFun_zero I d hd
      map_add' := shiftFun_add I d hd }
    (by
      intro c f
      change shiftFun I d hd (c • f) = c • shiftFun I d hd f
      rw [MvPowerSeries.smul_eq_C_mul, shiftFun_mul, shiftFun_C, MvPowerSeries.smul_eq_C_mul])

/-- `shiftAlgHom I d hd` acts as `shiftFun I d hd`. -/
lemma shiftAlgHom_apply (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ) :
    shiftAlgHom I d hd f = shiftFun I d hd f :=
  rfl

/-- Reducing `shiftAlgHom I d hd f` modulo `I ^ N` gives `subst (aN I d N) (f mod I ^ N)`. -/
lemma map_shiftAlgHom (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (f : MvPowerSeries (Fin n) Λ) (N : ℕ) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) (shiftAlgHom I d hd f) =
      MvPowerSeries.subst (aN I d N) (MvPowerSeries.map (Ideal.Quotient.mk (I ^ N)) f) := by
  rw [shiftAlgHom_apply, map_shiftFun]

/-- `shiftAlgHom I d hd` sends `X i` to `X i + C (d i)`. -/
lemma shiftAlgHom_X (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) (i : Fin n) :
    shiftAlgHom I d hd (MvPowerSeries.X i) = MvPowerSeries.X i + MvPowerSeries.C (d i) := by
  apply eq_of_map_eq I
  intro N
  rw [map_shiftAlgHom]
  simp only [MvPowerSeries.map_X, map_add, MvPowerSeries.map_C]
  rw [MvPowerSeries.subst_X (hasSubst_aN I d hd N)]
  rfl

omit [IsAdicComplete I Λ] in
/-- Substituting `aN I d N` into `aN I e N i` gives `aN I (d + e) N i`. -/
lemma subst_aN_aN (d e : Fin n → Λ) (hd : ∀ i, d i ∈ I) (N : ℕ) (i : Fin n) :
    MvPowerSeries.subst (aN I d N) (aN I e N i) = aN I (d + e) N i := by
  have hd' := hasSubst_aN I d hd N
  rw [aN, MvPowerSeries.subst_add hd', MvPowerSeries.subst_X hd', MvPowerSeries.subst_C]
  rw [aN, aN, add_assoc]
  simp only [Pi.add_apply, map_add]

/-- The composite of the translations by `d` and by `e` is the translation by `d + e`. -/
lemma shiftAlgHom_comp (d e : Fin n → Λ) (hd : ∀ i, d i ∈ I) (he : ∀ i, e i ∈ I)
    (hde : ∀ i, (d + e) i ∈ I) :
    (shiftAlgHom I d hd).comp (shiftAlgHom I e he) = shiftAlgHom I (d + e) hde := by
  refine AlgHom.ext fun f => eq_of_map_eq I _ _ fun N => ?_
  rw [AlgHom.comp_apply, map_shiftAlgHom, map_shiftAlgHom, map_shiftAlgHom]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_aN I e he N) (hasSubst_aN I d hd N)]
  exact congrArg (MvPowerSeries.subst · _) (funext (subst_aN_aN I d e hd N))

omit [IsAdicComplete I Λ] in
/-- The family `aN I 0 N` is the family of variables `X`. -/
lemma aN_zero (N : ℕ) : aN I (0 : Fin n → Λ) N = MvPowerSeries.X := by
  funext i
  rw [aN]
  simp

/-- The translation by `0` is the identity. -/
lemma shiftAlgHom_zero (h0 : ∀ i, (0 : Fin n → Λ) i ∈ I) :
    shiftAlgHom I (0 : Fin n → Λ) h0 = AlgHom.id Λ (MvPowerSeries (Fin n) Λ) := by
  refine AlgHom.ext fun f => eq_of_map_eq I _ _ fun N => ?_
  rw [map_shiftAlgHom, aN_zero, MvPowerSeries.subst_self]
  rfl

/-- Translations by equal families are equal. -/
lemma shiftAlgHom_congr (d d' : Fin n → Λ) (hd : ∀ i, d i ∈ I) (hd' : ∀ i, d' i ∈ I)
    (h : d = d') : shiftAlgHom I d hd = shiftAlgHom I d' hd' := by
  subst h
  rfl

/-- If `d + e = 0`, the composite of the translations by `d` and by `e` is the identity. -/
lemma shiftAlgHom_comp_eq_id (d e : Fin n → Λ) (hd : ∀ i, d i ∈ I) (he : ∀ i, e i ∈ I)
    (hde : d + e = 0) :
    (shiftAlgHom I d hd).comp (shiftAlgHom I e he) = AlgHom.id Λ (MvPowerSeries (Fin n) Λ) := by
  have h0 : ∀ i, (0 : Fin n → Λ) i ∈ I := fun _ => I.zero_mem
  have hde' : ∀ i, (d + e) i ∈ I := hde ▸ h0
  rw [shiftAlgHom_comp I d e hd he hde', shiftAlgHom_congr I (d + e) 0 hde' h0 hde,
    shiftAlgHom_zero I h0]

/-- The translation `X i ↦ X i + C (d i)` is bijective. -/
lemma shiftAlgHom_bijective (d : Fin n → Λ) (hd : ∀ i, d i ∈ I) :
    Function.Bijective (shiftAlgHom I d hd) := by
  have hnd : ∀ i, (-d) i ∈ I := fun i => by simpa using I.neg_mem (hd i)
  exact (AlgEquiv.ofAlgHom _ _ (shiftAlgHom_comp_eq_id I d (-d) hd hnd (by simp))
    (shiftAlgHom_comp_eq_id I (-d) d hnd hd (by simp))).bijective

end ShiftConstr
