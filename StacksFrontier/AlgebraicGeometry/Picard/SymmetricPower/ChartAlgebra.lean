module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The coordinate ring of a chart of the Hilbert scheme of points of an affine scheme

Let `R` be a ring, `A` an `R`-algebra and `w : Fin d → A` a `d`-tuple of elements of `A`. For an
`R`-algebra `R'` consider the ideals `J ⊆ R' ⊗_R A` such that the images of `1 ⊗ w l` form an
`R'`-basis of `(R' ⊗_R A) / J`. These are the `R'`-points of the chart `F_W` of the Hilbert
scheme of points of `Spec A` used in the proof of Stacks Tag 0B99. This file proves that this
functor of `R'` is representable by an `R`-algebra `chartRing w`.

An ideal `J` as above is determined by its coordinate functions `t l a ∈ R'`, the `l`-th
coordinate of the class of `1 ⊗ a` in the basis. The functions `t` that arise are exactly those
which are `R`-linear in `a`, take `w m` to the `m`-th standard basis vector and satisfy
`t l (a * b) = ∑ m, t m b * t l (a * w m)`, the condition saying that multiplication by `a`
is computed in the basis. Such a family of functions is a *chart function*, and `chartRing w`
is the polynomial ring on symbols `t l a` modulo these identities.

## Main definitions

* `Stacks.Hilbert.Chart.IsChartFunction`: the identities defining a chart function.
* `Stacks.Hilbert.Chart.chartRing`: the representing `R`-algebra.
* `Stacks.Hilbert.Chart.chartIdeal`: the ideal of `R' ⊗_R A` attached to a chart function.

## Main results

* `Stacks.Hilbert.Chart.liftEquiv`: `R`-algebra maps `chartRing w → R'` are chart functions.
* `Stacks.Hilbert.Chart.chartBasis`: for a chart function the images of `w` form a basis of the
  quotient by its ideal.
* `Stacks.Hilbert.Chart.isChartFunction_of_basis`: conversely the coordinates of an algebra map
  `A → B` into an `R'`-algebra in which the images of `w` form a basis are a chart function, and
  `Stacks.Hilbert.Chart.ker_lift_eq_chartIdeal` identifies the kernel of `R' ⊗_R A → B`.
* `Stacks.Hilbert.Chart.chartIdeal_comp`: formation of the ideal commutes with base change.

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open TensorProduct

universe u v w

namespace Stacks.Hilbert.Chart

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {d : ℕ}
  (w : Fin d → A)

variable (R) in
/-- A *chart function* for `w`: a family `t l : A → R'` of `R`-linear maps sending `w m` to the
`m`-th standard basis vector and satisfying `t l (a * b) = ∑ m, t m b * t l (a * w m)`. -/
structure IsChartFunction {R' : Type w} [CommRing R'] [Algebra R R'] (t : Fin d → A → R') :
    Prop where
  map_add : ∀ l a b, t l (a + b) = t l a + t l b
  map_smul : ∀ l (r : R) a, t l (r • a) = algebraMap R R' r * t l a
  map_basis : ∀ l m, t l (w m) = if l = m then 1 else 0
  map_mul : ∀ l a b, t l (a * b) = ∑ m, t m b * t l (a * w m)

variable (R) in
open MvPolynomial in
/-- The polynomial identities defining a chart function. -/
def relations : Set (MvPolynomial (Fin d × A) R) :=
  (Set.range fun p : Fin d × A × A =>
      X (p.1, p.2.1 + p.2.2) - X (p.1, p.2.1) - X (p.1, p.2.2)) ∪
    (Set.range fun p : Fin d × R × A => X (p.1, p.2.1 • p.2.2) - C p.2.1 * X (p.1, p.2.2)) ∪
    (Set.range fun p : Fin d × Fin d => X (p.1, w p.2) - if p.1 = p.2 then 1 else 0) ∪
    (Set.range fun p : Fin d × A × A =>
      X (p.1, p.2.1 * p.2.2) - ∑ m, X (m, p.2.2) * X (p.1, p.2.1 * w m))

variable (R) in
/-- The coordinate ring of the chart attached to `w`. -/
abbrev chartRing : Type (max u v) :=
  MvPolynomial (Fin d × A) R ⧸ Ideal.span (relations R w)

variable (R) in
/-- The universal chart function, with values in `chartRing R w`. -/
def tUniv (l : Fin d) (a : A) : chartRing R w :=
  Ideal.Quotient.mk _ (MvPolynomial.X (l, a))

variable {w}

open MvPolynomial in
theorem aeval_relations_eq_zero_iff {R' : Type w} [CommRing R'] [Algebra R R']
    (t : Fin d → A → R') :
    (∀ p ∈ relations R w, aeval (fun i : Fin d × A => t i.1 i.2) p = 0) ↔
      IsChartFunction R w t := by
  constructor
  · intro h
    refine ⟨fun l a b => ?_, fun l r a => ?_, fun l m => ?_, fun l a b => ?_⟩
    · have := h _ (Or.inl (Or.inl (Or.inl ⟨(l, a, b), rfl⟩)))
      simp only [map_sub, aeval_X] at this
      linear_combination this
    · have := h _ (Or.inl (Or.inl (Or.inr ⟨(l, r, a), rfl⟩)))
      simp only [map_sub, map_mul, aeval_X, aeval_C] at this
      linear_combination this
    · have := h _ (Or.inl (Or.inr ⟨(l, m), rfl⟩))
      split_ifs at this ⊢ <;> simp_all [sub_eq_zero]
    · have := h _ (Or.inr ⟨(l, a, b), rfl⟩)
      simp only [map_sub, map_sum, map_mul, aeval_X] at this
      linear_combination this
  · rintro ht p (((⟨⟨l, a, b⟩, rfl⟩ | ⟨⟨l, r, a⟩, rfl⟩) | ⟨⟨l, m⟩, rfl⟩) | ⟨⟨l, a, b⟩, rfl⟩)
    · simp only [map_sub, aeval_X, ht.map_add]; ring
    · simp only [map_sub, map_mul, aeval_X, aeval_C, ht.map_smul]; ring
    · simp only [map_sub, aeval_X, ht.map_basis]
      split_ifs <;> simp
    · simp only [map_sub, map_sum, map_mul, aeval_X, ht.map_mul l a b]; ring

theorem isChartFunction_tUniv : IsChartFunction R w (tUniv R w) := by
  rw [← aeval_relations_eq_zero_iff]
  have key : ∀ p, MvPolynomial.aeval (fun i : Fin d × A => tUniv R w i.1 i.2) p =
      Ideal.Quotient.mk (Ideal.span (relations R w)) p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C r => rw [MvPolynomial.aeval_C]; rfl
    | add p q hp' hq' => rw [map_add, map_add, hp', hq']
    | mul_X p i hp' => rw [map_mul, map_mul, hp', MvPolynomial.aeval_X]; rfl
  intro p hp
  rw [key, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span hp

theorem aeval_eq_zero_of_mem_span {R' : Type w} [CommRing R'] [Algebra R R']
    {t : Fin d → A → R'} (ht : IsChartFunction R w t) {p : MvPolynomial (Fin d × A) R}
    (hp : p ∈ Ideal.span (relations R w)) :
    MvPolynomial.aeval (fun i : Fin d × A => t i.1 i.2) p = 0 := by
  induction hp using Submodule.span_induction with
  | mem q hq => exact (aeval_relations_eq_zero_iff t).mpr ht q hq
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, map_mul, hx, mul_zero]

/-- The `R`-algebra map `chartRing R w → R'` of a chart function. -/
def lift {R' : Type w} [CommRing R'] [Algebra R R'] {t : Fin d → A → R'}
    (ht : IsChartFunction R w t) : chartRing R w →ₐ[R] R' :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun i : Fin d × A => t i.1 i.2)
    fun _ hp => aeval_eq_zero_of_mem_span ht hp

@[simp]
theorem lift_tUniv {R' : Type w} [CommRing R'] [Algebra R R'] {t : Fin d → A → R'}
    (ht : IsChartFunction R w t) (l : Fin d) (a : A) : lift ht (tUniv R w l a) = t l a :=
  MvPolynomial.aeval_X _ _

theorem algHom_ext {R' : Type w} [CommRing R'] [Algebra R R'] {φ ψ : chartRing R w →ₐ[R] R'}
    (h : ∀ l a, φ (tUniv R w l a) = ψ (tUniv R w l a)) : φ = ψ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i.1 i.2

theorem isChartFunction_comp {R' : Type w} [CommRing R'] [Algebra R R']
    (φ : chartRing R w →ₐ[R] R') : IsChartFunction R w fun l a => φ (tUniv R w l a) := by
  have h := isChartFunction_tUniv (R := R) (w := w)
  refine ⟨fun l a b => by rw [h.map_add, map_add], fun l r a => by
      rw [h.map_smul, map_mul, AlgHom.commutes],
    fun l m => by rw [h.map_basis]; split_ifs <;> simp,
    fun l a b => by rw [h.map_mul, map_sum]; simp only [map_mul]⟩

/-- **The universal property of the chart ring.** `R`-algebra maps `chartRing R w → R'` are the
chart functions with values in `R'`. -/
def liftEquiv (R' : Type w) [CommRing R'] [Algebra R R'] :
    (chartRing R w →ₐ[R] R') ≃ {t : Fin d → A → R' // IsChartFunction R w t} where
  toFun φ := ⟨fun l a => φ (tUniv R w l a), isChartFunction_comp φ⟩
  invFun t := lift t.2
  left_inv φ := algHom_ext fun l a => lift_tUniv _ l a
  right_inv t := by
    ext l a
    exact lift_tUniv t.2 l a

@[simp]
theorem liftEquiv_apply_coe (R' : Type w) [CommRing R'] [Algebra R R']
    (φ : chartRing R w →ₐ[R] R') (l : Fin d) (a : A) :
    (liftEquiv R' φ).1 l a = φ (tUniv R w l a) := rfl

@[simp]
theorem liftEquiv_symm_apply (R' : Type w) [CommRing R'] [Algebra R R']
    (t : {t : Fin d → A → R' // IsChartFunction R w t}) : (liftEquiv R').symm t = lift t.2 :=
  rfl

/-! ### The ideal of a chart function -/

section Ideal

variable {R' : Type w} [CommRing R'] [Algebra R R']

variable (R w) in
/-- The generators `1 ⊗ a - ∑ l, t l a ⊗ w l` of the ideal of a chart function. -/
def chartGenerator (t : Fin d → A → R') (a : A) : R' ⊗[R] A :=
  (1 : R') ⊗ₜ a - ∑ l, t l a ⊗ₜ w l

variable (R w) in
/-- The ideal of `R' ⊗_R A` attached to a family of coordinate functions. -/
def chartIdeal (t : Fin d → A → R') : Ideal (R' ⊗[R] A) :=
  Ideal.span (Set.range (chartGenerator R w t))

/-- The `R'`-linear coordinate map `R' ⊗_R A → R'^d`, `r ⊗ a ↦ r • t(-, a)`. -/
def coordMap {t : Fin d → A → R'} (ht : IsChartFunction R w t) : R' ⊗[R] A →ₗ[R'] (Fin d → R') :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun r =>
        { toFun := fun a => r • fun l => t l a
          map_add' := fun a b => by ext l; simp [ht.map_add, mul_add]
          map_smul' := fun s a => by
            ext l
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ht.map_smul]
            rw [Algebra.smul_def]
            ring }
      map_add' := fun r s => by ext a l; simp [add_mul]
      map_smul' := fun r s => by ext a l; simp [mul_assoc] }

@[simp]
theorem coordMap_tmul {t : Fin d → A → R'} (ht : IsChartFunction R w t) (r : R') (a : A) :
    coordMap ht (r ⊗ₜ a) = r • fun l => t l a := rfl

theorem coordMap_mul_chartGenerator {t : Fin d → A → R'} (ht : IsChartFunction R w t)
    (x : R' ⊗[R] A) (a : A) : coordMap ht (x * chartGenerator R w t a) = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r c =>
    simp only [chartGenerator, mul_sub, Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, map_sub, map_sum, coordMap_tmul]
    ext l
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, ht.map_mul l c a]
    rw [Finset.mul_sum, Pi.zero_apply, sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => by ring
  | add x y hx hy => simp [add_mul, hx, hy]

theorem coordMap_eq_zero_of_mem {t : Fin d → A → R'} (ht : IsChartFunction R w t)
    {x : R' ⊗[R] A} (hx : x ∈ chartIdeal R w t) : coordMap ht x = 0 := by
  let K : Ideal (R' ⊗[R] A) :=
    { carrier := {y | ∀ z, coordMap ht (z * y) = 0}
      add_mem' := fun {a b} ha hb z => by simp [mul_add, ha z, hb z]
      zero_mem' := fun z => by simp
      smul_mem' := fun c y hy z => by simpa [smul_eq_mul, mul_assoc] using hy (z * c) }
  have hK : chartIdeal R w t ≤ K := by
    rw [chartIdeal, Ideal.span_le]
    rintro _ ⟨a, rfl⟩ z
    exact coordMap_mul_chartGenerator ht z a
  simpa using hK hx 1

theorem coordMap_basis {t : Fin d → A → R'} (ht : IsChartFunction R w t) (c : Fin d → R') :
    coordMap ht (∑ l, c l ⊗ₜ w l) = c := by
  ext m
  simp only [map_sum, coordMap_tmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ht.map_basis]
  simp

theorem exists_sub_mem_chartIdeal (t : Fin d → A → R') (x : R' ⊗[R] A) :
    ∃ c : Fin d → R', x - ∑ l, c l ⊗ₜ w l ∈ chartIdeal R w t := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r a =>
    refine ⟨fun l => r * t l a, ?_⟩
    have : r ⊗ₜ[R] a - ∑ l, (r * t l a) ⊗ₜ[R] w l = (r ⊗ₜ[R] (1 : A)) * chartGenerator R w t a := by
      simp [chartGenerator, mul_sub, Finset.mul_sum]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, rfl⟩)
  | add x y hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨c', hc'⟩ := hy
    refine ⟨c + c', ?_⟩
    have : x + y - ∑ l, (c + c') l ⊗ₜ[R] w l =
        (x - ∑ l, c l ⊗ₜ[R] w l) + (y - ∑ l, c' l ⊗ₜ[R] w l) := by
      simp only [Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
      abel
    rw [this]
    exact add_mem hc hc'

variable (w) in
/-- The images of `1 ⊗ w l` in the quotient by an ideal. -/
def chartVector (J : Ideal (R' ⊗[R] A)) (l : Fin d) : R' ⊗[R] A ⧸ J :=
  Ideal.Quotient.mk J ((1 : R') ⊗ₜ w l)

theorem sum_smul_chartVector (J : Ideal (R' ⊗[R] A)) (c : Fin d → R') :
    ∑ l, c l • chartVector w J l = Ideal.Quotient.mk J (∑ l, c l ⊗ₜ w l) := by
  simp only [chartVector, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
  congr 1
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, mul_one]

theorem linearIndependent_chartVector {t : Fin d → A → R'} (ht : IsChartFunction R w t) :
    LinearIndependent R' (chartVector w (chartIdeal R w t)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc l
  rw [sum_smul_chartVector, Ideal.Quotient.eq_zero_iff_mem] at hc
  have := coordMap_eq_zero_of_mem ht hc
  rw [coordMap_basis] at this
  exact congrFun this l

theorem span_chartVector (t : Fin d → A → R') :
    Submodule.span R' (Set.range (chartVector w (chartIdeal R w t))) = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨c, hc⟩ := exists_sub_mem_chartIdeal (w := w) t x
  have : Ideal.Quotient.mk (chartIdeal R w t) x =
      ∑ l, c l • chartVector w (chartIdeal R w t) l := by
    rw [sum_smul_chartVector, Ideal.Quotient.eq]
    exact hc
  rw [this]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

/-- **The chart quotient is free with basis `w`.** For a chart function `t`, the images of
`1 ⊗ w l` form an `R'`-basis of `(R' ⊗_R A) / J_t`. -/
def chartBasis {t : Fin d → A → R'} (ht : IsChartFunction R w t) :
    Module.Basis (Fin d) R' (R' ⊗[R] A ⧸ chartIdeal R w t) :=
  Module.Basis.mk (linearIndependent_chartVector ht) (span_chartVector t).ge

@[simp]
theorem chartBasis_apply {t : Fin d → A → R'} (ht : IsChartFunction R w t) (l : Fin d) :
    chartBasis ht l = chartVector w (chartIdeal R w t) l := by
  simp [chartBasis]

/-! ### Coordinates of an algebra map in which `w` maps to a basis -/

variable {B : Type w} [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]

/-- The coordinates of `σ a` in a basis `b` of `B` over `R'`. -/
def coordinates (σ : A →ₐ[R] B) (b : Module.Basis (Fin d) R' B) : Fin d → A → R' :=
  fun l a => b.repr (σ a) l

/-- Expansion of `σ a` in the basis `b`, whose members are the images of `w`. -/
private theorem eq_sum_coordinates_smul {S : Type w} [CommRing S] [Algebra S B] (σ : A →ₐ[R] B)
    (b : Module.Basis (Fin d) S B)
    (hb : ∀ l, b l = σ (w l)) (a : A) : σ a = ∑ m, coordinates σ b m a • σ (w m) := by
  conv_lhs => rw [← b.sum_repr (σ a)]
  simp [coordinates, hb]

/-- **Coordinates of an algebra map form a chart function.** If the images of `w` under an
`R`-algebra map `σ : A → B` form an `R'`-basis `b` of the `R'`-algebra `B`, the coordinates of
`σ` in that basis are a chart function. -/
theorem isChartFunction_coordinates (σ : A →ₐ[R] B) (b : Module.Basis (Fin d) R' B)
    (hb : ∀ l, b l = σ (w l)) : IsChartFunction R w (coordinates σ b) := by
  refine ⟨fun l a c => by simp [coordinates], fun l r a => ?_, fun l m => ?_, fun l a c => ?_⟩
  · simp only [coordinates, map_smul]
    rw [← IsScalarTower.algebraMap_smul R' r (σ a), map_smul]
    simp [Algebra.smul_def]
  · simp only [coordinates, ← hb, Module.Basis.repr_self]
    by_cases h : l = m
    · subst h; simp
    · simp [h]
  · show b.repr (σ (a * c)) l = _
    conv_lhs => rw [map_mul, eq_sum_coordinates_smul σ b hb c, Finset.mul_sum]
    simp only [mul_smul_comm, ← map_mul, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    rfl

/-- The `R'`-algebra map `R' ⊗_R A → B` induced by an `R`-algebra map `σ : A → B`. -/
def tensorLift (σ : A →ₐ[R] B) : R' ⊗[R] A →ₐ[R'] B :=
  Algebra.TensorProduct.lift (Algebra.ofId R' B) σ fun _ _ => Commute.all _ _

@[simp]
theorem tensorLift_tmul (σ : A →ₐ[R] B) (r : R') (a : A) :
    tensorLift σ (r ⊗ₜ a) = r • σ a := by
  simp [tensorLift, Algebra.smul_def]

/-- **The kernel of `R' ⊗_R A → B` is the chart ideal of the coordinates.** -/
theorem ker_tensorLift_eq_chartIdeal (σ : A →ₐ[R] B) (b : Module.Basis (Fin d) R' B)
    (hb : ∀ l, b l = σ (w l)) :
    RingHom.ker (tensorLift (R' := R') σ) = chartIdeal R w (coordinates σ b) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc⟩ := exists_sub_mem_chartIdeal (w := w) (coordinates σ b) x
    have h0 : tensorLift σ (∑ l, c l ⊗ₜ w l) = 0 := by
      have h1 : tensorLift σ (x - ∑ l, c l ⊗ₜ w l) = 0 := by
        refine (RingHom.mem_ker).mp ?_
        refine (Ideal.span_le.mpr ?_) hc
        rintro _ ⟨a, rfl⟩
        simp [chartGenerator, ← eq_sum_coordinates_smul σ b hb a]
      rw [map_sub, (RingHom.mem_ker).mp hx, zero_sub, neg_eq_zero] at h1
      exact h1
    have hc0 : c = 0 := by
      simp only [map_sum, tensorLift_tmul, ← hb] at h0
      have := Fintype.linearIndependent_iff.mp b.linearIndependent c h0
      exact funext this
    simpa [hc0] using hc
  · rw [chartIdeal, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simp [chartGenerator, ← eq_sum_coordinates_smul σ b hb a]

/-! ### Base change -/

/-- Formation of the chart ideal commutes with base change of the coefficient ring. -/
theorem chartIdeal_comp {R'' : Type*} [CommRing R''] [Algebra R R''] (f : R' →ₐ[R] R'')
    (t : Fin d → A → R') :
    chartIdeal R w (fun l a => f (t l a)) =
      Ideal.map (Algebra.TensorProduct.map f (AlgHom.id R A)) (chartIdeal R w t) := by
  rw [chartIdeal, chartIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext a
  simp [chartGenerator]

end Ideal

/-! ### Quotients of `R' ⊗_R A` in which `w` maps to a basis, without module structures -/

section Surjection

variable {R' : Type w} [CommRing R'] [Algebra R R'] {B : Type*} [CommRing B]

variable (w) in
/-- The map `R'^d → B`, `c ↦ ψ (∑ l, c l ⊗ w l)`. -/
def chartSum (ψ : R' ⊗[R] A →+* B) (c : Fin d → R') : B := ψ (∑ l, c l ⊗ₜ w l)

theorem chartSum_add (ψ : R' ⊗[R] A →+* B) (c c' : Fin d → R') :
    chartSum w ψ (c + c') = chartSum w ψ c + chartSum w ψ c' := by
  simp [chartSum, TensorProduct.add_tmul, Finset.sum_add_distrib]

theorem chartSum_zero (ψ : R' ⊗[R] A →+* B) : chartSum w ψ 0 = 0 := by
  simp [chartSum]

theorem chartSum_smul (ψ : R' ⊗[R] A →+* B) (r : R') (c : Fin d → R') :
    chartSum w ψ (r • c) = ψ (r ⊗ₜ 1) * chartSum w ψ c := by
  simp only [chartSum, Finset.mul_sum, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    Pi.smul_apply, smul_eq_mul, map_sum]

theorem chartSum_single (ψ : R' ⊗[R] A →+* B) (m : Fin d) :
    chartSum w ψ (fun l => if l = m then 1 else 0) = ψ (1 ⊗ₜ w m) := by
  simp only [chartSum]
  congr 1
  rw [Finset.sum_eq_single m (fun l _ hl => by simp [hl]) (by simp)]
  simp

theorem chartSum_sub (ψ : R' ⊗[R] A →+* B) (c c' : Fin d → R') :
    chartSum w ψ (c - c') = chartSum w ψ c - chartSum w ψ c' := by
  simp [chartSum, TensorProduct.sub_tmul, Finset.sum_sub_distrib]

/-- **A quotient by a chart ideal has `w` as a basis**, in the form of bijectivity of
`chartSum`. -/
theorem bijective_chartSum_of_ker {t : Fin d → A → R'} (ht : IsChartFunction R w t)
    (ψ : R' ⊗[R] A →+* B) (hψ : Function.Surjective ψ) (hker : RingHom.ker ψ = chartIdeal R w t) :
    Function.Bijective (chartSum w ψ) := by
  constructor
  · intro c c' h
    have h0 : ψ (∑ l, (c - c') l ⊗ₜ w l) = 0 := by
      have := chartSum_sub (w := w) ψ c c'
      rw [h, sub_self] at this
      exact this
    have hmem : ∑ l, (c - c') l ⊗ₜ[R] w l ∈ chartIdeal R w t := by
      rw [← hker]
      exact h0
    have := coordMap_eq_zero_of_mem ht hmem
    rw [coordMap_basis] at this
    exact sub_eq_zero.mp this
  · intro b
    obtain ⟨x, rfl⟩ := hψ b
    obtain ⟨c, hc⟩ := exists_sub_mem_chartIdeal (w := w) t x
    refine ⟨c, ?_⟩
    have : ψ (x - ∑ l, c l ⊗ₜ w l) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact hc
    rw [map_sub, sub_eq_zero] at this
    exact this.symm

variable (w) in
/-- The coordinates of the images of `1 ⊗ a` when `chartSum` is bijective. -/
def chartCoords (ψ : R' ⊗[R] A →+* B) (hb : Function.Bijective (chartSum w ψ)) :
    Fin d → A → R' :=
  fun l a => (Equiv.ofBijective _ hb).symm (ψ (1 ⊗ₜ a)) l

theorem chartSum_chartCoords (ψ : R' ⊗[R] A →+* B) (hb : Function.Bijective (chartSum w ψ))
    (a : A) : chartSum w ψ (fun l => chartCoords w ψ hb l a) = ψ (1 ⊗ₜ a) :=
  (Equiv.ofBijective _ hb).apply_symm_apply _

theorem isChartFunction_chartCoords (ψ : R' ⊗[R] A →+* B)
    (hb : Function.Bijective (chartSum w ψ)) : IsChartFunction R w (chartCoords w ψ hb) := by
  have key : ∀ a c, chartSum w ψ c = ψ (1 ⊗ₜ a) → (fun l => chartCoords w ψ hb l a) = c :=
    fun a c h => hb.1 ((chartSum_chartCoords ψ hb a).trans h.symm)
  refine ⟨fun l a b => ?_, fun l r a => ?_, fun l m => ?_, fun l a b => ?_⟩
  · have := key (a + b) ((fun l => chartCoords w ψ hb l a) + fun l => chartCoords w ψ hb l b)
      (by rw [chartSum_add, chartSum_chartCoords, chartSum_chartCoords, ← map_add,
        TensorProduct.tmul_add])
    exact congrFun this l
  · have := key (r • a) (algebraMap R R' r • fun l => chartCoords w ψ hb l a) (by
      rw [chartSum_smul, chartSum_chartCoords, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        mul_one])
    exact congrFun this l
  · have := key (w m) (fun l => if l = m then 1 else 0) (chartSum_single ψ m)
    exact congrFun this l
  · have h1 : ψ (1 ⊗ₜ (a * b)) = ∑ m, ψ (chartCoords w ψ hb m b ⊗ₜ 1) * ψ (1 ⊗ₜ (a * w m)) := by
      rw [← mul_one (1 : R'), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul,
        ← chartSum_chartCoords ψ hb b, chartSum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, one_mul, mul_one]
    have := key (a * b) (∑ m, chartCoords w ψ hb m b • fun l => chartCoords w ψ hb l (a * w m))
      (by
        rw [h1]
        induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
        | empty => simp [chartSum_zero]
        | insert m s hm ih =>
          rw [Finset.sum_insert hm, Finset.sum_insert hm, chartSum_add, ih, chartSum_smul,
            chartSum_chartCoords])
    have := congrFun this l
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

theorem ker_eq_chartIdeal_chartCoords (ψ : R' ⊗[R] A →+* B)
    (hb : Function.Bijective (chartSum w ψ)) :
    RingHom.ker ψ = chartIdeal R w (chartCoords w ψ hb) := by
  have hle : chartIdeal R w (chartCoords w ψ hb) ≤ RingHom.ker ψ := by
    rw [chartIdeal, Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    show ψ (chartGenerator R w _ a) = 0
    rw [chartGenerator, map_sub, ← chartSum_chartCoords ψ hb a, chartSum, sub_self]
  refine le_antisymm (fun x hx => ?_) hle
  obtain ⟨c, hc⟩ := exists_sub_mem_chartIdeal (w := w) (chartCoords w ψ hb) x
  have h1 : ψ (x - ∑ l, c l ⊗ₜ w l) = 0 := hle hc
  rw [map_sub, RingHom.mem_ker.mp hx, zero_sub, neg_eq_zero] at h1
  have hc0 : c = 0 := hb.1 (h1.trans (chartSum_zero ψ).symm)
  simpa [hc0] using hc

theorem chartCoords_eq {t : Fin d → A → R'} (ψ : R' ⊗[R] A →+* B)
    (hb : Function.Bijective (chartSum w ψ)) (hker : RingHom.ker ψ = chartIdeal R w t) :
    chartCoords w ψ hb = t := by
  funext l a
  have : chartSum w ψ (fun l => t l a) = ψ (1 ⊗ₜ a) := by
    have hg : ψ (chartGenerator R w t a) = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact Ideal.subset_span ⟨a, rfl⟩
    rw [chartGenerator, map_sub, sub_eq_zero] at hg
    exact hg.symm
  exact congrFun (hb.1 ((chartSum_chartCoords ψ hb a).trans this.symm)) l

/-- A chart ideal determines its chart function. -/
theorem eq_of_chartIdeal_eq {t t' : Fin d → A → R'} (ht : IsChartFunction R w t)
    (h : chartIdeal R w t = chartIdeal R w t') : t = t' := by
  have hb := bijective_chartSum_of_ker ht (Ideal.Quotient.mk (chartIdeal R w t))
    Ideal.Quotient.mk_surjective (Ideal.mk_ker)
  rw [← chartCoords_eq _ hb Ideal.mk_ker, chartCoords_eq _ hb (Ideal.mk_ker.trans h)]

end Surjection

end Stacks.Hilbert.Chart

end
