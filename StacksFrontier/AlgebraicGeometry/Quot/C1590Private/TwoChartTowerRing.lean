module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartDatumThickening
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.TwoChartTowerSplitting
public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# The graded ring of a tower with a compatible two-chart datum

Let `⋯ → R₁ → R₀` be a tower of rings, `Xₙ ⟶ Spec Rₙ` schemes with maps `Xₙ ⟶ Xₙ₊₁` over the
transition maps, and `Dₙ` two-chart data on the `Xₙ` restricting to one another: a line bundle
`Lₙ` with sections `s, t` and `Xₙ = (Xₙ)_s ∪ (Xₙ)_t`, compatibly in `n`
(`AlgebraicGeometry.C1590Private.TwoChartTower.CompatibleCharts`). This file builds the graded
ring `S = ⨁_k lim_n Γ(Xₙ, Lₙ^{⊗ k})` of compatible sections and the ring maps from its
homogeneous localizations `S_(s)`, `S_(t)`, `S_(st)` to the rings of sections of the charts of
the `Xₙ`.

A section of `Lₙ^{⊗ k}` is read in the trivializations by `s^k` and `t^k` as a pair of functions
on the two charts (`AlgebraicGeometry.C1590Private.TwoChartDatum.sections`), so a compatible
system of sections is an element of the product over `n` of the products of the two rings of
sections, and `S` is the external direct sum of these groups.

## Main definitions

* `…TwoChartTower.CompatibleCharts`: the compatible two-chart data.
* `…CompatibleCharts.grade`: the compatible systems of sections of `L^{⊗ k}`.
* `…CompatibleCharts.ring`: the graded ring `S`; `…CompatibleCharts.sElt`, `…tElt` the sections
  `s`, `t` in degree one.
* `…CompatibleCharts.evalU`, `…evalV`, `…evalUV`: the maps from `S_(s)`, `S_(t)`, `S_(st)` to
  the rings of sections of `(Xₙ)_s`, `(Xₙ)_t` and `(Xₙ)_{st}`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Deformation.Artin.SquareZeroTower HomogeneousLocalization

universe u

namespace AlgebraicGeometry.C1590Private.TwoChartTower

/-! ### Formulas for the Čech differential -/

section Cech

variable {X : Scheme.{u}} (D : TwoChartDatum X)

/-- A pair `(f, g)` is killed by the Čech differential in degree `k` if and only if `f = b^k g`
on `U ∩ V`. -/
theorem cechDiff_eq_zero_iff (k : ℕ) (q : Γ(X, D.U) × Γ(X, D.V)) :
    D.cechDiff k q = 0 ↔ D.resU q.1 = D.resU D.b ^ k * D.resV q.2 := by
  rw [TwoChartDatum.cechDiff_apply, sub_eq_zero]

/-- The product of a pair killed by the Čech differential in degree `i` and one killed by it in
degree `j` is killed by it in degree `i + j`. -/
theorem cechDiff_mul_eq_zero {i j : ℕ} {p q : Γ(X, D.U) × Γ(X, D.V)} (hp : D.cechDiff i p = 0)
    (hq : D.cechDiff j q = 0) : D.cechDiff (i + j) (p * q) = 0 := by
  rw [cechDiff_eq_zero_iff] at hp hq ⊢
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, hp, hq, pow_add]
  ring

/-- On `U ∩ V`, `b · a = 1`. -/
theorem resU_b_mul_resV_a : D.resU D.b * D.resV D.a = 1 := D.mul_eq_one

/-- The function `b` is a unit on `U ∩ V`. -/
theorem isUnit_resU_b : IsUnit (D.resU D.b) :=
  IsUnit.of_mul_eq_one _ (resU_b_mul_resV_a D)

end Cech

/-! ### Lifting out of a localization away from an element -/

section LiftAway

variable {A T : Type*} [CommRing A] [CommRing T] (x : A) (g : A →+* T) (hg : IsUnit (g x))

/-- `lift (a / x^k) · g(x)^k = g(a)`. -/
theorem lift_mk_mul (a : A) (k : ℕ) :
    IsLocalization.Away.lift x hg
      (Localization.mk a (⟨x ^ k, k, rfl⟩ : Submonoid.powers x) : Localization.Away x) *
        g x ^ k = g a := by
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, ← map_pow, mul_comm]
  exact ((IsLocalization.lift_mk'_spec (M := Submonoid.powers x) (S := Localization.Away x)
    (g := g) _ a _ ⟨x ^ k, k, rfl⟩).mp rfl).symm

/-- `lift (a / 1) = g(a)`. -/
theorem lift_mk_one (a : A) :
    IsLocalization.Away.lift x hg (Localization.mk a 1 : Localization.Away x) = g a := by
  rw [Localization.mk_one_eq_algebraMap]
  exact IsLocalization.lift_eq _ _

end LiftAway

/-! ### Compatible two-chart data along a tower -/

section Setup

variable {X : ℕ → Scheme.{u}} (ι : ∀ n, X n ⟶ X (n + 1))

/-- **Two-chart data along a tower of schemes**, each restricting to the previous one along the
maps `ιₙ : Xₙ ⟶ Xₙ₊₁`: same opens, and the functions `b = t/s`, `a = s/t` restrict. -/
structure CompatibleCharts where
  /-- The datum on `Xₙ`. -/
  D : ∀ n, TwoChartDatum (X n)
  /-- `ιₙ⁻¹(Uₙ₊₁) = Uₙ`. -/
  preimage_U : ∀ n, ι n ⁻¹ᵁ (D (n + 1)).U = (D n).U
  /-- `ιₙ⁻¹(Vₙ₊₁) = Vₙ`. -/
  preimage_V : ∀ n, ι n ⁻¹ᵁ (D (n + 1)).V = (D n).V
  /-- `bₙ₊₁` restricts to `bₙ`. -/
  b_eq : ∀ n, (ι n).appLE _ _ (preimage_U n).ge (D (n + 1)).b = (D n).b
  /-- `aₙ₊₁` restricts to `aₙ`. -/
  a_eq : ∀ n, (ι n).appLE _ _ (preimage_V n).ge (D (n + 1)).a = (D n).a

namespace CompatibleCharts

variable {ι} (C : CompatibleCharts ι)

/-- Restriction `Γ(Xₙ₊₁, Uₙ₊₁) → Γ(Xₙ, Uₙ)`. -/
def ρU (n : ℕ) : Γ(X (n + 1), (C.D (n + 1)).U) →+* Γ(X n, (C.D n).U) :=
  ((ι n).appLE _ _ (C.preimage_U n).ge).hom

/-- Restriction `Γ(Xₙ₊₁, Vₙ₊₁) → Γ(Xₙ, Vₙ)`. -/
def ρV (n : ℕ) : Γ(X (n + 1), (C.D (n + 1)).V) →+* Γ(X n, (C.D n).V) :=
  ((ι n).appLE _ _ (C.preimage_V n).ge).hom

/-- `Uₙ ∩ Vₙ` lies in the preimage of `Uₙ₊₁ ∩ Vₙ₊₁` under `ιₙ`. -/
theorem inf_le_preimage (n : ℕ) :
    (C.D n).U ⊓ (C.D n).V ≤ ι n ⁻¹ᵁ ((C.D (n + 1)).U ⊓ (C.D (n + 1)).V) :=
  fun _ hx => ⟨(C.preimage_U n).ge hx.1, (C.preimage_V n).ge hx.2⟩

/-- Restriction `Γ(Xₙ₊₁, Uₙ₊₁ ∩ Vₙ₊₁) → Γ(Xₙ, Uₙ ∩ Vₙ)`. -/
def ρUV (n : ℕ) :
    Γ(X (n + 1), (C.D (n + 1)).U ⊓ (C.D (n + 1)).V) →+* Γ(X n, (C.D n).U ⊓ (C.D n).V) :=
  ((ι n).appLE _ _ (C.inf_le_preimage n)).hom

/-- Restricting from `Uₙ₊₁` to `Uₙ₊₁ ∩ Vₙ₊₁` commutes with restriction along `ιₙ`. -/
theorem ρUV_resU (n : ℕ) (x : Γ(X (n + 1), (C.D (n + 1)).U)) :
    C.ρUV n ((C.D (n + 1)).resU x) = (C.D n).resU (C.ρU n x) := by
  simp only [ρUV, ρU, TwoChartDatum.resU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

/-- Restricting from `Vₙ₊₁` to `Uₙ₊₁ ∩ Vₙ₊₁` commutes with restriction along `ιₙ`. -/
theorem ρUV_resV (n : ℕ) (y : Γ(X (n + 1), (C.D (n + 1)).V)) :
    C.ρUV n ((C.D (n + 1)).resV y) = (C.D n).resV (C.ρV n y) := by
  simp only [ρUV, ρV, TwoChartDatum.resV, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map,
    Scheme.Hom.map_appLE]

/-- `ρU` maps `bₙ₊₁` to `bₙ`. -/
theorem ρU_b (n : ℕ) : C.ρU n (C.D (n + 1)).b = (C.D n).b := C.b_eq n

/-- `ρV` maps `aₙ₊₁` to `aₙ`. -/
theorem ρV_a (n : ℕ) : C.ρV n (C.D (n + 1)).a = (C.D n).a := C.a_eq n

/-- The Čech differentials commute with restriction along the tower. -/
theorem ρUV_cechDiff (n k : ℕ)
    (q : Γ(X (n + 1), (C.D (n + 1)).U) × Γ(X (n + 1), (C.D (n + 1)).V)) :
    C.ρUV n ((C.D (n + 1)).cechDiff k q) = (C.D n).cechDiff k (C.ρU n q.1, C.ρV n q.2) := by
  rw [TwoChartDatum.cechDiff_apply, TwoChartDatum.cechDiff_apply, map_sub, map_mul, map_pow,
    C.ρUV_resU, C.ρUV_resU, C.ρUV_resV, C.ρU_b]

/-! ### The ambient ring and the graded pieces -/

/-- The product over `n` of the products of the rings of sections of the two charts. -/
def Amb : Type u := ∀ n, Γ(X n, (C.D n).U) × Γ(X n, (C.D n).V)

/-- The pointwise ring structure on `C.Amb`. -/
instance : CommRing C.Amb :=
  inferInstanceAs (CommRing (∀ n, Γ(X n, (C.D n).U) × Γ(X n, (C.D n).V)))

/-- Addition in `C.Amb` is levelwise. -/
@[simp] theorem Amb.add_apply (c c' : C.Amb) (n : ℕ) : (c + c') n = c n + c' n := rfl
/-- Multiplication in `C.Amb` is levelwise. -/
@[simp] theorem Amb.mul_apply (c c' : C.Amb) (n : ℕ) : (c * c') n = c n * c' n := rfl
/-- Negation in `C.Amb` is levelwise. -/
@[simp] theorem Amb.neg_apply (c : C.Amb) (n : ℕ) : (-c) n = -c n := rfl
/-- Subtraction in `C.Amb` is levelwise. -/
@[simp] theorem Amb.sub_apply (c c' : C.Amb) (n : ℕ) : (c - c') n = c n - c' n := rfl
/-- The zero of `C.Amb` is zero at every level. -/
@[simp] theorem Amb.zero_apply (n : ℕ) : (0 : C.Amb) n = 0 := rfl
/-- The unit of `C.Amb` is one at every level. -/
@[simp] theorem Amb.one_apply (n : ℕ) : (1 : C.Amb) n = 1 := rfl
/-- Powers in `C.Amb` are levelwise. -/
@[simp] theorem Amb.pow_apply (c : C.Amb) (m n : ℕ) : (c ^ m) n = c n ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [pow_succ, Amb.mul_apply, ih, pow_succ]
/-- Finite sums in `C.Amb` are levelwise. -/
@[simp] theorem Amb.sum_apply {ι : Type*} (s : Finset ι) (c : ι → C.Amb) (n : ℕ) :
    (∑ i ∈ s, c i) n = ∑ i ∈ s, c i n := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Amb.add_apply, ih, Finset.sum_insert ha]

/-- A family over the levels as an element of the ambient ring. -/
def Amb.mk (c : ∀ n, Γ(X n, (C.D n).U) × Γ(X n, (C.D n).V)) : C.Amb := c

/-- The `n`-th component of `Amb.mk C c` is `c n`. -/
@[simp] theorem Amb.mk_apply (c : ∀ n, Γ(X n, (C.D n).U) × Γ(X n, (C.D n).V)) (n : ℕ) :
    Amb.mk C c n = c n := rfl

/-- A family is compatible if it restricts along the tower. -/
def IsCompat (c : C.Amb) : Prop :=
  ∀ n, C.ρU n (c (n + 1)).1 = (c n).1 ∧ C.ρV n (c (n + 1)).2 = (c n).2

/-- **The compatible systems of sections of `L^{⊗ k}`.** -/
def grade (k : ℕ) : AddSubgroup C.Amb where
  carrier := {c | C.IsCompat c ∧ ∀ n, (C.D n).cechDiff k (c n) = 0}
  add_mem' := by
    rintro c c' ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨fun n => ⟨?_, ?_⟩, fun n => ?_⟩
    · simp only [Amb.add_apply, Prod.fst_add, map_add, (hc n).1, (hd n).1]
    · simp only [Amb.add_apply, Prod.snd_add, map_add, (hc n).2, (hd n).2]
    · simp only [Amb.add_apply, map_add, hc' n, hd' n, add_zero]
  zero_mem' := ⟨fun n => ⟨map_zero (C.ρU n), map_zero (C.ρV n)⟩, fun n => map_zero _⟩
  neg_mem' := by
    rintro c ⟨hc, hc'⟩
    refine ⟨fun n => ⟨?_, ?_⟩, fun n => ?_⟩
    · simp only [Amb.neg_apply, Prod.fst_neg, map_neg, (hc n).1]
    · simp only [Amb.neg_apply, Prod.snd_neg, map_neg, (hc n).2]
    · simp only [Amb.neg_apply, map_neg, hc' n, neg_zero]

/-- A family lies in `C.grade k` if and only if it is compatible and killed at every level by
the Čech differential in degree `k`. -/
theorem mem_grade {k : ℕ} {c : C.Amb} :
    c ∈ C.grade k ↔ C.IsCompat c ∧ ∀ n, (C.D n).cechDiff k (c n) = 0 := Iff.rfl

/-- The pieces `C.grade k` form a graded monoid in `C.Amb`. -/
instance gradedMonoid : SetLike.GradedMonoid C.grade where
  one_mem := ⟨fun n => ⟨map_one (C.ρU n), map_one (C.ρV n)⟩, fun n => by
    rw [cechDiff_eq_zero_iff]; simp⟩
  mul_mem := by
    rintro i j c c' ⟨hc, hc'⟩ ⟨hd, hd'⟩
    refine ⟨fun n => ⟨?_, ?_⟩, fun n => cechDiff_mul_eq_zero _ (hc' n) (hd' n)⟩
    · simp only [Amb.mul_apply, Prod.fst_mul, map_mul, (hc n).1, (hd n).1]
    · simp only [Amb.mul_apply, Prod.snd_mul, map_mul, (hc n).2, (hd n).2]

/-- **The graded ring `⨁_k lim_n Γ(Xₙ, Lₙ^{⊗ k})`.** -/
abbrev ring : Type u := DirectSum ℕ fun k => C.grade k

/-- The grading of `C.ring` by its summands. -/
abbrev 𝒜 : ℕ → AddSubgroup C.ring := Stacks.ExternalGrading.summand fun k => C.grade k

/-- The family `s = (1, a)`. -/
def sAmb : C.Amb := Amb.mk C fun n => (1, (C.D n).a)

/-- The family `t = (b, 1)`. -/
def tAmb : C.Amb := Amb.mk C fun n => ((C.D n).b, 1)

/-- The family `s` lies in degree one. -/
theorem sAmb_mem : C.sAmb ∈ C.grade 1 := by
  refine ⟨fun n => ⟨map_one (C.ρU n), C.ρV_a n⟩, fun n => ?_⟩
  rw [cechDiff_eq_zero_iff]
  simp [sAmb, resU_b_mul_resV_a (C.D n)]

/-- The family `t` lies in degree one. -/
theorem tAmb_mem : C.tAmb ∈ C.grade 1 := by
  refine ⟨fun n => ⟨C.ρU_b n, map_one (C.ρV n)⟩, fun n => ?_⟩
  rw [cechDiff_eq_zero_iff]
  simp [tAmb]

/-- The degree-one element of `S` defined by a compatible family `w` of sections of `L`. -/
def xElt {w : C.Amb} (hw : w ∈ C.grade 1) : C.ring := DirectSum.of (fun k => C.grade k) 1 ⟨w, hw⟩

/-- The element `C.xElt hw` is homogeneous of degree one. -/
theorem xElt_mem {w : C.Amb} (hw : w ∈ C.grade 1) : C.xElt hw ∈ C.𝒜 1 :=
  Stacks.ExternalGrading.of_mem_summand _ _

/-- **The section `s` of `L`, in degree one.** -/
abbrev sElt : C.ring := C.xElt C.sAmb_mem

/-- **The section `t` of `L`, in degree one.** -/
abbrev tElt : C.ring := C.xElt C.tAmb_mem

/-- The section `s` is homogeneous of degree one. -/
theorem sElt_mem : C.sElt ∈ C.𝒜 1 := C.xElt_mem _

/-- The section `t` is homogeneous of degree one. -/
theorem tElt_mem : C.tElt ∈ C.𝒜 1 := C.xElt_mem _

/-! ### Evaluation at a level -/

/-- The `n`-th component of a family in degree `k`. -/
def evalComp (n k : ℕ) : C.grade k →+ Γ(X n, (C.D n).U) × Γ(X n, (C.D n).V) where
  toFun c := (c : C.Amb) n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- **Evaluation at level `n`**: `S → Γ(Xₙ, Uₙ) × Γ(Xₙ, Vₙ)`, the `n`-th component in every
degree. -/
def evalAt (n : ℕ) : C.ring →+* Γ(X n, (C.D n).U) × Γ(X n, (C.D n).V) :=
  DirectSum.toSemiring (fun k => C.evalComp n k) (show (1 : C.Amb) n = 1 from rfl)
    (fun _ _ => show ((_ : C.Amb) * _) n = _ from rfl)

/-- Evaluation at level `n` of an element of degree `k` is its `n`-th component. -/
@[simp] theorem evalAt_of (n k : ℕ) (c : C.grade k) :
    C.evalAt n (DirectSum.of (fun k => C.grade k) k c) = (c : C.Amb) n :=
  DirectSum.toSemiring_of _ _ _ _ _

/-- The section `s` evaluates at level `n` to `(1, aₙ)`. -/
theorem evalAt_sElt (n : ℕ) : C.evalAt n C.sElt = (1, (C.D n).a) := C.evalAt_of n 1 _

/-- The section `t` evaluates at level `n` to `(bₙ, 1)`. -/
theorem evalAt_tElt (n : ℕ) : C.evalAt n C.tElt = ((C.D n).b, 1) := C.evalAt_of n 1 _

/-- The `U`-coordinate of evaluation, inverting `s`. -/
def evalU (n : ℕ) : Away C.𝒜 C.sElt →+* Γ(X n, (C.D n).U) :=
  (IsLocalization.Away.lift C.sElt (g := (RingHom.fst _ _).comp (C.evalAt n))
      (by simp [C.evalAt_sElt])).comp
    (algebraMap (Away C.𝒜 C.sElt) (Localization.Away C.sElt))

/-- The `V`-coordinate of evaluation, inverting `t`. -/
def evalV (n : ℕ) : Away C.𝒜 C.tElt →+* Γ(X n, (C.D n).V) :=
  (IsLocalization.Away.lift C.tElt (g := (RingHom.snd _ _).comp (C.evalAt n))
      (by simp [C.evalAt_tElt])).comp
    (algebraMap (Away C.𝒜 C.tElt) (Localization.Away C.tElt))

/-- Evaluation on `U ∩ V`, read in the trivialization by `s`, inverting `st`. -/
def evalUV (n : ℕ) : Away C.𝒜 (C.sElt * C.tElt) →+* Γ(X n, (C.D n).U ⊓ (C.D n).V) :=
  (IsLocalization.Away.lift (C.sElt * C.tElt)
      (g := (C.D n).resU.comp ((RingHom.fst _ _).comp (C.evalAt n)))
      (by simpa [C.evalAt_sElt, C.evalAt_tElt] using isUnit_resU_b (C.D n))).comp
    (algebraMap (Away C.𝒜 (C.sElt * C.tElt)) (Localization.Away (C.sElt * C.tElt)))

/-- `C.evalU n` sends `a / s^k` to the `U`-coordinate of `a` at level `n`. -/
theorem evalU_mk (n k : ℕ) (a : C.ring) (ha : a ∈ C.𝒜 (k • 1)) :
    C.evalU n (Away.mk C.𝒜 C.sElt_mem k a ha) = (C.evalAt n a).1 := by
  have h := lift_mk_mul C.sElt ((RingHom.fst _ _).comp (C.evalAt n))
    (by simp [C.evalAt_sElt]) a k
  simpa [evalU, C.evalAt_sElt] using h

/-- `C.evalV n` sends `a / t^k` to the `V`-coordinate of `a` at level `n`. -/
theorem evalV_mk (n k : ℕ) (a : C.ring) (ha : a ∈ C.𝒜 (k • 1)) :
    C.evalV n (Away.mk C.𝒜 C.tElt_mem k a ha) = (C.evalAt n a).2 := by
  have h := lift_mk_mul C.tElt ((RingHom.snd _ _).comp (C.evalAt n))
    (by simp [C.evalAt_tElt]) a k
  simpa [evalV, C.evalAt_tElt] using h

end CompatibleCharts

end Setup

/-! ### The projections of the limit ring are surjective -/

section LimitSurjective

/-- With surjective transition maps, every projection `lim Rₙ → Rₙ` is surjective. -/
theorem towerLimitProj_surjective {R : ℕ → Type u} [∀ n, CommRing (R n)]
    (f : ∀ n, R (n + 1) →+* R n) (hf : ∀ n, Function.Surjective (f n)) (n : ℕ) :
    Function.Surjective (towerLimitProj f n) := by
  induction n generalizing R with
  | zero =>
    intro x
    choose u hu using fun (k : ℕ) (z : R k) => hf k z
    exact ⟨⟨fun k => Nat.rec (motive := fun k => R k) x (fun k z => u k z) k,
      fun k => hu k _⟩, rfl⟩
  | succ n ih =>
    intro x
    obtain ⟨a, ha⟩ := ih (R := fun k => R (k + 1)) (fun k => f (k + 1)) (fun k => hf (k + 1)) x
    refine ⟨⟨fun m => Nat.rec (motive := fun m => R m) (f 0 (a.1 0)) (fun m _ => a.1 m) m, ?_⟩, ha⟩
    intro m
    cases m with
    | zero => rfl
    | succ m => exact a.2 m

end LimitSurjective

/-! ### The base rings -/

section Base

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {X : ℕ → Scheme.{u}} (π : ∀ n, X n ⟶ Spec (.of (R n))) {ι : ∀ n, X n ⟶ X (n + 1)}

namespace CompatibleCharts

variable (C : CompatibleCharts ι)

/-- Two families agreeing at every level are equal. -/
theorem Amb.ext {c c' : C.Amb} (h : ∀ n, c n = c' n) : c = c' := funext h

/-- **The structure map `lim Rₙ → ∏ₙ Γ(Xₙ, Uₙ) × Γ(Xₙ, Vₙ)`.** -/
def κ : limit f →+* C.Amb where
  toFun r := Amb.mk C fun n =>
    (TwoChartDatum.baseOfSpecOn (π n) (C.D n).U (r.1 n),
      TwoChartDatum.baseOfSpecOn (π n) (C.D n).V (r.1 n))
  map_one' := Amb.ext C fun n => by simp
  map_mul' _ _ := Amb.ext C fun n => by simp
  map_zero' := Amb.ext C fun n => by simp
  map_add' _ _ := Amb.ext C fun n => by simp

/-- The value of `C.κ π r` at level `n` is the pair of images of `rₙ` in the two charts. -/
@[simp] theorem κ_apply (r : limit f) (n : ℕ) :
    C.κ π r n = (TwoChartDatum.baseOfSpecOn (π n) (C.D n).U (r.1 n),
      TwoChartDatum.baseOfSpecOn (π n) (C.D n).V (r.1 n)) := rfl

variable {π}

/-- When the squares of the tower are pullbacks, restricting the image of `r ∈ Rₙ₊₁` in
`Γ(Xₙ₊₁, Uₙ₊₁)` gives the image of `fₙ r` in `Γ(Xₙ, Uₙ)`. -/
theorem ρU_baseOfSpecOn
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    (n : ℕ) (r : R (n + 1)) :
    C.ρU n (TwoChartDatum.baseOfSpecOn (π (n + 1)) (C.D (n + 1)).U r) =
      TwoChartDatum.baseOfSpecOn (π n) (C.D n).U (f n r) :=
  congrArg (fun φ : R (n + 1) →+* _ => φ r)
    (appLE_comp_baseOfSpecOn (hpb n) (W' := (C.D (n + 1)).U) (C.preimage_U n).ge)

/-- When the squares of the tower are pullbacks, restricting the image of `r ∈ Rₙ₊₁` in
`Γ(Xₙ₊₁, Vₙ₊₁)` gives the image of `fₙ r` in `Γ(Xₙ, Vₙ)`. -/
theorem ρV_baseOfSpecOn
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    (n : ℕ) (r : R (n + 1)) :
    C.ρV n (TwoChartDatum.baseOfSpecOn (π (n + 1)) (C.D (n + 1)).V r) =
      TwoChartDatum.baseOfSpecOn (π n) (C.D n).V (f n r) :=
  congrArg (fun φ : R (n + 1) →+* _ => φ r)
    (appLE_comp_baseOfSpecOn (hpb n) (W' := (C.D (n + 1)).V) (C.preimage_V n).ge)

/-- The images of `r ∈ Rₙ` in `Γ(Xₙ, Uₙ)` and in `Γ(Xₙ, Vₙ)` agree on `Uₙ ∩ Vₙ`. -/
theorem resU_baseOfSpecOn (n : ℕ) (r : R n) :
    (C.D n).resU (TwoChartDatum.baseOfSpecOn (π n) (C.D n).U r) =
      (C.D n).resV (TwoChartDatum.baseOfSpecOn (π n) (C.D n).V r) :=
  ((C.D n).resU_res_top _).trans ((C.D n).resV_res_top _).symm

/-- When the squares of the tower are pullbacks, `C.κ π` takes values in degree zero. -/
theorem κ_mem
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    (r : limit f) : C.κ π r ∈ C.grade 0 := by
  refine ⟨fun n => ⟨?_, ?_⟩, fun n => ?_⟩
  · simp only [κ_apply, C.ρU_baseOfSpecOn hpb, (mem_limit f).mp r.2 n]
  · simp only [κ_apply, C.ρV_baseOfSpecOn hpb, (mem_limit f).mp r.2 n]
  · rw [cechDiff_eq_zero_iff, κ_apply, pow_zero, one_mul, C.resU_baseOfSpecOn]

/-! ### Good towers -/

variable (π) (f)

/-- **A good tower of two-chart data**: every level is good, and the section modules form a
tower of surjections whose kernels are the base-change kernels. -/
structure IsGoodTower : Prop where
  /-- Every level is good. -/
  good : ∀ n, (C.D n).IsGood (TwoChartDatum.baseOfSpec (π n))
  /-- In positive degree, every section at level `n` lifts to level `n + 1`. -/
  lift : ∀ n k, 1 ≤ k → ∀ q, (C.D n).cechDiff k q = 0 →
    ∃ q', (C.D (n + 1)).cechDiff k q' = 0 ∧ (C.ρU n q'.1, C.ρV n q'.2) = q
  /-- In positive degree, a section at level `n + 1` restricting to zero at level `n` lies in
  `Ker(fₙ)` times the sections. -/
  ker : ∀ n k, 1 ≤ k →
    letI := (C.D (n + 1)).algebraU (TwoChartDatum.baseOfSpec (π (n + 1)))
    letI := (C.D (n + 1)).algebraV (TwoChartDatum.baseOfSpec (π (n + 1)))
    ∀ q' ∈ (C.D (n + 1)).sections (TwoChartDatum.baseOfSpec (π (n + 1))) k,
      (C.ρU n q'.1, C.ρV n q'.2) = 0 →
        q' ∈ RingHom.ker (f n) • (C.D (n + 1)).sections (TwoChartDatum.baseOfSpec (π (n + 1))) k

end CompatibleCharts

end Base

/-! ### The graded pieces are the limits of the section modules -/

section Splitting

variable {R : ℕ → Type u} [∀ n, CommRing (R n)] {f : ∀ n, R (n + 1) →+* R n}
  {X : ℕ → Scheme.{u}} (π : ∀ n, X n ⟶ Spec (.of (R n))) {ι : ∀ n, X n ⟶ X (n + 1)}

namespace CompatibleCharts

variable (C : CompatibleCharts ι)

/-- **The splitting of a graded piece `lim_n Γ(Xₙ, Lₙ^{⊗ k})`**: it maps onto every level, the
kernel of the map to level `n` is `Ker(lim R → Rₙ)` times the piece, and every relation among
its elements with coefficients in `lim Rₙ` is trivial. -/
structure PieceSplit (k : ℕ) : Prop where
  /-- The piece maps onto the sections at every level. -/
  surj : ∀ n q, (C.D n).cechDiff k q = 0 → ∃ c ∈ C.grade k, c n = q
  /-- An element vanishing at level `n` is a combination of elements of the piece with
  coefficients in `Ker(lim R → Rₙ)`. -/
  ker : ∀ c ∈ C.grade k, ∀ n, c n = 0 → ∃ (m : ℕ) (r : Fin m → limit f) (c' : Fin m → C.Amb),
    (∀ i, c' i ∈ C.grade k) ∧ (∀ i, (r i).1 n = 0) ∧ c = ∑ i, C.κ π (r i) * c' i
  /-- Every relation among elements of the piece with coefficients in `lim Rₙ` is trivial. -/
  rel : ∀ (l : ℕ) (r : Fin l → limit f) (c : Fin l → C.Amb), (∀ i, c i ∈ C.grade k) →
    ∑ i, C.κ π (r i) * c i = 0 → ∃ (m : ℕ) (a : Fin l → Fin m → limit f) (y : Fin m → C.Amb),
      (∀ j, y j ∈ C.grade k) ∧ (∀ i, c i = ∑ j, C.κ π (a i j) * y j) ∧
        ∀ j, ∑ i, r i * a i j = 0

variable {π} {C}

/-- Each piece `C.grade k` is stable under multiplication by the image of `C.κ π`. -/
theorem κ_mul_mem
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    {k : ℕ} (r : limit f) {c : C.Amb} (hc : c ∈ C.grade k) : C.κ π r * c ∈ C.grade k := by
  simpa using SetLike.mul_mem_graded (C.κ_mem hpb r) hc

/-- Each piece `C.grade k` contains every combination of its elements with coefficients in the
image of `C.κ π`. -/
theorem sum_κ_mul_mem
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    {k m : ℕ} (r : Fin m → limit f) {c : Fin m → C.Amb} (hc : ∀ i, c i ∈ C.grade k) :
    ∑ i, C.κ π (r i) * c i ∈ C.grade k :=
  AddSubgroup.sum_mem _ fun i _ => κ_mul_mem hpb (r i) (hc i)

/-- **The graded pieces of positive degree split.** -/
theorem pieceSplit (hf : ∀ n, Function.Surjective (f n)) (hsq : ∀ n, RingHom.ker (f n) ^ 2 = ⊥)
    (hpb : ∀ n, IsPullback (ι n) (π n) (π (n + 1)) (Spec.map (CommRingCat.ofHom (f n))))
    (hG : C.IsGoodTower f π) (k : ℕ) (hk : 1 ≤ k) : C.PieceSplit (f := f) π k := by
  classical
  let : ∀ n, Algebra (R n) Γ(X n, (C.D n).U) := fun n =>
    (C.D n).algebraU (TwoChartDatum.baseOfSpec (π n))
  let : ∀ n, Algebra (R n) Γ(X n, (C.D n).V) := fun n =>
    (C.D n).algebraV (TwoChartDatum.baseOfSpec (π n))
  have hmemg : ∀ n (q : (C.D (n + 1)).sections (TwoChartDatum.baseOfSpec (π (n + 1))) k),
      (C.ρU n q.1.1, C.ρV n q.1.2) ∈ (C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k := by
    intro n q
    change (C.D n).cechDiff k _ = 0
    rw [← C.ρUV_cechDiff]
    exact (congrArg (C.ρUV n) q.2).trans (map_zero _)
  let g : ∀ n, (C.D (n + 1)).sections (TwoChartDatum.baseOfSpec (π (n + 1))) k →ₛₗ[f n]
      (C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k := fun n =>
    { toFun := fun q => ⟨(C.ρU n q.1.1, C.ρV n q.1.2), hmemg n q⟩
      map_add' := fun q q' => Subtype.ext (Prod.ext (map_add _ _ _) (map_add _ _ _))
      map_smul' := fun r q => Subtype.ext (Prod.ext
        (by
          change C.ρU n (TwoChartDatum.baseOfSpecOn (π (n + 1)) _ r * q.1.1) =
            TwoChartDatum.baseOfSpecOn (π n) _ (f n r) * C.ρU n q.1.1
          rw [map_mul, C.ρU_baseOfSpecOn hpb])
        (by
          change C.ρV n (TwoChartDatum.baseOfSpecOn (π (n + 1)) _ r * q.1.2) =
            TwoChartDatum.baseOfSpecOn (π n) _ (f n r) * C.ρV n q.1.2
          rw [map_mul, C.ρV_baseOfSpecOn hpb])) }
  have : ∀ n, Module.Finite (R n) ((C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k) :=
    fun n => ((hG.good n).2 k hk).1
  have : ∀ n, Module.Projective (R n) ((C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k) :=
    fun n => ((hG.good n).2 k hk).2
  have hg : ∀ n, Function.Surjective (g n) := by
    intro n q
    obtain ⟨q', hq', hq'q⟩ := hG.lift n k hk q.1 q.2
    exact ⟨⟨q', hq'⟩, Subtype.ext hq'q⟩
  have hker : ∀ n x, g n x = 0 → x ∈ RingHom.ker (f n) • (⊤ : Submodule (R (n + 1))
      ((C.D (n + 1)).sections (TwoChartDatum.baseOfSpec (π (n + 1))) k)) := by
    intro n x hx
    rw [Submodule.mem_smul_top_iff]
    exact hG.ker n k hk x.1 x.2 (congrArg Subtype.val hx)
  obtain ⟨m, e', σ', he', hσ', hcomp⟩ := exists_compatible_splitting
    (M := fun n => (C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k) f g hf hsq hg hker
  let e : Fin m → C.Amb := fun i => Amb.mk C fun n => (e' i n : Γ(X n, _) × Γ(X n, _))
  have he : ∀ i, e i ∈ C.grade k := fun i =>
    ⟨fun n => Prod.ext_iff.mp (congrArg Subtype.val (he' i n)), fun n => (e' i n).2⟩
  let pt : ∀ c, c ∈ C.grade k → ∀ n, (C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k :=
    fun c hc n => ⟨c n, (C.mem_grade.mp hc).2 n⟩
  have hgc : ∀ c (hc : c ∈ C.grade k) n, g n (pt c hc (n + 1)) = pt c hc n := by
    intro c hc n
    exact Subtype.ext (Prod.ext ((C.mem_grade.mp hc).1 n).1 ((C.mem_grade.mp hc).1 n).2)
  let coord : ∀ c ∈ C.grade k, Fin m → limit f := fun c hc i =>
    ⟨fun n => σ' n (pt c hc n) i, fun n => by rw [hcomp n _ i, hgc c hc n]⟩
  have hcoord : ∀ c (hc : c ∈ C.grade k) n i,
      (coord c hc i).1 n = σ' n (pt c hc n) i := fun _ _ _ _ => rfl
  have hval : ∀ (w : Fin m → limit f) n,
      (∑ i, C.κ π (w i) * e i) n = ((∑ i, (w i).1 n • e' i n :
        (C.D n).sections (TwoChartDatum.baseOfSpec (π n)) k) : Γ(X n, _) × Γ(X n, _)) := by
    intro w n
    rw [Amb.sum_apply, Submodule.coe_sum]
    rfl
  have hdecomp : ∀ c (hc : c ∈ C.grade k), c = ∑ i, C.κ π (coord c hc i) * e i := by
    intro c hc
    refine Amb.ext C fun n => ?_
    rw [hval]
    exact (congrArg Subtype.val (hσ' n (pt c hc n))).symm
  refine ⟨fun n q hq => ?_, fun c hc n hcn => ?_, fun l r c hc hrel => ?_⟩
  · choose w hw using fun i => towerLimitProj_surjective f hf n (σ' n ⟨q, hq⟩ i)
    refine ⟨∑ i, C.κ π (w i) * e i, sum_κ_mul_mem hpb w he, ?_⟩
    rw [hval]
    have : (∑ i, (w i).1 n • e' i n) = (∑ i, σ' n ⟨q, hq⟩ i • e' i n) :=
      Finset.sum_congr rfl fun i _ => by rw [← hw i]; rfl
    rw [this, hσ']
  · refine ⟨m, coord c hc, e, he, fun i => ?_, hdecomp c hc⟩
    rw [hcoord c hc]
    have : pt c hc n = 0 := Subtype.ext hcn
    rw [this, map_zero, Pi.zero_apply]
  · refine ⟨m, fun i => coord (c i) (hc i), e, he, fun i => hdecomp (c i) (hc i), fun j => ?_⟩
    refine Subtype.ext (funext fun n => ?_)
    have hsum : (∑ i, (r i).1 n • pt (c i) (hc i) n) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero, ← Amb.zero_apply C n, ← hrel, Amb.sum_apply]
      rfl
    have := congrArg (fun x => σ' n x j) hsum
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_zero,
      Pi.zero_apply] at this
    simpa [hcoord] using this

end CompatibleCharts

end Splitting

end AlgebraicGeometry.C1590Private.TwoChartTower

end
