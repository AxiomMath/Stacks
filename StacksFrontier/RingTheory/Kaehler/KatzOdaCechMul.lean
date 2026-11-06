module

public import StacksFrontier.RingTheory.Kaehler.KatzOdaCech
public import StacksFrontier.RingTheory.DeRham.WedgeLeibniz
public import StacksFrontier.LinearAlgebra.ExteriorPower.Wedge
public import StacksFrontier.RingTheory.Kaehler.DeRhamShiftedSum

/-!
# Multiplying a total Čech complex of forms by forms from the base

In the situation of `StacksFrontier.RingTheory.Kaehler.KatzOdaCech` (algebras `B_t` over `A` on the
Čech intersections and a complex of presheaves `P` whose values on `U_t` are the forms
`Ω^•[B_t⁄R]`), a form `ν ∈ Ω^b[A⁄R]` acts on `Tot(Č(U, P))` by right multiplication with its
pullbacks to the intersections, raising the degree by `b`. This file defines this action and
proves the Leibniz rule `D(y ν) = D(y) ν + (-1)^m y dν` for `y` of degree `m`.

## Main definitions

* `Stacks.KatzOda.wedgeTo`: the wedge product `⋀^c × ⋀^b → ⋀^a` for `c + b = a`.
* `Stacks.KatzOda.Cech.mulTot`: right multiplication of `Tot(Č(U, P))` by a form from the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryTheory.CechComplex
open scoped TensorProduct

universe w v u

namespace Stacks.KatzOda

/-! ### The wedge product into a given degree -/

section Ring

variable {R B : CommRingCat.{w}} (ψ : R ⟶ B)

/-- **The wedge product** `⋀^c Ω[B⁄R] × ⋀^b Ω[B⁄R] → ⋀^a Ω[B⁄R]`, for `c + b = a`. -/
def wedgeTo (c b a : ℕ) (h : c + b = a) :
    ⋀[B]^c ↑(CommRingCat.KaehlerDifferential ψ) →ₗ[B]
      ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ) →ₗ[B]
        ⋀[B]^a ↑(CommRingCat.KaehlerDifferential ψ) :=
  (exteriorPower.wedgeMul c b).compr₂ (exteriorPower.degCongr h).toLinearMap

/-- In the exterior algebra, `wedgeTo ψ c b a h x y` is the product `x * y`. -/
theorem coe_wedgeTo (c b a : ℕ) (h : c + b = a) (x : ⋀[B]^c ↑(CommRingCat.KaehlerDifferential ψ))
    (y : ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ)) :
    (wedgeTo ψ c b a h x y : ExteriorAlgebra B ↑(CommRingCat.KaehlerDifferential ψ)) =
      (x : ExteriorAlgebra B ↑(CommRingCat.KaehlerDifferential ψ)) * y := by
  simp [wedgeTo, exteriorPower.coe_degCongr]

/-- Into the degree `c + b`, `wedgeTo` is the wedge product `exteriorPower.wedgeMul c b`. -/
theorem wedgeTo_self (c b : ℕ) (x : ⋀[B]^c ↑(CommRingCat.KaehlerDifferential ψ))
    (y : ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ)) :
    wedgeTo ψ c b (c + b) rfl x y = exteriorPower.wedgeMul c b x y :=
  Subtype.ext (by rw [coe_wedgeTo, exteriorPower.wedgeMul_apply_coe])

/-- **The Leibniz rule** `d(x ∧ y) = dx ∧ y + (-1)^c x ∧ dy`. -/
theorem dForms_wedgeTo (c b a : ℕ) (h : c + b = a)
    (x : ⋀[B]^c ↑(CommRingCat.KaehlerDifferential ψ))
    (y : ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ)) :
    dForms ψ a (wedgeTo ψ c b a h x y) =
      wedgeTo ψ (c + 1) b (a + 1) (by omega) (dForms ψ c x) y +
        ((-1 : ℤ) ^ c) • wedgeTo ψ c (b + 1) (a + 1) (by omega) x (dForms ψ b y) := by
  subst h
  let := ψ.hom.toAlgebra
  refine Subtype.ext ?_
  rw [Submodule.coe_add, Submodule.coe_smul_of_tower, coe_wedgeTo, coe_wedgeTo, wedgeTo_self,
    dForms_eq, dForms_eq, dForms_eq]
  refine (KaehlerDifferential.coe_deRhamDifferential_wedgeMul (A := R) c b x y).trans ?_
  congr 1
  rw [zsmul_eq_mul]
  push_cast
  rfl

variable {B' : CommRingCat.{w}} (ψ' : R ⟶ B') (ρ : B ⟶ B') (hψ : ψ ≫ ρ = ψ')

/-- **Restriction of forms is multiplicative.** -/
theorem formsMap_wedgeTo (c b a : ℕ) (h : c + b = a)
    (x : ⋀[B]^c ↑(CommRingCat.KaehlerDifferential ψ))
    (y : ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ)) :
    Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap ψ ψ' ρ hψ a (wedgeTo ψ c b a h x y) =
      wedgeTo ψ' c b a h (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap ψ ψ' ρ hψ c x)
        (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap ψ ψ' ρ hψ b y) := by
  subst h
  rw [wedgeTo_self, wedgeTo_self]
  let := ψ.hom.toAlgebra
  let := ψ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  have := Stacks.AlgebraicGeometry.AffineOpenDeRham.isScalarTower_of_comp_eq ψ ψ' ρ hψ
  exact KaehlerDifferential.mapExteriorPower_wedgeMul R B B' c b x y

/-- **Restriction of forms commutes with the de Rham differential.** -/
theorem formsMap_dForms (p : ℕ) (x : ⋀[B]^p ↑(CommRingCat.KaehlerDifferential ψ)) :
    Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap ψ ψ' ρ hψ (p + 1) (dForms ψ p x) =
      dForms ψ' p (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap ψ ψ' ρ hψ p x) := by
  let := ψ.hom.toAlgebra
  let := ψ'.hom.toAlgebra
  let := ρ.hom.toAlgebra
  have := Stacks.AlgebraicGeometry.AffineOpenDeRham.isScalarTower_of_comp_eq ψ ψ' ρ hψ
  rw [dForms_eq, dForms_eq]
  exact KaehlerDifferential.mapExteriorPower_deRhamDifferential R B B' p x

end Ring

section Filtration

variable {R A B : CommRingCat.{w}} (gR : R ⟶ A) (φ : A ⟶ B) (ψ : R ⟶ B) (h : gR ≫ φ = ψ)

/-- The filtration `step gR φ ψ h k n` is antitone in `k`. -/
theorem step_antitone {k k' : ℕ} (hk : k ≤ k') (n : ℕ) :
    step gR φ ψ h k' n ≤ step gR φ ψ h k n := by
  induction hk with
  | refl => exact le_rfl
  | step _ ih => exact (step_succ_le gR φ ψ h _ n).trans ih

/-- Transporting a form along an equality of degrees preserves membership in the filtration. -/
theorem degCongr_mem_step {k n n' : ℕ} (e : n = n')
    {z : ⋀[B]^n ↑(CommRingCat.KaehlerDifferential ψ)}
    (hz : z ∈ step gR φ ψ h k n) : exteriorPower.degCongr e z ∈ step gR φ ψ h k n' := by
  subst e
  exact hz

/-- **A form wedged on the right with a form pulled back from `A` of degree `b` lies in `F^b`.** -/
theorem wedgeTo_formsMap_mem (c b a : ℕ) (hc : c + b = a)
    (x : ⋀[B]^c ↑(CommRingCat.KaehlerDifferential ψ))
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    wedgeTo ψ c b a hc x (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR ψ φ h b ν) ∈
      step gR φ ψ h b a := by
  subst hc
  rw [wedgeTo_self, exteriorPower.wedgeMul_comm]
  exact Submodule.smul_mem _ _
    (degCongr_mem_step gR φ ψ h _ (wedgeMul_formsMap_mem gR φ ψ h b c ν x))

/-- The projection `formsProj` is additive. -/
theorem formsProj_add (n : ℕ) (x y : ⋀[B]^n ↑(CommRingCat.KaehlerDifferential ψ)) :
    formsProj gR φ ψ h n (x + y) = formsProj gR φ ψ h n x + formsProj gR φ ψ h n y := by
  let := gR.hom.toAlgebra
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  have := isScalarTower gR φ ψ h
  exact map_add (exteriorPower.map n (KaehlerDifferential.map R A B B)) x y

/-- The projection `formsProj` sends `0` to `0`. -/
theorem formsProj_zero (n : ℕ) : formsProj gR φ ψ h n 0 = 0 := by
  simpa using formsProj_add gR φ ψ h n 0 0

/-- Graded commutativity: `y ∧ ν = (-1)^(k b) ν ∧ y` for `y` of degree `b` and a form `ν` of
degree `k` pulled back from `A`. -/
theorem wedgeTo_formsMap_eq_zsmul (b k : ℕ) (y : ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ))
    (ν : ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR)) :
    wedgeTo ψ b k (k + b) (Nat.add_comm b k) y
        (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR ψ φ h k ν) =
      ((-1 : ℤ) ^ (k * b)) • exteriorPower.wedgeMul k b
        (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR ψ φ h k ν) y := by
  refine Subtype.ext ?_
  rw [coe_wedgeTo, Submodule.coe_smul_of_tower, ← neg_one_pow_smul_eq_zsmul (S := B),
    exteriorPower.wedgeMul_apply_coe,
    exteriorPower.mul_comm_of_mem y.2 (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR ψ φ
      h k ν).2, Algebra.smul_def, map_pow, map_neg, map_one, Nat.mul_comm b k]

/-- **The identification of the graded pieces, with the form from `A` on the right**:
`ν ⊗ m ↦ [m̂ ∧ ν]` for any lift `m̂` of `m`. -/
theorem gradedTensor_tmul_wedgeTo {M : Type w} [AddCommGroup M] [Module A M] {b : ℕ}
    (eM : M ≃+ ⋀[B]^b ↑(CommRingCat.KaehlerDifferential φ))
    (heM : ∀ (a : A) (m : M), eM (a • m) = φ a • eM m) (hsm : φ.hom.FormallySmooth) (k : ℕ)
    (ν : ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR)) (m : M)
    (y : ⋀[B]^b ↑(CommRingCat.KaehlerDifferential ψ)) (hy : formsProj gR φ ψ h b y = eM m) :
    gradedTensor gR φ ψ h eM heM hsm k (ν ⊗ₜ m) =
      Submodule.Quotient.mk ⟨wedgeTo ψ b k (k + b) (Nat.add_comm b k) y
        (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR ψ φ h k ν),
        wedgeTo_formsMap_mem gR φ ψ h b k (k + b) (Nat.add_comm b k) y ν⟩ := by
  rw [gradedTensor_tmul gR φ ψ h eM heM hsm k ν m y hy, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext ?_
  rw [Submodule.coe_smul_of_tower]
  exact (wedgeTo_formsMap_eq_zsmul gR φ ψ h b k y ν).symm

end Filtration

/-! ### Multiplication on the Čech intersections -/

namespace Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} [Fintype ι]
  [DecidableEq ι] {U : ι → C} {R A : CommRingCat.{w}} {gR : R ⟶ A} (D : ChartData (ι := ι) gR)

/-- The pullback of a form of `A` to the intersection selected by `t`. -/
abbrev baseForm (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    ⋀[D.B t]^b ↑(CommRingCat.KaehlerDifferential (D.ψ t)) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR (D.ψ t) (D.φ t) (D.comp_φ t) b ν

omit [Fintype ι] [DecidableEq ι] in
/-- Restricting the pullback of `ν` along a face map gives the pullback of `ν`. -/
theorem formsMap_baseForm (b : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap (D.ψ (t ∘ Fin.succAbove j)) (D.ψ t)
        (D.ρ t j) (D.ψ_ρ t j) b (baseForm D b (t ∘ Fin.succAbove j) ν) = baseForm D b t ν :=
  formsMap_formsMap gR (D.φ _) (D.ψ _) (D.comp_φ _) (D.φ t) (D.ψ t) (D.comp_φ t) (D.ρ t j)
    (D.φ_ρ t j) (D.ψ_ρ t j) b ν

omit [Fintype ι] [DecidableEq ι] in
/-- The de Rham differential of the pullback of `ν` is the pullback of `dν`. -/
theorem dForms_baseForm (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    dForms (D.ψ t) b (baseForm D b t ν) = baseForm D (b + 1) t (dForms gR b ν) :=
  (formsMap_dForms gR (D.ψ t) (D.φ t) (D.comp_φ t) b ν).symm

variable {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (EP : FormsData U D D.ψ D.ψ_ρ P)

/-- **Right multiplication by a form from the base over an intersection**:
`P^c(U_t) → P^a(U_t)`, `y ↦ y ∧ ν` for `ν` of degree `b = a - c`. -/
def mulAt (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X c).obj (op (inter U t))) :
    (P.X a).obj (op (inter U t)) :=
  (EP.e a t).symm (wedgeTo (D.ψ t) c b a h (EP.e c t y) (baseForm D b t ν))

omit [Fintype ι] [DecidableEq ι] in
/-- Under the identification with forms, `mulAt` is right wedge multiplication by the pullback
of `ν`. -/
theorem e_mulAt (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X c).obj (op (inter U t))) :
    EP.e a t (mulAt D EP c b a h t ν y) = wedgeTo (D.ψ t) c b a h (EP.e c t y) (baseForm D b t ν) :=
  AddEquiv.apply_symm_apply _ _

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` is additive in the section. -/
theorem mulAt_add (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y y' : (P.X c).obj (op (inter U t))) :
    mulAt D EP c b a h t ν (y + y') = mulAt D EP c b a h t ν y + mulAt D EP c b a h t ν y' := by
  refine (EP.e a t).injective ?_
  rw [map_add, e_mulAt, e_mulAt, e_mulAt, map_add, LinearMap.map_add₂]

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` commutes with integer multiples of the section. -/
theorem mulAt_zsmul (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (z : ℤ)
    (y : (P.X c).obj (op (inter U t))) :
    mulAt D EP c b a h t ν (z • y) = z • mulAt D EP c b a h t ν y := by
  refine (EP.e a t).injective ?_
  rw [map_zsmul, e_mulAt, e_mulAt, map_zsmul, map_zsmul, LinearMap.smul_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` commutes with finite sums of sections. -/
theorem mulAt_sum (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {J : Type*} (s : Finset J)
    (y : J → (P.X c).obj (op (inter U t))) :
    mulAt D EP c b a h t ν (∑ j ∈ s, y j) = ∑ j ∈ s, mulAt D EP c b a h t ν (y j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine (EP.e a t).injective ?_
    rw [Finset.sum_empty, Finset.sum_empty, map_zero, e_mulAt, map_zero, LinearMap.map_zero₂]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, mulAt_add, ih]

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` commutes with restriction along a face map of the Čech intersections. -/
theorem mulAt_cres (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR))
    (y : (P.X c).obj (op (inter U (t ∘ Fin.succAbove j)))) :
    mulAt D EP c b a h t ν (cres U (P.X c) (Fin.succAbove j) t y) =
      cres U (P.X a) (Fin.succAbove j) t (mulAt D EP c b a h (t ∘ Fin.succAbove j) ν y) := by
  refine (EP.e a t).injective ?_
  rw [e_mulAt, EP.e_cres, EP.e_cres, e_mulAt, formsMap_wedgeTo, formsMap_baseForm]

omit [Fintype ι] [DecidableEq ι] in
/-- The Leibniz rule over an intersection: `d(y ν) = (dy) ν + (-1)^c y dν` for `y` of
degree `c`. -/
theorem mulAt_d (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X c).obj (op (inter U t))) :
    ((P.d a (a + 1)).app (op (inter U t))).hom (mulAt D EP c b a h t ν y) =
      mulAt D EP (c + 1) b (a + 1) (by omega) t ν (((P.d c (c + 1)).app (op (inter U t))).hom y) +
        ((-1 : ℤ) ^ c) • mulAt D EP c (b + 1) (a + 1) (by omega) t (dForms gR b ν) y := by
  refine (EP.e (a + 1) t).injective ?_
  rw [EP.e_d, e_mulAt, map_add, map_zsmul, e_mulAt, e_mulAt, EP.e_d, dForms_wedgeTo,
    dForms_baseForm]

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` sends the zero section to `0`. -/
theorem mulAt_zero (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    mulAt D EP c b a h t ν 0 = 0 := by
  refine (EP.e a t).injective ?_
  simp only [e_mulAt, map_zero, LinearMap.zero_apply]

/-! ### The base cochain of a form, and products of forms on the intersections -/

/-- **The Čech `0`-cochain of a form `ν` of `A`**: its pull-back to each member of the
covering. -/
def baseCochain (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    Cochain U (P.X b) 0 := fun s => (EP.e b s).symm (baseForm D b s ν)

omit [Fintype ι] [DecidableEq ι] in
/-- **The restrictions of the base cochain are the pull-backs of the form**: restricted from any
vertex to a Čech intersection, the base cochain of `ν` is the pull-back of `ν`. -/
theorem e_cres_baseCochain (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) :
    ∀ (r : ℕ) (t : Fin (r + 1) → ι) (φ : Fin 1 → Fin (r + 1)),
      EP.e b t (cres U (P.X b) φ t (baseCochain D EP b ν (t ∘ φ))) = baseForm D b t ν
  | 0, t, φ => by
    obtain rfl : φ = id := funext fun i => Fin.ext (by omega)
    rw [cres_id]
    exact AddEquiv.apply_symm_apply _ _
  | r + 1, t, φ => by
    obtain ⟨j, hj⟩ : ∃ j : Fin (r + 2), φ 0 ≠ j := by
      by_cases h : φ 0 = 0
      · refine ⟨Fin.last _, ?_⟩
        rw [h]
        intro h'
        have := congrArg Fin.val h'
        simp at this
      · exact ⟨0, h⟩
    obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hj
    obtain rfl : φ = Fin.succAbove j ∘ fun _ => z := funext fun i => by
      rw [show i = 0 from Fin.ext (by omega)]
      exact hz.symm
    rw [cres_comp, EP.e_cres,
      show baseCochain D EP b ν (t ∘ Fin.succAbove j ∘ fun _ => z) =
        baseCochain D EP b ν ((t ∘ Fin.succAbove j) ∘ fun _ => z) from rfl,
      e_cres_baseCochain b ν r (t ∘ Fin.succAbove j) (fun _ => z), formsMap_baseForm]

/-- **Forms with a product on the intersections**: forms data together with products
`P^a(U_t) × P^b(U_t) → P^{a+b}(U_t)` which the identifications with Kähler forms carry to the
wedge product. -/
structure FormsMulData extends FormsData U D D.ψ D.ψ_ρ P where
  /-- The product of sections over the intersection selected by `t`. -/
  mul : ∀ (a b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    (P.X a).obj (op (inter U t)) → (P.X b).obj (op (inter U t)) →
      (P.X (a + b)).obj (op (inter U t))
  /-- The identifications with Kähler forms carry the product to the wedge product. -/
  e'_mul : ∀ (a b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t)))
    (y' : (P.X b).obj (op (inter U t))),
    letI := instAddCommGroup a t
    letI := instModule a t
    letI := instAddCommGroup b t
    letI := instModule b t
    letI := instAddCommGroup (a + b) t
    letI := instModule (a + b) t
    e' (a + b) t (s (a + b) t (mul a b t y y')) =
      exteriorPower.wedgeMul a b (e' a t (s a t y)) (e' b t (s b t y'))

omit [Fintype ι] [DecidableEq ι] in
/-- The identifications with Kähler forms carry the product to the wedge product. -/
theorem FormsMulData.e_mul (MD : FormsMulData D (P := P)) (a b : ℕ) {m : ℕ}
    (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t)))
    (y' : (P.X b).obj (op (inter U t))) :
    MD.e (a + b) t (MD.mul a b t y y') = exteriorPower.wedgeMul a b (MD.e a t y) (MD.e b t y') :=
  MD.e'_mul a b t y y'

omit [Fintype ι] [DecidableEq ι] in
/-- **On the Čech intersections, multiplication by a form from the base is the product with the
restriction of its base cochain** from the last vertex. -/
theorem mulAt_eq_mul (MD : FormsMulData D (P := P)) (a b : ℕ) {r : ℕ} (t : Fin (r + 1) → ι)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X a).obj (op (inter U t))) :
    mulAt D MD.toFormsData a b (a + b) rfl t ν y =
      MD.mul a b t y (cres U (P.X b) (fun _ : Fin 1 => Fin.last r) t
        (baseCochain D MD.toFormsData b ν (t ∘ fun _ : Fin 1 => Fin.last r))) := by
  refine (MD.e (a + b) t).injective ?_
  rw [e_mulAt, MD.e_mul, e_cres_baseCochain, wedgeTo_self]

/-! ### Multiplication on the total Čech complex -/

/-- The component in the summand `(p, a)` of the product of `y ∈ Tot^m(Č(U, P))` with a form
`ν` of degree `b` from the base: `y_{(p, a - b)} ∧ ν`, and zero for `a < b`. -/
def mulTotAt (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) (y : TotX U P m) (p a : ℕ) (hpa : (p : ℤ) + a = N) : Cochain U (P.X a) p :=
  if hb : b ≤ a then fun t =>
    mulAt D EP (a - b) b a (Nat.sub_add_cancel hb) t ν (y ⟨(p, a - b), by omega⟩ t)
  else 0

/-- **Right multiplication of `Tot(Č(U, P))` by a form from the base**, of degree `b`. -/
def mulTot (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) (y : TotX U P m) : TotX U P N :=
  fun j => mulTotAt D EP b ν hN y j.1.1 j.1.2 j.2

omit [Fintype ι] [DecidableEq ι] in
/-- For `c + b = a`, the component of the product in the summand `(p, a)` is `y_{(p, c)} ∧ ν`. -/
theorem mulTotAt_eq (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) (y : TotX U P m) (p c a : ℕ) (hc : c + b = a) (hpa : (p : ℤ) + a = N)
    (hpc : (p : ℤ) + c = m) :
    mulTotAt D EP b ν hN y p a hpa = fun t => mulAt D EP c b a hc t ν (y ⟨(p, c), hpc⟩ t) := by
  rw [mulTotAt, dite_eq_left (by omega)]
  have key : ∀ (c' : ℕ) (e : c' = c) (h1 : c' + b = a) (h2 : (p : ℤ) + c' = m),
      (fun t => mulAt D EP c' b a h1 t ν (y ⟨(p, c'), h2⟩ t)) =
        fun t => mulAt D EP c b a hc t ν (y ⟨(p, c), hpc⟩ t) := by
    rintro _ rfl _ _
    rfl
  exact key (a - b) (by omega) _ _

omit [Fintype ι] [DecidableEq ι] in
/-- For `a < b`, the component of the product in the summand `(p, a)` is zero. -/
theorem mulTotAt_of_lt (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) (y : TotX U P m) (p a : ℕ) (hpa : (p : ℤ) + a = N) (h : a < b) :
    mulTotAt D EP b ν hN y p a hpa = 0 :=
  dite_eq_right (by omega)

omit [Fintype ι] [DecidableEq ι] in
/-- The components of `mulTot` are given by `mulTotAt`. -/
theorem mulTot_apply (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) (y : TotX U P m) (j : TotIndex N) :
    mulTot D EP b ν hN y j = mulTotAt D EP b ν hN y j.1.1 j.1.2 j.2 :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- **The Leibniz rule on the total Čech complex**: `D(y ν) = D(y) ν + (-1)^m y dν` for `y` of
degree `m`. -/
theorem totDTo_mulTot (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (m : ℕ)
    {N : ℤ} (hN : (m : ℤ) + b = N) (y : TotX U P m) :
    totDTo U P N (N + 1) rfl (mulTot D EP b ν hN y) =
      mulTot D EP b ν (show ((m : ℤ) + 1) + b = N + 1 by omega)
          (totDTo U P m (m + 1) rfl y) +
        ((-1 : ℤ) ^ m) • mulTot D EP (b + 1) (dForms gR b ν)
          (show (m : ℤ) + ((b + 1 : ℕ) : ℤ) = N + 1 by push_cast; omega) y := by
  funext ⟨⟨p, a⟩, hpa⟩ t
  simp only [Pi.add_apply, Pi.smul_apply, totDTo_apply, mulTot_apply]
  have hcech : ∀ (c : ℕ) (hc : c + b = a) (hpc : (p : ℤ) + c = (m : ℤ) + 1),
      totDCech U P (mulTot D EP b ν hN y) p a hpa t =
        mulAt D EP c b a hc t ν (totDCech U P y p c hpc t) := by
    intro c hc hpc
    rcases p with _ | q
    · simp only [totDCech_zero, Pi.zero_apply]
      exact (mulAt_zero D EP c b a hc t ν).symm
    · simp only [totDCech_succ, cechD_apply, mulTot_apply]
      rw [mulTotAt_eq D EP b ν hN y q c a hc _ (by omega), mulAt_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulAt_zsmul, mulAt_cres]
  have hzero : ∀ (q a' : ℕ) (hq : (q : ℤ) + a' = N), a' < b →
      mulTot D EP b ν hN y ⟨(q, a'), hq⟩ = 0 :=
    fun q a' hq h => mulTotAt_of_lt D EP b ν hN y q a' hq h
  have hcoef0 : ∀ (e : ℕ) (he : (p : ℤ) + (e + 1 : ℕ) = N + 1), e < b →
      totDCoef U P (mulTot D EP b ν hN y) p (e + 1) he t = 0 := by
    intro e he heb
    rw [totDCoef_succ, hzero p e _ heb]
    simp
  rcases a with _ | e
  · rw [totDCoef_zero, mulTotAt_of_lt D EP (b + 1) _ _ y p 0 hpa (by omega)]
    rcases b with _ | b
    · rw [mulTotAt_eq D EP 0 ν _ _ p 0 0 rfl hpa (by omega),
        hcech 0 rfl (by omega), totDTo_apply, totDCoef_zero]
      simp
    · rw [mulTotAt_of_lt D EP (b + 1) ν _ _ p 0 hpa (by omega)]
      rcases p with _ | q
      · simp
      · rw [totDCech_succ, hzero q 0 _ (by omega)]
        simp
  · by_cases heb : e + 1 < b
    · rw [hcoef0 e hpa (by omega), mulTotAt_of_lt D EP b ν _ _ p (e + 1) hpa heb,
        mulTotAt_of_lt D EP (b + 1) _ _ y p (e + 1) hpa (by omega)]
      rcases p with _ | q
      · simp
      · rw [totDCech_succ, hzero q (e + 1) _ heb]
        simp
    · by_cases heb' : e + 1 = b
      · subst heb'
        rw [hcoef0 e hpa (by omega), mulTotAt_of_lt D EP (e + 1 + 1) _ _ y p (e + 1) hpa
          (by omega), mulTotAt_eq D EP (e + 1) ν _ _ p 0 (e + 1) (by omega) hpa
          (by omega), hcech 0 (by omega) (by omega),
          totDTo_apply, totDCoef_zero]
        simp
      · obtain ⟨c', rfl⟩ : ∃ c', e = c' + b := ⟨e - b, by omega⟩
        have hm : m = p + c' := by push_cast at hpa hN; omega
        rw [mulTotAt_eq D EP b ν _ _ p (c' + 1) (c' + b + 1) (by omega) hpa
            (by omega),
          mulTotAt_eq D EP (b + 1) _ _ y p c' (c' + b + 1) (by omega) hpa
            (by omega),
          hcech (c' + 1) (by omega) (by omega), totDTo_apply,
          totDCoef_succ, totDCoef_succ, mulTot_apply,
          mulTotAt_eq D EP b ν hN y p c' (c' + b) rfl _ (by omega)]
        simp only [cochainMap_apply, Pi.smul_apply, Pi.add_apply]
        rw [mulAt_d, mulAt_add, mulAt_zsmul, smul_add, smul_smul,
          show ((-1 : ℤ) ^ m) = (-1) ^ p * (-1) ^ c' by rw [hm, pow_add]]
        exact (add_assoc _ _ _).symm


/-! ### Linearity in the form from the base -/

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` is additive in the form from the base. -/
theorem mulAt_add_form (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι)
    (ν ν' : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X c).obj (op (inter U t))) :
    mulAt D EP c b a h t (ν + ν') y = mulAt D EP c b a h t ν y + mulAt D EP c b a h t ν' y := by
  refine (EP.e a t).injective ?_
  rw [map_add, e_mulAt, e_mulAt, e_mulAt, baseForm, baseForm, baseForm,
    Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_add, map_add]

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` is `R`-linear in the form from the base. -/
theorem mulAt_smul_form (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι) (r : R)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X c).obj (op (inter U t))) :
    mulAt D EP c b a h t (gR r • ν) y = r • mulAt D EP c b a h t ν y := by
  refine (EP.e a t).injective ?_
  rw [EP.e_smul, e_mulAt, e_mulAt, baseForm, baseForm,
    Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_smul, map_smul]
  congr 1
  rw [← D.comp_φ t]
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `mulAt` commutes with integer multiples of the form from the base. -/
theorem mulAt_zsmul_form (c b a : ℕ) (h : c + b = a) {m : ℕ} (t : Fin (m + 1) → ι) (z : ℤ)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) (y : (P.X c).obj (op (inter U t))) :
    mulAt D EP c b a h t (z • ν) y = z • mulAt D EP c b a h t ν y := by
  refine (EP.e a t).injective ?_
  rw [map_zsmul, e_mulAt, e_mulAt, baseForm, baseForm,
    show Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR (D.ψ t) (D.φ t) (D.comp_φ t) b
      (z • ν) = z • Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR (D.ψ t) (D.φ t)
        (D.comp_φ t) b ν from
      map_zsmul (AddMonoidHom.mk' (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap gR (D.ψ t)
        (D.φ t) (D.comp_φ t) b)
        (Stacks.AlgebraicGeometry.AffineOpenDeRham.formsMap_add gR (D.ψ t) (D.φ t) (D.comp_φ t) b))
        z ν, map_zsmul]

omit [Fintype ι] [DecidableEq ι] in
/-- `mulTot` is additive in the form from the base. -/
theorem mulTot_add_form (b : ℕ) (ν ν' : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) (y : TotX U P m) :
    mulTot D EP b (ν + ν') hN y = mulTot D EP b ν hN y + mulTot D EP b ν' hN y := by
  funext j t
  simp only [mulTot_apply, Pi.add_apply, mulTotAt]
  split_ifs
  · exact mulAt_add_form D EP _ _ _ _ t ν ν' _
  · exact (add_zero 0).symm

omit [Fintype ι] [DecidableEq ι] in
/-- `mulTot` is `R`-linear in the form from the base. -/
theorem mulTot_smul_form (b : ℕ) (r : R) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR))
    {m N : ℤ} (hN : m + b = N) (y : TotX U P m) :
    mulTot D EP b (gR r • ν) hN y = r • mulTot D EP b ν hN y := by
  funext j t
  simp only [mulTot_apply, Pi.smul_apply, mulTotAt]
  split_ifs
  · exact mulAt_smul_form D EP _ _ _ _ t r ν _
  · exact (smul_zero r).symm

omit [Fintype ι] [DecidableEq ι] in
/-- `mulTot` commutes with integer multiples of the form from the base. -/
theorem mulTot_zsmul_form (b : ℕ) (z : ℤ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR))
    {m N : ℤ} (hN : m + b = N) (y : TotX U P m) :
    mulTot D EP b (z • ν) hN y = z • mulTot D EP b ν hN y := by
  funext j t
  simp only [mulTot_apply, Pi.smul_apply, mulTotAt]
  split_ifs
  · exact mulAt_zsmul_form D EP _ _ _ _ t z ν _
  · exact (smul_zero z).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Multiplication by the zero form is zero. -/
theorem mulTot_zero_form (b : ℕ) {m N : ℤ} (hN : m + b = N) (y : TotX U P m) :
    mulTot D EP b 0 hN y = 0 := by
  have h := mulTot_zsmul_form D EP b 0 0 hN y
  rwa [zero_smul, zero_smul] at h

omit [Fintype ι] [DecidableEq ι] in
/-- Multiplying the zero cochain by a form gives zero. -/
theorem mulTot_zero (b : ℕ) (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ}
    (hN : m + b = N) : mulTot D EP b ν hN (0 : TotX U P m) = 0 := by
  funext j t
  simp only [mulTot_apply, Pi.zero_apply, mulTotAt]
  split_ifs
  · exact mulAt_zero D EP _ _ _ _ t ν
  · rfl

/-! ### The cup product map from the sum of shifted de Rham complexes of the base -/

/-- There is at most one natural number `b` with `k + b = N`. -/
instance subsingleton_degree (k N : ℤ) : Subsingleton {b : ℕ // k + b = N} :=
  ⟨fun a c => Subtype.ext (by have := a.2; have := c.2; omega)⟩

/-- The natural numbers `b` with `k + b = N` form a finite type. -/
noncomputable instance fintype_degree (k N : ℤ) : Fintype {b : ℕ // k + b = N} :=
  Fintype.ofFinite _

variable {I : Type w} [Fintype I] (n : I → ℕ) (x : ∀ i, TotX U P (n i))

omit [Fintype ι] [DecidableEq ι] in
variable (gR) in
/-- An element of the algebraic de Rham complex of `A/R`, read as a Kähler form. -/
def toForms {b : ℕ}
    (ν : (Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).X b) :
    ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR) :=
  ν

omit [Fintype ι] [DecidableEq ι] in
/-- `toForms` is additive. -/
theorem toForms_add {b : ℕ}
    (ν ν' : (Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).X b) :
    toForms gR (ν + ν') = toForms gR ν + toForms gR ν' :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `toForms` sends `r • ν` to `gR r • toForms gR ν`. -/
theorem toForms_smul {b : ℕ} (r : R)
    (ν : (Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).X b) :
    toForms gR (r • ν) = gR r • toForms gR ν :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `toForms` commutes with integer multiples. -/
theorem toForms_zsmul {b : ℕ} (z : ℤ)
    (ν : (Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).X b) :
    toForms gR (z • ν) = z • toForms gR ν :=
  map_zsmul (AddMonoidHom.mk' (toForms gR (b := b)) (toForms_add (gR := gR))) z ν

omit [Fintype ι] [DecidableEq ι] in
/-- `toForms` carries the differential of the de Rham complex to `dForms`. -/
theorem toForms_d {b : ℕ}
    (ν : (Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).X b) :
    toForms gR
        (((Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).d b
          (b + 1)).hom ν) =
      dForms gR b (toForms gR ν) :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- `toForms` sends `0` to `0`. -/
theorem toForms_zero {b : ℕ} :
    toForms gR
      (0 : (Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).X b) = 0 :=
  rfl

open ShiftedSum in
/-- **The cup product map** `⨁_i Ω^•_{A/R}[-n_i] → Tot(Č(U, P))`, degreewise:
`(ω_i)_i ↦ ∑_i x_i ∧ ω_i`. -/
def cupMap (N : ℤ) : MX gR n N →ₗ[R] TotX U P N where
  toFun ω := ∑ i, ∑ b : {b : ℕ // (n i : ℤ) + b = N}, mulTot D EP b.1 (toForms gR (ω i b)) b.2 (x i)
  map_add' ω ω' := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => (congrArg (mulTot D EP b.1 · b.2 (x i))
      (toForms_add _ _)).trans (mulTot_add_form D EP _ _ _ _ _)
  map_smul' r ω := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
    exact (congrArg (mulTot D EP b.1 · b.2 (x i)) (toForms_smul r _)).trans
      (mulTot_smul_form D EP _ r _ _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- The cup product map sends `(ω_i)_i` to `∑_i x_i ∧ ω_i`. -/
theorem cupMap_apply (N : ℤ) (ω : ShiftedSum.MX gR n N) :
    cupMap D EP n x N ω = ∑ i, ∑ b : {b : ℕ // (n i : ℤ) + b = N},
      mulTot D EP b.1 (toForms gR (ω i b)) b.2 (x i) :=
  rfl

variable (hx : ∀ i, totDTo U P (n i) (n i + 1) rfl (x i) = 0)

omit [Fintype ι] [DecidableEq ι] in
include hx in
open ShiftedSum in
/-- For cocycles `x_i`, the cup product map commutes with the differentials. -/
theorem totDTo_cupMap (N : ℤ) (ω : MX gR n N) :
    totDTo U P N (N + 1) rfl (cupMap D EP n x N ω) =
      cupMap D EP n x (N + 1) (ShiftedSum.dTo gR n N (N + 1) rfl ω) := by
  rw [cupMap_apply, cupMap_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  simp only [totDTo_mulTot, hx i, mulTot_zero, zero_add]
  by_cases hi : (n i : ℤ) ≤ N
  · let b0 : {b : ℕ // (n i : ℤ) + b = N} := ⟨(N - n i).toNat, by omega⟩
    let b1 : {b : ℕ // (n i : ℤ) + b = N + 1} := ⟨(N - n i).toNat + 1, by push_cast; omega⟩
    rw [Fintype.sum_subsingleton _ b0, Fintype.sum_subsingleton _ b1]
    show _ = mulTot D EP b1.1 (toForms gR (((-1 : ℤ) ^ n i) •
      ((Stacks.AlgebraicGeometry.AffineDifferentialsIso.ringDeRhamComplex gR).d b0.1
        (b0.1 + 1)).hom (ω i ⟨b0.1, b0.2⟩))) _ (x i)
    rw [toForms_zsmul, mulTot_zsmul_form, toForms_d]
  · have : IsEmpty {b : ℕ // (n i : ℤ) + b = N} := ⟨fun b => by have := b.2; omega⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine (Finset.sum_eq_zero fun b' _ => ?_).symm
    obtain ⟨_ | c, hc⟩ := b'
    · show mulTot D EP 0 (toForms gR (dAt gR n ω i 0 hc)) _ (x i) = 0
      rw [dAt_zero, toForms_zero]
      exact mulTot_zero_form D EP 0 _ (x i)
    · exfalso
      push_cast at hc
      omega

include hx in
/-- **The cup product map** `⨁_i Ω^•_{A/R}[-n_i] → Tot(Č(U, P))`, `(ω_i)_i ↦ ∑_i x_i ∧ ω_i`, for
cocycles `x_i` of degree `n_i`: a map of complexes. -/
def cupHom : ShiftedSum.complex gR n ⟶ cechTot U P where
  f N := ModuleCat.ofHom (cupMap D EP n x N)
  comm' N N' h := by
    change N + 1 = N' at h
    subst h
    refine ModuleCat.hom_ext (LinearMap.ext fun ω => ?_)
    change ((cechTot U P).d N (N + 1)).hom (cupMap D EP n x N ω) =
      (cupMap D EP n x (N + 1)) (((ShiftedSum.complex gR n).d N (N + 1)).hom ω)
    rw [ShiftedSum.complex_d_apply gR n rfl, cechTot_d_apply' U P rfl, totDTo_cupMap D EP n x hx]

omit [Fintype ι] [DecidableEq ι] in
/-- In degree `N`, `cupHom` is `cupMap`. -/
theorem cupHom_f_apply (N : ℤ) (ω : ShiftedSum.MX gR n N) :
    ((cupHom D EP n x hx).f N).hom ω = cupMap D EP n x N ω :=
  rfl

omit [Fintype ι] [DecidableEq ι] in
/-- Multiplication by a form of degree `b ≥ k` from the base lands in the `k`-th step of the
filtration of the total complex. -/
theorem mulTot_mem_totStep {k : ℕ} (b : ℕ) (hb : k ≤ b)
    (ν : ⋀[A]^b ↑(CommRingCat.KaehlerDifferential gR)) {m N : ℤ} (hN : m + b = N)
    (y : TotX U P m) : mulTot D EP b ν hN y ∈ (filtration D EP).totStep (U := U) k N := by
  intro j t
  show mulTotAt D EP b ν hN y j.1.1 j.1.2 j.2 t ∈ (filtration D EP).step k j.1.2 t
  rw [mulTotAt]
  split_ifs with hab
  · refine (mem_comapStep _ _ _ _ (D.ψ t).hom _ (EP.e_smul j.1.2 t)).2 ?_
    show EP.e j.1.2 t (mulAt D EP _ b j.1.2 _ t ν _) ∈ _
    rw [e_mulAt]
    exact step_antitone gR (D.φ t) (D.ψ t) (D.comp_φ t) hb _
      (wedgeTo_formsMap_mem gR (D.φ t) (D.ψ t) (D.comp_φ t) _ b _ _ _ ν)
  · exact zero_mem _

omit [Fintype ι] [DecidableEq ι] [Fintype I] in
  /-- The term `x_i ∧ ω_i` lies in the `k`-th step if each component of `ω_i` vanishes or has
  degree at least `k`. -/
  private theorem sum_mulTot_mem_totStep {k : ℕ} {N : ℤ} (ω : ShiftedSum.MX gR n N) (i : I)
      (h : ∀ b : {b : ℕ // (n i : ℤ) + b = N}, ω i b = 0 ∨ k ≤ b.1) :
      ∑ b : {b : ℕ // (n i : ℤ) + b = N}, mulTot D EP b.1 (toForms gR (ω i b)) b.2 (x i) ∈
        (filtration D EP).totStep (U := U) k N := by
    refine Submodule.sum_mem _ fun b _ => ?_
    rcases h b with hb | hb
    · rw [hb, toForms_zero, mulTot_zero_form]
      exact zero_mem _
    · exact mulTot_mem_totStep D EP b.1 hb _ b.2 (x i)

omit [Fintype ι] [DecidableEq ι] in
include hx in
/-- **The cup product map respects the filtrations.** -/
theorem cupHom_step_le (k : ℕ) (N : ℤ) :
    ((ShiftedSum.filtration gR n).step k N).map ((cupHom D EP n x hx).f N).hom ≤
      ((filtration D EP).totFiltration (U := U)).step k N := by
  rintro _ ⟨ω, hω, rfl⟩
  rw [cupHom_f_apply, cupMap_apply]
  exact Submodule.sum_mem _ fun i _ =>
    sum_mulTot_mem_totStep D EP n x _ i fun b => (lt_or_ge b.1 k).imp (hω i b) id

/-! ### The projection to the forms relative to `A` -/

variable {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} A) ℕ} (EQ : FormsData U D D.φ D.φ_ρ Q)

/-- The projection `Ω^a[B_t⁄R] → Ω^a[B_t⁄A]` over an intersection, transported to `P` and `Q`. -/
def projAt (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    (P.X a).obj (op (inter U t)) →+ (Q.X a).obj (op (inter U t)) where
  toFun y := (EQ.e a t).symm (formsProj gR (D.φ t) (D.ψ t) (D.comp_φ t) a (EP.e a t y))
  map_zero' := by rw [map_zero, formsProj_zero, map_zero]
  map_add' y y' := by rw [map_add, formsProj_add, map_add]

omit [Fintype ι] [DecidableEq ι] in
/-- Under the identifications with forms, `projAt` is the projection `formsProj`. -/
theorem e_projAt (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))) :
    EQ.e a t (projAt D EP EQ a t y) = formsProj gR (D.φ t) (D.ψ t) (D.comp_φ t) a (EP.e a t y) :=
  AddEquiv.apply_symm_apply _ _

/-- **The projection from the forms relative to `R` to those relative to `A`**, on the Čech
intersections. -/
def projHom : InterHom U P Q where
  app a _ t := projAt D EP EQ a t
  app_cres a m t j y := by
    refine (EQ.e a t).injective ?_
    rw [e_projAt, EP.e_cres, EQ.e_cres, e_projAt,
      formsProj_formsMap gR (D.φ _) (D.ψ _) (D.comp_φ _) (D.φ t) (D.ψ t) (D.comp_φ t) (D.ρ t j)
        (D.φ_ρ t j) (D.ψ_ρ t j)]
  app_d a m t y := by
    refine (EQ.e (a + 1) t).injective ?_
    rw [e_projAt, EP.e_d, EQ.e_d, e_projAt, formsProj_dForms]

/-- A cochain of the total Čech complex, read in an equal degree. -/
def reTot {S : Type w} [Ring S] {P' : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} S) ℕ} {q q' : ℤ}
    (h : q = q') (y : TotX U P' q) : TotX U P' q' :=
  fun j => y ⟨j.1, j.2.trans h.symm⟩

/-- The images in `Tot(Č(U, Q))` of the cocycles `x_i`. -/
def xbar (i : I) : TotX U Q (n i) :=
  (projHom D EP EQ).totAddHom (n i) (x i)

omit [Fintype ι] [DecidableEq ι] [Fintype I] in
include hx in
/-- Each `x̄_i` is a cocycle. -/
theorem totDTo_xbar (i : I) : totDTo U Q (n i) (n i + 1) rfl (xbar D EP n x EQ i) = 0 := by
  have h := (projHom D EP EQ).totAddHom_totD (n i) (x i)
  change (projHom D EP EQ).totAddHom (n i + 1) (totDTo U P (n i) (n i + 1) rfl (x i)) = _ at h
  rw [hx i, map_zero] at h
  exact h.symm

/-- The map `⨁_i A[-n_i] → Tot(Č(U, Q))`, degreewise: `(v_i)_i ↦ ∑_i v_i x̄_i`. -/
def unitMap (q : ℤ) : (∀ (_ : {i : I // (n i : ℤ) = q}), A) →ₗ[A] TotX U Q q where
  toFun v := ∑ i : {i : I // (n i : ℤ) = q}, v i • reTot i.2 (xbar D EP n x EQ i.1)
  map_add' v v' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

omit [Fintype ι] [DecidableEq ι] in
include hx in
/-- The image of `unitMap` consists of cocycles. -/
theorem totDTo_unitMap (q : ℤ) (v : ∀ (_ : {i : I // (n i : ℤ) = q}), A) :
    totDTo U Q q (q + 1) rfl (unitMap D EP n x EQ q v) = 0 := by
  show totDTo U Q q (q + 1) rfl (∑ i : {i : I // (n i : ℤ) = q},
    v i • reTot i.2 (xbar D EP n x EQ i.1)) = 0
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_smul]
  obtain ⟨i, rfl⟩ := i
  show v ⟨i, rfl⟩ • totDTo U Q (n i) (n i + 1) rfl (xbar D EP n x EQ i) = 0
  rw [totDTo_xbar D EP n x hx EQ i, smul_zero]

include hx in
/-- **The map `⨁_i A[-n_i] → Tot(Č(U, Q))`, `1_i ↦ x̄_i`**, a map of complexes. -/
def unitHom : ShiftedSum.unitComplex A n ⟶ cechTot U Q where
  f q := ModuleCat.ofHom (unitMap D EP n x EQ q)
  comm' q q' h := by
    change q + 1 = q' at h
    subst h
    refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
    change ((cechTot U Q).d q (q + 1)).hom (unitMap D EP n x EQ q v) =
      (unitMap D EP n x EQ (q + 1)) 0
    rw [cechTot_d_apply' U Q rfl, totDTo_unitMap D EP n x hx EQ, map_zero]

/-! ### The graded pieces of the cup product map -/

/-- A sum of `if h : p i then f i h else 0` over `I` is the sum of `f` over the subtype of `p`. -/
theorem sum_dite_subtype {M : Type*} [AddCommMonoid M] (p : I → Prop) [DecidablePred p]
    (f : ∀ i, p i → M) :
    ∑ i, (if h : p i then f i h else 0) = ∑ i : {i : I // p i}, f i.1 i.2 := by
  rw [← Fintype.sum_subtype_add_sum_subtype p]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {i : I // ¬p i})) fun i _ => dite_eq_right i.2,
    add_zero]
  exact Finset.sum_congr rfl fun i _ => dite_eq_left i.2

omit [Fintype ι] [DecidableEq ι] in
/-- The class in the graded quotient of a finite sum of forms in the filtration is the sum of
their classes. -/
theorem mk_sum_step {k a : ℕ} {m : ℕ} (t : Fin (m + 1) → ι) {J : Type*} (s : Finset J)
    (f : J → ⋀[D.B t]^a ↑(CommRingCat.KaehlerDifferential (D.ψ t)))
    (hf : ∀ j, f j ∈ step gR (D.φ t) (D.ψ t) (D.comp_φ t) k a) :
    (Submodule.Quotient.mk ⟨∑ j ∈ s, f j, Submodule.sum_mem _ fun j _ => hf j⟩ :
        gradedQuot gR (D.φ t) (D.ψ t) (D.comp_φ t) k a) =
      ∑ j ∈ s, Submodule.Quotient.mk ⟨f j, hf j⟩ := by
  have e : (⟨∑ j ∈ s, f j, Submodule.sum_mem _ fun j _ => hf j⟩ :
      step gR (D.φ t) (D.ψ t) (D.comp_φ t) k a) = ∑ j ∈ s, ⟨f j, hf j⟩ :=
    Subtype.ext (by rw [Submodule.coe_sum])
  rw [e, ← Submodule.mkQ_apply, map_sum]
  rfl

omit [Fintype ι] [DecidableEq ι] [Fintype I] in
open ShiftedSum in
/-- For `ω` in the `k`-th step of the filtration, the term `x_i ∧ ω_i` lies in the `k`-th step
of the filtration of the total complex. -/
theorem cupTerm_mem_totStep {k : ℕ} {N : ℤ} {ω : MX gR n N} (hω : ω ∈ ShiftedSum.step gR n k N)
    (i : I) :
    ∑ b : {b : ℕ // (n i : ℤ) + b = N}, mulTot D EP b.1 (toForms gR (ω i b)) b.2 (x i) ∈
      (filtration D EP).totStep (U := U) k N := by
  exact sum_mulTot_mem_totStep D EP n x _ i fun b => (lt_or_ge b.1 k).imp (hω i b) id

omit [Fintype ι] [DecidableEq ι] [Fintype I] in
open ShiftedSum in
/-- The class of the term `x_i ∧ ω_i` in `gr^k` over an intersection is the image of
`ω_i ⊗ x̄_i` when `n_i + k = N`, and zero otherwise. -/
theorem mk_cupTerm {k : ℕ} {N : ℤ} {ω : MX gR n N} (hω : ω ∈ ShiftedSum.step gR n k N) (i : I)
    (p b : ℕ) (hpb : (p : ℤ) + (k + b : ℕ) = N) (t : Fin (p + 1) → ι) :
    (Submodule.Quotient.mk ⟨EP.e (k + b) t ((∑ b' : {b : ℕ // (n i : ℤ) + b = N},
        mulTot D EP b'.1 (toForms gR (ω i b')) b'.2 (x i)) ⟨(p, k + b), hpb⟩ t),
        (mem_comapStep _ _ _ _ (D.ψ t).hom _ (EP.e_smul (k + b) t)).1
          (cupTerm_mem_totStep D EP n x hω i ⟨(p, k + b), hpb⟩ t)⟩ :
        gradedQuot gR (D.φ t) (D.ψ t) (D.comp_φ t) k (k + b)) =
      if h : (n i : ℤ) + k = N then gradedOpen D EQ k b t
        ((toForms gR (ω i ⟨k, h⟩) ⊗ₜ[A] xbar D EP n x EQ i ⟨(p, b), by
          push_cast at hpb; omega⟩ t : ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t))))
      else 0 := by
  by_cases h : (n i : ℤ) + k = N
  · rw [dite_eq_left h]
    have hsum : (∑ b' : {b : ℕ // (n i : ℤ) + b = N},
        mulTot D EP b'.1 (toForms gR (ω i b')) b'.2 (x i)) =
          mulTot D EP k (toForms gR (ω i ⟨k, h⟩)) h (x i) :=
      Fintype.sum_subsingleton (fun b' : {b : ℕ // (n i : ℤ) + b = N} =>
        mulTot D EP b'.1 (toForms gR (ω i b')) b'.2 (x i)) ⟨k, h⟩
    have hy := (e_projAt D EP EQ b t (x i (⟨(p, b), by push_cast at hpb; omega⟩ : TotIndex (n i))
      t)).symm
    change _ = gradedTensor gR (D.φ t) (D.ψ t) (D.comp_φ t) (EQ.e b t) (EQ.e_smul b t)
      (D.formallySmooth t) k (toForms gR (ω i ⟨k, h⟩) ⊗ₜ[A] projAt D EP EQ b t
        (x i (⟨(p, b), by push_cast at hpb; omega⟩ : TotIndex (n i)) t))
    rw [gradedTensor_tmul_wedgeTo gR (D.φ t) (D.ψ t) (D.comp_φ t) (EQ.e b t) (EQ.e_smul b t)
      (D.formallySmooth t) k _ _ _ hy]
    congr 1
    refine Subtype.ext ?_
    show EP.e (k + b) t ((∑ b' : {b : ℕ // (n i : ℤ) + b = N},
        mulTot D EP b'.1 (toForms gR (ω i b')) b'.2 (x i)) ⟨(p, k + b), hpb⟩ t) = _
    rw [hsum, mulTot_apply, mulTotAt_eq D EP k _ h (x i) p b (k + b) (Nat.add_comm b k) hpb
      (by push_cast at hpb; omega), e_mulAt]
  · rw [dite_eq_right h]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    have hS : (∑ b' : {b : ℕ // (n i : ℤ) + b = N},
        mulTot D EP b'.1 (toForms gR (ω i b')) b'.2 (x i)) ∈
          (filtration D EP).totStep (U := U) (k + 1) N := by
      refine sum_mulTot_mem_totStep D EP n x _ i fun b' => (lt_or_ge b'.1 k).imp (hω i b') ?_
      intro hb
      have := b'.2
      omega
    exact (mem_comapStep _ _ _ _ (D.ψ t).hom _ (EP.e_smul (k + b) t)).1
      (hS ⟨(p, k + b), hpb⟩ t)

omit [Fintype ι] [DecidableEq ι] in
open ShiftedSum in
/-- **The cup product map on the graded pieces, over an intersection**: the class of
`(∑_i x_i ∧ ω_i)` in `gr^k` is the image of `∑_{n_i + k = N} ω_i ⊗ x̄_i`. -/
theorem gradedTransport_cupMap {k : ℕ} {N : ℤ} {ω : MX gR n N}
    (hω : ω ∈ ShiftedSum.step gR n k N) (p b : ℕ) (hpb : (p : ℤ) + (k + b : ℕ) = N)
    (t : Fin (p + 1) → ι)
    (hmem : cupMap D EP n x N ω ⟨(p, k + b), hpb⟩ t ∈ (filtration D EP).step k (k + b) t) :
    gradedTransport D EP k (k + b) t (Submodule.Quotient.mk ⟨_, hmem⟩) =
      ∑ i : {i : I // (n i : ℤ) + k = N}, gradedOpen D EQ k b t
        ((toForms gR (ω i.1 ⟨k, i.2⟩) ⊗ₜ[A] xbar D EP n x EQ i.1 ⟨(p, b), by
          have := i.2; push_cast at hpb; omega⟩ t :
            ((tensorCoeff (formsN gR k) Q).X b).obj (op (inter U t)))) := by
  rw [gradedTransport_mk]
  have e : (⟨EP.e (k + b) t (cupMap D EP n x N ω ⟨(p, k + b), hpb⟩ t),
      (mem_comapStep _ _ _ _ (D.ψ t).hom _ (EP.e_smul (k + b) t)).1 hmem⟩ :
        step gR (D.φ t) (D.ψ t) (D.comp_φ t) k (k + b)) =
      ⟨∑ i, EP.e (k + b) t ((∑ b' : {b : ℕ // (n i : ℤ) + b = N},
        mulTot D EP b'.1 (toForms gR (ω i b')) b'.2 (x i)) ⟨(p, k + b), hpb⟩ t),
        Submodule.sum_mem _ fun i _ =>
          (mem_comapStep _ _ _ _ (D.ψ t).hom _ (EP.e_smul (k + b) t)).1
            (cupTerm_mem_totStep D EP n x hω i ⟨(p, k + b), hpb⟩ t)⟩ := by
    refine Subtype.ext ?_
    show EP.e (k + b) t (cupMap D EP n x N ω ⟨(p, k + b), hpb⟩ t) = _
    rw [cupMap_apply, Finset.sum_apply, Finset.sum_apply, map_sum]
  rw [e, mk_sum_step D (t := t) (s := Finset.univ) (hf := fun i =>
    (mem_comapStep _ _ _ _ (D.ψ t).hom _ (EP.e_smul (k + b) t)).1
      (cupTerm_mem_totStep D EP n x hω i ⟨(p, k + b), hpb⟩ t))]
  simp only [mk_cupTerm D EP n x EQ hω]
  exact sum_dite_subtype _ _

omit [Fintype ι] [DecidableEq ι] in
/-- `unitMap` sends the basis vector `1_i` to `x̄_i`. -/
theorem unitMap_single [DecidableEq I] (q : ℤ) (i : {i : I // (n i : ℤ) = q}) :
    unitMap D EP n x EQ q (Pi.single i (1 : A) : ∀ (_ : {i : I // (n i : ℤ) = q}), A) =
      reTot i.2 (xbar D EP n x EQ i.1) := by
  show ∑ i' : {i : I // (n i : ℤ) = q}, (Pi.single i (1 : A) :
    ∀ (_ : {i : I // (n i : ℤ) = q}), A) i' • reTot i'.2 (xbar D EP n x EQ i'.1) = _
  rw [Finset.sum_eq_single i (fun i' _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]

omit [Fintype ι] [DecidableEq ι] in
/-- `Ω^k_{A/R} ⊗ unitMap` sends `ν` placed in the summand `i` to `ν ⊗ x̄_i`. -/
theorem unitTensor_single [DecidableEq I] (k : ℕ) (N : ℤ) (i : {i : I // (n i : ℤ) + k = N})
    (ν : ⋀[A]^k ↑(CommRingCat.KaehlerDifferential gR)) :
    TensorProduct.map LinearMap.id (unitMap D EP n x EQ (N - k))
        ((ShiftedSum.tensorXEquiv gR n k N).symm (Pi.single i ν)) =
      (ν : formsN gR k) ⊗ₜ[A] reTot (by have := i.2; omega : (n i.1 : ℤ) = N - k)
        (xbar D EP n x EQ i.1) := by
  rw [ShiftedSum.tensorXEquiv_symm_single, TensorProduct.map_tmul, LinearMap.id_apply]
  exact congrArg _ (unitMap_single D EP n x EQ (N - k) ⟨i.1, _⟩)

include hx in
set_option maxRecDepth 8000 in
/-- **The cup product map on the graded pieces is `Ω^k_{A/R} ⊗` the map `1_i ↦ x̄_i`.** -/
theorem cupHom_graded_comm [DecidableEq I] (k : ℕ) :
    (CochainComplex.SubmoduleFiltration.forgetAb R).map
        (CochainComplex.SubmoduleFiltration.gradedMap (ShiftedSum.filtration gR n)
          ((filtration D EP).totFiltration (U := U)) (cupHom D EP n x hx)
          (cupHom_step_le D EP n x hx) k) ≫ (gradedIso D EP EQ k).hom =
      (ShiftedSum.gradedIso gR n k).hom ≫ (CochainComplex.SubmoduleFiltration.forgetAb A).map
        (CochainComplex.reindexMap
          (((MonoidalCategory.tensorLeft (formsN gR k)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (unitHom D EP n x hx EQ)) k) := by
  ext N z
  revert z
  intro (z : ((ShiftedSum.filtration gR n).graded k).X N)
  induction z using Submodule.Quotient.induction_on with | H ω =>
  revert ω
  intro (ω : (ShiftedSum.filtration gR n).step k N)
  refine (tensorTotEquiv U (formsN gR k) Q (N - k)).symm.symm.injective ?_
  show (tensorTotEquiv U (formsN gR k) Q (N - k)) ((tensorTotEquiv U (formsN gR k) Q (N - k)).symm
      ((gradedTensorData D EP EQ k).degreeEquiv N (Submodule.Quotient.mk
        ⟨cupMap D EP n x N ω.1, cupHom_step_le D EP n x hx k N
          ⟨ω.1, ω.2, cupHom_f_apply D EP n x hx N ω.1⟩⟩))) =
    tensorTotEquiv U (formsN gR k) Q (N - k) (TensorProduct.map LinearMap.id
      (unitMap D EP n x EQ (N - k)) ((ShiftedSum.tensorXEquiv gR n k N).symm
        (ShiftedSum.castX gR n k N (ShiftedSum.gradedProj gR n k N ω))))
  rw [LinearEquiv.apply_symm_apply]
  conv_rhs => rw [← Finset.univ_sum_single (ShiftedSum.castX gR n k N
    (ShiftedSum.gradedProj gR n k N ω))]
  simp only [map_sum]
  funext ⟨⟨p, b⟩, hpb⟩ t
  rw [Finset.sum_apply, Finset.sum_apply]
  show (gradedPiece D EP EQ k b t).symm _ = _
  rw [AddEquiv.symm_apply_eq, map_sum]
  refine (gradedTransport D EP k (k + b) t).injective ?_
  rw [map_sum]
  simp only
  have hpb' : (p : ℤ) + (k + b : ℕ) = N := by
    have h := hpb
    dsimp only at h
    push_cast
    omega
  convert gradedTransport_cupMap D EP n x EQ ω.2 p b hpb' t
    ((cupHom_step_le D EP n x hx k N ⟨ω.1, ω.2, cupHom_f_apply D EP n x hx N ω.1⟩)
      ⟨(p, k + b), hpb'⟩ t) using 3
  · rfl
  · rename_i i _
    rw [unitTensor_single]
    refine (gradedTransport_gradedPiece D EP EQ k b t _).trans (congrArg (gradedOpen D EQ k b t) ?_)
    exact congrFun (congrFun (tensorTotEquiv_tmul U (formsN gR k) Q (N - k) _ _) _) t

include hx in
/-- **The cup product map is a quasi-isomorphism once its graded zeroth piece is**: if the map
`⨁_i A[-n_i] → Tot(Č(U, Q))`, `1_i ↦ x̄_i`, is a quasi-isomorphism between K-flat complexes, then
the cup product map `⨁_i Ω^•_{A/R}[-n_i] → Tot(Č(U, P))`, `(ω_i)_i ↦ ∑_i x_i ∧ ω_i`, is a
quasi-isomorphism. -/
theorem quasiIso_cupHom [DecidableEq I] [QuasiIso (unitHom D EP n x hx EQ)]
    (hGM : CochainComplex.KFlat.{w, w} (ShiftedSum.unitComplex A n))
    (hGK : CochainComplex.KFlat.{w, w} (cechTot U Q)) :
    QuasiIso (cupHom D EP n x hx) :=
  CochainComplex.SubmoduleFiltration.quasiIso_of_graded_iso_tensor_of_kFlat
    (ShiftedSum.filtration gR n) ((filtration D EP).totFiltration (U := U)) (cupHom D EP n x hx)
    (cupHom_step_le D EP n x hx) (unitHom D EP n x hx EQ) hGM hGK (formsN gR)
    (ShiftedSum.gradedIso gR n) (gradedIso D EP EQ) (cupHom_graded_comm D EP n x hx EQ)

end Cech

end Stacks.KatzOda

end
