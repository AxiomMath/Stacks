module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechClasses

/-!
# The Čech cup product with a cochain of Čech degree zero, elementwise

Let `D` be a pairing of complexes of presheaves of `R`-modules `K`, `L` into `M` on a category with
finite products, and `W` a family of objects. The Alexander--Whitney cup product
`Tot(Č(W, K)) ⊗ Tot(Č(W, L)) ⟶ Tot(Č(W, M))` of the library
(`Stacks.Cech.LinearCupProduct.cechCupProduct`) has, against a right factor of Čech degree `0`,
no sign and no restriction of the left factor: on the summand of Čech degree `r` it pairs a
cochain `z` with the restriction of `y` from the last vertex,

`(z ∪ y)_t = μ(z_t, y_{t_r}|_{U_t})`.

This file states that formula on the elementwise total Čech complexes
(`Stacks.CategoryTheory.CechComplex.cechTot`), through the comparison
`Stacks.CategoryTheory.CechComplex.totalCechIso`.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.rightMul`: right multiplication of the elementwise total
  complex by a Čech `0`-cochain, for a pairing of the coefficients.

## Main results

* `Stacks.CategoryTheory.CechComplex.totalTo_ιTensorSource_cechCupProduct_zero`: on a single
  summand, the cup product with a Čech `0`-cochain is right multiplication by it.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open Stacks.Cech.LinearCupProduct (PresheafModules cechCochains cechCochainsMap
  totalCechComplexFunctor ιTotalCech ιTotalCechTo ComplexPairing cechCupProduct ιTensorSource
  ιTensorSource_eq ιTensorSource_cechCupProductDegree cechCupProductSummand_eq ιPairingTarget
  cechAlexanderWhitney cechAlexanderWhitney_comp_π cechCochainsMap_comp_π)

universe u uC vC

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

attribute [local implicit_reducible] CategoryTheory.cechComplexFunctor
  HomologicalComplex₂.ofGradedObject
  HomologicalComplex₂.flip
  HomologicalComplex₂.flipFunctor
  ComplexShape.Embedding.extendFunctor
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
  CategoryTheory.Functor.mapBifunctorHomologicalComplexObj
  CategoryTheory.GradedObject.mapBifunctor
  HomologicalComplex₂.totalFunctor

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] {ι : Type u} (W : ι → C)
  {R : Type u} [CommRing R] {P Q T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ}
  (μc : ∀ (a b c : ℕ), a + b = c → ∀ V : Cᵒᵖ,
    (P.X a).obj V →+ (Q.X b).obj V →+ (T.X c).obj V)

/-- **Right multiplication by a Čech `0`-cochain**: on the summand of Čech degree `r` and
coefficient degree `c ≥ b`, pair the component of Čech degree `r` and coefficient degree `c - b`
with the restriction of `y` from the last vertex; zero for `c < b`. -/
def rightMul (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N) (z : TotX W P m) :
    TotX W T N := fun j =>
  if hc : b ≤ j.1.2 then fun t =>
    μc (j.1.2 - b) b j.1.2 (Nat.sub_add_cancel hc) (op (inter W t))
      (z ⟨(j.1.1, j.1.2 - b), by have := j.2; omega⟩ t)
      (cres W (Q.X b) (fun _ : Fin 1 => Fin.last j.1.1) t (y _))
  else 0

/-- Right multiplication on a summand of coefficient degree `c ≥ b`. -/
theorem rightMul_apply_of_le (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N)
    (z : TotX W P m) (r c : ℕ) (hj : (r : ℤ) + c = N) (hc : b ≤ c) (t : Fin (r + 1) → ι) :
    rightMul W μc b y hN z ⟨(r, c), hj⟩ t =
      μc (c - b) b c (Nat.sub_add_cancel hc) (op (inter W t))
        (z ⟨(r, c - b), by omega⟩ t) (cres W (Q.X b) (fun _ : Fin 1 => Fin.last r) t (y _)) := by
  simp only [rightMul, dite_eq_left hc]

/-- Right multiplication vanishes on a summand of coefficient degree `c < b`. -/
theorem rightMul_apply_of_lt (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N)
    (z : TotX W P m) (r c : ℕ) (hj : (r : ℤ) + c = N) (hc : c < b) :
    rightMul W μc b y hN z ⟨(r, c), hj⟩ = 0 := by
  simp only [rightMul, dite_eq_right (Nat.not_le.mpr hc)]


/-- Right multiplication sends `0` to `0`. -/
theorem rightMul_zero (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N) :
    rightMul W μc b y hN 0 = 0 := by
  funext j
  by_cases hc : b ≤ j.1.2 <;> simp [rightMul, hc]
  rfl

/-- Right multiplication is additive. -/
theorem rightMul_add (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N)
    (z z' : TotX W P m) :
    rightMul W μc b y hN (z + z') = rightMul W μc b y hN z + rightMul W μc b y hN z' := by
  funext j
  by_cases hc : b ≤ j.1.2 <;> simp [rightMul, hc]
  rfl

/-- Right multiplication commutes with finite sums. -/
theorem rightMul_sum (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N)
    {J : Type*} (s : Finset J) (z : J → TotX W P m) :
    rightMul W μc b y hN (∑ j ∈ s, z j) = ∑ j ∈ s, rightMul W μc b y hN (z j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, rightMul_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, rightMul_add, ih]

/-- Right multiplication of a single summand of bidegree `(r, a)` is the single summand of bidegree
`(r, a + b)` obtained by pairing pointwise with the restriction of `y` from the last vertex. -/
theorem rightMul_totSingle (b : ℕ) (y : Cochain W (Q.X b) 0) {m N : ℤ} (hN : m + b = N)
    (r a : ℕ) (h : (r : ℤ) + a = m) (c : Cochain W (P.X a) r) :
    rightMul W μc b y hN (totSingle W P m r a h c) =
      totSingle W T N r (a + b) (by push_cast; omega) (fun t =>
        μc a b (a + b) rfl (op (inter W t)) (c t)
          (cres W (Q.X b) (fun _ : Fin 1 => Fin.last r) t (y _))) := by
  funext ⟨⟨r', c'⟩, hj⟩
  by_cases hc : b ≤ c'
  · funext t
    rw [rightMul_apply_of_le W μc b y hN _ r' c' hj hc]
    by_cases hrc : r' = r ∧ c' = a + b
    · obtain ⟨rfl, rfl⟩ := hrc
      rw [totSingle_apply_self]
      have key : ∀ (a' : ℕ) (e : a' = a) (h1 : a' + b = a + b) (h2 : (r' : ℤ) + a' = m),
          μc a' b (a + b) h1 (op (inter W t)) (totSingle W P m r' a h c ⟨(r', a'), h2⟩ t)
            (cres W (Q.X b) (fun _ : Fin 1 => Fin.last r') t (y _)) =
          μc a b (a + b) rfl (op (inter W t)) (c t)
            (cres W (Q.X b) (fun _ : Fin 1 => Fin.last r') t (y _)) := by
        rintro _ rfl _ _
        rw [totSingle_apply_self]
      exact key (a + b - b) (by omega) _ _
    · rw [totSingle_apply_of_ne W T N _ _ _ _ _ _ _ hrc,
        totSingle_apply_of_ne W P m _ _ _ _ _ _ _ (by omega)]
      simp only [Pi.zero_apply, map_zero, AddMonoidHom.zero_apply]
  · rw [rightMul_apply_of_lt W μc b y hN _ r' c' hj (by omega),
      totSingle_apply_of_ne W T N _ _ _ _ _ _ _ (by omega)]


/-! ### The cup product against a summand of Čech degree zero -/

attribute [local instance] totIndexFintype

variable {K : CochainComplex (PresheafModules.{u} C R) ℤ} (eK : ∀ b : ℕ, K.X (b : ℤ) ≅ P.X b)

/-- The comparison from the elementwise total complex, on a single summand. -/
theorem totalFrom_totSingle (n : ℤ) (p b : ℕ) (h : (p : ℤ) + b = n) (y : Cochain W (P.X b) p) :
    (totalFrom W K P eK n).hom (totSingle W P n p b h y) =
      (ιTotalCechTo W R K p (b : ℤ) n h).hom ((cechCochainsMap W R (eK b).inv p).hom
        ((cochainsIso W (P.X b) p).inv.hom y)) := by
  rw [totalFrom_apply, Finset.sum_eq_single (⟨(p, b), h⟩ : TotIndex n)]
  · rw [totSingle_apply_self]
  · intro i _ hi
    rw [totSingle_apply_ne W P n p b h y i hi]
    simp
  · intro h'
    exact absurd (Finset.mem_univ _) h'


variable {L M : CochainComplex (PresheafModules.{u} C R) ℤ} (D : ComplexPairing R K L M)

/-- **Against a summand of Čech degree `0` the cup product has no sign**: it is the unsigned
Alexander--Whitney product. -/
theorem ιTensorSource_cechCupProduct_zero (r : ℕ) (a b N : ℤ)
    (h : ((r : ℤ) + a) + (((0 : ℕ) : ℤ) + b) = N) :
    ιTensorSource W R K L r 0 a b N h ≫ (cechCupProduct W R D).f N =
      cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r 0 ≫
        ιTotalCechTo W R M r (a + b) N (by push_cast at h; omega) := by
  refine (ιTensorSource_cechCupProductDegree W R D r 0 a b N h).trans
    ((cechCupProductSummand_eq W R D r 0 a b N h).trans ?_)
  simp only [CharP.cast_eq_zero, mul_zero, Int.negOnePow_zero, Units.val_one, one_smul]
  rfl

/-- **The Alexander--Whitney product with a cochain of Čech degree `0`, componentwise**: the left
factor is not restricted (its front face is the whole tuple) and the right factor is restricted
from the last vertex. -/
theorem π_cechAlexanderWhitney_zero {P' Q' T' : PresheafModules.{u} C R}
    (μ : Stacks.Cech.LinearCupProduct.Pairing.{u} R P' Q' T') (r : ℕ)
    (c : cechCochains W R P' r) (d : cechCochains W R Q' 0) (t : Fin (r + 1) → ι) :
    (π W T' r t).hom ((cechAlexanderWhitney W R μ r 0).hom (c ⊗ₜ d)) =
      (μ.app (op (inter W t))).hom ((π W P' r t).hom c ⊗ₜ
        (Q'.map (interMap W t (Stacks.Cech.LinearCupProduct.backIdx r 0 r (by omega))).op).hom
          ((π W Q' 0 (t ∘ Stacks.Cech.LinearCupProduct.backIdx r 0 r (by omega))).hom d)) := by
  have h := ConcreteCategory.congr_hom (cechAlexanderWhitney_comp_π W R μ r 0 t) (c ⊗ₜ d)
  refine h.trans ?_
  change (μ.app (op (inter W t))).hom
      ((P'.map (interMap W t (Stacks.Cech.LinearCupProduct.frontIdx r (r + 0) (by omega))).op).hom
          ((π W P' r (t ∘ Stacks.Cech.LinearCupProduct.frontIdx r (r + 0) (by omega))).hom c) ⊗ₜ
        (Q'.map (interMap W t
          (Stacks.Cech.LinearCupProduct.backIdx r 0 (r + 0) (by omega))).op).hom
          ((π W Q' 0 (t ∘ Stacks.Cech.LinearCupProduct.backIdx r 0 (r + 0) (by omega))).hom d)) = _
  have hf : interMap W t (Stacks.Cech.LinearCupProduct.frontIdx r (r + 0) (by omega)) =
      interMap W t id := rfl
  rw [hf, interMap_id]
  have hid := ConcreteCategory.congr_hom (P'.map_id (op (inter W t))) ((π W P' r t).hom c)
  congr 2

/-- The back face of length `0` of an `r`-simplex is its last vertex. -/
theorem backIdx_zero_eq_last (r : ℕ) (h : r + 0 ≤ r) :
    Stacks.Cech.LinearCupProduct.backIdx r 0 r h = fun _ : Fin 1 => Fin.last r := by
  funext i
  ext
  have hi : (i : ℕ) = 0 := by omega
  rw [Stacks.Cech.LinearCupProduct.backIdx_val, hi, Fin.val_last, add_zero]

variable (eL : ∀ b : ℕ, L.X (b : ℤ) ≅ Q.X b) (eM : ∀ b : ℕ, M.X (b : ℤ) ≅ T.X b)

/-- **The cup product with a cochain of Čech degree `0`, on a single summand**, read on the
elementwise total complexes: when the coefficient pairing `D` is `μc` through the
identifications `eK`, `eL`, `eM`, the cup product of a cochain `c` of bidegree `(r, a)` with a
Čech `0`-cochain `y` of coefficient degree `b` is right multiplication of `c` by `y`. -/
theorem totalTo_ιTensorSource_cechCupProduct_zero
    (hμ : ∀ (a b : ℕ) (V : Cᵒᵖ) (x : (K.X a).obj V) (y : (L.X b).obj V),
      ((eM (a + b)).hom.app V).hom (((D.μ a b (a + b) rfl).app V).hom (x ⊗ₜ y)) =
        μc a b (a + b) rfl V (((eK a).hom.app V).hom x) (((eL b).hom.app V).hom y))
    (r a b : ℕ) (N : ℤ) (h : ((r : ℤ) + (a : ℤ)) + (((0 : ℕ) : ℤ) + (b : ℤ)) = N)
    (c : Cochain W (P.X a) r) (y : Cochain W (Q.X b) 0) :
    (totalTo W M T eM N).hom ((ιTensorSource W R K L r 0 a b N h ≫
        (cechCupProduct W R D).f N).hom
      ((cechCochainsMap W R (eK a).inv r).hom ((cochainsIso W (P.X a) r).inv.hom c) ⊗ₜ
        (cechCochainsMap W R (eL b).inv 0).hom ((cochainsIso W (Q.X b) 0).inv.hom y))) =
      rightMul W μc b y (m := (r : ℤ) + a) (by push_cast at h; omega)
        (totSingle W P _ r a rfl c) := by
  rw [ιTensorSource_cechCupProduct_zero, rightMul_totSingle]
  have h3 := ConcreteCategory.congr_hom
    (ιTotalCechTo_totalTo W M T eM N r ((a : ℤ) + b) (by push_cast at h; omega))
    ((cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r 0).hom
      ((cechCochainsMap W R (eK a).inv r).hom ((cochainsIso W (P.X a) r).inv.hom c) ⊗ₜ
        (cechCochainsMap W R (eL b).inv 0).hom ((cochainsIso W (Q.X b) 0).inv.hom y)))
  rw [ConcreteCategory.comp_apply] at h3
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  refine h3.trans ?_
  change (totSingle W T N r (a + b) _) ((cochainsIso W (T.X (a + b)) r).hom
    ((cechCochainsMap W R (eM (a + b)).hom r).hom _)) = _
  congr 1
  funext t
  rw [cochainsIso_hom_apply]
  have hπ : ∀ {A B : PresheafModules.{u} C R} (f : A ⟶ B) (n : ℕ) (s : Fin (n + 1) → ι)
      (x : cechCochains W R A n), (π W B n s).hom ((cechCochainsMap W R f n).hom x) =
        (f.app (op (inter W s))).hom ((π W A n s).hom x) := fun f n s x =>
    ConcreteCategory.congr_hom (cechCochainsMap_comp_π W R f n s) x
  rw [hπ, π_cechAlexanderWhitney_zero, hπ, hπ, π_cochainsIso_inv_apply, π_cochainsIso_inv_apply]
  have hnat := ConcreteCategory.congr_hom ((eL b).inv.naturality
    (interMap W t (Stacks.Cech.LinearCupProduct.backIdx r 0 r (by omega))).op)
    (y (t ∘ Stacks.Cech.LinearCupProduct.backIdx r 0 r (by omega)))
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hnat
  rw [← hnat, hμ]
  have e1 := Iso.inv_hom_id_app_apply (eK a) (op (inter W t)) (c t)
  have e2 := Iso.inv_hom_id_app_apply (eL b) (op (inter W t))
    (((Q.X b).map (interMap W t (Stacks.Cech.LinearCupProduct.backIdx r 0 r (by omega))).op)
      (y (t ∘ Stacks.Cech.LinearCupProduct.backIdx r 0 r (by omega))))
  refine (congrArg₂ (fun u v => μc a b (a + b) rfl (op (inter W t)) u v) e1 e2).trans ?_
  rw [backIdx_zero_eq_last]

end

end Stacks.CategoryTheory.CechComplex

end
