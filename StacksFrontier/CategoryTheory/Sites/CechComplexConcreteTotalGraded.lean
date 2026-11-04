module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalFiltration
public import StacksFrontier.Algebra.Homology.FilteredTensorGradedQuasiIso
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Tensor products and graded pieces of total Čech complexes

Let `U : ι → C` be a finite family of objects of a category with finite products. This file
supplies two identifications for the elementwise total Čech complex `Tot(Č(U, -))` of
`StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotal`.

* **Tensor products.** For a module `N` over a commutative ring `A` and a complex `Q` of
  presheaves of `A`-modules, `N ⊗_A Tot(Č(U, Q)) ≅ Tot(Č(U, N ⊗_A Q))`: each term of the total
  complex is a finite product, and tensor products commute with finite products.
* **Graded pieces.** Let `F` be a filtration of a complex `P` of presheaves of modules on the Čech
  intersections (`Stacks.CategoryTheory.CechComplex.InterFiltration`). If the graded pieces
  `F^k P^{k+b}(U_t) / F^{k+1} P^{k+b}(U_t)` are identified with `N ⊗_A Q^b(U_t)`, compatibly with
  the restrictions along the face maps and with the differentials, then `gr^k Tot(Č(U, P))` is
  `Tot(Č(U, N ⊗_A Q))` moved up by `k` degrees, as complexes of abelian groups.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.tensorCoeff`: the complex of presheaves `N ⊗_A Q`.
* `Stacks.CategoryTheory.CechComplex.tensorTotIso`: `N ⊗_A Tot(Č(U, Q)) ≅ Tot(Č(U, N ⊗_A Q))`.
* `Stacks.CategoryTheory.CechComplex.GradedTensorData`: the componentwise identification of the
  graded pieces.
* `Stacks.CategoryTheory.CechComplex.GradedTensorData.gradedTotIso`: the resulting identification
  of `gr^k Tot(Č(U, P))`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TensorProduct

universe w v u r

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)

/-! ### Finiteness of the degrees -/

/-- Each degree of the total complex has finitely many index pairs `(p, a)`. -/
instance (n : ℤ) : Fintype (TotIndex n) :=
  haveI := finite_totIndex n
  Fintype.ofFinite _

/-! ### Tensoring the coefficients -/

variable {A : Type w} [CommRing A] (N : ModuleCat.{w} A)
  (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} A) ℕ)

/-- **The complex of presheaves `N ⊗_A Q`**: in degree `a` the presheaf `V ↦ N ⊗_A Q^a(V)`. -/
abbrev tensorCoeff : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} A) ℕ where
  X a := Q.X a ⋙ tensorLeft N
  d a b := Functor.whiskerRight (Q.d a b) (tensorLeft N)
  shape a b h := by
    rw [Q.shape a b h]
    ext V : 2
    exact MonoidalPreadditive.whiskerLeft_zero
  d_comp_d' a b c _ _ := by
    rw [← Functor.whiskerRight_comp, Q.d_comp_d]
    ext V : 2
    exact MonoidalPreadditive.whiskerLeft_zero

omit [HasFiniteProducts C] in
/-- The differential of `N ⊗_A Q` acts on a pure tensor through its second factor. -/
theorem tensorCoeff_d_app_tmul (a b : ℕ) (V : Cᵒᵖ) (ν : N) (y : (Q.X a).obj V) :
    ((tensorCoeff N Q).d a b).app V (ν ⊗ₜ y) = ν ⊗ₜ (Q.d a b).app V y :=
  rfl

omit [HasFiniteProducts C] in
/-- The restriction maps of `N ⊗_A Q` act on a pure tensor through its second factor. -/
theorem tensorCoeff_map_tmul (a : ℕ) {V V' : Cᵒᵖ} (g : V ⟶ V') (ν : N) (y : (Q.X a).obj V) :
    ((tensorCoeff N Q).X a).map g (ν ⊗ₜ y) = ν ⊗ₜ (Q.X a).map g y :=
  rfl

section Finite

variable [Fintype ι] [DecidableEq ι]

/-- **The tensor product with a total Čech complex, degreewise**: each term is a finite product,
and tensor products commute with finite products. -/
def tensorTotEquiv (n : ℤ) : N ⊗[A] TotX U Q n ≃ₗ[A] TotX U (tensorCoeff N Q) n :=
  (TensorProduct.piRight A A N (fun i : TotIndex n => Cochain U (Q.X i.1.2) i.1.1)).trans
    (LinearEquiv.piCongrRight fun i =>
      TensorProduct.piRight A A N (fun t : Fin (i.1.1 + 1) → ι => (Q.X i.1.2).obj (op (inter U t))))

/-- `tensorTotEquiv` sends `ν ⊗ x` to the cochain with components `ν ⊗ x_{i,t}`. -/
theorem tensorTotEquiv_tmul (n : ℤ) (ν : N) (x : TotX U Q n) :
    tensorTotEquiv U N Q n (ν ⊗ₜ x) = fun i t => ν ⊗ₜ x i t :=
  rfl

/-- `tensorTotEquiv` commutes with the differentials of the two total complexes. -/
theorem tensorTotEquiv_comm (n m : ℤ) (h : n + 1 = m) (z : N ⊗[A] TotX U Q n) :
    tensorTotEquiv U N Q m ((TensorProduct.map LinearMap.id (totDTo U Q n m h)) z) =
      totDTo U (tensorCoeff N Q) n m h (tensorTotEquiv U N Q n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul ν x =>
    rw [TensorProduct.map_tmul, LinearMap.id_apply, tensorTotEquiv_tmul, tensorTotEquiv_tmul]
    funext ⟨⟨p, a⟩, hpa⟩ t
    simp only [totDTo_apply]
    rcases p with _ | q <;> rcases a with _ | b <;>
      simp only [totDCech_zero, totDCech_succ, totDCoef_zero, totDCoef_succ, add_zero,
        zero_add, tmul_zero, tmul_add, Pi.smul_apply, tmul_smul, cochainMap_apply, cechD_apply,
        tmul_sum, cres, Pi.add_apply, Pi.zero_apply] <;> rfl

/-- **`N ⊗_A Tot(Č(U, Q)) ≅ Tot(Č(U, N ⊗_A Q))`** for a finite family `U`. -/
def tensorTotIso :
    ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj (cechTot U Q) ≅
      cechTot U (tensorCoeff N Q) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tensorTotEquiv U N Q n).toModuleIso)
    (by
      rintro n m (h : n + 1 = m)
      refine ModuleCat.hom_ext (TensorProduct.ext' fun ν x => ?_)
      change ((cechTot U (tensorCoeff N Q)).d n m).hom (tensorTotEquiv U N Q n (ν ⊗ₜ x)) =
        tensorTotEquiv U N Q m ((N ◁ (cechTot U Q).d n m) (ν ⊗ₜ x))
      rw [ModuleCat.MonoidalCategory.whiskerLeft_apply, cechTot_d_apply' U (tensorCoeff N Q) h,
        cechTot_d_apply' U Q h]
      have := tensorTotEquiv_comm U N Q n m h (ν ⊗ₜ x)
      rw [TensorProduct.map_tmul, LinearMap.id_apply] at this
      exact this.symm)

/-- In degree `n`, `tensorTotIso` sends `ν ⊗ x` to the cochain with components `ν ⊗ x_{i,t}`. -/
theorem tensorTotIso_hom_f_tmul (n : ℤ) (ν : N) (x : TotX U Q n) :
    ((tensorTotIso U N Q).hom.f n).hom (ν ⊗ₜ x) = fun i t => ν ⊗ₜ x i t :=
  tensorTotEquiv_tmul U N Q n ν x

end Finite

/-! ### Graded pieces -/

namespace InterFiltration

variable {U} {R : Type w} [Ring R] {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  (F : InterFiltration U P)

/-- The restriction along a face map, on the graded pieces of the coefficients. -/
def gradedCres (k a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)) :
    F.GradedValue (U := U) k a (t ∘ Fin.succAbove j) →ₗ[R] F.GradedValue (U := U) k a t :=
  Submodule.mapQ _ _
    ((cres U (P.X a) (Fin.succAbove j) t).restrict fun _ hy => F.cres_mem k a t j hy)
    fun _ hy => F.cres_mem (k + 1) a t j hy

/-- `gradedCres` sends the class of an element of the `k`-th step to the class of its
restriction. -/
theorem gradedCres_mk (k a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (y : F.step k a (t ∘ Fin.succAbove j)) :
    F.gradedCres k a t j (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨cres U (P.X a) (Fin.succAbove j) t y, F.cres_mem k a t j y.2⟩ :=
  rfl

/-- The differential, on the graded pieces of the coefficients. -/
def gradedD (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) :
    F.GradedValue (U := U) k a t →ₗ[R] F.GradedValue (U := U) k (a + 1) t :=
  Submodule.mapQ _ _
    (((P.d a (a + 1)).app (op (inter U t))).hom.restrict fun y hy => F.d_le k a t ⟨y, hy, rfl⟩)
    fun y hy => F.d_le (k + 1) a t ⟨y, hy, rfl⟩

/-- `gradedD` sends the class of an element of the `k`-th step to the class of its image under
the differential. -/
theorem gradedD_mk (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : F.step k a t) :
    F.gradedD k a t (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ⟨((P.d a (a + 1)).app (op (inter U t))).hom y,
        F.d_le k a t ⟨y, y.2, rfl⟩⟩ :=
  rfl

/-- An element of the `k`-th step in degree `a < k` vanishes. -/
theorem eq_zero_of_mem_step {k a : ℕ} (h : a < k) {m : ℕ} {t : Fin (m + 1) → ι}
    {y : (P.X a).obj (op (inter U t))} (hy : y ∈ F.step k a t) : y = 0 := by
  rwa [F.step_eq_bot k a t h, Submodule.mem_bot] at hy

/-- The `k`-th graded piece in degree `a < k` is trivial. -/
theorem subsingleton_gradedValue {k a : ℕ} (h : a < k) {m : ℕ} (t : Fin (m + 1) → ι) :
    Subsingleton (F.GradedValue (U := U) k a t) := by
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with | H x =>
  induction y using Submodule.Quotient.induction_on with | H y =>
  congr 1
  exact Subtype.ext ((F.eq_zero_of_mem_step h x.2).trans (F.eq_zero_of_mem_step h y.2).symm)


/-- In the `k`-th graded piece, the class of the Čech differential `(δs)_t` is the alternating
sum over the face maps of the restrictions of the classes of the components of `s`. -/
theorem mk_cechD (k a q : ℕ) {s : Cochain U (P.X a) q} (hs : ∀ t, s t ∈ F.step k a t)
    (t : Fin (q + 2) → ι) :
    (Submodule.Quotient.mk ⟨cechD U (P.X a) q s t, F.cechD_mem k a q hs t⟩ :
        F.GradedValue (U := U) k a t) =
      ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        F.gradedCres k a t j (Submodule.Quotient.mk ⟨s (t ∘ Fin.succAbove j), hs _⟩) := by
  have e : (⟨cechD U (P.X a) q s t, F.cechD_mem k a q hs t⟩ : F.step k a t) =
      ∑ j : Fin (q + 2), ((-1 : ℤ) ^ (j : ℕ)) •
        (⟨cres U (P.X a) (Fin.succAbove j) t (s (t ∘ Fin.succAbove j)),
          F.cres_mem k a t j (hs _)⟩ : F.step k a t) :=
    Subtype.ext (by simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower]; rfl)
  rw [e, ← Submodule.mkQ_apply, map_sum]
  simp only [map_zsmul, Submodule.mkQ_apply, gradedCres_mk]

/-- In the `k`-th graded piece, the class of `e • d(s_t)` is `e` times `gradedD` of the class of
`s_t`. -/
theorem mk_zsmul_cochainMap_d (k a q : ℕ) (e : ℤ) {s : Cochain U (P.X a) q}
    (hs : ∀ t, s t ∈ F.step k a t) (t : Fin (q + 1) → ι) :
    (Submodule.Quotient.mk ⟨e • cochainMap U (P.d a (a + 1)) q s t,
        Submodule.smul_of_tower_mem _ e (F.d_mem k a q hs t)⟩ :
        F.GradedValue (U := U) k (a + 1) t) =
      e • F.gradedD k a t (Submodule.Quotient.mk ⟨s t, hs t⟩) := by
  rw [gradedD_mk, ← Submodule.Quotient.mk_smul]
  rfl

/-- For an element of the `k`-th step of the total complex, the part of its total differential
coming from the differential of the coefficients vanishes in coefficient degree `k`. -/
theorem totDCoef_bottom {k : ℕ} {n : ℤ} {y : TotX U P n} (hy : y ∈ F.totStep k n) (p : ℕ)
    (h : (p : ℤ) + k = n + 1) : totDCoef U P y p k h = 0 := by
  rcases k with _ | k
  · rfl
  · rw [totDCoef_succ]
    have hz : y ⟨(p, k), by push_cast at h; omega⟩ = 0 :=
      funext fun t => F.eq_zero_of_mem_step (Nat.lt_succ_self k) (hy _ t)
    rw [hz]
    funext t
    simp

end InterFiltration

variable {R : Type w} [Ring R] {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}

/-- **The graded pieces of a filtration of the coefficients as tensor products**: identifications
`N ⊗_A Q^b(U_t) ≅ F^k P^{k+b}(U_t) / F^{k+1} P^{k+b}(U_t)` over the Čech intersections, compatible
with the restrictions along the face maps and with the differentials. -/
structure GradedTensorData (F : InterFiltration U P) (k : ℕ) where
  /-- The identification over the intersection selected by `t`, in degree `b`. -/
  Φ : ∀ (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    ((tensorCoeff N Q).X b).obj (op (inter U t)) ≃+ F.GradedValue (U := U) k (k + b) t
  /-- The identifications commute with the restrictions along the face maps. -/
  map_cres : ∀ (b : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (z : ((tensorCoeff N Q).X b).obj (op (inter U (t ∘ Fin.succAbove j)))),
    Φ b t (cres U ((tensorCoeff N Q).X b) (Fin.succAbove j) t z) =
      F.gradedCres k (k + b) t j (Φ b (t ∘ Fin.succAbove j) z)
  /-- The identifications commute with the differentials. -/
  map_d : ∀ (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (z : ((tensorCoeff N Q).X b).obj (op (inter U t))),
    Φ (b + 1) t (((tensorCoeff N Q).d b (b + 1)).app (op (inter U t)) z) =
      F.gradedD k (k + b) t (Φ b t z)

namespace GradedTensorData

variable {U N Q} {F : InterFiltration U P} {k : ℕ} (D : GradedTensorData U N Q F k)

/-- The index `(p, k + b)` of degree `n` corresponding to the index `(p, b)` of degree `n - k`. -/
abbrev upIndex {n : ℤ} (j : TotIndex (n - k)) : TotIndex n :=
  ⟨(j.1.1, k + j.1.2), by have := j.2; push_cast; omega⟩

/-- The componentwise identification of the graded pieces, in degree `n`. -/
def gradedMap (n : ℤ) :
    (∀ (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι), F.GradedValue (U := U) k i.1.2 t) →+
      TotX U (tensorCoeff N Q) (n - k) where
  toFun x j t := (D.Φ j.1.2 t).symm (x (upIndex j) t)
  map_zero' := by funext j t; exact map_zero _
  map_add' x y := by funext j t; exact map_add _ _ _

/-- The component of `gradedMap` at the index `j` is the inverse identification applied to the
component at `upIndex j`. -/
theorem gradedMap_apply (n : ℤ)
    (x : ∀ (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι), F.GradedValue (U := U) k i.1.2 t)
    (j : TotIndex (n - k)) (t : Fin (j.1.1 + 1) → ι) :
    D.gradedMap n x j t = (D.Φ j.1.2 t).symm (x (upIndex j) t) :=
  rfl

/-- `gradedMap` is injective. -/
theorem gradedMap_injective (n : ℤ) : Function.Injective (D.gradedMap n) := by
  intro x y hxy
  funext ⟨⟨p, a⟩, h⟩ t
  by_cases ha : a < k
  · have := F.subsingleton_gradedValue ha t
    exact Subsingleton.elim _ _
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 ha)
    have := congrFun (congrFun hxy ⟨(p, b), by push_cast at h ⊢; omega⟩) t
    exact (D.Φ b t).symm.injective this

/-- `gradedMap` is surjective. -/
theorem gradedMap_surjective (n : ℤ) : Function.Surjective (D.gradedMap n) := by
  intro z
  classical
  refine ⟨fun i t => if h : k ≤ i.1.2 then
    (Nat.add_sub_cancel' h) ▸ D.Φ (i.1.2 - k) t (z ⟨(i.1.1, i.1.2 - k), by
      have := i.2; push_cast [Nat.cast_sub h]; omega⟩ t) else 0, ?_⟩
  funext ⟨⟨p, b⟩, hpb⟩ t
  rw [gradedMap_apply]
  simp only [upIndex, Nat.le_add_right, dite_true]
  have key : ∀ (c : ℕ) (hc : c = b) (e : k + c = k + b)
      (h' : ((p, c).1 : ℤ) + ((p, c).2 : ℤ) = n - k),
      (D.Φ b t).symm (e ▸ D.Φ c t (z ⟨(p, c), h'⟩ t)) = z ⟨(p, b), hpb⟩ t := by
    rintro c rfl e h'
    simp
  exact key (k + b - k) (by omega) _ _

/-- The inverse identifications commute with the restrictions along the face maps. -/
theorem symm_gradedCres (b : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (g : F.GradedValue (U := U) k (k + b) (t ∘ Fin.succAbove j)) :
    (D.Φ b t).symm (F.gradedCres k (k + b) t j g) =
      cres U ((tensorCoeff N Q).X b) (Fin.succAbove j) t
        ((D.Φ b (t ∘ Fin.succAbove j)).symm g) := by
  rw [AddEquiv.symm_apply_eq, D.map_cres, AddEquiv.apply_symm_apply]

/-- The inverse identifications commute with the differentials. -/
theorem symm_gradedD (b : ℕ) {m : ℕ} (t : Fin (m + 1) → ι)
    (g : F.GradedValue (U := U) k (k + b) t) :
    (D.Φ (b + 1) t).symm (F.gradedD k (k + b) t g) =
      ((tensorCoeff N Q).d b (b + 1)).app (op (inter U t)) ((D.Φ b t).symm g) := by
  rw [AddEquiv.symm_apply_eq, D.map_d, AddEquiv.apply_symm_apply]

/-- The identification of the graded pieces, in degree `n`:
`(gr^k Tot(Č(U, P)))^n ≅ Tot(Č(U, N ⊗_A Q))^{n-k}`. -/
def degreeEquiv (n : ℤ) :
    ((F.totFiltration (U := U)).graded k).X n ≃+ TotX U (tensorCoeff N Q) (n - k) :=
  (F.gradedXEquiv (U := U) k n).toAddEquiv.trans
    (AddEquiv.ofBijective (D.gradedMap n) ⟨D.gradedMap_injective n, D.gradedMap_surjective n⟩)

/-- At the index `j`, `degreeEquiv` sends the class of an element `y` of the `k`-th step to the
inverse identification of the class of the component of `y` at `upIndex j`. -/
theorem degreeEquiv_mk (n : ℤ) (y : F.totStep (U := U) k n) (j : TotIndex (n - k))
    (t : Fin (j.1.1 + 1) → ι) :
    D.degreeEquiv n (Submodule.Quotient.mk y) j t =
      (D.Φ j.1.2 t).symm
        (Submodule.Quotient.mk ⟨(y : TotX U P n) (upIndex j) t, y.2 (upIndex j) t⟩) :=
  rfl

/-- `degreeEquiv` sends the class of an element `y` of the `k`-th step to the cochain whose
component at `j` is the inverse identification of the class of the component of `y` at
`upIndex j`. -/
theorem degreeEquiv_mk' (n : ℤ) (y : F.totStep (U := U) k n) :
    D.degreeEquiv n (Submodule.Quotient.mk y) = fun j t =>
      (D.Φ j.1.2 t).symm
        (Submodule.Quotient.mk ⟨(y : TotX U P n) (upIndex j) t, y.2 (upIndex j) t⟩) :=
  rfl

/-- The differential of `gr^k Tot(Č(U, P))` sends the class of `y` to the class of the total
differential of `y`. -/
theorem graded_d_mk (n m : ℤ) (h : n + 1 = m) (y : F.totStep (U := U) k n) :
    ((F.totFiltration (U := U)).graded k).d n m (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (⟨totDTo U P n m h y, by
        rw [← cechTot_d_apply' U P h]
        exact (F.totFiltration (U := U)).map_d_le k n m (Submodule.mem_map_of_mem y.2)⟩ :
          F.totStep (U := U) k m) := by
  show Submodule.Quotient.mk (⟨((cechTot U P).d n m).hom y, _⟩ : F.totStep (U := U) k m) = _
  congr 2
  exact cechTot_d_apply' U P h y

/-- `degreeEquiv` commutes with the differentials. -/
theorem degreeEquiv_comm (n m : ℤ) (h : n + 1 = m)
    (x : ((F.totFiltration (U := U)).graded k).X n) :
    D.degreeEquiv m (((F.totFiltration (U := U)).graded k).d n m x) =
      totDTo U (tensorCoeff N Q) (n - k) (m - k) (by omega) (D.degreeEquiv n x) := by
  induction x using Submodule.Quotient.induction_on with | H y =>
  refine (congrArg (D.degreeEquiv m) (graded_d_mk (F := F) (k := k) n m h y)).trans ?_
  refine ((D.degreeEquiv_mk' m _).trans ?_).trans
    (congrArg (totDTo U (tensorCoeff N Q) (n - k) (m - k) (by omega)) (D.degreeEquiv_mk' n y)).symm
  funext ⟨⟨p, b⟩, hpb⟩ t
  simp only [totDTo_apply]
  rcases y with ⟨y, hy⟩
  have hy' : ∀ (p a : ℕ) (h' : (p : ℤ) + a = n) (t' : Fin (p + 1) → ι),
      y ⟨(p, a), h'⟩ t' ∈ F.step k a t' := fun p a h' t' => hy ⟨(p, a), h'⟩ t'
  have hcech : ∀ (p a : ℕ) (h' : (p : ℤ) + a = n + 1) (t' : Fin (p + 1) → ι),
      totDCech U P y p a h' t' ∈ F.step k a t' := by
    rintro (_ | q) a h' t'
    · exact zero_mem _
    · exact F.cechD_mem k a q (hy' q a (by omega)) t'
  have hcoef : ∀ (p a : ℕ) (h' : (p : ℤ) + a = n + 1) (t' : Fin (p + 1) → ι),
      totDCoef U P y p a h' t' ∈ F.step k a t' := by
    rintro p (_ | c) h' t'
    · exact zero_mem _
    · exact Submodule.smul_of_tower_mem _ ((-1 : ℤ) ^ p)
        (F.d_mem k c p (hy' p c (by omega)) t')
  have hsplit := Submodule.Quotient.mk_add ((F.step (k + 1) (k + b) t).comap
    (F.step k (k + b) t).subtype) (x := ⟨_, hcech p (k + b) (by omega) t⟩)
    (y := ⟨_, hcoef p (k + b) (by omega) t⟩)
  refine (congrArg (D.Φ b t).symm hsplit).trans ?_
  rw [map_add]
  congr 1
  · rcases p with _ | q
    · exact (congrArg (D.Φ b t).symm (Submodule.Quotient.mk_zero _)).trans (map_zero _)
    · refine (congrArg (D.Φ b t).symm (F.mk_cechD k (k + b) q
        (hy' q (k + b) (by omega)) t)).trans ?_
      simp only [map_sum, map_zsmul, D.symm_gradedCres, totDCech_succ, cechD_apply]
  · rcases b with _ | c
    · have h0 : totDCoef U P y p (k + 0) (by omega) = 0 :=
        F.totDCoef_bottom hy p _
      have : (⟨totDCoef U P y p (k + 0) (by omega) t,
          hcoef p (k + 0) (by omega) t⟩ : F.step k (k + 0) t) = 0 :=
        Subtype.ext (by
          change totDCoef U P y p (k + 0) (by omega) t = 0
          rw [h0]; rfl)
      rw [this, Submodule.Quotient.mk_zero, map_zero]
      rfl
    · refine (congrArg (D.Φ (c + 1) t).symm
        (F.mk_zsmul_cochainMap_d k (k + c) p ((-1 : ℤ) ^ p)
          (hy' p (k + c) (by omega)) t)).trans ?_
      rw [map_zsmul, D.symm_gradedD]
      rfl

/-- **The graded pieces of the induced filtration of a total Čech complex**: under
identifications `gr^k P^{k+b}(U_t) ≅ N ⊗_A Q^b(U_t)` compatible with the restrictions and the
differentials, `gr^k Tot(Č(U, P))` is `Tot(Č(U, N ⊗_A Q))` moved up by `k` degrees, as complexes
of abelian groups. -/
def gradedTotIso :
    (CochainComplex.SubmoduleFiltration.forgetAb R).obj ((F.totFiltration (U := U)).graded k) ≅
      (CochainComplex.SubmoduleFiltration.forgetAb A).obj
        (CochainComplex.reindex (cechTot U (tensorCoeff N Q)) k) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (D.degreeEquiv n).toAddCommGrpIso) (by
    rintro n m (h : n + 1 = m)
    ext x
    change ((cechTot U (tensorCoeff N Q)).d (n - k) (m - k)).hom (D.degreeEquiv n x) =
      D.degreeEquiv m ((((F.totFiltration (U := U)).graded k).d n m).hom x)
    rw [cechTot_d_apply' U (tensorCoeff N Q) (by omega)]
    exact (D.degreeEquiv_comm n m h x).symm)

/-- In degree `n` the identification `gradedTotIso` is `degreeEquiv`. -/
theorem gradedTotIso_hom_f_apply (n : ℤ) (x : ((F.totFiltration (U := U)).graded k).X n) :
    (D.gradedTotIso.hom.f n) x = D.degreeEquiv n x :=
  rfl

end GradedTensorData

end

end Stacks.CategoryTheory.CechComplex
