module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Linear
public import StacksFrontier.CategoryTheory.Sites.CechComplexAlternating

/-!
# The total Čech complex of a complex of presheaves of modules, elementwise

Let `C` be a category with finite products, `U : ι → C` a family of objects and `P` a complex,
indexed by `ℕ`, of presheaves of `R`-modules on `C`. The total complex of the Čech double complex
`Č^p(U, P^a) = ∏_{t : Fin (p + 1) → ι} P^a(U_{t_0} × ⋯ × U_{t_p})` is

`Tot(Č(U, P))^n = ∏_{p + a = n} Č^p(U, P^a)`,

with differential `δ + (-1)^p d_P` on `Č^p(U, P^a)`, where `δ` is the alternating sum of the
restrictions along the face maps. This file builds it with *elementwise* terms: the degree-`n` term
is a type of dependent functions, indexed by the pairs `(p, a)` of natural numbers with `p + a = n`
and then by the tuples `t`.

There are only finitely many pairs `(p, a)` in each degree, so this is also the direct-sum
totalization; for a finite family each term is a finite product of the values of `P`.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.Cochain`: the Čech cochains of a presheaf of modules, as an
  `R`-module of dependent functions.
* `Stacks.CategoryTheory.CechComplex.cechD`: the Čech differential, an `R`-linear map.
* `Stacks.CategoryTheory.CechComplex.cochainMap`: a morphism of presheaves on cochains.
* `Stacks.CategoryTheory.CechComplex.cechTot`: the total Čech complex `Tot(Č(U, P))`.
* `Stacks.CategoryTheory.CechComplex.cechTotMap`: its functoriality in `P`.

## Main results

* `Stacks.CategoryTheory.CechComplex.cechD_cechD`: `δ ∘ δ = 0`, which is
  `Stacks.CategoryTheory.CechComplex.Alternating.cechDiff_comp_cechDiff` read in modules.
* `Stacks.CategoryTheory.CechComplex.cechD_cochainMap`: `δ` commutes with morphisms of presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u r

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {R : Type r} [Ring R]

/-! ### Čech cochains of a presheaf of modules -/

/-- The Čech `p`-cochains of a presheaf of `R`-modules: a section over the intersection selected by
each `(p + 1)`-tuple of indices. -/
abbrev Cochain (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (p : ℕ) : Type w :=
  ∀ t : Fin (p + 1) → ι, F.obj (op (inter U t))

/-- The restriction of a section along a reindexing `φ` of a tuple `t`. -/
abbrev cres (F : Cᵒᵖ ⥤ ModuleCat.{w} R) {m n : ℕ} (φ : Fin m → Fin n) (t : Fin n → ι) :
    F.obj (op (inter U (t ∘ φ))) →ₗ[R] F.obj (op (inter U t)) :=
  (F.map (interMap U t φ).op).hom

/-- Restriction along the identity reindexing is the identity. -/
theorem cres_id (F : Cᵒᵖ ⥤ ModuleCat.{w} R) {n : ℕ} (t : Fin n → ι)
    (y : F.obj (op (inter U t))) : cres U F id t y = y := by
  simp [cres, interMap_id]

/-- Restriction along a composite of reindexings is the composite of the restrictions. -/
theorem cres_comp (F : Cᵒᵖ ⥤ ModuleCat.{w} R) {k m n : ℕ} (φ : Fin m → Fin n)
    (ψ : Fin k → Fin m) (t : Fin n → ι) (y : F.obj (op (inter U (t ∘ φ ∘ ψ)))) :
    cres U F (φ ∘ ψ) t y = cres U F φ t (cres U F ψ (t ∘ φ) y) := by
  simp only [cres, interMap_comp, op_comp, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply]

/-- **The Čech differential** `δ : Č^p ⟶ Č^{p+1}`, `(δ s)_t = ∑_j (-1)^j s_{t ∘ δ_j}|_{U_t}`, where
`δ_j = Fin.succAbove j` omits the `j`-th index. -/
def cechD (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (p : ℕ) : Cochain U F p →ₗ[R] Cochain U F (p + 1) where
  toFun s t := ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
    cres U F (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))
  map_add' s₁ s₂ := by funext t; simp [Finset.sum_add_distrib]
  map_smul' c s := by
    funext t
    simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => smul_comm _ _ _

/-- The component of `δ s` at a tuple `t` is the alternating sum of the restrictions of the
components of `s` at the faces of `t`. -/
theorem cechD_apply (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (p : ℕ) (s : Cochain U F p)
    (t : Fin (p + 2) → ι) :
    cechD U F p s t = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
      cres U F (Fin.succAbove j) t (s (t ∘ Fin.succAbove j)) :=
  rfl

/-- **`δ ∘ δ = 0`.** -/
theorem cechD_cechD (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (p : ℕ) (s : Cochain U F p) :
    cechD U F (p + 1) (cechD U F p s) = 0 :=
  DFunLike.congr_fun (Alternating.cechDiff_comp_cechDiff
    (F ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) U p) s

/-- A morphism of presheaves of modules, applied to Čech cochains. -/
def cochainMap {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (f : F ⟶ G) (p : ℕ) :
    Cochain U F p →ₗ[R] Cochain U G p where
  toFun s t := (f.app (op (inter U t))).hom (s t)
  map_add' _ _ := by funext t; simp
  map_smul' _ _ := by funext t; simp

/-- The component of the image of a cochain at a tuple `t` is the image of its component at `t`. -/
@[simp]
theorem cochainMap_apply {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (f : F ⟶ G) (p : ℕ) (s : Cochain U F p)
    (t : Fin (p + 1) → ι) : cochainMap U f p s t = (f.app (op (inter U t))).hom (s t) :=
  rfl

/-- The identity morphism of presheaves acts as the identity on cochains. -/
theorem cochainMap_id (F : Cᵒᵖ ⥤ ModuleCat.{w} R) (p : ℕ) (s : Cochain U F p) :
    cochainMap U (𝟙 F) p s = s :=
  rfl

/-- A composite of morphisms of presheaves acts on cochains as the composite of their actions. -/
theorem cochainMap_comp {F G H : Cᵒᵖ ⥤ ModuleCat.{w} R} (f : F ⟶ G) (g : G ⟶ H) (p : ℕ)
    (s : Cochain U F p) : cochainMap U (f ≫ g) p s = cochainMap U g p (cochainMap U f p s) :=
  rfl

/-- A sum of morphisms of presheaves acts on cochains as the sum of their actions. -/
theorem cochainMap_add {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (f g : F ⟶ G) (p : ℕ) (s : Cochain U F p) :
    cochainMap U (f + g) p s = cochainMap U f p s + cochainMap U g p s :=
  rfl

/-- The zero morphism of presheaves acts on cochains as zero. -/
theorem cochainMap_zero {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (p : ℕ) (s : Cochain U F p) :
    cochainMap U (0 : F ⟶ G) p s = 0 :=
  rfl

/-- **`δ` commutes with morphisms of presheaves.** -/
theorem cechD_cochainMap {F G : Cᵒᵖ ⥤ ModuleCat.{w} R} (f : F ⟶ G) (p : ℕ)
    (s : Cochain U F p) :
    cechD U G p (cochainMap U f p s) = cochainMap U f (p + 1) (cechD U F p s) := by
  funext t
  simp only [cechD_apply, cochainMap_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact (ConcreteCategory.congr_hom (f.naturality (interMap U t (Fin.succAbove j)).op)
    (s (t ∘ Fin.succAbove j))).symm

/-! ### The total complex -/

/-- The pairs `(p, a)` of a Čech degree and a coefficient degree with `p + a = n`. -/
abbrev TotIndex (n : ℤ) : Type := {pa : ℕ × ℕ // (pa.1 : ℤ) + pa.2 = n}

/-- There are finitely many pairs `(p, a)` in each total degree. -/
theorem finite_totIndex (n : ℤ) : Finite (TotIndex n) := by
  refine Finite.of_injective
    (fun i : TotIndex n => (⟨i.1.1, by have := i.2; omega⟩ : Fin (n.toNat + 1))) ?_
  intro i j hij
  have h₁ : i.1.1 = j.1.1 := congrArg Fin.val hij
  have hi := i.2
  have hj := j.2
  exact Subtype.ext (Prod.ext h₁ (by omega))

variable (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

/-- The degree-`n` term `∏_{p + a = n} Č^p(U, P^a)` of the total Čech complex. -/
abbrev TotX (n : ℤ) : Type w := ∀ i : TotIndex n, Cochain U (P.X i.1.2) i.1.1

/-- The Čech half of the total differential, landing in the summand `(p, a)` of degree `n + 1`: `δ`
of the component `(p - 1, a)`, and zero when `p = 0`. -/
def totDCech {n : ℤ} (x : TotX U P n) : ∀ (p a : ℕ), (p : ℤ) + a = n + 1 → Cochain U (P.X a) p
  | 0, _, _ => 0
  | q + 1, a, h => cechD U (P.X a) q (x ⟨(q, a), by push_cast at h; omega⟩)

/-- The coefficient half of the total differential, landing in the summand `(p, a)` of degree
`n + 1`: `(-1)^p d_P` of the component `(p, a - 1)`, and zero when `a = 0`. -/
def totDCoef {n : ℤ} (x : TotX U P n) : ∀ (p a : ℕ), (p : ℤ) + a = n + 1 → Cochain U (P.X a) p
  | _, 0, _ => 0
  | p, b + 1, h =>
    ((-1 : ℤ) ^ p) • cochainMap U (P.d b (b + 1)) p (x ⟨(p, b), by push_cast at h; omega⟩)

/-- The Čech half of the total differential vanishes on the summands with `p = 0`. -/
@[simp] theorem totDCech_zero {n : ℤ} (x : TotX U P n) (a : ℕ) (h) : totDCech U P x 0 a h = 0 :=
  rfl

/-- On the summand `(q + 1, a)` the Čech half of the total differential is `δ`. -/
@[simp] theorem totDCech_succ {n : ℤ} (x : TotX U P n) (q a : ℕ) (h) :
    totDCech U P x (q + 1) a h = cechD U (P.X a) q (x ⟨(q, a), by push_cast at h; omega⟩) :=
  rfl

/-- The coefficient half of the total differential vanishes on the summands with `a = 0`. -/
@[simp] theorem totDCoef_zero {n : ℤ} (x : TotX U P n) (p : ℕ) (h) : totDCoef U P x p 0 h = 0 :=
  rfl

/-- On the summand `(p, b + 1)` the coefficient half of the total differential is `(-1)^p d_P`. -/
@[simp] theorem totDCoef_succ {n : ℤ} (x : TotX U P n) (p b : ℕ) (h) :
    totDCoef U P x p (b + 1) h =
      ((-1 : ℤ) ^ p) • cochainMap U (P.d b (b + 1)) p (x ⟨(p, b), by push_cast at h; omega⟩) :=
  rfl

/-- The Čech half of the total differential is additive. -/
theorem totDCech_add {n : ℤ} (x y : TotX U P n) (p a : ℕ) (h) :
    totDCech U P (x + y) p a h = totDCech U P x p a h + totDCech U P y p a h := by
  cases p <;> simp

/-- The coefficient half of the total differential is additive. -/
theorem totDCoef_add {n : ℤ} (x y : TotX U P n) (p a : ℕ) (h) :
    totDCoef U P (x + y) p a h = totDCoef U P x p a h + totDCoef U P y p a h := by
  cases a <;> simp [smul_add]

/-- The Čech half of the total differential is `R`-linear. -/
theorem totDCech_smul {n : ℤ} (c : R) (x : TotX U P n) (p a : ℕ) (h) :
    totDCech U P (c • x) p a h = c • totDCech U P x p a h := by
  cases p <;> simp

/-- The coefficient half of the total differential is `R`-linear. -/
theorem totDCoef_smul {n : ℤ} (c : R) (x : TotX U P n) (p a : ℕ) (h) :
    totDCoef U P (c • x) p a h = c • totDCoef U P x p a h := by
  cases a <;> simp [smul_comm c]

/-- The differential `Tot^n ⟶ Tot^m` for `n + 1 = m`: on the summand `(p, a)` it is
`δ + (-1)^p d_P`. -/
def totDTo (n m : ℤ) (hm : n + 1 = m) : TotX U P n →ₗ[R] TotX U P m where
  toFun x i := totDCech U P x i.1.1 i.1.2 (i.2.trans hm.symm) +
    totDCoef U P x i.1.1 i.1.2 (i.2.trans hm.symm)
  map_add' x y := by
    funext i
    simp only [Pi.add_apply, totDCech_add, totDCoef_add]
    abel
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, totDCech_smul, totDCoef_smul, RingHom.id_apply, smul_add]

/-- The component of `totDTo` in the summand `(p, a)` is the sum of its two halves. -/
theorem totDTo_apply (n m : ℤ) (hm : n + 1 = m) (x : TotX U P n) (i : TotIndex m) :
    totDTo U P n m hm x i = totDCech U P x i.1.1 i.1.2 (i.2.trans hm.symm) +
      totDCoef U P x i.1.1 i.1.2 (i.2.trans hm.symm) :=
  rfl

/-- The differential `Tot^n ⟶ Tot^{n+1}`: on the summand `(p, a)` it is `δ + (-1)^p d_P`. -/
abbrev totD (n : ℤ) : TotX U P n →ₗ[R] TotX U P (n + 1) := totDTo U P n (n + 1) rfl

/-- The component of `totD` in the summand `(p, a)` is the sum of its two halves. -/
theorem totD_apply (n : ℤ) (x : TotX U P n) (i : TotIndex (n + 1)) :
    totD U P n x i = totDCech U P x i.1.1 i.1.2 i.2 + totDCoef U P x i.1.1 i.1.2 i.2 :=
  rfl

/-- `d_P` applied twice to a cochain vanishes. -/
theorem cochainMap_d_d (a p : ℕ) (s : Cochain U (P.X a) p) :
    cochainMap U (P.d (a + 1) (a + 2)) p (cochainMap U (P.d a (a + 1)) p s) = 0 := by
  rw [← cochainMap_comp, P.d_comp_d, cochainMap_zero]

/-- **`d ∘ d = 0`** for the total differential. -/
theorem totD_totD (n : ℤ) (x : TotX U P n) : totD U P (n + 1) (totD U P n x) = 0 := by
  funext ⟨⟨p, a⟩, h⟩
  rcases p with _ | _ | q <;> rcases a with _ | _ | b <;>
    simp only [totD_apply, totDCech_zero, totDCech_succ, totDCoef_zero, totDCoef_succ,
      map_add, map_zsmul, map_zero, add_zero, zero_add, cechD_cechD,
      cochainMap_d_d, smul_zero, Pi.zero_apply] <;>
    simp only [← cechD_cochainMap] <;>
    first
    | rfl
    | (rw [← add_smul]; norm_num [pow_succ])

/-- The total differential between two arbitrary degrees: `totD` from `n` to `n + 1`, and zero
otherwise. -/
def totDiff (n m : ℤ) : ModuleCat.of R (TotX U P n) ⟶ ModuleCat.of R (TotX U P m) :=
  if h : n + 1 = m then ModuleCat.ofHom (totDTo U P n m h) else 0

/-- From degree `n` to degree `n + 1` the total differential is `totD`. -/
theorem totDiff_self (n : ℤ) : totDiff U P n (n + 1) = ModuleCat.ofHom (totD U P n) :=
  dif_pos rfl

/-- **The total Čech complex** `Tot(Č(U, P))` of a complex of presheaves of `R`-modules: in degree
`n` the product of `Č^p(U, P^a)` over `p + a = n`, with differential `δ + (-1)^p d_P`. -/
abbrev cechTot : CochainComplex (ModuleCat.{w} R) ℤ where
  X n := ModuleCat.of R (TotX U P n)
  d := totDiff U P
  shape i j h := dif_neg h
  d_comp_d' i j k hij hjk := by
    subst hij hjk
    rw [totDiff_self, totDiff_self]
    ext x : 2
    exact totD_totD U P i x

/-- The differential of the total Čech complex from degree `n` to degree `n + 1` is `totD`. -/
theorem cechTot_d_apply (n : ℤ) (x : TotX U P n) :
    ((cechTot U P).d n (n + 1)).hom x = totD U P n x := by
  show (totDiff U P n (n + 1)).hom x = totD U P n x
  rw [totDiff_self]
  rfl

/-- The differential of the total Čech complex from degree `n` to a degree `m = n + 1` is
`totDTo`. -/
theorem cechTot_d_apply' {n m : ℤ} (h : n + 1 = m) (x : TotX U P n) :
    ((cechTot U P).d n m).hom x = totDTo U P n m h x := by
  subst h
  exact cechTot_d_apply U P n x

/-- The differential of the total Čech complex vanishes between degrees `n` and `m` unless
`m = n + 1`. -/
theorem cechTot_d_eq_zero {n m : ℤ} (h : n + 1 ≠ m) : (cechTot U P).d n m = 0 :=
  dif_neg h

variable {U P} in
/-- The degreewise map of total Čech complexes induced by a morphism of complexes of presheaves. -/
def totMap {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (φ : P ⟶ Q) (n : ℤ) :
    TotX U P n →ₗ[R] TotX U Q n where
  toFun x i := cochainMap U (φ.f i.1.2) i.1.1 (x i)
  map_add' _ _ := by funext i; simp
  map_smul' _ _ := by funext i; simp

/-- The component of `totMap φ` in the summand `(p, a)` is the action of `φ` in degree `a` on
`p`-cochains. -/
theorem totMap_apply {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (φ : P ⟶ Q) (n : ℤ)
    (x : TotX U P n) (i : TotIndex n) : totMap φ n x i = cochainMap U (φ.f i.1.2) i.1.1 (x i) :=
  rfl

/-- The degreewise map induced by a morphism of complexes commutes with the total differential. -/
theorem totMap_totD {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (φ : P ⟶ Q) (n : ℤ)
    (x : TotX U P n) : totMap φ (n + 1) (totD U P n x) = totD U Q n (totMap φ n x) := by
  funext ⟨⟨p, a⟩, h⟩
  rcases p with _ | q <;> rcases a with _ | b <;>
    simp only [totD_apply, totMap_apply, totDCech_zero, totDCech_succ, totDCoef_zero,
      totDCoef_succ, map_add, map_zsmul, add_zero, zero_add, map_zero, cechD_cochainMap] <;>
    simp only [← cochainMap_comp, φ.comm]

/-- **The functoriality of the total Čech complex.** -/
def cechTotMap {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (φ : P ⟶ Q) :
    cechTot U P ⟶ cechTot U Q where
  f n := (ModuleCat.ofHom (totMap φ n) : (cechTot U P).X n ⟶ (cechTot U Q).X n)
  comm' := by
    rintro n _ rfl
    ext x : 2
    revert x
    intro (x : TotX U P n)
    change ((cechTot U Q).d n (n + 1)).hom (totMap φ n x) =
      totMap φ (n + 1) (((cechTot U P).d n (n + 1)).hom x)
    rw [cechTot_d_apply U Q, cechTot_d_apply U P]
    exact (totMap_totD U P φ n x).symm

/-- In degree `n` the map of total Čech complexes induced by `φ` is `totMap φ n`. -/
@[simp]
theorem cechTotMap_f_apply {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (φ : P ⟶ Q) (n : ℤ)
    (x : TotX U P n) : ((cechTotMap U P φ).f n).hom x = totMap φ n x :=
  rfl

/-- The identity of a complex of presheaves induces the identity of its total Čech complex. -/
theorem cechTotMap_id : cechTotMap U P (𝟙 P) = 𝟙 _ := by
  ext n x : 3
  rfl

/-- A composite of morphisms of complexes induces the composite of the induced maps of total Čech
complexes. -/
theorem cechTotMap_comp {Q T : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (φ : P ⟶ Q) (ψ : Q ⟶ T) :
    cechTotMap U P (φ ≫ ψ) = cechTotMap U P φ ≫ cechTotMap U Q ψ := by
  ext n x : 3
  rfl

end

end Stacks.CategoryTheory.CechComplex
