module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotal
public import StacksFrontier.Algebra.Homology.SubmoduleFiltrationQuasiIso

/-!
# Filtrations and intersection-wise maps of total Čech complexes

Let `P` be a complex, indexed by `ℕ`, of presheaves of `R`-modules on a category with finite
products, and `U : ι → C` a family of objects. This file supplies two tools for the elementwise
total Čech complex `Tot(Č(U, P))` of `StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotal`.

* **Filtrations.** A decreasing family `F^k P^a(U_t) ⊆ P^a(U_t)` of submodules over the Čech
  intersections `U_t`, stable under the restrictions along the face maps and under the
  differential, with `F^0 = P` and `F^k P^a = 0` for `a < k`, induces a finite filtration of
  `Tot(Č(U, P))` by subcomplexes (`CochainComplex.SubmoduleFiltration`): a cochain lies in the
  `k`-th step when every one of its components does.
* **Intersection-wise maps.** A family of additive maps `P^a(U_t) ⟶ Q^a(U_t)`, given only on the
  Čech intersections `U_t = U_{t_0} × ⋯ × U_{t_p}` and compatible there with the restrictions
  along the face maps and with the differentials, induces a map of total Čech complexes, even
  when `P` and `Q` are presheaves of modules over different rings. Only the intersections enter
  the Čech complex, so nothing is required elsewhere.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.InterFiltration`: such a filtration of `P` on the
  intersections.
* `Stacks.CategoryTheory.CechComplex.InterFiltration.totFiltration`: the induced filtration of
  `Tot(Č(U, P))`.
* `Stacks.CategoryTheory.CechComplex.InterHom`: an intersection-wise map, and
  `Stacks.CategoryTheory.CechComplex.InterHom.totAddHom` the induced degreewise map.

## Main results

* `Stacks.CategoryTheory.CechComplex.InterHom.totAddHom_totD`: the induced map commutes with the
  total differentials.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u r r'

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {ι : Type w} (U : ι → C)
  {R : Type r} [Ring R]

/-! ### Filtrations -/

/-- A finite decreasing filtration of a complex of presheaves of modules on the Čech intersections
of a family `U`: submodules of the values over the intersections `U_t`, stable under the
restrictions along the face maps and under the differential, such that the zeroth step is
everything and the `k`-th step vanishes in degrees `< k`. Only the intersections enter the Čech
complex, so nothing is required elsewhere. -/
structure InterFiltration (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ) where
  /-- The `k`-th step in degree `a`, over the intersection selected by `t`. -/
  step : ℕ → ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι), Submodule R ((P.X a).obj (op (inter U t)))
  map_le : ∀ (k a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2)),
    (step k a (t ∘ Fin.succAbove j)).map (cres U (P.X a) (Fin.succAbove j) t) ≤ step k a t
  d_le : ∀ (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    (step k a t).map ((P.d a (a + 1)).app (op (inter U t))).hom ≤ step k (a + 1) t
  step_succ_le : ∀ (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι), step (k + 1) a t ≤ step k a t
  step_zero : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι), step 0 a t = ⊤
  step_eq_bot : ∀ (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι), a < k → step k a t = ⊥

namespace InterFiltration

variable {U} {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ} (F : InterFiltration U P)

/-- The `k`-th step of the filtration of `Tot(Č(U, P))` in degree `n`: the cochains all of whose
components lie in the `k`-th step. -/
def totStep (k : ℕ) (n : ℤ) : Submodule R (TotX U P n) where
  carrier := {x | ∀ (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι), x i t ∈ F.step k i.1.2 t}
  add_mem' hx hy i t := add_mem (hx i t) (hy i t)
  zero_mem' _ _ := zero_mem _
  smul_mem' c _ hx i t := Submodule.smul_mem _ c (hx i t)

/-- A cochain lies in the `k`-th step of the filtration of `Tot(Č(U, P))` if and only if each of
its components lies in the `k`-th step of the filtration of the coefficients. -/
theorem mem_totStep {k : ℕ} {n : ℤ} (x : TotX U P n) :
    x ∈ F.totStep k n ↔ ∀ (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι),
      x i t ∈ F.step k i.1.2 t :=
  Iff.rfl

/-- Restriction along a face map carries the `k`-th step of the filtration over
`U_{t ∘ succAbove j}` into the `k`-th step over `U_t`. -/
theorem cres_mem (k a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    {y : (P.X a).obj (op (inter U (t ∘ Fin.succAbove j)))}
    (hy : y ∈ F.step k a (t ∘ Fin.succAbove j)) :
    cres U (P.X a) (Fin.succAbove j) t y ∈ F.step k a t :=
  F.map_le k a t j ⟨y, hy, rfl⟩

/-- The Čech differential preserves the `k`-th step of the filtration of the coefficients. -/
theorem cechD_mem (k a q : ℕ) {s : Cochain U (P.X a) q}
    (hs : ∀ t, s t ∈ F.step k a t) (t : Fin (q + 2) → ι) :
    cechD U (P.X a) q s t ∈ F.step k a t := by
  rw [cechD_apply]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_of_tower_mem _ ((-1 : ℤ) ^ (j : ℕ)) (F.cres_mem k a t j (hs _))

/-- The differential of the complex of coefficients carries the `k`-th step in degree `a` into the
`k`-th step in degree `a + 1`. -/
theorem d_mem (k a q : ℕ) {s : Cochain U (P.X a) q}
    (hs : ∀ t, s t ∈ F.step k a t) (t : Fin (q + 1) → ι) :
    cochainMap U (P.d a (a + 1)) q s t ∈ F.step k (a + 1) t :=
  F.d_le k a t ⟨s t, hs t, rfl⟩

/-- The total differential preserves the `k`-th step of the filtration of `Tot(Č(U, P))`. -/
theorem totD_mem (k : ℕ) (n : ℤ) {x : TotX U P n} (hx : x ∈ F.totStep k n) :
    totD U P n x ∈ F.totStep k (n + 1) := by
  rintro ⟨⟨p, a⟩, h⟩ t
  rw [totD_apply]
  refine add_mem ?_ ?_
  · rcases p with _ | q
    · exact zero_mem _
    · exact F.cechD_mem k a q (fun t' => hx ⟨(q, a), by push_cast at h; omega⟩ t') t
  · rcases a with _ | b
    · exact zero_mem _
    · exact Submodule.smul_of_tower_mem _ ((-1 : ℤ) ^ p)
        (F.d_mem k b p (fun t' => hx ⟨(p, b), by push_cast at h; omega⟩ t') t)

/-- **The filtration of the total Čech complex induced by a filtration of the coefficients.** -/
def totFiltration : CochainComplex.SubmoduleFiltration (cechTot U P) where
  step := F.totStep
  map_d_le k n m := by
    by_cases hnm : n + 1 = m
    · subst hnm
      rintro _ ⟨x, hx, rfl⟩
      rw [cechTot_d_apply]
      exact F.totD_mem k n hx
    · rw [cechTot_d_eq_zero U P hnm]
      rintro _ ⟨x, -, rfl⟩
      exact zero_mem _
  step_succ_le k n x hx i t := F.step_succ_le k _ t (hx i t)
  step_zero n := eq_top_iff.2 fun x _ i t => by
    rw [F.step_zero]
    trivial
  step_eq_bot k n hn := eq_bot_iff.2 fun x hx => by
    refine (Submodule.mem_bot R).2 (funext fun i => funext fun t => ?_)
    have h := hx i t
    rw [F.step_eq_bot k i.1.2 t (by have := i.2; omega)] at h
    exact h

/-- The graded piece `F^k / F^{k+1}` of the coefficients in degree `a`, over the intersection
selected by `t`. -/
abbrev GradedValue (k a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) : Type w :=
  F.step k a t ⧸ (F.step (k + 1) a t).comap (F.step k a t).subtype

/-- The componentwise projection of the `k`-th step of `Tot(Č(U, P))` onto the graded pieces of
the coefficients. -/
def totStepToGraded (k : ℕ) (n : ℤ) :
    F.totStep (U := U) k n →ₗ[R] ∀ (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι),
      F.GradedValue (U := U) k i.1.2 t where
  toFun x i t := Submodule.Quotient.mk ⟨(x : TotX U P n) i t, x.2 i t⟩
  map_add' _ _ := by funext i t; rfl
  map_smul' _ _ := by funext i t; rfl

/-- The componentwise projection onto the graded pieces of the coefficients is surjective. -/
theorem totStepToGraded_surjective (k : ℕ) (n : ℤ) :
    Function.Surjective (F.totStepToGraded (U := U) k n) := by
  intro z
  choose y hy using fun (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι) =>
    Submodule.Quotient.mk_surjective _ (z i t)
  exact ⟨⟨fun i t => (y i t : (P.X i.1.2).obj (op (inter U t))), fun i t => (y i t).2⟩,
    funext fun i => funext fun t => hy i t⟩

/-- The kernel of the componentwise projection of the `k`-th step onto the graded pieces of the
coefficients is the `(k + 1)`-st step. -/
theorem ker_totStepToGraded (k : ℕ) (n : ℤ) :
    LinearMap.ker (F.totStepToGraded (U := U) k n) =
      (F.totStep (U := U) (k + 1) n).comap (F.totStep (U := U) k n).subtype := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, funext_iff]
  exact forall_congr' fun i => forall_congr' fun t => Submodule.Quotient.mk_eq_zero _

/-- **The graded pieces of the induced filtration, componentwise**: in degree `n`,
`gr^k Tot(Č(U, P)) ≅ ∏_{p + a = n} ∏_t gr^k P^a(U_t)`. -/
noncomputable def gradedXEquiv (k : ℕ) (n : ℤ) :
    ((F.totFiltration (U := U)).graded k).X n ≃ₗ[R] ∀ (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι),
      F.GradedValue (U := U) k i.1.2 t :=
  (Submodule.quotEquivOfEq _ _ (F.ker_totStepToGraded (U := U) k n).symm).trans
    ((F.totStepToGraded (U := U) k n).quotKerEquivOfSurjective
      (F.totStepToGraded_surjective (U := U) k n))

/-- On the class of a cochain of the `k`-th step, `gradedXEquiv` is the componentwise projection
onto the graded pieces of the coefficients. -/
theorem gradedXEquiv_mk (k : ℕ) (n : ℤ) (x : F.totStep (U := U) k n) :
    F.gradedXEquiv (U := U) k n (Submodule.Quotient.mk x) = F.totStepToGraded (U := U) k n x :=
  rfl

end InterFiltration

/-! ### Intersection-wise maps -/

variable {R' : Type r'} [Ring R']

/-- **A map of complexes of presheaves given on the Čech intersections only**: additive maps
`P^a(U_t) ⟶ Q^a(U_t)` for every tuple `t`, compatible with the restrictions along the face maps
and with the differentials. `P` and `Q` may be presheaves of modules over different rings. -/
structure InterHom (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ)
    (Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R') ℕ) where
  /-- The map over the intersection selected by `t`, in degree `a`. -/
  app : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι),
    (P.X a).obj (op (inter U t)) →+ (Q.X a).obj (op (inter U t))
  app_cres : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 2) → ι) (j : Fin (m + 2))
    (y : (P.X a).obj (op (inter U (t ∘ Fin.succAbove j)))),
    app a t (cres U (P.X a) (Fin.succAbove j) t y) =
      cres U (Q.X a) (Fin.succAbove j) t (app a (t ∘ Fin.succAbove j) y)
  app_d : ∀ (a : ℕ) {m : ℕ} (t : Fin (m + 1) → ι) (y : (P.X a).obj (op (inter U t))),
    app (a + 1) t (((P.d a (a + 1)).app (op (inter U t))).hom y) =
      ((Q.d a (a + 1)).app (op (inter U t))).hom (app a t y)

namespace InterHom

variable {U} {P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R) ℕ}
  {Q : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{w} R') ℕ} (g : InterHom U P Q)

/-- The degreewise map of total Čech complexes induced by an intersection-wise map. -/
def totAddHom (n : ℤ) : TotX U P n →+ TotX U Q n where
  toFun x i t := g.app i.1.2 t (x i t)
  map_zero' := by funext i t; exact map_zero _
  map_add' x y := by funext i t; exact map_add _ _ _

/-- The induced degreewise map applies the intersection-wise map to each component. -/
theorem totAddHom_apply (n : ℤ) (x : TotX U P n) (i : TotIndex n) (t : Fin (i.1.1 + 1) → ι) :
    g.totAddHom n x i t = g.app i.1.2 t (x i t) :=
  rfl

/-- An intersection-wise map commutes with the Čech differentials. -/
theorem app_cechD (a q : ℕ) (s : Cochain U (P.X a) q) (t : Fin (q + 2) → ι) :
    g.app a t (cechD U (P.X a) q s t) = cechD U (Q.X a) q (fun t' => g.app a t' (s t')) t := by
  simp only [cechD_apply, map_sum, map_zsmul, g.app_cres]

/-- **An intersection-wise map commutes with the total differentials.** -/
theorem totAddHom_totD (n : ℤ) (x : TotX U P n) :
    g.totAddHom (n + 1) (totD U P n x) = totD U Q n (g.totAddHom n x) := by
  funext ⟨⟨p, a⟩, h⟩ t
  rw [totAddHom_apply, totD_apply, totD_apply, Pi.add_apply, Pi.add_apply, map_add]
  congr 1
  · rcases p with _ | q
    · exact map_zero _
    · exact g.app_cechD a q _ t
  · rcases a with _ | b
    · exact map_zero _
    · simp only [totDCoef_succ, Pi.smul_apply, cochainMap_apply, map_zsmul, g.app_d]
      rfl

end InterHom

end

end Stacks.CategoryTheory.CechComplex
