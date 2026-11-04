module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.Algebra.Order.Group.Int

/-!
# The addition law for integer powers of an autoequivalence

For an autoequivalence `e : C ≌ C` with integer powers `e ^ n` (`CategoryTheory.Equivalence.pow`),
we construct the natural isomorphisms `(e ^ n).functor ⋙ (e ^ m).functor ≅ (e ^ p).functor` for
`n + m = p`, and prove their naturality, their cocycle identity and their normalisations at the
exponents `0` and `1`. The target exponent is an explicit argument constrained by an equation,
as for `CategoryTheory.shiftFunctorAdd'`.

## Main definitions

* `CategoryTheory.Equivalence.powStepUp`, `CategoryTheory.Equivalence.powStepDown`: the one-step
  comparisons `e.functor ⋙ (e ^ n).functor ≅ (e ^ (n + 1)).functor` and
  `e.inverse ⋙ (e ^ n).functor ≅ (e ^ (n - 1)).functor`.
* `CategoryTheory.Equivalence.powAdd`: the addition law
  `(e ^ n).functor ⋙ (e ^ m).functor ≅ (e ^ p).functor` for `n + m = p`.
* `CategoryTheory.Equivalence.powSucc`: the successor comparison
  `(e ^ n).functor ⋙ e.functor ≅ (e ^ p).functor`, the addition law at right exponent one.

## Main results

* `powAdd_hom_naturality`, `powAdd_inv_naturality`: the addition law is natural in the object it
  is applied to.
* `powAdd_zero_left`, `powAdd_zero_right`: the addition law at a zero exponent is the identity
  isomorphism.
* `powAdd_one_right`: the addition law at right exponent one is the successor comparison.
* `powAdd_succ`, `powAdd_pred`: the one-step recursions of the addition law in its left
  exponent, for every integer `n`.
* `powAdd_assoc`: the cocycle identity relating the two ways of composing three powers.
* `powStepDown_powStepUp`, `powStepUp_powStepDown`: the two one-step comparisons cancel against
  each other up to the unit, respectively the counit, of `e`.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

universe v u

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C] (e : C ≌ C)

/-- The functor of the identity equivalence is the identity functor. -/
theorem refl_functor_eq : (Equivalence.refl (C := C)).functor = 𝟭 C := rfl

/-- The `-m`-th power of `e.symm` is the `m`-th power of `e`. -/
theorem pow_symm_neg (m : ℤ) : e.symm ^ (-m) = e ^ m := by
  match m with
  | Int.ofNat 0 => rfl
  | Int.ofNat (k + 1) => rfl
  | Int.negSucc k => rfl

/-- For `n ≥ 0`, the functor of `e ^ (n + 1)` is `e.functor ⋙ (e ^ n).functor`. -/
theorem powFunctor_succ_eq_of_nonneg {n : ℤ} (h : 0 ≤ n) :
    (e ^ (n + 1)).functor = e.functor ⋙ (e ^ n).functor := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
  cases k <;> rfl

/-- For `n < 0`, the functor of `e ^ n` is `e.inverse ⋙ (e ^ (n + 1)).functor`. -/
theorem powFunctor_eq_inverse_comp_of_neg {n : ℤ} (h : n < 0) :
    (e ^ n).functor = e.inverse ⋙ (e ^ (n + 1)).functor := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = Int.negSucc k := ⟨(-n - 1).toNat, by omega⟩
  cases k <;> rfl

/-- For `n ≤ 0`, the functor of `e ^ (n - 1)` is `e.inverse ⋙ (e ^ n).functor`. -/
theorem powFunctor_pred_eq_of_nonpos {n : ℤ} (h : n ≤ 0) :
    (e ^ (n - 1)).functor = e.inverse ⋙ (e ^ n).functor := by
  rw [powFunctor_eq_inverse_comp_of_neg e (show n - 1 < 0 by omega),
    show n - 1 + 1 = n by omega]

/-- For `n > 0`, the functor of `e ^ n` is `e.functor ⋙ (e ^ (n - 1)).functor`. -/
theorem powFunctor_eq_functor_comp_of_pos {n : ℤ} (h : 0 < n) :
    (e ^ n).functor = e.functor ⋙ (e ^ (n - 1)).functor := by
  rw [← powFunctor_succ_eq_of_nonneg e (show (0:ℤ) ≤ n - 1 by omega),
    show n - 1 + 1 = n by omega]

/-- The comparison `e.functor ⋙ (e ^ n).functor ≅ (e ^ p).functor` for `n + 1 = p`. -/
noncomputable def powStepUp (n p : ℤ) (h : n + 1 = p) :
    e.functor ⋙ (e ^ n).functor ≅ (e ^ p).functor :=
  if hn : 0 ≤ n then eqToIso (by rw [← h, powFunctor_succ_eq_of_nonneg e hn])
  else
    eqToIso (by rw [powFunctor_eq_inverse_comp_of_neg e (show n < 0 by omega),
      ← Functor.assoc, h]) ≪≫ Functor.isoWhiskerRight e.unitIso.symm (e ^ p).functor

/-- The comparison `e.inverse ⋙ (e ^ n).functor ≅ (e ^ p).functor` for `n - 1 = p`. -/
noncomputable def powStepDown (n p : ℤ) (h : n - 1 = p) :
    e.inverse ⋙ (e ^ n).functor ≅ (e ^ p).functor :=
  if hn : n ≤ 0 then eqToIso (by rw [← h, powFunctor_pred_eq_of_nonpos e hn])
  else
    eqToIso (by rw [powFunctor_eq_functor_comp_of_pos e (show 0 < n by omega),
      ← Functor.assoc, h]) ≪≫ Functor.isoWhiskerRight e.counitIso (e ^ p).functor

/-- For `n ≥ 0`, `powStepUp e n p h` is an `eqToIso`. -/
theorem powStepUp_of_nonneg {n p : ℤ} (h : n + 1 = p) (hn : 0 ≤ n) :
    powStepUp e n p h = eqToIso (by rw [← h, powFunctor_succ_eq_of_nonneg e hn]) := by
  rw [powStepUp, dite_eq_left_of_eq_true (by simpa using hn)]

/-- For `n < 0`, `powStepUp e n p h` is an `eqToIso` followed by the inverse of the unit of `e`. -/
theorem powStepUp_of_neg {n p : ℤ} (h : n + 1 = p) (hn : n < 0) :
    powStepUp e n p h =
      eqToIso (by rw [powFunctor_eq_inverse_comp_of_neg e hn, ← Functor.assoc, h]) ≪≫
        Functor.isoWhiskerRight e.unitIso.symm (e ^ p).functor := by
  rw [powStepUp, dite_eq_right_of_eq_false (by simp; omega)]

/-- For `n ≤ 0`, `powStepDown e n p h` is an `eqToIso`. -/
theorem powStepDown_of_nonpos {n p : ℤ} (h : n - 1 = p) (hn : n ≤ 0) :
    powStepDown e n p h = eqToIso (by rw [← h, powFunctor_pred_eq_of_nonpos e hn]) := by
  rw [powStepDown, dite_eq_left_of_eq_true (by simpa using hn)]

/-- For `n > 0`, `powStepDown e n p h` is an `eqToIso` followed by the counit of `e`. -/
theorem powStepDown_of_pos {n p : ℤ} (h : n - 1 = p) (hn : 0 < n) :
    powStepDown e n p h =
      eqToIso (by rw [powFunctor_eq_functor_comp_of_pos e hn, ← Functor.assoc, h]) ≪≫
        Functor.isoWhiskerRight e.counitIso (e ^ p).functor := by
  rw [powStepDown, dite_eq_right_of_eq_false (by simp; omega)]

/-! ### The two cancellation identities between the steps -/

/-- A step down followed by a step up is the inverse of the unit of `e`. -/
theorem powStepDown_powStepUp (n p : ℤ) (h : n - 1 = p) :
    Functor.isoWhiskerLeft e.functor (powStepDown e n p h) ≪≫
        powStepUp e p n (by omega) =
      Functor.isoWhiskerRight e.unitIso.symm (e ^ n).functor := by
  subst h
  by_cases hn : n ≤ 0
  · rw [powStepDown_of_nonpos e rfl hn, powStepUp_of_neg e (by omega) (by omega)]
    ext X
    simp [eqToHom_app]
  · rw [powStepDown_of_pos e rfl (by omega), powStepUp_of_nonneg e (by omega) (by omega)]
    ext X
    have hc := Functor.congr_hom (powFunctor_eq_functor_comp_of_pos e (show 0 < n by omega))
      (e.unitIso.inv.app X)
    simp [eqToHom_app, Equivalence.counit_app_functor, hc]

/-- A step up followed by a step down is the counit of `e`. -/
theorem powStepUp_powStepDown (n p : ℤ) (h : n + 1 = p) :
    Functor.isoWhiskerLeft e.inverse (powStepUp e n p h) ≪≫
        powStepDown e p n (by omega) =
      Functor.isoWhiskerRight e.counitIso (e ^ n).functor := by
  subst h
  by_cases hn : 0 ≤ n
  · rw [powStepUp_of_nonneg e rfl hn, powStepDown_of_pos e (by omega) (by omega)]
    ext X
    simp [eqToHom_app]
  · rw [powStepUp_of_neg e rfl (by omega), powStepDown_of_nonpos e (by omega) (by omega)]
    ext X
    have hc := Functor.congr_hom (powFunctor_eq_inverse_comp_of_neg e (show n < 0 by omega))
      (e.counitIso.hom.app X)
    simp [eqToHom_app, Equivalence.unitInv_app_inverse, hc]

/-- `powStepDown_powStepUp`, evaluated at an object. -/
@[reassoc]
theorem powStepDown_powStepUp_hom_app (n p : ℤ) (h : n - 1 = p) (X : C) :
    (powStepDown e n p h).hom.app (e.functor.obj X) ≫ (powStepUp e p n (by omega)).hom.app X =
      (e ^ n).functor.map (e.unitIso.inv.app X) := by
  simpa using NatTrans.congr_app (congrArg Iso.hom (powStepDown_powStepUp e n p h)) X

/-- `powStepUp_powStepDown`, evaluated at an object. -/
@[reassoc]
theorem powStepUp_powStepDown_hom_app (n p : ℤ) (h : n + 1 = p) (X : C) :
    (powStepUp e n p h).hom.app (e.inverse.obj X) ≫ (powStepDown e p n (by omega)).hom.app X =
      (e ^ n).functor.map (e.counitIso.hom.app X) := by
  simpa using NatTrans.congr_app (congrArg Iso.hom (powStepUp_powStepDown e n p h)) X

/-- The inverse of `powStepDown_powStepUp`, evaluated at an object. -/
@[reassoc]
theorem powStepUp_powStepDown_inv_app (n p : ℤ) (h : n - 1 = p) (X : C) :
    (powStepUp e p n (by omega)).inv.app X ≫
        (powStepDown e n p h).inv.app (e.functor.obj X) =
      (e ^ n).functor.map (e.unitIso.hom.app X) := by
  simpa using NatTrans.congr_app (congrArg Iso.inv (powStepDown_powStepUp e n p h)) X

/-- The inverse of `powStepUp_powStepDown`, evaluated at an object. -/
@[reassoc]
theorem powStepDown_powStepUp_inv_app (n p : ℤ) (h : n + 1 = p) (X : C) :
    (powStepDown e p n (by omega)).inv.app X ≫
        (powStepUp e n p h).inv.app (e.inverse.obj X) =
      (e ^ n).functor.map (e.counitIso.inv.app X) := by
  simpa using NatTrans.congr_app (congrArg Iso.inv (powStepUp_powStepDown e n p h)) X

/-! ### The addition law -/

/-- The addition law with a natural number as left exponent. -/
noncomputable def powAddNat (m : ℤ) : (k : ℕ) → (p : ℤ) → ((k : ℤ) + m = p) →
    ((e ^ (k : ℤ)).functor ⋙ (e ^ m).functor ≅ (e ^ p).functor)
  | 0, _, h => eqToIso (by
      rw [← h, show ((0:ℕ) : ℤ) + m = m from by omega]
      exact Functor.id_comp _)
  | k + 1, p, h =>
      Functor.isoWhiskerRight (powStepUp e (k : ℤ) ((k + 1 : ℕ) : ℤ) (by omega)).symm
          (e ^ m).functor ≪≫
        Functor.isoWhiskerLeft e.functor (powAddNat m k ((k : ℤ) + m) rfl) ≪≫
        powStepUp e ((k : ℤ) + m) p (by omega)

/-- The addition law with a nonpositive left exponent. -/
noncomputable def powAddNegNat (m : ℤ) : (k : ℕ) → (p : ℤ) → (-(k : ℤ) + m = p) →
    ((e ^ (-(k : ℤ))).functor ⋙ (e ^ m).functor ≅ (e ^ p).functor)
  | 0, _, h => eqToIso (by
      rw [← h, show -((0:ℕ) : ℤ) + m = m from by omega]
      exact Functor.id_comp _)
  | k + 1, p, h =>
      Functor.isoWhiskerRight (powStepDown e (-(k : ℤ)) (-((k + 1 : ℕ) : ℤ)) (by omega)).symm
          (e ^ m).functor ≪≫
        Functor.isoWhiskerLeft e.inverse (powAddNegNat m k (-(k : ℤ) + m) rfl) ≪≫
        powStepDown e (-(k : ℤ) + m) p (by omega)

/-- The addition law for the integer powers of an autoequivalence. -/
noncomputable def powAdd : (n m p : ℤ) → (n + m = p) →
    ((e ^ n).functor ⋙ (e ^ m).functor ≅ (e ^ p).functor)
  | Int.ofNat k, m, p, h => powAddNat e m k p h
  | Int.negSucc k, m, p, h => powAddNegNat e m (k + 1) p h

/-- The addition law at left exponent zero is the identity. -/
theorem powAdd_zero_left (m : ℤ) : powAdd e 0 m m (zero_add m) = Iso.refl _ := rfl

/-- The up-recursion of the addition law in its left exponent, for `n ≥ 0`. -/
theorem powAdd_succ_of_nonneg {n : ℤ} (hn : 0 ≤ n) (m p q r : ℤ) (hr : n + 1 = r)
    (hp : n + m = p) (hq : p + 1 = q) :
    powAdd e r m q (by omega) =
      Functor.isoWhiskerRight (powStepUp e n r hr).symm (e ^ m).functor ≪≫
        Functor.isoWhiskerLeft e.functor (powAdd e n m p hp) ≪≫ powStepUp e p q hq := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) := ⟨n.toNat, by omega⟩
  subst hp hr
  rfl

/-- The down-recursion of the addition law in its left exponent, for `n ≤ 0`. -/
theorem powAdd_pred_of_nonpos {n : ℤ} (hn : n ≤ 0) (m p q r : ℤ) (hr : n - 1 = r)
    (hp : n + m = p) (hq : p - 1 = q) :
    powAdd e r m q (by omega) =
      Functor.isoWhiskerRight (powStepDown e n r hr).symm (e ^ m).functor ≪≫
        Functor.isoWhiskerLeft e.inverse (powAdd e n m p hp) ≪≫ powStepDown e p q hq := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -(k : ℤ) := ⟨(-n).toNat, by omega⟩
  subst hp hr
  cases k <;> rfl

/-- Factoring `Φ.hom.app X` through `Φ.hom.app Y` along a morphism `u` with a retraction `v`. -/
private theorem hom_app_eq_of_comp_eq_map {F G H : C ⥤ C} (Φ : F ⋙ H ≅ G) {X Y Z W : C}
    (u : X ⟶ Y) (v : Y ⟶ X) (huv : u ≫ v = 𝟙 X) (a : F.obj X ⟶ Z) (b : Z ⟶ F.obj Y)
    (c : G.obj Y ⟶ W) (d : W ⟶ G.obj X) (hab : a ≫ b = F.map u) (hcd : c ≫ d = G.map v) :
    Φ.hom.app X = H.map a ≫ H.map b ≫ Φ.hom.app Y ≫ c ≫ d := by
  have hnat : H.map (F.map u) ≫ Φ.hom.app Y = Φ.hom.app X ≫ G.map u := Φ.hom.naturality u
  rw [← Functor.map_comp_assoc, hab, hcd, reassoc_of% hnat, ← G.map_comp, huv, G.map_id,
    Category.comp_id]

/-- The up-recursion of the addition law in its left exponent. -/
theorem powAdd_succ (n m p q r : ℤ) (hr : n + 1 = r) (hp : n + m = p) (hq : p + 1 = q) :
    powAdd e r m q (by omega) =
      Functor.isoWhiskerRight (powStepUp e n r hr).symm (e ^ m).functor ≪≫
        Functor.isoWhiskerLeft e.functor (powAdd e n m p hp) ≪≫ powStepUp e p q hq := by
  by_cases hn : 0 ≤ n
  · exact powAdd_succ_of_nonneg e hn m p q r hr hp hq
  · rw [powAdd_pred_of_nonpos e (show r ≤ 0 by omega) m q p n (by omega) (by omega) (by omega)]
    ext X
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
    exact hom_app_eq_of_comp_eq_map _ (e.unitIso.hom.app X) (e.unitIso.inv.app X) (by simp) _ _ _ _
      (powStepUp_powStepDown_inv_app ..) (powStepDown_powStepUp_hom_app ..)

/-- The down-recursion of the addition law in its left exponent. -/
theorem powAdd_pred (n m p q r : ℤ) (hr : n - 1 = r) (hp : n + m = p) (hq : p - 1 = q) :
    powAdd e r m q (by omega) =
      Functor.isoWhiskerRight (powStepDown e n r hr).symm (e ^ m).functor ≪≫
        Functor.isoWhiskerLeft e.inverse (powAdd e n m p hp) ≪≫ powStepDown e p q hq := by
  by_cases hn : n ≤ 0
  · exact powAdd_pred_of_nonpos e hn m p q r hr hp hq
  · rw [powAdd_succ_of_nonneg e (show (0:ℤ) ≤ r by omega) m q p n (by omega) (by omega)
      (by omega)]
    ext X
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc]
    exact hom_app_eq_of_comp_eq_map _ (e.counitIso.inv.app X) (e.counitIso.hom.app X) (by simp) _ _
      _ _ (powStepDown_powStepUp_inv_app ..) (powStepUp_powStepDown_hom_app ..)

/-- The addition law at right exponent zero is the identity. -/
theorem powAdd_zero_right (n : ℤ) : powAdd e n 0 n (add_zero n) = Iso.refl _ := by
  induction n using Int.induction_on with
  | zero => exact powAdd_zero_left e 0
  | succ i ih =>
      rw [powAdd_succ e i 0 i (i + 1) (i + 1) rfl (add_zero _) rfl, ih]
      ext X
      simp [refl_functor_eq]
  | pred i ih =>
      rw [powAdd_pred e (-i) 0 (-i) (-i - 1) (-i - 1) rfl (add_zero _) rfl, ih]
      ext X
      simp [refl_functor_eq]

/-- The cocycle identity: the two ways of multiplying three powers agree. -/
theorem powAdd_assoc (n : ℤ) :
    ∀ (m k p t s : ℤ) (h₁ : n + m = p) (h₂ : m + k = t) (h₃ : p + k = s),
      Functor.isoWhiskerRight (powAdd e n m p h₁) (e ^ k).functor ≪≫ powAdd e p k s h₃ =
        Functor.isoWhiskerLeft (e ^ n).functor (powAdd e m k t h₂) ≪≫
          powAdd e n t s (by omega) := by
  induction n using Int.induction_on with
  | zero =>
      intro m k p t s h₁ h₂ h₃
      obtain rfl : p = m := by omega
      obtain rfl : s = t := by omega
      ext X
      simp [powAdd_zero_left, refl_functor_eq]
  | succ i ih =>
      intro m k p t s h₁ h₂ h₃
      rw [powAdd_succ e i m (i + m) p (i + 1) rfl rfl (by omega),
        powAdd_succ e (i + m) k (i + t) s p (by omega) (by omega) (by omega),
        powAdd_succ e i t (i + t) s (i + 1) rfl rfl (by omega)]
      ext X
      have hIH := NatTrans.congr_app
        (congrArg Iso.hom (ih m k (i + m) t (i + t) rfl h₂ (by omega))) (e.functor.obj X)
      have hnat := (powAdd e m k t h₂).hom.naturality ((powStepUp e i (i + 1) rfl).inv.app X)
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map] at hIH hnat ⊢
      rw [← Functor.map_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, Category.comp_id, Functor.map_comp, Category.assoc]
      rw [reassoc_of% hIH, reassoc_of% hnat]
  | pred i ih =>
      intro m k p t s h₁ h₂ h₃
      rw [powAdd_pred e (-i) m (-i + m) p (-i - 1) rfl rfl (by omega),
        powAdd_pred e (-i + m) k (-i + t) s p (by omega) (by omega) (by omega),
        powAdd_pred e (-i) t (-i + t) s (-i - 1) rfl rfl (by omega)]
      ext X
      have hIH := NatTrans.congr_app
        (congrArg Iso.hom (ih m k (-i + m) t (-i + t) rfl h₂ (by omega))) (e.inverse.obj X)
      have hnat := (powAdd e m k t h₂).hom.naturality ((powStepDown e (-i) (-i - 1) rfl).inv.app X)
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
        Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
        Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map] at hIH hnat ⊢
      rw [← Functor.map_comp_assoc, Category.assoc, Category.assoc, Iso.hom_inv_id_app]
      simp only [Functor.comp_obj, Category.comp_id, Functor.map_comp, Category.assoc]
      rw [reassoc_of% hIH, reassoc_of% hnat]

/-! ### Naturality and the normalisation at exponent one -/

/-- Naturality of the addition law. -/
theorem powAdd_hom_naturality (n m p : ℤ) (h : n + m = p) {X Y : C} (f : X ⟶ Y) :
    (e ^ m).functor.map ((e ^ n).functor.map f) ≫ (powAdd e n m p h).hom.app Y =
      (powAdd e n m p h).hom.app X ≫ (e ^ p).functor.map f :=
  (powAdd e n m p h).hom.naturality f

/-- Naturality of the inverse of the addition law. -/
theorem powAdd_inv_naturality (n m p : ℤ) (h : n + m = p) {X Y : C} (f : X ⟶ Y) :
    (e ^ p).functor.map f ≫ (powAdd e n m p h).inv.app Y =
      (powAdd e n m p h).inv.app X ≫ (e ^ m).functor.map ((e ^ n).functor.map f) :=
  (powAdd e n m p h).inv.naturality f

/-- The successor comparison `(e ^ n).functor ⋙ e.functor ≅ (e ^ p).functor` for `n + 1 = p`,
the addition law at right exponent one. -/
noncomputable def powSucc (n p : ℤ) (h : n + 1 = p) :
    (e ^ n).functor ⋙ e.functor ≅ (e ^ p).functor :=
  powAdd e n 1 p (by omega)

/-- The addition law at right exponent one is the successor comparison. -/
theorem powAdd_one_right (n p : ℤ) (h : n + 1 = p) :
    powAdd e n 1 p h = powSucc e n p h := rfl

/-- The successor comparison at exponent zero is the identity. -/
theorem powSucc_zero : powSucc e 0 1 rfl = Iso.refl _ := powAdd_zero_left e 1

/-- The up-recursion of the successor comparison. -/
theorem powSucc_succ (n p q : ℤ) (hp : n + 1 = p) (hq : p + 1 = q) :
    powSucc e p q hq =
      Functor.isoWhiskerRight (powStepUp e n p hp).symm e.functor ≪≫
        Functor.isoWhiskerLeft e.functor (powSucc e n p hp) ≪≫ powStepUp e p q hq :=
  powAdd_succ e n 1 p q p hp hp hq

end CategoryTheory.Equivalence

end
