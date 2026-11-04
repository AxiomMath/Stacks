module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.TopTruncationExt

/-!
# The trace map `y ↦ t[m] ∘ Φ(y)` of a triangulated functor

Let `Φ : C ⥤ C'` be a functor commuting with the shifts, `B` an object of `C`, `L` an object of
`C'` and `t : Φ(B) ⟶ L[c₀]` a morphism (the trace). For every object `A` and integers
`c₀ + m = c` there is the additive map

`Hom(A, B[m]) → Hom(Φ(A), L[c]),  y ↦ t[m] ∘ Φ(y)`

(`Stacks.RelativeDuality.traceMap`). Relative Poincaré duality for a smooth family of curves
`f : X → S` of relative dimension one says that this map is bijective in every degree
(`Stacks.RelativeDuality.IsBijectiveAt`) for `Φ = Rf_!`, `B = Λ_X`, `L = Λ_S`, `c₀ = -2` and `t`
the top-degree trace. This file collects the formal properties of this condition used to reduce
relative duality for an elementary fibration to the smooth proper curve and the boundary divisor,
in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH):

* the **five lemma** for a distinguished triangle `A₁ → A₂ → A₃ → A₁[1]` and a triangulated `Φ`
  (`Stacks.RelativeDuality.isBijectiveAt_obj₂`): the long exact sequences of `Hom(-, B[m])` and
  of `Hom(Φ(-), L[c])` are compatible on the nose;
* invariance under isomorphisms of `A` (`Stacks.RelativeDuality.isBijectiveAt_of_iso`), under
  composing the trace with an isomorphism `L ≅ L'`
  (`Stacks.RelativeDuality.isBijectiveAt_comp_mk₀_iff`), and the effect of changing `B` along a
  morphism `B ⟶ B'` (`Stacks.RelativeDuality.traceMap_mk₀_map_comp`);
* **changing the functor** along an isomorphism `Φ ≅ Φ'` which need not commute with the shifts:
  the trace map of `Φ'` is that of `Φ` for the trace twisted by an automorphism of `Φ(B)`
  (`Stacks.RelativeDuality.exists_traceMap_eq_of_iso`);
* **rigidity of top-degree traces**: two morphisms `K ⟶ M[0][-n]` from an object of `D(ℬ)` living
  in degrees `≤ n`, both invertible on `Hⁿ`, differ by an automorphism of `M`
  (`Stacks.RelativeDuality.exists_iso_eq_comp_of_isIso_homology`).

## Main definitions

* `Stacks.RelativeDuality.traceMap`, `Stacks.RelativeDuality.IsBijectiveAt`.

## Main results

* `Stacks.RelativeDuality.isBijectiveAt_obj₂`.
* `Stacks.RelativeDuality.exists_traceMap_eq_of_iso`.
* `Stacks.RelativeDuality.exists_iso_eq_comp_of_isIso_homology`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.RelativeDuality

/-! ### Exactness of `Hom(-, X[n])` on a distinguished triangle, for shifted morphisms -/

section Exactness

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (T : Triangle C) (hT : T ∈ distTriang C) {X : C}

include hT in
/-- Exactness of `Hom(T.obj₂, X[n]) → Hom(T.obj₁, X[n]) → Hom(T.obj₃, X[n + 1])`. -/
lemma shiftedHom_exact₁ {n n' : ℤ} (hn : n + 1 = n') (y : ShiftedHom T.obj₁ X n)
    (hy : ShiftedHom.comp (a := (1 : ℤ)) T.mor₃ y hn = 0) :
    ∃ z : ShiftedHom T.obj₂ X n, (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁).comp z (add_zero n) = y := by
  have hy' : T.mor₃ ≫ y⟦(1 : ℤ)⟧' = 0 := by
    simp only [ShiftedHom.comp] at hy
    rw [← Category.assoc] at hy
    exact (cancel_mono _).1 (hy.trans zero_comp.symm)
  obtain ⟨g, hg⟩ : ∃ g : T.obj₂⟦(1 : ℤ)⟧ ⟶ (X⟦n⟧)⟦(1 : ℤ)⟧,
      y⟦(1 : ℤ)⟧' = (-(T.mor₁⟦(1 : ℤ)⟧')) ≫ g := by
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang T hT) (y⟦(1 : ℤ)⟧') hy'
    exact ⟨g, hg⟩
  refine ⟨(shiftFunctor C (1 : ℤ)).preimage (-g), ?_⟩
  rw [ShiftedHom.mk₀_comp]
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_comp, Functor.map_preimage, hg]
  simp

include hT in
/-- Exactness of `Hom(T.obj₃, X[n]) → Hom(T.obj₂, X[n]) → Hom(T.obj₁, X[n])`. -/
lemma shiftedHom_exact₂ {n : ℤ} (y : ShiftedHom T.obj₂ X n)
    (hy : (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁).comp y (add_zero n) = 0) :
    ∃ z : ShiftedHom T.obj₃ X n, (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂).comp z (add_zero n) = y := by
  rw [ShiftedHom.mk₀_comp] at hy
  obtain ⟨z, hz⟩ := Triangle.yoneda_exact₂ T hT y hy
  exact ⟨z, by rw [ShiftedHom.mk₀_comp, hz]⟩

include hT in
/-- Exactness of `Hom(T.obj₁, X[n]) → Hom(T.obj₃, X[n + 1]) → Hom(T.obj₂, X[n + 1])`. -/
lemma shiftedHom_exact₃ {n n' : ℤ} (hn : n + 1 = n') (y : ShiftedHom T.obj₃ X n')
    (hy : (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂).comp y (add_zero n') = 0) :
    ∃ z : ShiftedHom T.obj₁ X n, ShiftedHom.comp (a := (1 : ℤ)) T.mor₃ z hn = y := by
  rw [ShiftedHom.mk₀_comp] at hy
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ T hT y hy
  refine ⟨(shiftFunctor C (1 : ℤ)).preimage (g ≫ (shiftFunctorAdd' C n 1 n' hn).hom.app X), ?_⟩
  simp only [ShiftedHom.comp, Functor.map_preimage, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]
  exact hg.symm

end Exactness

/-! ### Composition with isomorphisms -/

section Iso

variable {D : Type*} [Category* D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive]

omit [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] in
/-- Composing with an isomorphism `Y ≅ Y'` is bijective on shifted morphisms into `Y`. -/
lemma bijective_comp_mk₀_of_iso {X Y Y' : D} (g : Y ≅ Y') (c : ℤ) :
    Function.Bijective (fun x : ShiftedHom X Y c =>
      x.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g.hom) (zero_add c)) := by
  refine ⟨fun x₁ x₂ hx => ?_, fun x => ⟨x.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g.inv) (zero_add c), ?_⟩⟩
  · simp only [ShiftedHom.comp_mk₀] at hx
    simpa using congrArg (· ≫ g.inv⟦c⟧') hx
  · simp [ShiftedHom.comp_mk₀]

omit [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive] in
/-- Precomposing with an isomorphism `X ≅ X'` is bijective on shifted morphisms out of `X'`. -/
lemma bijective_mk₀_comp_of_iso {X X' Y : D} (g : X ≅ X') (c : ℤ) :
    Function.Bijective (fun x : ShiftedHom X' Y c =>
      (ShiftedHom.mk₀ (0 : ℤ) rfl g.hom).comp x (add_zero c)) := by
  refine ⟨fun x₁ x₂ hx => ?_, fun x => ⟨(ShiftedHom.mk₀ (0 : ℤ) rfl g.inv).comp x (add_zero c),
    ?_⟩⟩
  · simp only [ShiftedHom.mk₀_comp] at hx
    exact (cancel_epi g.hom).1 hx
  · simp [ShiftedHom.mk₀_comp]

end Iso

/-! ### The trace map -/

section TraceMap

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasShift C ℤ] [HasShift C' ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (Φ : C ⥤ C') [Φ.CommShift ℤ] [Φ.Additive] {B : C} {L : C'} {c₀ : ℤ}
  (t : ShiftedHom (Φ.obj B) L c₀)

/-- **The trace map** `Hom(A, B[m]) → Hom(Φ(A), L[c])`, `y ↦ t[m] ∘ Φ(y)`, for `c₀ + m = c`. -/
def traceMap (A : C) (m c : ℤ) (h : c₀ + m = c) :
    ShiftedHom A B m →+ ShiftedHom (Φ.obj A) L c where
  toFun y := (y.map Φ).comp t h
  map_zero' := by simp [ShiftedHom.zero_comp]
  map_add' y₁ y₂ := by simp [ShiftedHom.add_comp]

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- The trace map sends `y` to `t[m] ∘ Φ(y)`. -/
lemma traceMap_apply (A : C) (m c : ℤ) (h : c₀ + m = c) (y : ShiftedHom A B m) :
    traceMap Φ t A m c h y = (y.map Φ).comp t h :=
  rfl

/-- **The trace map is bijective at `A`** in every degree. -/
def IsBijectiveAt (A : C) : Prop :=
  ∀ (m c : ℤ) (h : c₀ + m = c), Function.Bijective (traceMap Φ t A m c h)

variable {Φ t}

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- The trace map is natural in `A`. -/
lemma traceMap_mk₀_comp {A A' : C} (u : A ⟶ A') (m c : ℤ) (h : c₀ + m = c)
    (y : ShiftedHom A' B m) :
    traceMap Φ t A m c h ((ShiftedHom.mk₀ (0 : ℤ) rfl u).comp y (add_zero m)) =
      (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map u)).comp (traceMap Φ t A' m c h y) (add_zero c) := by
  simp only [traceMap_apply, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- The trace map commutes with composition with a shifted morphism `A₃ ⟶ A₁[1]`. -/
lemma traceMap_comp_shift {A₁ A₃ : C} (δ : ShiftedHom A₃ A₁ (1 : ℤ)) {m m' c c' : ℤ}
    (hm : m + 1 = m') (h : c₀ + m = c) (h' : c₀ + m' = c') (hc : c + 1 = c')
    (y : ShiftedHom A₁ B m) :
    traceMap Φ t A₃ m' c' h' (δ.comp y hm) = (δ.map Φ).comp (traceMap Φ t A₁ m c h y) hc := by
  simp only [traceMap_apply, ShiftedHom.map_comp]
  exact ShiftedHom.comp_assoc _ _ _ _ _ (by omega)

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- Composing the trace with a morphism `g : L ⟶ L'` composes the trace map with `g`. -/
lemma traceMap_comp_mk₀ {L' : C'} (g : L ⟶ L') (A : C) (m c : ℤ) (h : c₀ + m = c)
    (y : ShiftedHom A B m) :
    traceMap Φ (t.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g) (zero_add c₀)) A m c h y =
      (traceMap Φ t A m c h y).comp (ShiftedHom.mk₀ (0 : ℤ) rfl g) (zero_add c) := by
  simp only [traceMap_apply]
  exact (ShiftedHom.comp_assoc _ _ _ _ _ (by omega)).symm

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- Changing `B` along `ε : B ⟶ B'`: the trace map for the trace `t' ∘ Φ(ε)` at `y` is the trace
map for `t'` at `ε[m] ∘ y`. -/
lemma traceMap_mk₀_map_comp {B' : C} (ε : B ⟶ B') (t' : ShiftedHom (Φ.obj B') L c₀) (A : C)
    (m c : ℤ) (h : c₀ + m = c) (y : ShiftedHom A B m) :
    traceMap Φ ((ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map ε)).comp t' (add_zero c₀)) A m c h y =
      traceMap Φ t' A m c h (y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ε) (zero_add m)) := by
  simp only [traceMap_apply, ShiftedHom.map_comp, ShiftedHom.map_mk₀]
  exact (ShiftedHom.comp_assoc _ _ _ _ _ (by omega)).symm

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- **Bijectivity of the trace map does not change when the trace is composed with an
isomorphism `L ≅ L'`.** -/
lemma isBijectiveAt_comp_mk₀_iff {L' : C'} (g : L ≅ L') (A : C) :
    IsBijectiveAt Φ (t.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g.hom) (zero_add c₀)) A ↔
      IsBijectiveAt Φ t A := by
  refine forall_congr' fun m => forall_congr' fun c => forall_congr' fun h => ?_
  have e : ⇑(traceMap Φ (t.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g.hom) (zero_add c₀)) A m c h) =
      (fun x => x.comp (ShiftedHom.mk₀ (0 : ℤ) rfl g.hom) (zero_add c)) ∘ traceMap Φ t A m c h :=
    funext (traceMap_comp_mk₀ g.hom A m c h)
  rw [e]
  exact Function.Bijective.of_comp_iff' (bijective_comp_mk₀_of_iso (X := Φ.obj A) g c) _

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- **Bijectivity of the trace map in one degree is invariant under isomorphisms of `A`.** -/
theorem bijective_traceMap_of_iso {A A' : C} (e : A ≅ A') {m c : ℤ} (h : c₀ + m = c)
    (hA : Function.Bijective (traceMap Φ t A m c h)) :
    Function.Bijective (traceMap Φ t A' m c h) := by
  have hfac : (fun y => (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map e.hom)).comp y (add_zero c)) ∘
      traceMap Φ t A' m c h =
      traceMap Φ t A m c h ∘ (fun y => (ShiftedHom.mk₀ (0 : ℤ) rfl e.hom).comp y (add_zero m)) := by
    funext y
    exact (traceMap_mk₀_comp e.hom m c h y).symm
  have h₁ : Function.Bijective (fun y : ShiftedHom (Φ.obj A') L c =>
      (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map e.hom)).comp y (add_zero c)) :=
    bijective_mk₀_comp_of_iso (Y := L) (Φ.mapIso e) c
  exact (Function.Bijective.of_comp_iff' h₁ _).1
    (by rw [hfac]; exact hA.comp (bijective_mk₀_comp_of_iso (Y := B) e m))

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- **Bijectivity of the trace map is invariant under isomorphisms of `A`.** -/
theorem isBijectiveAt_of_iso {A A' : C} (e : A ≅ A') (hA : IsBijectiveAt Φ t A) :
    IsBijectiveAt Φ t A' :=
  fun m c h => bijective_traceMap_of_iso e h (hA m c h)

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- **Changing `B` along an isomorphism `ε : B ≅ B'`**: the trace map for the trace `t' ∘ Φ(ε)`
is bijective exactly when the trace map for `t'` is. -/
theorem bijective_traceMap_mk₀_map_comp_iff {B' : C} (ε : B ≅ B') (t' : ShiftedHom (Φ.obj B') L c₀)
    (A : C) {m c : ℤ} (h : c₀ + m = c) :
    Function.Bijective
        (traceMap Φ ((ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map ε.hom)).comp t' (add_zero c₀)) A m c h) ↔
      Function.Bijective (traceMap Φ t' A m c h) := by
  have e :
      ⇑(traceMap Φ ((ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map ε.hom)).comp t' (add_zero c₀)) A m c h) =
      traceMap Φ t' A m c h ∘ (fun y => y.comp (ShiftedHom.mk₀ (0 : ℤ) rfl ε.hom) (zero_add m)) :=
    funext (traceMap_mk₀_map_comp ε.hom t' A m c h)
  rw [e]
  exact Function.Bijective.of_comp_iff _ (bijective_comp_mk₀_of_iso ε m)

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- **Changing the functor along an isomorphism which need not commute with the shifts.** Let
`Φ'` be a second functor, `α_A : Φ(A) ≅ Φ'(A)`, `α_B : Φ(B) ≅ Φ'(B)` and
`α : Φ(B[m]) ≅ Φ'(B[m])` compatible with `Φ` and `Φ'` on morphisms `A ⟶ B[m]`. Then for every
trace `t'` on `Φ'(B)` there is an automorphism `s` of `Φ(B)` such that the trace map of `Φ'` and
`t'` in degree `m` is that of `Φ` and `t' ∘ α_B ∘ s`, followed by `α_A⁻¹`. -/
theorem exists_traceMap_eq_of_iso (Φ' : C ⥤ C') [Φ'.CommShift ℤ] [Φ'.Additive] {A : C}
    {m : ℤ} (αA : Φ.obj A ≅ Φ'.obj A) (αB : Φ.obj B ≅ Φ'.obj B)
    (α : Φ.obj (B⟦m⟧) ≅ Φ'.obj (B⟦m⟧))
    (hα : ∀ y : A ⟶ B⟦m⟧, Φ.map y ≫ α.hom = αA.hom ≫ Φ'.map y)
    (t' : ShiftedHom (Φ'.obj B) L c₀) :
    ∃ s : Φ.obj B ≅ Φ.obj B, ∀ (c : ℤ) (h : c₀ + m = c) (y : ShiftedHom A B m),
      traceMap Φ' t' A m c h y = (ShiftedHom.mk₀ (0 : ℤ) rfl αA.inv).comp
        (traceMap Φ (s.hom ≫ αB.hom ≫ t') A m c h y) (add_zero c) := by
  let δ : (Φ.obj B)⟦m⟧ ≅ (Φ.obj B)⟦m⟧ :=
    ((Φ.commShiftIso m).app B).symm ≪≫ α ≪≫ (Φ'.commShiftIso m).app B ≪≫
      ((shiftFunctor C' m).mapIso αB).symm
  obtain ⟨s, hs⟩ : ∃ s : Φ.obj B ≅ Φ.obj B, (shiftFunctor C' m).map s.hom = δ.hom :=
    ⟨(shiftFunctor C' m).preimageIso δ, by simp⟩
  refine ⟨s, fun c h y => ?_⟩
  rw [traceMap_apply, traceMap_apply, ShiftedHom.mk₀_comp]
  simp only [ShiftedHom.comp, ShiftedHom.map, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hs]
  simp only [δ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (hα y)]
  simp

end TraceMap

/-! ### The five lemma -/

section FiveLemma

variable {C C' : Type*} [Category* C] [Category* C'] [Preadditive C] [Preadditive C']
  [HasZeroObject C] [HasZeroObject C'] [HasShift C ℤ] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C' n).Additive]
  [Pretriangulated C] [Pretriangulated C']
  {Φ : C ⥤ C'} [Φ.CommShift ℤ] [Φ.IsTriangulated] {B : C} {L : C'} {c₀ : ℤ}
  {t : ShiftedHom (Φ.obj B) L c₀} (T : Triangle C) (hT : T ∈ distTriang C)

include hT in
/-- **The five lemma for the trace map**: for a distinguished triangle `A₁ → A₂ → A₃ → A₁[1]`
and a triangulated functor `Φ`, if the trace map is bijective at `A₁` and at `A₃` in every
degree, it is bijective at `A₂` in every degree. -/
theorem isBijectiveAt_obj₂ (h₁ : IsBijectiveAt Φ t T.obj₁) (h₃ : IsBijectiveAt Φ t T.obj₃) :
    IsBijectiveAt Φ t T.obj₂ := by
  have hT' := Φ.map_distinguished T hT
  have hδ : (Φ.mapTriangle.obj T).mor₃ = ShiftedHom.map (a := (1 : ℤ)) T.mor₃ Φ := rfl
  intro m c h
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have hy₁ : (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁).comp y (add_zero m) = 0 := by
      apply (h₁ m c h).1
      rw [traceMap_mk₀_comp, hy, ShiftedHom.comp_zero, map_zero]
    obtain ⟨z, rfl⟩ := shiftedHom_exact₂ T hT y hy₁
    have hz : (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₂)).comp
        (traceMap Φ t T.obj₃ m c h z) (add_zero c) = 0 := by
      rwa [← traceMap_mk₀_comp]
    obtain ⟨w', hw'⟩ := shiftedHom_exact₃ _ hT' (show c - 1 + 1 = c by omega) _ hz
    obtain ⟨w, rfl⟩ := (h₁ (m - 1) (c - 1) (by omega)).2 w'
    have hzw : z = ShiftedHom.comp (a := (1 : ℤ)) T.mor₃ w
        (show m - 1 + 1 = m by omega) := by
      apply (h₃ m c h).1
      rw [traceMap_comp_shift (m := m - 1) (c := c - 1) _ (show m - 1 + 1 = m by omega)
        (show c₀ + (m - 1) = c - 1 by omega) h (show c - 1 + 1 = c by omega), ← hw', hδ]
      rfl
    rw [hzw, ShiftedHom.mk₀_comp]
    simp only [ShiftedHom.comp]
    rw [← Category.assoc, comp_distTriang_mor_zero₂₃ T hT, zero_comp]
  · intro x
    obtain ⟨w₁, hw₁⟩ := (h₁ m c h).2 ((ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₁)).comp x
      (add_zero c))
    have h0 : ShiftedHom.map (a := (1 : ℤ)) T.mor₃ Φ ≫ (Φ.map T.mor₁)⟦(1 : ℤ)⟧' = 0 :=
      comp_distTriang_mor_zero₃₁ _ hT'
    have hw₁' : ShiftedHom.comp (a := (1 : ℤ)) T.mor₃ w₁
        (show m + 1 = m + 1 from rfl) = 0 := by
      apply (h₃ (m + 1) (c + 1) (by omega)).1
      rw [traceMap_comp_shift _ rfl h (by omega) rfl, hw₁, map_zero, ShiftedHom.mk₀_comp]
      simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
      rw [← Category.assoc, h0, zero_comp]
    obtain ⟨y₀, rfl⟩ := shiftedHom_exact₁ T hT rfl w₁ hw₁'
    have e1 := traceMap_mk₀_comp (Φ := Φ) (t := t) T.mor₁ m c h y₀
    rw [hw₁, ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp] at e1
    have hx' : (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₁)).comp
        (x - traceMap Φ t T.obj₂ m c h y₀) (add_zero c) = 0 := by
      rw [ShiftedHom.mk₀_comp, Preadditive.comp_sub, e1, sub_self]
    obtain ⟨x₃, hx₃⟩ : ∃ x₃ : ShiftedHom (Φ.obj T.obj₃) L c,
        (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₂)).comp x₃ (add_zero c) =
          x - traceMap Φ t T.obj₂ m c h y₀ := shiftedHom_exact₂ _ hT' _ hx'
    obtain ⟨z₃, rfl⟩ := (h₃ m c h).2 x₃
    refine ⟨y₀ + (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂).comp z₃ (add_zero m), ?_⟩
    rw [map_add, traceMap_mk₀_comp, hx₃]
    abel

include hT in
/-- **The five lemma for the trace map, at the first vertex**: for a distinguished triangle
`A₁ → A₂ → A₃ → A₁[1]` and a triangulated functor `Φ`, if the trace map is bijective at `A₂` and
at `A₃` in every degree, it is bijective at `A₁` in every degree. -/
theorem isBijectiveAt_obj₁ (h₂ : IsBijectiveAt Φ t T.obj₂) (h₃ : IsBijectiveAt Φ t T.obj₃) :
    IsBijectiveAt Φ t T.obj₁ := by
  have hT' := Φ.map_distinguished T hT
  intro m c h
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have hδy : ShiftedHom.comp (a := (1 : ℤ)) T.mor₃ y (rfl : m + 1 = m + 1) = 0 := by
      apply (h₃ (m + 1) (c + 1) (by omega)).1
      rw [traceMap_comp_shift _ rfl h (by omega) rfl, hy, ShiftedHom.comp_zero, map_zero]
    obtain ⟨z, rfl⟩ := shiftedHom_exact₁ T hT rfl y hδy
    have hz : (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₁)).comp
        (traceMap Φ t T.obj₂ m c h z) (add_zero c) = 0 := by
      rwa [← traceMap_mk₀_comp]
    obtain ⟨x₃, hx₃⟩ : ∃ x₃ : ShiftedHom (Φ.obj T.obj₃) L c,
        (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₂)).comp x₃ (add_zero c) =
          traceMap Φ t T.obj₂ m c h z := shiftedHom_exact₂ _ hT' _ hz
    obtain ⟨w, rfl⟩ := (h₃ m c h).2 x₃
    have hzw : z = (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂).comp w (add_zero m) := by
      apply (h₂ m c h).1
      rw [traceMap_mk₀_comp, hx₃]
    rw [hzw, ShiftedHom.mk₀_comp, ShiftedHom.mk₀_comp, ← Category.assoc,
      comp_distTriang_mor_zero₁₂ T hT, zero_comp]
  · intro x
    obtain ⟨w, hw⟩ := (h₃ (m + 1) (c + 1) (by omega)).2
      (ShiftedHom.comp (a := (1 : ℤ)) (ShiftedHom.map (a := (1 : ℤ)) T.mor₃ Φ) x
        (rfl : c + 1 = c + 1))
    have h0 : Φ.map T.mor₂ ≫ ShiftedHom.map (a := (1 : ℤ)) T.mor₃ Φ = 0 :=
      comp_distTriang_mor_zero₂₃ _ hT'
    have hw' : (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₂).comp w (add_zero (m + 1)) = 0 := by
      apply (h₂ (m + 1) (c + 1) (by omega)).1
      rw [traceMap_mk₀_comp, hw, map_zero, ShiftedHom.mk₀_comp]
      simp only [ShiftedHom.comp]
      rw [← Category.assoc, h0, zero_comp]
    obtain ⟨y₀, rfl⟩ := shiftedHom_exact₃ T hT rfl w hw'
    have e1 := traceMap_comp_shift (Φ := Φ) (t := t) T.mor₃ (rfl : m + 1 = m + 1) h
      (show c₀ + (m + 1) = c + 1 by omega) rfl y₀
    rw [hw] at e1
    have hx' : ShiftedHom.comp (a := (1 : ℤ)) (ShiftedHom.map (a := (1 : ℤ)) T.mor₃ Φ)
        (x - traceMap Φ t T.obj₁ m c h y₀) (rfl : c + 1 = c + 1) = 0 := by
      rw [sub_eq_add_neg, ShiftedHom.comp_add, ShiftedHom.comp_neg, e1, add_neg_cancel]
    obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ShiftedHom (Φ.obj T.obj₂) L c,
        (ShiftedHom.mk₀ (0 : ℤ) rfl (Φ.map T.mor₁)).comp x₂ (add_zero c) =
          x - traceMap Φ t T.obj₁ m c h y₀ := shiftedHom_exact₁ _ hT' rfl _ hx'
    obtain ⟨z, rfl⟩ := (h₂ m c h).2 x₂
    refine ⟨y₀ + (ShiftedHom.mk₀ (0 : ℤ) rfl T.mor₁).comp z (add_zero m), ?_⟩
    rw [map_add, traceMap_mk₀_comp, hx₂]
    abel

end FiveLemma

/-! ### Rigidity of top-degree traces -/

section Rigidity

variable {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]

/-- **Two top-degree traces differ by an automorphism.** For `K` in `D(ℬ)` living in degrees
`≤ n` and two morphisms `t, t' : K ⟶ M[0][-n]` both inducing isomorphisms on `Hⁿ`, there is an
automorphism `a` of `M` with `t' = a[0][-n] ∘ t`. -/
theorem exists_iso_eq_comp_of_isIso_homology {K : DerivedCategory B} (n : ℤ) (hK : K.IsLE n)
    {M : B} (t t' : ShiftedHom K ((DerivedCategory.singleFunctor B 0).obj M) (-n))
    (ht : IsIso ((DerivedCategory.homologyFunctor B n).map t))
    (ht' : IsIso ((DerivedCategory.homologyFunctor B n).map t')) :
    ∃ a : M ≅ M, t' = t.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor B 0).map a.hom)) (zero_add _) := by
  let σ := (Stacks.TopTruncationExt.singleShiftHomologyIso (B := B) n).app M
  let φ : (DerivedCategory.homologyFunctor B n).obj K ≅ M :=
    asIso ((DerivedCategory.homologyFunctor B n).map t) ≪≫ σ
  let φ' : (DerivedCategory.homologyFunctor B n).obj K ≅ M :=
    asIso ((DerivedCategory.homologyFunctor B n).map t') ≪≫ σ
  refine ⟨φ.symm ≪≫ φ', ?_⟩
  apply (Stacks.TopTruncationExt.bijective_homologyFunctor_map K n hK M).injective
  have hnat := (Stacks.TopTruncationExt.singleShiftHomologyIso (B := B) n).hom.naturality
    (φ.symm ≪≫ φ').hom
  dsimp at hnat
  dsimp only
  rw [ShiftedHom.comp_mk₀, Functor.map_comp, Category.assoc]
  simp only [Iso.trans_hom, Iso.symm_hom] at hnat ⊢
  rw [hnat]
  simp [φ, φ', σ]

/-- **Bijectivity of the trace map does not depend on the choice of a top-degree trace**: for
`Φ(B)` living in degrees `≤ n` and two traces `t, t' : Φ(B) ⟶ M[0][-n]` inducing isomorphisms
on `Hⁿ`, the trace maps of `t` and of `t'` are bijective in the same degrees. -/
theorem bijective_traceMap_iff_of_isIso_homology {C : Type*} [Category* C] [Preadditive C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] (Φ : C ⥤ DerivedCategory B)
    [Φ.CommShift ℤ] [Φ.Additive] {X : C} (n : ℤ) (hK : (Φ.obj X).IsLE n) {M : B}
    (t t' : ShiftedHom (Φ.obj X) ((DerivedCategory.singleFunctor B 0).obj M) (-n))
    (ht : IsIso ((DerivedCategory.homologyFunctor B n).map t))
    (ht' : IsIso ((DerivedCategory.homologyFunctor B n).map t')) (A : C) {m c : ℤ}
    (h : -n + m = c) :
    Function.Bijective (traceMap Φ t A m c h) ↔ Function.Bijective (traceMap Φ t' A m c h) := by
  obtain ⟨a, rfl⟩ := exists_iso_eq_comp_of_isIso_homology n hK t t' ht ht'
  have e : ⇑(traceMap Φ (t.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
      ((DerivedCategory.singleFunctor B 0).map a.hom)) (zero_add _)) A m c h) =
      (fun x => x.comp (ShiftedHom.mk₀ (0 : ℤ) rfl
        ((DerivedCategory.singleFunctor B 0).map a.hom)) (zero_add c)) ∘ traceMap Φ t A m c h :=
    funext (traceMap_comp_mk₀ _ A m c h)
  rw [e]
  exact (Function.Bijective.of_comp_iff'
    (bijective_comp_mk₀_of_iso ((DerivedCategory.singleFunctor B 0).mapIso a) c) _).symm

end Rigidity

end Stacks.RelativeDuality

end
