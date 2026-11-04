module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.Grp.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.WayOutPairing

/-!
# Duality pairings for a homological functor on a pretriangulated category

Let `C` be a category with a shift by `ℤ`, `H : C ⥤ Ab` an additive functor, `D` an object,
`N` an integer and `τ : H(D[N]) → A` an additive map to an abelian group. For an object `M` and
`i + j = N` there is a pairing

`H(M[i]) × Hom(M, D[j]) → A,  (x, y) ↦ τ (H(y[i]) x)`,

(`Stacks.HomologicalDuality.pairing`, with `y[i] : M[i] ⟶ D[j][i] ≅ D[N]`), and *duality holds at
`M`* (`Stacks.HomologicalDuality.IsPerfect`) when for all integers `i + j = N` the induced map
`H(M[i]) → Hom(Hom(M, D[j]), A)` is bijective. For `H = Hom(Λ_k, RΓ_c(-))` on the derived category
of a variety, `D = Λ` and `τ` a trace on `H^N_c`, this is Poincaré duality for the complex `M`,
`H^i_c(M) × Ext^j(M, Λ) → H^N_c(Λ) → Λ`, in all integer degrees.

The results are the formal properties used to prove Poincaré duality for the complex `Rf_! Λ` of
an elementary fibration in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH):

* duality is invariant under isomorphisms and under shifts of `M`
  (`Stacks.HomologicalDuality.isPerfect_iff_of_iso`, `Stacks.HomologicalDuality.isPerfect_shift`);
* the **five lemma**: for a distinguished triangle `M₁ → M₂ → M₃ → M₁[1]` and `H` homological,
  duality at `M₁` and at `M₃` gives duality at `M₂`, when `A` has the extension property for
  subgroups of the groups `Hom(M, D[j])` (`Stacks.HomologicalDuality.isPerfect_obj₂`); the long
  exact sequences are those of `H` (`CategoryTheory.Functor.homologySequence_exact₂`, for the
  tautological shift sequence) and of `Hom(-, D[j])`, and the squares commute on the nose;
* **transfer along a functor**: for `F : C ⥤ C'` commuting with the shifts, `H ≅ F ⋙ H'` and
  `θ : F D ⟶ D'[c]`, duality at `M` for `τ' ∘ θ_*` is duality at `F M` for `τ'` as soon as
  `y ↦ θ[j] ∘ F(y)` is bijective `Hom(M, D[j]) → Hom(F M, D'[j + c])` for all `j`
  (`Stacks.HomologicalDuality.isPerfect_iff_of_transfer`). For an elementary fibration
  `f : U → S` this moves duality on `U` to duality on `S` for `Rf_! Λ`, through relative duality
  for curves.

## Main definitions

* `Stacks.HomologicalDuality.pairing`, `Stacks.HomologicalDuality.IsPerfect`.
* `Stacks.HomologicalDuality.transferTrace`.

## Main results

* `Stacks.HomologicalDuality.bijective_iff_of_comp`.
* `Stacks.HomologicalDuality.isPerfect_iff_of_iso`, `Stacks.HomologicalDuality.isPerfect_shift`.
* `Stacks.HomologicalDuality.isPerfect_obj₂`.
* `Stacks.HomologicalDuality.isPerfect_iff_of_transfer`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v v' u u'

namespace Stacks.HomologicalDuality

/-- **Bijectivity of a pairing transported along bijections**: if `P' (a x) ∘ g = P x` for
bijections `a : X → X'` and `g : Y →+ Y'`, then `P` is bijective if and only if `P'` is. -/
theorem bijective_iff_of_comp {X X' Y Y' A : Type*} [AddCommGroup Y] [AddCommGroup Y']
    [AddCommGroup A] (P : X → (Y →+ A)) (P' : X' → (Y' →+ A)) (a : X → X')
    (ha : Function.Bijective a) (g : Y →+ Y') (hg : Function.Bijective g)
    (hP : ∀ x y, P' (a x) (g y) = P x y) :
    Function.Bijective P ↔ Function.Bijective P' := by
  let eg : Y ≃+ Y' := AddEquiv.ofBijective g hg
  let β : (Y' →+ A) ≃ (Y →+ A) :=
    { toFun φ := φ.comp g
      invFun φ := φ.comp eg.symm.toAddMonoidHom
      left_inv φ := by
        ext y
        simp [eg, AddEquiv.ofBijective_apply_symm_apply]
      right_inv φ := by
        ext y
        exact congrArg φ (eg.symm_apply_apply y) }
  have hcomp : β ∘ P' ∘ a = P := by
    funext x
    ext y
    exact hP x y
  rw [← hcomp, Function.Bijective.of_comp_iff' β.bijective, Function.Bijective.of_comp_iff _ ha]

section Pairing

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  (H : C ⥤ AddCommGrpCat.{w}) [H.Additive] (D : C) (N : ℤ) {A : Type*} [AddCommGroup A]
  (τ : H.obj (D⟦N⟧) →+ A)

/-- The morphism `H(M[i]) ⟶ H(D[N])` induced by `y : M ⟶ D[j]` when `i + j = N`: the shift
`y[i] : M[i] ⟶ D[j][i]` followed by `D[j][i] ≅ D[N]`. -/
def shiftHom {M : C} {j : ℤ} (y : M ⟶ D⟦j⟧) (i : ℤ) (h : i + j = N) :
    H.obj (M⟦i⟧) ⟶ H.obj (D⟦N⟧) :=
  H.map (y⟦i⟧' ≫ (shiftFunctorAdd' C j i N (by omega)).inv.app D)

/-- **The duality pairing** `H(M[i]) → Hom(Hom(M, D[j]), A)`, `x ↦ (y ↦ τ (H(y[i]) x))`, for
`i + j = N`. -/
def pairing (M : C) (i j : ℤ) (h : i + j = N) : H.obj (M⟦i⟧) →+ ((M ⟶ D⟦j⟧) →+ A) where
  toFun x :=
    { toFun y := τ ((shiftHom H D N y i h).hom x)
      map_zero' := by simp [shiftHom]
      map_add' y₁ y₂ := by simp [shiftHom, Functor.map_add, Preadditive.add_comp] }
  map_zero' := by ext; simp
  map_add' x₁ x₂ := by ext; simp

/-- The pairing evaluated at `x` and `y` is `τ (H(y[i]) x)`. -/
@[simp]
lemma pairing_apply (M : C) (i j : ℤ) (h : i + j = N) (x : H.obj (M⟦i⟧)) (y : M ⟶ D⟦j⟧) :
    pairing H D N τ M i j h x y = τ ((shiftHom H D N y i h).hom x) :=
  rfl

/-- **Duality holds at `M`**: for all integers `i + j = N` the pairing
`H(M[i]) × Hom(M, D[j]) → A` identifies `H(M[i])` with `Hom(Hom(M, D[j]), A)`. -/
def IsPerfect (M : C) : Prop :=
  ∀ (i j : ℤ) (h : i + j = N), Function.Bijective (pairing H D N τ M i j h)

variable {H D N τ}

omit [Preadditive C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [H.Additive] in
/-- For `u : M ⟶ M'` and `y : M' ⟶ D[j]`, the morphism induced by `u ≫ y` is `H(u[i])` followed
by the morphism induced by `y`. -/
lemma shiftHom_comp {M M' : C} (u : M ⟶ M') {j : ℤ} (y : M' ⟶ D⟦j⟧) (i : ℤ) (h : i + j = N) :
    shiftHom H D N (u ≫ y) i h = H.map (u⟦i⟧') ≫ shiftHom H D N y i h := by
  simp [shiftHom]

/-- The pairing is natural in `M`: for `u : M ⟶ M'`, `y` paired with `H(u[i]) x` is `u ≫ y`
paired with `x`. -/
lemma pairing_map {M M' : C} (u : M ⟶ M') {i j : ℤ} (h : i + j = N) (x : H.obj (M⟦i⟧))
    (y : M' ⟶ D⟦j⟧) :
    pairing H D N τ M' i j h ((H.map (u⟦i⟧')).hom x) y = pairing H D N τ M i j h x (u ≫ y) := by
  simp only [pairing_apply, shiftHom_comp, AddCommGrpCat.hom_comp, AddMonoidHom.comp_apply]

/-- **Duality is invariant under isomorphisms of `M`.** -/
theorem isPerfect_of_iso {M M' : C} (e : M ≅ M') (hM : IsPerfect H D N τ M) :
    IsPerfect H D N τ M' := by
  intro i j h
  let a := (H.mapIso ((shiftFunctor C i).mapIso e)).addCommGroupIsoToAddEquiv
  let g : (M ⟶ D⟦j⟧) →+ (M' ⟶ D⟦j⟧) := Preadditive.leftComp _ e.inv
  have hg : Function.Bijective g :=
    ⟨fun y₁ y₂ hy => (cancel_epi e.inv).1 hy,
      fun y => ⟨e.hom ≫ y, by simp [g, Preadditive.leftComp]⟩⟩
  refine (bijective_iff_of_comp _ _ a a.bijective g hg (fun x y => ?_)).1 (hM i j h)
  show pairing H D N τ M' i j h ((H.map (e.hom⟦i⟧')).hom x) (e.inv ≫ y) = _
  rw [pairing_map]
  simp

/-- Duality holds at `M` if and only if it holds at an isomorphic object `M'`. -/
theorem isPerfect_iff_of_iso {M M' : C} (e : M ≅ M') :
    IsPerfect H D N τ M ↔ IsPerfect H D N τ M' :=
  ⟨isPerfect_of_iso e, isPerfect_of_iso e.symm⟩

/-- **Duality is invariant under shifts**: duality at `M` gives duality at `M[n]`; the pairing of
`M[n]` in degrees `(i, j)` is the pairing of `M` in degrees `(n + i, j - n)`. -/
theorem isPerfect_shift {M : C} (n : ℤ) (hM : IsPerfect H D N τ M) :
    IsPerfect H D N τ (M⟦n⟧) := by
  intro i j h
  let a := (H.mapIso ((shiftFunctorAdd' C n i (n + i) rfl).app M)).addCommGroupIsoToAddEquiv
  let g : (M ⟶ D⟦j - n⟧) →+ (M⟦n⟧ ⟶ D⟦j⟧) :=
    { toFun y := y⟦n⟧' ≫ (shiftFunctorAdd' C (j - n) n j (by omega)).inv.app D
      map_zero' := by simp
      map_add' := by simp [Functor.map_add, Preadditive.add_comp] }
  have hpost : Function.Bijective (fun z : M⟦n⟧ ⟶ (D⟦j - n⟧)⟦n⟧ =>
      z ≫ (shiftFunctorAdd' C (j - n) n j (by omega)).inv.app D) :=
    ⟨fun z₁ z₂ hz => (cancel_mono _).1 hz,
      fun z => ⟨z ≫ (shiftFunctorAdd' C (j - n) n j (by omega)).hom.app D, by simp⟩⟩
  have hg : Function.Bijective g :=
    hpost.comp ((Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).map_bijective
      M (D⟦j - n⟧))
  refine (bijective_iff_of_comp _ _ a a.bijective g hg (fun x y => ?_)).1
    (hM (n + i) (j - n) (by omega))
  have nat := (shiftFunctorAdd' C n i (n + i) rfl).inv.naturality y
  dsimp at nat
  have key : (shiftFunctorAdd' C n i (n + i) rfl).hom.app M ≫
      ((y⟦n⟧' ≫ (shiftFunctorAdd' C (j - n) n j (by omega)).inv.app D)⟦i⟧' ≫
        (shiftFunctorAdd' C j i N (by omega)).inv.app D) =
      y⟦n + i⟧' ≫ (shiftFunctorAdd' C (j - n) (n + i) N (by omega)).inv.app D := by
    rw [Functor.map_comp, Category.assoc,
      shiftFunctorAdd'_assoc_inv_app (j - n) n i j (n + i) N (by omega) rfl (by omega),
      ← Category.assoc ((y⟦n⟧')⟦i⟧'), nat]
    simp
  show τ ((shiftHom H D N (g y) i h).hom
      ((H.map ((shiftFunctorAdd' C n i (n + i) rfl).hom.app M)).hom x)) =
    τ ((shiftHom H D N y (n + i) (by omega)).hom x)
  rw [← AddCommGrpCat.comp_apply]
  simp only [shiftHom, ← H.map_comp]
  show τ ((H.map ((shiftFunctorAdd' C n i (n + i) rfl).hom.app M ≫
      ((y⟦n⟧' ≫ (shiftFunctorAdd' C (j - n) n j (by omega)).inv.app D)⟦i⟧' ≫
        (shiftFunctorAdd' C j i N (by omega)).inv.app D))).hom x) = _
  rw [key]

end Pairing

section FiveLemma

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {H : C ⥤ AddCommGrpCat.{w}} [H.IsHomological] {D : C} {N : ℤ} {A : Type*} [AddCommGroup A]
  {τ : H.obj (D⟦N⟧) →+ A} (T : Triangle C) (hT : T ∈ distTriang C)

/-- The connecting map `H(M₃[i]) ⟶ H(M₁[i + 1])` of a triangle `M₁ → M₂ → M₃ → M₁[1]`. -/
def connectingHom (i : ℤ) : H.obj (T.obj₃⟦i⟧) ⟶ H.obj (T.obj₁⟦i + 1⟧) :=
  H.map (T.mor₃⟦i⟧' ≫ (shiftFunctorAdd' C 1 i (i + 1) (by omega)).inv.app T.obj₁)

/-- The connecting map `Hom(M₁, D[j]) → Hom(M₃, D[j + 1])`, `y ↦ y[1] ∘ (M₃ → M₁[1])`. -/
def connectingYoneda (j : ℤ) : (T.obj₁ ⟶ D⟦j⟧) →+ (T.obj₃ ⟶ D⟦j + 1⟧) where
  toFun y := T.mor₃ ≫ y⟦1⟧' ≫ (shiftFunctorAdd' C j 1 (j + 1) rfl).inv.app D
  map_zero' := by simp
  map_add' := by simp [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

include hT in
/-- Exactness of `H(M₁[i]) → H(M₂[i]) → H(M₃[i])` for a distinguished triangle. -/
lemma exact₂_homology (i : ℤ) (x : H.obj (T.obj₂⟦i⟧))
    (hx : (H.map (T.mor₂⟦i⟧')).hom x = 0) : ∃ x₁, (H.map (T.mor₁⟦i⟧')).hom x₁ = x := by
  let := Functor.ShiftSequence.tautological H ℤ
  exact (ShortComplex.ab_exact_iff _).1 (H.homologySequence_exact₂ T hT i) x hx

include hT in
/-- Exactness of `H(M₂[i]) → H(M₃[i]) → H(M₁[i + 1])` at `H(M₃[i])` for a distinguished
triangle. -/
lemma exact₃_homology (i : ℤ) (x : H.obj (T.obj₃⟦i⟧))
    (hx : (connectingHom (H := H) T i).hom x = 0) :
    ∃ x₂, (H.map (T.mor₂⟦i⟧')).hom x₂ = x := by
  let := Functor.ShiftSequence.tautological H ℤ
  have e : H.homologySequenceδ T i (i + 1) rfl = connectingHom (H := H) T i := by
    rw [connectingHom, H.map_comp]
    rfl
  refine (ShortComplex.ab_exact_iff _).1 (H.homologySequence_exact₃ T hT i (i + 1) rfl) x ?_
  show (H.homologySequenceδ T i (i + 1) rfl).hom x = 0
  rwa [e]

include hT in
/-- The connecting map `H(M₃[i]) ⟶ H(M₁[i + 1])` followed by `H(M₁[i + 1]) ⟶ H(M₂[i + 1])` is
zero for a distinguished triangle. -/
lemma map_mor₁_connectingHom (i : ℤ) (x : H.obj (T.obj₃⟦i⟧)) :
    (H.map (T.mor₁⟦i + 1⟧')).hom ((connectingHom (H := H) T i).hom x) = 0 := by
  rw [← AddCommGrpCat.comp_apply, connectingHom, ← H.map_comp, Category.assoc,
    ← NatTrans.naturality]
  dsimp
  rw [← Functor.map_comp_assoc, comp_distTriang_mor_zero₃₁ _ hT]
  simp

include hT in
/-- Exactness of `Hom(M₂, D[j]) → Hom(M₁, D[j]) → Hom(M₃, D[j + 1])` at `Hom(M₁, D[j])` for a
distinguished triangle. -/
lemma exact₁_yoneda (j : ℤ) (y : T.obj₁ ⟶ D⟦j⟧) (hy : connectingYoneda T j y = 0) :
    ∃ y₂, T.mor₁ ≫ y₂ = y := by
  have h₀ : T.mor₃ ≫ y⟦1⟧' = 0 := by
    have h' : T.mor₃ ≫ y⟦1⟧' ≫ (shiftFunctorAdd' C j 1 (j + 1) rfl).inv.app D = 0 := hy
    rw [← Category.assoc] at h'
    exact (cancel_mono ((shiftFunctorAdd' C j 1 (j + 1) rfl).inv.app D)).1
      (h'.trans zero_comp.symm)
  obtain ⟨g, hg⟩ : ∃ g : T.obj₂⟦(1 : ℤ)⟧ ⟶ (D⟦j⟧)⟦(1 : ℤ)⟧,
      y⟦(1 : ℤ)⟧' = -(T.mor₁⟦(1 : ℤ)⟧' ≫ g) := by
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ (rot_of_distTriang _ hT) (y⟦1⟧') h₀
    exact ⟨g, hg.trans (Preadditive.neg_comp (T.mor₁⟦(1 : ℤ)⟧') g)⟩
  refine ⟨-(shiftFunctor C (1 : ℤ)).preimage g, ?_⟩
  apply (shiftFunctor C (1 : ℤ)).map_injective
  rw [Functor.map_comp, Functor.map_neg, Functor.map_preimage, Preadditive.comp_neg, hg]

include hT in
/-- The connecting map `Hom(M₁, D[j]) → Hom(M₃, D[j + 1])` followed by composition with
`M₂ → M₃` is zero for a distinguished triangle. -/
lemma connectingYoneda_mor₂ (j : ℤ) (y : T.obj₁ ⟶ D⟦j⟧) :
    T.mor₂ ≫ connectingYoneda T j y = 0 := by
  simp only [connectingYoneda, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [← Category.assoc, comp_distTriang_mor_zero₂₃ _ hT, zero_comp]

/-- The connecting maps of the two long exact sequences are adjoint under the pairing. -/
lemma pairing_connectingHom {i j : ℤ} (h : i + 1 + j = N) (x : H.obj (T.obj₃⟦i⟧))
    (y : T.obj₁ ⟶ D⟦j⟧) :
    pairing H D N τ T.obj₁ (i + 1) j h ((connectingHom (H := H) T i).hom x) y =
      pairing H D N τ T.obj₃ i (j + 1) (by omega) x (connectingYoneda T j y) := by
  have nat := (shiftFunctorAdd' C 1 i (i + 1) (by omega)).inv.naturality y
  dsimp at nat
  have key : (T.mor₃⟦i⟧' ≫ (shiftFunctorAdd' C 1 i (i + 1) (by omega)).inv.app T.obj₁) ≫
      (y⟦i + 1⟧' ≫ (shiftFunctorAdd' C j (i + 1) N (by omega)).inv.app D) =
      (connectingYoneda T j y)⟦i⟧' ≫ (shiftFunctorAdd' C (j + 1) i N (by omega)).inv.app D := by
    simp only [connectingYoneda, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Functor.map_comp,
      Category.assoc]
    rw [shiftFunctorAdd'_assoc_inv_app j 1 i (j + 1) (i + 1) N rfl (by omega) (by omega),
      ← reassoc_of% nat]
  simp only [pairing_apply, connectingHom, shiftHom]
  rw [← AddCommGrpCat.comp_apply, ← H.map_comp, key]

variable (hA : ∀ (M : C) (j : ℤ) (Hs : AddSubgroup (M ⟶ D⟦j⟧)) (φ : Hs →+ A),
  ∃ ψ : (M ⟶ D⟦j⟧) →+ A, ∀ x : Hs, ψ x = φ x)

include hT hA in
/-- **The five lemma for duality**: for a distinguished triangle `M₁ → M₂ → M₃ → M₁[1]` and a
homological functor `H`, duality at `M₁` and at `M₃` gives duality at `M₂`, when `A` has the
extension property for subgroups of the groups `Hom(M, D[j])`. -/
theorem isPerfect_obj₂ (h₁ : IsPerfect H D N τ T.obj₁) (h₃ : IsPerfect H D N τ T.obj₃) :
    IsPerfect H D N τ T.obj₂ := by
  intro i j h
  constructor
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hx3 : (H.map (T.mor₂⟦i' + 1⟧')).hom x = 0 := by
      apply (h₃ (i' + 1) j h).1
      rw [map_zero]
      ext y₃
      rw [pairing_map, AddMonoidHom.zero_apply]
      exact DFunLike.congr_fun hx _
    obtain ⟨x₁, rfl⟩ := exact₂_homology T hT (i' + 1) x hx3
    obtain ⟨χ, hχ⟩ := CategoryTheory.Abelian.Ext.exists_comp_eq_of_ker_le (hA T.obj₃ (j + 1))
      (connectingYoneda T j) (pairing H D N τ T.obj₁ (i' + 1) j h x₁) (fun y hy => by
        obtain ⟨y₂, rfl⟩ := exact₁_yoneda T hT j y hy
        have := DFunLike.congr_fun hx y₂
        rwa [pairing_map, AddMonoidHom.zero_apply] at this)
    obtain ⟨z, hz⟩ := (h₃ i' (j + 1) (by omega)).2 χ
    have hz' : pairing H D N τ T.obj₁ (i' + 1) j h x₁ = pairing H D N τ T.obj₁ (i' + 1) j h
        ((connectingHom (H := H) T i').hom z) := by
      rw [← hχ, ← hz]
      ext y
      rw [AddMonoidHom.comp_apply, pairing_connectingHom T h]
    rw [(h₁ (i' + 1) j h).1 hz']
    exact map_mor₁_connectingHom T hT i' z
  · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    intro φ
    let α₂ : (T.obj₃ ⟶ D⟦j' + 1⟧) →+ (T.obj₂ ⟶ D⟦j' + 1⟧) := Preadditive.leftComp _ T.mor₂
    obtain ⟨x₃, hx₃⟩ := (h₃ i (j' + 1) h).2 (φ.comp α₂)
    have hδ : (connectingHom (H := H) T i).hom x₃ = 0 := by
      apply (h₁ (i + 1) j' (by omega)).1
      rw [map_zero]
      ext y₁
      rw [AddMonoidHom.zero_apply, pairing_connectingHom T (by omega) x₃ y₁, hx₃,
        AddMonoidHom.comp_apply]
      show φ (T.mor₂ ≫ connectingYoneda T j' y₁) = 0
      rw [connectingYoneda_mor₂ T hT, map_zero]
    obtain ⟨x₂, rfl⟩ := exact₃_homology T hT i x₃ hδ
    let α₁ : (T.obj₂ ⟶ D⟦j' + 1⟧) →+ (T.obj₁ ⟶ D⟦j' + 1⟧) := Preadditive.leftComp _ T.mor₁
    obtain ⟨ψ, hψ⟩ := CategoryTheory.Abelian.Ext.exists_comp_eq_of_ker_le (hA T.obj₁ (j' + 1)) α₁
      (φ - pairing H D N τ T.obj₂ i (j' + 1) h x₂) (fun y hy => by
        obtain ⟨y₃, rfl⟩ := Triangle.yoneda_exact₂ T hT y hy
        have := DFunLike.congr_fun hx₃ y₃
        rw [pairing_map, AddMonoidHom.comp_apply] at this
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply]
        exact sub_eq_zero.2 this.symm)
    obtain ⟨x₁, hx₁⟩ := (h₁ i (j' + 1) h).2 ψ
    refine ⟨x₂ + (H.map (T.mor₁⟦i⟧')).hom x₁, ?_⟩
    rw [map_add]
    have : pairing H D N τ T.obj₂ i (j' + 1) h ((H.map (T.mor₁⟦i⟧')).hom x₁) =
        φ - pairing H D N τ T.obj₂ i (j' + 1) h x₂ := by
      rw [← hψ, ← hx₁]
      ext y
      rw [pairing_map]
      rfl
    rw [this, add_sub_cancel]

end FiveLemma

section Transfer

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  {C' : Type u'} [Category.{v'} C'] [Preadditive C'] [HasShift C' ℤ]
  [∀ n : ℤ, (shiftFunctor C' n).Additive]
  (F : C ⥤ C') [F.CommShift ℤ] [F.Additive]
  {H : C ⥤ AddCommGrpCat.{w}} [H.Additive] {H' : C' ⥤ AddCommGrpCat.{w}} [H'.Additive]
  (e : H ≅ F ⋙ H') {D : C} {D' : C'} {c : ℤ} (θ : F.obj D ⟶ D'⟦c⟧) {N N' : ℤ}
  (hN : N + c = N') {A : Type*} [AddCommGroup A] (τ' : H'.obj (D'⟦N'⟧) →+ A)

/-- The map `H(D[N]) ⟶ H'(D'[N'])` induced by `θ : F D ⟶ D'[c]`, for `N + c = N'`. -/
def transferHom : H.obj (D⟦N⟧) ⟶ H'.obj (D'⟦N'⟧) :=
  e.hom.app (D⟦N⟧) ≫ H'.map ((F.commShiftIso N).hom.app D ≫ θ⟦N⟧' ≫
    (shiftFunctorAdd' C' c N N' (by omega)).inv.app D')

/-- **The transferred trace** `τ' ∘ θ_*` on `H(D[N])`. -/
def transferTrace : H.obj (D⟦N⟧) →+ A :=
  τ'.comp (transferHom F e θ hN).hom

/-- The map `Hom(M, D[j]) → Hom(F M, D'[j + c])`, `y ↦ θ[j] ∘ F(y)`. -/
def transferMap (M : C) (j : ℤ) : (M ⟶ D⟦j⟧) →+ (F.obj M ⟶ D'⟦j + c⟧) where
  toFun y := F.map y ≫ (F.commShiftIso j).hom.app D ≫ θ⟦j⟧' ≫
    (shiftFunctorAdd' C' c j (j + c) (add_comm c j)).inv.app D'
  map_zero' := by simp
  map_add' := by simp [F.map_add, Preadditive.add_comp]

omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- The map `transferMap F θ M j` sends `y` to `θ[j] ∘ F(y)`, with the shift isomorphisms made
explicit. -/
lemma transferMap_apply (M : C) (j : ℤ) (y : M ⟶ D⟦j⟧) :
    transferMap F θ M j y = F.map y ≫ (F.commShiftIso j).hom.app D ≫ θ⟦j⟧' ≫
      (shiftFunctorAdd' C' c j (j + c) (add_comm c j)).inv.app D' :=
  rfl

include hN in
omit [∀ (n : ℤ), (shiftFunctor C n).Additive] [∀ (n : ℤ), (shiftFunctor C' n).Additive] in
/-- Applying `F` to the morphism `M[i] ⟶ D[N]` induced by `y : M ⟶ D[j]` and composing with
`θ[N]` gives the morphism `F M[i] ⟶ D'[N']` induced by `transferMap F θ M j y`, up to the
commutation isomorphism `F(M[i]) ≅ (F M)[i]`. -/
lemma transfer_comm (M : C) {i j : ℤ} (h : i + j = N) (y : M ⟶ D⟦j⟧) :
    F.map (y⟦i⟧' ≫ (shiftFunctorAdd' C j i N (by omega)).inv.app D) ≫
        ((F.commShiftIso N).hom.app D ≫ θ⟦N⟧' ≫
          (shiftFunctorAdd' C' c N N' (by omega)).inv.app D') =
      (F.commShiftIso i).hom.app M ≫ ((transferMap F θ M j y)⟦i⟧' ≫
        (shiftFunctorAdd' C' (j + c) i N' (by omega)).inv.app D') := by
  have h1 := NatTrans.congr_app
    (congrArg Iso.hom (F.commShiftIso_add' (show j + i = N by omega))) D
  simp only [Functor.CommShift.isoAdd'_hom_app] at h1
  have h2 : F.map ((shiftFunctorAdd' C j i N (by omega)).inv.app D) ≫
      (F.commShiftIso N).hom.app D = (F.commShiftIso i).hom.app (D⟦j⟧) ≫
        ((F.commShiftIso j).hom.app D)⟦i⟧' ≫
          (shiftFunctorAdd' C' j i N (by omega)).inv.app (F.obj D) := by
    rw [h1, ← F.map_comp_assoc, Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  have nat := (shiftFunctorAdd' C' j i N (by omega)).inv.naturality θ
  dsimp at nat
  rw [F.map_comp, Category.assoc, reassoc_of% h2, Functor.commShiftIso_hom_naturality_assoc]
  congr 1
  rw [transferMap_apply]
  simp only [Functor.map_comp, Category.assoc]
  rw [shiftFunctorAdd'_assoc_inv_app c j i (j + c) N N' (add_comm c j) (by omega) (by omega),
    reassoc_of% nat]

include hN in
/-- **Transfer of duality along a functor**: for `F : C ⥤ C'` commuting with the shifts,
`e : H ≅ F ⋙ H'` and `θ : F D ⟶ D'[c]` with `N + c = N'`, if `y ↦ θ[j] ∘ F(y)` is bijective
`Hom(M, D[j]) → Hom(F M, D'[j + c])` for every `j`, then duality holds at `M` for the trace
`τ' ∘ θ_*` exactly when it holds at `F M` for `τ'`. -/
theorem isPerfect_iff_of_transfer (M : C)
    (hΨ : ∀ j, Function.Bijective (transferMap F θ M j)) :
    IsPerfect H D N (transferTrace F e θ hN τ') M ↔ IsPerfect H' D' N' τ' (F.obj M) := by
  have key : ∀ (i j : ℤ) (h : i + j = N),
      Function.Bijective (pairing H D N (transferTrace F e θ hN τ') M i j h) ↔
        Function.Bijective (pairing H' D' N' τ' (F.obj M) i (j + c) (by omega)) := by
    intro i j h
    let a := (e.app (M⟦i⟧) ≪≫ H'.mapIso ((F.commShiftIso i).app M)).addCommGroupIsoToAddEquiv
    refine bijective_iff_of_comp _ _ a a.bijective _ (hΨ j) (fun x y => ?_)
    show τ' ((shiftHom H' D' N' (transferMap F θ M j y) i _).hom
        ((e.hom.app (M⟦i⟧) ≫ H'.map ((F.commShiftIso i).hom.app M)).hom x)) =
      τ' ((transferHom F e θ hN).hom ((shiftHom H D N y i h).hom x))
    congr 1
    rw [← AddCommGrpCat.comp_apply, ← AddCommGrpCat.comp_apply]
    congr 1
    simp only [shiftHom, transferHom]
    rw [e.hom.naturality_assoc]
    dsimp only [Functor.comp_map]
    rw [← H'.map_comp, transfer_comm F θ hN M h y]
    simp only [Functor.map_comp, Category.assoc]
  refine ⟨fun hM i j' h' => ?_, fun hM i j h => (key i j h).2 (hM i (j + c) (by omega))⟩
  obtain ⟨j, rfl⟩ : ∃ j, j' = j + c := ⟨j' - c, by omega⟩
  exact (key i j (by omega)).1 (hM i j (by omega))

end Transfer

end Stacks.HomologicalDuality

end
