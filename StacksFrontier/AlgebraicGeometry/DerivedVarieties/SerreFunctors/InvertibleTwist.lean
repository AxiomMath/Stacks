module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SerreFunctors.Basic
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence

/-!
# Serre functors given by twisting with an invertible object

Let `C` be a `k`-linear braided monoidal category, let `Z` be an invertible object of `C` and let
`τ : Hom(𝟙, Z) ⟶ k` be a linear form. Suppose that `τ` is a *perfect trace* on a class of objects
`E`: the pairing `Hom(𝟙, E) × Hom(E, Z) ⟶ k`, `(x, h) ↦ τ(x ≫ h)`, identifies `Hom(E, Z)` with the
dual of the finite dimensional space `Hom(𝟙, E)`. Then on a full subcategory of objects with right
duals, stable under `- ⊗ Z`, whose objects `A, B` have `Aᘁ ⊗ B` in that class, the functor
`- ⊗ Z` is a Serre functor: the Serre pairing is

`Hom(A, B) ⟶ Hom(B, A ⊗ Z)^∨,  f ↦ (g ↦ τ(Ψ f ≫ Φ g))`,

where `Ψ f = η_A ≫ (f ▷ Aᘁ) ≫ β : 𝟙 ⟶ Aᘁ ⊗ B` and `Φ g : Aᘁ ⊗ B ⟶ Z` is the transpose of `g`.
This is the argument of [Stacks, Tag 0FY8], with `Hom_X(K, L) = H^0(X, L ⊗ K^∨)` and the duality
`Hom_X(E, ω_X^•) = H^0(X, E)^∨`.

## Main definitions

* `CategoryTheory.SerreTrace.homToUnit` — `Ψ : Hom(A, B) ⟶ Hom(𝟙, Aᘁ ⊗ B)`.
* `CategoryTheory.SerreTrace.homFromDual` — `Φ : Hom(B, A ⊗ Z) ⟶ Hom(Aᘁ ⊗ B, Z)`.
* `CategoryTheory.SerreTrace.traceDual` — `Hom(E, Z) ⟶ Hom(𝟙, E)^∨`, `h ↦ (x ↦ τ(x ≫ h))`.
* `CategoryTheory.SerreTrace.pairing` — the Serre pairing.
* `CategoryTheory.SerreEquivalence.ofTensorInvertible` — the Serre equivalence `- ⊗ Z`.

## Implementation notes

Both naturality conditions of the pairing are reduced to the passage of a morphism `f : A₁ ⟶ A`
through `Ψ` and `Φ` as its right adjoint mate `fᘁ : Aᘁ ⟶ A₁ᘁ`
(`CategoryTheory.coevaluation_comp_rightAdjointMate` and
`CategoryTheory.rightAdjointMate_comp_evaluation`), and of a morphism `g : B ⟶ B'` as `Aᘁ ◁ g`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u v w

namespace CategoryTheory

variable {k : Type u} [Field k] {C : Type v} [Category.{w} C] [Preadditive C] [Linear k C]
  [MonoidalCategory C]

namespace SerreTrace

section Trace

variable (Z : C) (τ : (𝟙_ C ⟶ Z) →ₗ[k] k)

/-- The linear form `τ` read as `Hom(E, Z) ⟶ Hom(𝟙, E)^∨`, `h ↦ (x ↦ τ(x ≫ h))`. -/
def traceDual (E : C) : (E ⟶ Z) →ₗ[k] Module.Dual k (𝟙_ C ⟶ E) where
  toFun h := τ ∘ₗ Linear.rightComp k (𝟙_ C) h
  map_add' h₁ h₂ := by ext x; simp
  map_smul' c h := by ext x; simp

/-- The linear form `τ` read as `Hom(𝟙, E) ⟶ Hom(E, Z)^∨`, `x ↦ (h ↦ τ(x ≫ h))`. -/
def traceDualFlip (E : C) : (𝟙_ C ⟶ E) →ₗ[k] Module.Dual k (E ⟶ Z) where
  toFun x := τ ∘ₗ Linear.leftComp k Z x
  map_add' x₁ x₂ := by ext h; simp
  map_smul' c x := by ext h; simp

/-- `traceDualFlip Z τ E` is the evaluation map `Hom(𝟙, E) ⟶ Hom(𝟙, E)^∨^∨` followed by the
transpose of `traceDual Z τ E`. -/
theorem traceDualFlip_eq (E : C) :
    traceDualFlip Z τ E = (traceDual Z τ E).dualMap ∘ₗ Module.Dual.eval k (𝟙_ C ⟶ E) := by
  ext x h
  rfl

/-- If `τ` identifies `Hom(E, Z)` with the dual of the finite dimensional `Hom(𝟙, E)`, it also
identifies `Hom(𝟙, E)` with the dual of `Hom(E, Z)`. -/
theorem bijective_traceDualFlip (E : C) [FiniteDimensional k (𝟙_ C ⟶ E)]
    (h : Function.Bijective (traceDual Z τ E)) :
    Function.Bijective (traceDualFlip Z τ E) := by
  rw [traceDualFlip_eq, LinearMap.coe_comp]
  exact (LinearEquiv.ofBijective _ h).dualMap.bijective.comp
    (Module.evalEquiv k (𝟙_ C ⟶ E)).bijective

end Trace

variable [MonoidalPreadditive C] [MonoidalLinear k C] [BraidedCategory C]

variable (k)

/-- `Ψ : Hom(A, B) ⟶ Hom(𝟙, Aᘁ ⊗ B)`, `f ↦ η_A ≫ (f ▷ Aᘁ) ≫ β_{B, Aᘁ}`. -/
def homToUnit (A B : C) [HasRightDual A] : (A ⟶ B) →ₗ[k] (𝟙_ C ⟶ Aᘁ ⊗ B) where
  toFun f := η_ A Aᘁ ≫ f ▷ Aᘁ ≫ (β_ B Aᘁ).hom
  map_add' f g := by simp
  map_smul' c f := by simp

/-- `homToUnit k A B f = η_A ≫ (f ▷ Aᘁ) ≫ β_{B, Aᘁ}`. -/
theorem homToUnit_apply (A B : C) [HasRightDual A] (f : A ⟶ B) :
    homToUnit k A B f = η_ A Aᘁ ≫ f ▷ Aᘁ ≫ (β_ B Aᘁ).hom :=
  rfl

/-- `Ψ f` is the image of `λ_A ≫ f` under `tensorRightHomEquiv`, followed by the braiding
`β_{B, Aᘁ}`. -/
theorem homToUnit_eq_tensorRightHomEquiv (A B : C) [HasRightDual A] (f : A ⟶ B) :
    homToUnit k A B f =
      tensorRightHomEquiv (𝟙_ C) A Aᘁ B ((λ_ A).hom ≫ f) ≫ (β_ B Aᘁ).hom := by
  simp only [homToUnit_apply, tensorRightHomEquiv, Equiv.coe_fn_mk, comp_whiskerRight,
    Category.assoc]
  monoidal

/-- `Ψ : Hom(A, B) ⟶ Hom(𝟙, Aᘁ ⊗ B)` is bijective. -/
theorem bijective_homToUnit (A B : C) [HasRightDual A] :
    Function.Bijective (homToUnit k A B) := by
  let e₁ : (A ⟶ B) ≃ (𝟙_ C ⊗ A ⟶ B) :=
    ⟨fun f => (λ_ A).hom ≫ f, fun g => (λ_ A).inv ≫ g, fun f => by simp, fun g => by simp⟩
  let e₂ : (𝟙_ C ⟶ B ⊗ Aᘁ) ≃ (𝟙_ C ⟶ Aᘁ ⊗ B) :=
    ⟨fun g => g ≫ (β_ B Aᘁ).hom, fun g => g ≫ (β_ B Aᘁ).inv, fun f => by simp,
      fun g => by simp⟩
  have h : ⇑(homToUnit k A B) = e₂ ∘ tensorRightHomEquiv (𝟙_ C) A Aᘁ B ∘ e₁ :=
    funext (homToUnit_eq_tensorRightHomEquiv k A B)
  rw [h]
  exact e₂.bijective.comp ((tensorRightHomEquiv _ _ _ _).bijective.comp e₁.bijective)

/-- `Φ : Hom(B, A ⊗ Z) ⟶ Hom(Aᘁ ⊗ B, Z)`, the transpose along the exact pairing of `A` and
`Aᘁ`. -/
def homFromDual (A B Z : C) [HasRightDual A] : (B ⟶ A ⊗ Z) →ₗ[k] (Aᘁ ⊗ B ⟶ Z) where
  toFun g := (tensorLeftHomEquiv B A Aᘁ Z).symm g
  map_add' f g := by simp [tensorLeftHomEquiv]
  map_smul' c f := by simp [tensorLeftHomEquiv]

omit [BraidedCategory C] in
/-- `homFromDual k A B Z g` is the image of `g` under the inverse of `tensorLeftHomEquiv`. -/
theorem homFromDual_apply (A B Z : C) [HasRightDual A] (g : B ⟶ A ⊗ Z) :
    homFromDual k A B Z g = (tensorLeftHomEquiv B A Aᘁ Z).symm g :=
  rfl

omit [BraidedCategory C] in
/-- `Φ : Hom(B, A ⊗ Z) ⟶ Hom(Aᘁ ⊗ B, Z)` is bijective. -/
theorem bijective_homFromDual (A B Z : C) [HasRightDual A] :
    Function.Bijective (homFromDual k A B Z) :=
  (tensorLeftHomEquiv B A Aᘁ Z).symm.bijective

variable {k}

/-- **`Ψ` in the first variable.** For `f' : A₁ ⟶ A`, precomposing with `f'` is postcomposing with
`f'ᘁ ▷ B`. -/
theorem homToUnit_comp_left {A₁ A B : C} [HasRightDual A₁] [HasRightDual A] (f' : A₁ ⟶ A)
    (f : A ⟶ B) :
    homToUnit k A₁ B (f' ≫ f) = homToUnit k A B f ≫ (f'ᘁ) ▷ B := by
  simp only [homToUnit_apply, comp_whiskerRight, Category.assoc]
  rw [← coevaluation_comp_rightAdjointMate_assoc, whisker_exchange_assoc,
    BraidedCategory.braiding_naturality_right]

/-- **`Ψ` in the second variable.** -/
theorem homToUnit_comp_right {A B B' : C} [HasRightDual A] (f : A ⟶ B) (g : B ⟶ B') :
    homToUnit k A B' (f ≫ g) = homToUnit k A B f ≫ Aᘁ ◁ g := by
  simp only [homToUnit_apply, comp_whiskerRight, Category.assoc,
    BraidedCategory.braiding_naturality_left, BraidedCategory.braiding_naturality_left_assoc]

omit [BraidedCategory C] in
/-- **`Φ` in the first variable.** For `f' : A₁ ⟶ A`, postcomposing with `f' ▷ Z` is
precomposing with `f'ᘁ ▷ B`. -/
theorem homFromDual_comp_whiskerRight {A₁ A B Z : C} [HasRightDual A₁] [HasRightDual A]
    (f' : A₁ ⟶ A) (g : B ⟶ A₁ ⊗ Z) :
    homFromDual k A B Z (g ≫ f' ▷ Z) = (f'ᘁ) ▷ B ≫ homFromDual k A₁ B Z g := by
  simp only [homFromDual_apply, tensorLeftHomEquiv, Equiv.coe_fn_symm_mk,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation, comp_whiskerRight_assoc,
    associator_inv_naturality_middle_assoc]

omit [BraidedCategory C] in
/-- **`Φ` in the second variable.** -/
theorem homFromDual_comp {A B B' Z : C} [HasRightDual A] (g : B ⟶ B') (h : B' ⟶ A ⊗ Z) :
    homFromDual k A B Z (g ≫ h) = Aᘁ ◁ g ≫ homFromDual k A B' Z h :=
  tensorLeftHomEquiv_symm_naturality g h

variable (Z : C) (τ : (𝟙_ C ⟶ Z) →ₗ[k] k)

/-- **The Serre pairing** `Hom(A, B) ⟶ Hom(B, A ⊗ Z)^∨`, `f ↦ (g ↦ τ(Ψ f ≫ Φ g))`. -/
def pairing (A B : C) [HasRightDual A] : (A ⟶ B) →ₗ[k] Module.Dual k (B ⟶ A ⊗ Z) :=
  (homFromDual k A B Z).dualMap ∘ₗ traceDualFlip Z τ (Aᘁ ⊗ B) ∘ₗ homToUnit k A B

/-- The Serre pairing sends `f` and `g` to `τ(Ψ f ≫ Φ g)`. -/
theorem pairing_apply (A B : C) [HasRightDual A] (f : A ⟶ B) (g : B ⟶ A ⊗ Z) :
    pairing Z τ A B f g = τ (homToUnit k A B f ≫ homFromDual k A B Z g) :=
  rfl

/-- If `Hom(𝟙, Aᘁ ⊗ B)` is finite dimensional and `traceDual Z τ (Aᘁ ⊗ B)` is bijective, then
the Serre pairing `Hom(A, B) ⟶ Hom(B, A ⊗ Z)^∨` is bijective. -/
theorem bijective_pairing (A B : C) [HasRightDual A] [FiniteDimensional k (𝟙_ C ⟶ Aᘁ ⊗ B)]
    (h : Function.Bijective (traceDual Z τ (Aᘁ ⊗ B))) :
    Function.Bijective (pairing Z τ A B) := by
  rw [pairing, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (LinearEquiv.ofBijective _ (bijective_homFromDual k A B Z)).dualMap.bijective.comp
    ((bijective_traceDualFlip Z τ _ h).comp (bijective_homToUnit k A B))

/-- **Naturality of the pairing in the first variable.** -/
theorem pairing_comp_left {A₁ A B : C} [HasRightDual A₁] [HasRightDual A] (f' : A₁ ⟶ A)
    (f : A ⟶ B) (g : B ⟶ A₁ ⊗ Z) :
    pairing Z τ A₁ B (f' ≫ f) g = pairing Z τ A B f (g ≫ f' ▷ Z) := by
  rw [pairing_apply, pairing_apply, homToUnit_comp_left, homFromDual_comp_whiskerRight,
    Category.assoc]

/-- **Naturality of the pairing in the second variable.** -/
theorem pairing_comp_right {A B B' : C} [HasRightDual A] (f : A ⟶ B) (g : B ⟶ B')
    (h : B' ⟶ A ⊗ Z) :
    pairing Z τ A B' (f ≫ g) h = pairing Z τ A B f (g ≫ h) := by
  rw [pairing_apply, pairing_apply, homToUnit_comp_right, homFromDual_comp, Category.assoc]

end SerreTrace

open SerreTrace

variable [MonoidalPreadditive C] [MonoidalLinear k C] [BraidedCategory C]

/-- **Twisting by an invertible object is a Serre functor.** Let `P` be a property of objects of
`C`, closed under isomorphisms, whose objects have right duals, and let `Z` be an invertible object
with `A ⊗ Z ∈ P ↔ A ∈ P`. Let `τ : Hom(𝟙, Z) ⟶ k` be a perfect trace on a class `Q` of objects
(`Hom(𝟙, E)` is finite dimensional and `traceDual Z τ E` is bijective for `E ∈ Q`) which contains
`Aᘁ ⊗ B` for `A, B ∈ P`. Then `- ⊗ Z` is a Serre functor on the full subcategory of `P`, with
Serre pairing `SerreTrace.pairing`. -/
def SerreEquivalence.ofTensorInvertible (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    (dual : ∀ A, P A → HasRightDual A) (Z : C) (hZ : MonoidalCategory.HasInverse Z)
    (hP : P.inverseImage (tensorRight Z) = P) (τ : (𝟙_ C ⟶ Z) →ₗ[k] k)
    (Q : ObjectProperty C)
    (hQ : ∀ (A B : C) (hA : P A), P B → letI := dual A hA; Q (Aᘁ ⊗ B))
    (hfin : ∀ E, Q E → FiniteDimensional k (𝟙_ C ⟶ E))
    (hnd : ∀ E, Q E → Function.Bijective (traceDual Z τ E)) :
    SerreEquivalence k (C := P.FullSubcategory) where
  equivalence := hZ.tensorRightEquivalence.congrFullSubcategory hP
  linear := ⟨fun {X Y} f r => by
    ext
    exact MonoidalLinear.smul_whiskerRight r f.hom Z⟩
  pairing X Y :=
    letI := dual X.obj X.property
    haveI := hfin _ (hQ X.obj Y.obj X.property Y.property)
    InducedCategory.homLinearEquiv ≪≫ₗ
      LinearEquiv.ofBijective (SerreTrace.pairing Z τ X.obj Y.obj)
        (bijective_pairing Z τ X.obj Y.obj (hnd _ (hQ X.obj Y.obj X.property Y.property))) ≪≫ₗ
      (InducedCategory.homLinearEquiv (R := k) (X := Y)
        (Y := (hZ.tensorRightEquivalence.congrFullSubcategory hP).functor.obj X)).dualMap
  pairing_naturality_left {X X' Y} f g := by
    let := dual X.obj X.property
    let := dual X'.obj X'.property
    ext h
    exact SerreTrace.pairing_comp_left Z τ f.hom g.hom h.hom
  pairing_naturality_right {X Y Y'} f g := by
    let := dual X.obj X.property
    ext h
    exact SerreTrace.pairing_comp_right Z τ f.hom g.hom h.hom

end CategoryTheory
