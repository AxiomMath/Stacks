module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import StacksCore.CategoryTheory.GradedObject.Monoidal.Summand

/-! # Duals of graded objects, degree by degree

If `W` is a dual of `V` as graded objects, then in each degree `n` the object `W (-n)` is a dual
of `V n`. This is the key reduction behind Stacks 0FFV: it turns a question about graded
dualizability into the corresponding ungraded question in each degree, at which point ordinary
linear algebra takes over.

Mathlib has no notion of duality for graded objects at all, so everything here is new. Nothing
below needs a field, finiteness, or `ℤ` in particular: the statements hold for any `AddGroup`
grading and any monoidal preadditive category carrying the standard graded-monoidal hypotheses.

The proof is element-free. Reading a triangle identity in degree `n`, every summand of the
coevaluation except the `(n, -n)` one is killed because the unit is initial away from degree `0`,
so `Summand.eq_πTensorObj_whisker*_comp` replaces it by that single component.
-/

@[expose] public section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Category Limits MonoidalCategory GradedObject

universe w3 v3 u3

variable {I : Type w3} [AddGroup I] [DecidableEq I] {C : Type u3} [Category.{v3} C]
  [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C] [HasInitial C]
  [∀ (X₁ X₂ : GradedObject I C), HasTensor X₁ X₂]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject I C), HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ X₁ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂ : C, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), HasTensor₄ObjExt X₁ X₂ X₃ X₄]

section EP

variable (V W : GradedObject I C) [ExactPairing V W] (n : I)

/-- The degree-`n` component of a graded coevaluation. -/
noncomputable def coevApply : 𝟙_ C ⟶ V n ⊗ W (-n) :=
  tensorUnit₀.inv ≫ (η_ V W) 0 ≫ πTensorObj V W n (-n) 0 (add_neg_cancel n)

/-- The degree-`n` component of a graded evaluation. -/
noncomputable def evalApply : W (-n) ⊗ V n ⟶ 𝟙_ C :=
  ιTensorObj W V (-n) n 0 (neg_add_cancel n) ≫ (ε_ V W) 0 ≫ tensorUnit₀.hom

section Bridge
variable {V W}

omit [Preadditive C] [MonoidalPreadditive C]
lemma whiskerRight_apply {X₁ X₂ : GradedObject I C} (φ : X₁ ⟶ X₂) (Y : GradedObject I C) (j : I) :
    (φ ▷ Y) j = (tensorHom φ (𝟙 Y)) j := rfl
lemma whiskerLeft_apply (X : GradedObject I C) {Y₁ Y₂ : GradedObject I C} (φ : Y₁ ⟶ Y₂) (j : I) :
    (X ◁ φ) j = (tensorHom (𝟙 X) φ) j := rfl
lemma associator_hom_apply (X Y Z : GradedObject I C) (j : I) :
    (α_ X Y Z).hom j = (associator X Y Z).hom j := rfl
lemma associator_inv_apply (X Y Z : GradedObject I C) (j : I) :
    (α_ X Y Z).inv j = (associator X Y Z).inv j := rfl
lemma rightUnitor_hom_apply (X : GradedObject I C) (j : I) :
    (ρ_ X).hom j = (rightUnitor X).hom j := rfl
lemma leftUnitor_hom_apply (X : GradedObject I C) (j : I) :
    (λ_ X).hom j = (leftUnitor X).hom j := rfl

/-- The monoidal unit of `GradedObject I C` is `GradedObject.Monoidal.tensorUnit`. The two are
definitionally equal but not syntactically so, which `rw` cannot see through; this lemma is the
bridge, and belongs to the same family as the `_apply` lemmas above. -/
lemma tensorUnit_def : 𝟙_ (GradedObject I C) = tensorUnit := rfl

/-- The monoidal tensor product on `GradedObject I C` is `GradedObject.Monoidal.tensorObj`,
the companion of `tensorUnit_def`. -/
lemma tensorObj_def (X Y : GradedObject I C) : X ⊗ Y = tensorObj X Y := rfl

/-- Compatibility of the graded right unitor with the inclusion of the `(j, 0)` summand. -/
lemma ιTensorObj_rightUnitor_hom (X : GradedObject I C) (j : I) :
    ιTensorObj X (𝟙_ (GradedObject I C)) j 0 j (add_zero j) ≫ (rightUnitor X).hom j =
      (X j ◁ tensorUnit₀.hom) ≫ (ρ_ (X j)).hom := by
  have h : X j ◁ tensorUnit₀.inv ≫ ιTensorObj X tensorUnit j 0 j (add_zero j) ≫
      (rightUnitor X).hom j = (ρ_ (X j)).hom := Iso.inv_comp_eq_id _|>.1 <| by
    simpa [-Iso.inv_hom_id_eval, rightUnitor_inv_apply] using congr($((rightUnitor X).inv_hom_id) j)
  simp [← h, tensorUnit_def]

/-- Compatibility of the graded left unitor with the inclusion of the `(0, j)` summand. -/
lemma ιTensorObj_leftUnitor_hom (X : GradedObject I C) (j : I) :
    ιTensorObj (𝟙_ (GradedObject I C)) X 0 j j (zero_add j) ≫ (leftUnitor X).hom j =
      (tensorUnit₀.hom ▷ X j) ≫ (λ_ (X j)).hom := by
  have h : tensorUnit₀.inv ▷ X j ≫ ιTensorObj tensorUnit X 0 j j (zero_add j) ≫
      (leftUnitor X).hom j = (λ_ (X j)).hom := Iso.inv_comp_eq_id _|>.1 <| by
    simpa [-Iso.inv_hom_id_eval, leftUnitor_inv_apply] using congr($((leftUnitor X).inv_hom_id) j)
  simp [← h, tensorUnit_def]

end Bridge


/-- Contracting the degree-`0` part of `V ⊗ W` against `V n` on the right. -/
private noncomputable abbrev contractRight : tensorObj V W 0 ⊗ V n ⟶ V n :=
  ιTensorObj (tensorObj V W) V 0 n n (zero_add n) ≫
    (α_ V W V).hom n ≫ (V ◁ ε_ V W) n ≫ (ρ_ V).hom n

/-- Contracting the degree-`0` part of `V ⊗ W` against `W (-n)` on the left. -/
private noncomputable abbrev contractLeft : W (-n) ⊗ tensorObj V W 0 ⟶ W (-n) :=
  ιTensorObj W (tensorObj V W) (-n) 0 (-n) (add_zero _) ≫
    (α_ W V W).inv (-n) ≫ (ε_ V W ▷ W) (-n) ≫ (λ_ W).hom (-n)

omit [Preadditive C] [MonoidalPreadditive C] in
/-- On the `(n, -n)` summand, the right contraction is the ungraded evaluation. -/
private lemma ι_contractRight :
    (ιTensorObj V W n (-n) 0 (add_neg_cancel n) ▷ V n) ≫ contractRight V W n =
      (α_ (V n) (W (-n)) (V n)).hom ≫ ((V n) ◁ evalApply V W n) ≫ (ρ_ (V n)).hom := by
  rw [contractRight, associator_hom_apply, rightUnitor_hom_apply, whiskerLeft_apply, ← assoc,
    ← ιTensorObj₃'_eq V W V n (-n) n n (by simp) 0 (by simp),
    ιTensorObj₃'_associator_hom_assoc, ιTensorObj₃_eq V W V n (-n) n n (by simp) 0 (by simp)]
  simp [evalApply, ιTensorObj_rightUnitor_hom, whiskerLeft_comp]

omit [MonoidalPreadditive C] in
/-- Every other summand is killed, because the unit is initial away from degree `0`. -/
private lemma ι_contractRight_eq_zero (a b : I) (hab : a + b = 0) (hne : ¬ (a = n ∧ b = -n)) :
    (ιTensorObj V W a b 0 hab ▷ V n) ≫ contractRight V W n = 0 := by
  have hb : b + n ≠ 0 := fun h0 ↦ hne <| by
    obtain rfl := add_eq_zero_iff_eq_neg.1 h0; exact ⟨add_neg_eq_zero.1 hab, rfl⟩
  have hzero : ιTensorObj V (𝟙_ (GradedObject I C)) a (b + n) n
      (by rw [← add_assoc, hab, zero_add]) ≫ (rightUnitor V).hom n = 0 :=
    (IsInitial.isInitialObj ((curriedTensor C).obj (V a)) _
      (isInitialTensorUnitApply (b + n) hb)).hom_ext _ _
  rw [contractRight, associator_hom_apply, rightUnitor_hom_apply, whiskerLeft_apply, ← assoc,
    ← ιTensorObj₃'_eq V W V a b n n (by simp [hab]) 0 hab, ιTensorObj₃'_associator_hom_assoc,
    ιTensorObj₃_eq V W V a b n n (by simp [hab]) (b + n) rfl, assoc, ι_tensorHom_assoc, hzero]
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
/-- The graded triangle identity, read in degree `n`. -/
private lemma coevaluation_contractRight :
    ((η_ V W) 0 ▷ V n) ≫ contractRight V W n
      = (tensorUnit₀.hom ▷ V n) ≫ (λ_ (V n)).hom := by
  have h := congrArg (fun φ => ιTensorObj (𝟙_ (GradedObject I C)) V 0 n n (zero_add n) ≫
    φ ≫ (ρ_ V).hom n) (congrFun (ExactPairing.evaluation_coevaluation V W) n)
  simp only [categoryOfGradedObjects_comp, assoc, Iso.inv_hom_id_eval, comp_id,
    whiskerRight_apply, ι_tensorHom_assoc, leftUnitor_hom_apply, ιTensorObj_leftUnitor_hom,
    categoryOfGradedObjects_id, tensorHom_id] at h
  exact h

omit [Preadditive C] [MonoidalPreadditive C] in
/-- On the `(n, -n)` summand, the left contraction is the ungraded evaluation. -/
private lemma ι_contractLeft :
    (W (-n) ◁ ιTensorObj V W n (-n) 0 (add_neg_cancel n)) ≫ contractLeft V W n =
      (α_ (W (-n)) (V n) (W (-n))).inv ≫ (evalApply V W n ▷ W (-n)) ≫ (λ_ (W (-n))).hom := by
  rw [contractLeft, ← assoc, ← ιTensorObj₃_eq W V W (-n) n (-n) (-n) (by simp) 0
      (add_neg_cancel n), associator_inv_apply, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq W V W (-n) n (-n) (-n) (by simp) 0 (neg_add_cancel n), assoc,
    whiskerRight_apply, ι_tensorHom_assoc, leftUnitor_hom_apply, ιTensorObj_leftUnitor_hom]
  simp [evalApply, comp_whiskerRight]

omit [MonoidalPreadditive C] in
/-- Every other summand is killed, because the unit is initial away from degree `0`. -/
private lemma ι_contractLeft_eq_zero (a b : I) (hab : a + b = 0) (hne : ¬ (a = n ∧ b = -n)) :
    (W (-n) ◁ ιTensorObj V W a b 0 hab) ≫ contractLeft V W n = 0 := by
  have ha : -n + a ≠ 0 := fun h0 ↦ hne <| by
    obtain rfl := (neg_add_eq_zero.1 h0).symm; exact ⟨rfl, eq_neg_of_add_eq_zero_right hab⟩
  have hzero : ιTensorObj (𝟙_ (GradedObject I C)) W (-n + a) b (-n)
      (by rw [add_assoc, hab, add_zero]) ≫ (leftUnitor W).hom (-n) = 0 :=
    (IsInitial.isInitialObj ((curriedTensor C).flip.obj (W b)) _
      (isInitialTensorUnitApply (-n + a) ha)).hom_ext _ _
  rw [contractLeft, ← assoc, ← ιTensorObj₃_eq W V W (-n) a b (-n) (by simp [add_assoc, hab]) 0 hab,
    associator_inv_apply, ιTensorObj₃_associator_inv_assoc,
    ιTensorObj₃'_eq W V W (-n) a b (-n) (by simp [add_assoc, hab]) (-n + a) rfl, assoc,
    whiskerRight_apply, ι_tensorHom_assoc, leftUnitor_hom_apply, hzero]
  simp

omit [Preadditive C] [MonoidalPreadditive C] in
/-- The graded triangle identity, read in degree `-n`. -/
private lemma coevaluation_contractLeft :
    (W (-n) ◁ (η_ V W) 0) ≫ contractLeft V W n
      = (W (-n) ◁ tensorUnit₀.hom) ≫ (ρ_ (W (-n))).hom := by
  have h := congrArg (fun φ => ιTensorObj W (𝟙_ (GradedObject I C)) (-n) 0 (-n) (add_zero _) ≫
    φ ≫ (λ_ W).hom (-n)) (congrFun (ExactPairing.coevaluation_evaluation V W) (-n))
  simpa [whiskerLeft_apply, rightUnitor_hom_apply,
    ιTensorObj_rightUnitor_hom, tensorObj_def] using h

/-- **The structural heart of Stacks 0FFV.**  A graded exact pairing is, degree by degree,
an exact pairing in the base category. -/
@[implicit_reducible]
noncomputable def exactPairingApply : ExactPairing (V n) (W (-n)) where
  coevaluation' := coevApply V W n
  evaluation' := evalApply V W n
  evaluation_coevaluation' := by
    simp [Iso.eq_comp_inv, coevApply, ← ι_contractRight V W n, ← eq_πTensorObj_whiskerRight_comp
      (hg := ι_contractRight_eq_zero V W n), coevaluation_contractRight]
  coevaluation_evaluation' := by
    simp [Iso.eq_comp_inv, coevApply, ← ι_contractLeft V W n, ← eq_πTensorObj_whiskerLeft_comp
      (hg := ι_contractLeft_eq_zero V W n), coevaluation_contractLeft]

/-- If a coevaluation vanishes, the object it is a coevaluation for is zero. -/
lemma isZero_of_coevaluation_eq_zero {D : Type u3} [Category.{v3} D] [MonoidalCategory D]
    [Preadditive D] [MonoidalPreadditive D] {X Y : D} [ExactPairing X Y] (h : η_ X Y = 0) :
    Limits.IsZero X := Limits.IsZero.iff_id_eq_zero _|>.2 <| by
  rw [← Iso.inv_hom_id (λ_ X), ← cancel_mono (f := (ρ_ X).inv), ← cancel_mono (f := (ρ_ X).hom),
    assoc, assoc, ← reassoc_of% ExactPairing.evaluation_coevaluation X Y]
  simp [h]

end EP


end CategoryTheory.GradedObject.Monoidal
