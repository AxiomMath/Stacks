module

public import StacksCore.Algebra.Homology.HomologicalTricomplex

/-! # The total complex of a tricomplex, first two indices first

For a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃`, `K.total₁₂ c₁₂ c` is the total complex of
the bicomplex `K.int₁₂ c₁₂ : HomologicalComplex₂ C c₁₂ c₃`: Stacks' `Tot(Tot₁₂(A^{•, •, •}))`.
Its degree-`j` term is the coproduct of the `((K.X i₁).X i₂).X i₃` over the triples with
`π c₁₂ c₃ c (π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j`, with inclusions `ιTotal₁₂`, and its differential
is `D₁ + D₂ + D₃` (`total₁₂_d`), where the three pieces act on a summand by the three
differentials of `K` up to the signs of the two `TotalComplexShape`s (`d₁_eq`, `d₂_eq`,
`d₃_eq`). For `ℤ`-cochain tricomplexes the signs are Stacks 08BI's
`d₁ + (-1)^p d₂ + (-1)^{p + q} d₃`; this is spelled out in
`StacksCore.Algebra.Homology.HomologicalTricomplex.Associator`.

The structure mirrors Mathlib's `HomologicalComplex.mapBifunctor₁₂` in
`Mathlib.Algebra.Homology.BifunctorAssociator`, which treats the tricomplexes `F₁₂(K₁, K₂)` and
`G(-, K₃)` built from bifunctors.
Adapted from Joël Riou's unmerged Mathlib pull request #10717 (`HomologicalTricomplex.lean`,
Copyright (c) 2024 Joël Riou, released under the Apache 2.0 license), modernized to the current
Mathlib API.
-/

@[expose] public section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C] [Preadditive C] {I₁ I₂ I₃ I₁₂ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

namespace HomologicalComplex₃

variable (K : HomologicalComplex₃ C c₁ c₂ c₃)
  (c₁₂ : ComplexShape I₁₂) (c : ComplexShape J) [DecidableEq I₁₂] [DecidableEq J]
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₁₂ c₃ c] [K.HasInt₁₂ c₁₂]

/-- The condition that one may obtain a total complex of a tricomplex
`K : HomologicalComplex₃ C c₁ c₂ c₃` in two steps by taking the total complex of the bicomplex
`K.int₁₂ c₁₂ : HomologicalComplex₂ C c₁₂ c₃`. -/
abbrev HasTotal₁₂ := (K.int₁₂ c₁₂).HasTotal c

variable [K.HasTotal₁₂ c₁₂ c]

/-- **Stacks 08BI**, the total complex of a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃`, formed
as the total complex of the bicomplex `K.int₁₂ c₁₂ : HomologicalComplex₂ C c₁₂ c₃`. For
`ℤ`-cochain shapes its differential carries the tag's signs `d₁ + (-1)^p d₂ + (-1)^{p + q} d₃`,
see `ιTotal₁₂_d_up_ℤ`, so this is the tag's `Tot(A^{•, •, •})` itself, and also its
`Tot(Tot₁₂(A^{•, •, •}))`. -/
@[stacks 08BI "the tag's `Tot`, as `Tot(Tot₁₂)`; any shapes, signs from the `TotalComplexShape`s"]
noncomputable abbrev total₁₂ : HomologicalComplex C c := (K.int₁₂ c₁₂).total c

section

variable (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)

/-- The inclusion of a summand in the total complex `K.total₁₂ c₁₂ c` of a tricomplex. -/
noncomputable def ιTotal₁₂
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (K.X' i₃).ιTotal c₁₂ i₁ i₂ _ rfl ≫
    (K.int₁₂ c₁₂).ιTotal c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩) i₃ j h

@[reassoc]
lemma ιTotal₁₂_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j)
    (i₁₂ : I₁₂) (h' : ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂) = i₁₂) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h = (K.X' i₃).ιTotal c₁₂ i₁ i₂ i₁₂ h' ≫
    (K.int₁₂ c₁₂).ιTotal c i₁₂ i₃ j (by rw [← h', h]) := by
  subst h'
  rfl

/-- The inclusion of a summand in the total complex `K.total₁₂ c₁₂ c` of a tricomplex,
or zero. -/
noncomputable def ιTotal₁₂OrZero :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  if h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j then
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h
  else 0

lemma ιTotal₁₂OrZero_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂OrZero c₁₂ c i₁ i₂ i₃ j = K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h := dite_eq_left h

lemma ιTotal₁₂OrZero_eq_zero
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) ≠ j) :
    K.ιTotal₁₂OrZero c₁₂ c i₁ i₂ i₃ j = 0 := dite_eq_right h

end

section

variable (i₁ i₁' : I₁) (h₁ : c₁.Rel i₁ i₁')
  (i₂ i₂' : I₂) (h₂ : c₂.Rel i₂ i₂')
  (i₃ i₃' : I₃) (h₃ : c₃.Rel i₃ i₃') (j : J)

/-- The first differential on a summand of the total complex `K.total₁₂ c₁₂ c` of a
tricomplex. -/
noncomputable def d₁ : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
    ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
      ((K.d i₁ (c₁.next i₁)).f i₂).f i₃ ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _

/-- The second differential on a summand of the total complex `K.total₁₂ c₁₂ c` of a
tricomplex. -/
noncomputable def d₂ : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
    ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)) •
  ((K.X i₁).d i₂ (c₂.next i₂)).f i₃ ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _

/-- The third differential on a summand of the total complex `K.total₁₂ c₁₂ c` of a
tricomplex. -/
noncomputable def d₃ : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₁₂ c₁₂ c).X j :=
  ComplexShape.ε₂ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) •
    ((K.X i₁).X i₂).d i₃ (c₃.next i₃) ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _

lemma d₁_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) : K.d₁ c₁₂ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₁]
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f,
    HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₂_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) : K.d₂ c₁₂ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₂]
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₃_eq_zero (h : ¬ c₃.Rel i₃ (c₃.next i₃)) : K.d₃ c₁₂ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₃]
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

section

variable {i₁ i₁'}
include h₁

lemma d₁_eq' :
    K.d₁ c₁₂ c i₁ i₂ i₃ j = (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _ := by
  obtain rfl := c₁.next_eq' h₁
  rfl

lemma d₁_eq_zero'
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂), i₃) ≠ j) :
    K.d₁ c₁₂ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₁_eq' c₁₂ c h₁, ιTotal₁₂OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₁_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁', i₂), i₃) = j) :
    K.d₁ c₁₂ c i₁ i₂ i₃ j = (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
      ComplexShape.ε₁ c₁ c₂ c₁₂ (i₁, i₂)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ ιTotal₁₂ K c₁₂ c i₁' i₂ i₃ j h := by
  rw [K.d₁_eq' c₁₂ c h₁, ιTotal₁₂OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₂ i₂'}
include h₂

lemma d₂_eq' : K.d₂ c₁₂ c i₁ i₂ i₃ j =
    (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
    ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
      K.ιTotal₁₂OrZero c₁₂ c _ _ _ _ := by
  obtain rfl := c₂.next_eq' h₂
  rfl

lemma d₂_eq_zero'
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂'), i₃) ≠ j) :
    K.d₂ c₁₂ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₂_eq' c₁₂ c i₁ h₂, ιTotal₁₂OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₂_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂'), i₃) = j) :
    K.d₂ c₁₂ c i₁ i₂ i₃ j =
      (ComplexShape.ε₁ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) *
        ComplexShape.ε₂ c₁ c₂ c₁₂ (i₁, i₂)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
          ιTotal₁₂ K c₁₂ c i₁ i₂' i₃ j h := by
  rw [K.d₂_eq' c₁₂ c i₁ h₂, ιTotal₁₂OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₃ i₃'}
include h₃

lemma d₃_eq' : K.d₃ c₁₂ c i₁ i₂ i₃ j =
    ComplexShape.ε₂ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ K.ιTotal₁₂OrZero c₁₂ c _ _ _ _ := by
  obtain rfl := c₃.next_eq' h₃
  rfl

lemma d₃_eq_zero'
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃') ≠ j) :
    K.d₃ c₁₂ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₃_eq' c₁₂ c i₁ i₂ h₃, ιTotal₁₂OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₃_eq
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃') = j) :
    K.d₃ c₁₂ c i₁ i₂ i₃ j = ComplexShape.ε₂ c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, i₃) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ ιTotal₁₂ K c₁₂ c i₁ i₂ i₃' j h := by
  rw [K.d₃_eq' c₁₂ c i₁ i₂ h₃, ιTotal₁₂OrZero_eq _ _ _ _ _ _ _ h]

end

end

section

variable {c₁₂ c}
variable {A : C} {j : J} (f : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (_ : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j),
      ((K.X i₁).X i₂).X i₃ ⟶ A)

/-- Constructor for morphisms from one of the objects constituting the total complex
`K.total₁₂ c₁₂ c` of a tricomplex. -/
noncomputable def total₁₂Desc : (K.total₁₂ c₁₂ c).X j ⟶ A :=
  (K.int₁₂ c₁₂).totalDesc (fun i₁₂ i₃ h => (K.X' i₃).totalDesc
    (fun i₁ i₂ h' => f i₁ i₂ i₃ (by rw [h', h])))

@[reassoc (attr := simp)]
lemma ι_total₁₂Desc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ total₁₂Desc K f = f i₁ i₂ i₃ h := by
  simp [ιTotal₁₂, total₁₂Desc]

end

variable {K c₁₂ c} in
@[ext]
lemma total₁₂.hom_ext {A : C} {j : J} {f g : (K.total₁₂ c₁₂ c).X j ⟶ A}
    (hfg : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
      (h' : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j),
        K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h' ≫ f = K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h' ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext c (fun i₁₂ i₃ h =>
    HomologicalComplex₂.total.hom_ext c₁₂ (fun i₁ i₂ h' => by
      have := hfg i₁ i₂ i₃ (by rw [h', h])
      rw [K.ιTotal₁₂_eq c₁₂ c i₁ i₂ i₃ j _ i₁₂ h', Category.assoc, Category.assoc] at this
      exact this))

/-- The first differential on the total complex `K.total₁₂ c₁₂ c` of a tricomplex. -/
noncomputable def D₁ (j j' : J) : (K.total₁₂ c₁₂ c).X j ⟶ (K.total₁₂ c₁₂ c).X j' :=
  K.total₁₂Desc (fun _ _ _ _ => K.d₁ _ _ _ _ _ _)

/-- The second differential on the total complex `K.total₁₂ c₁₂ c` of a tricomplex. -/
noncomputable def D₂ (j j' : J) : (K.total₁₂ c₁₂ c).X j ⟶ (K.total₁₂ c₁₂ c).X j' :=
  K.total₁₂Desc (fun _ _ _ _ => K.d₂ _ _ _ _ _ _)

/-- The third differential on the total complex `K.total₁₂ c₁₂ c` of a tricomplex. -/
noncomputable def D₃ (j j' : J) : (K.total₁₂ c₁₂ c).X j ⟶ (K.total₁₂ c₁₂ c).X j' :=
  K.total₁₂Desc (fun _ _ _ _ => K.d₃ _ _ _ _ _ _)

@[reassoc (attr := simp)]
lemma ι_D₁ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ K.D₁ c₁₂ c j j' = K.d₁ _ _ _ _ _ _ := by
  simp [D₁]

@[reassoc (attr := simp)]
lemma ι_D₂ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ K.D₂ c₁₂ c j j' = K.d₂ _ _ _ _ _ _ := by
  simp [D₂]

@[reassoc (attr := simp)]
lemma ι_D₃ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j) :
    K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j h ≫ K.D₃ c₁₂ c j j' = K.d₃ _ _ _ _ _ _ := by
  simp [D₃]

lemma D₁_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₁ c₁₂ c j j' = 0 := by
  apply total₁₂.hom_ext
  intro i₁ i₂ i₃ h'
  rw [ι_D₁, comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · rw [K.d₁_eq_zero' _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₁ c₃ c (ComplexShape.rel_π₁ c₂ c₁₂ h₁ i₂) i₃
  · rw [K.d₁_eq_zero _ _ _ _ _ _ h₁]

lemma D₂_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₂ c₁₂ c j j' = 0 := by
  apply total₁₂.hom_ext
  intro i₁ i₂ i₃ h'
  rw [ι_D₂, comp_zero]
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · rw [K.d₂_eq_zero' _ _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₁ c₃ c (ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₁) i₃
  · rw [K.d₂_eq_zero _ _ _ _ _ _ h₁]

lemma D₃_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₃ c₁₂ c j j' = 0 := by
  apply total₁₂.hom_ext
  intro i₁ i₂ i₃ h'
  rw [ι_D₃, comp_zero]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · rw [K.d₃_eq_zero' _ _ _ _ h₁]
    intro h₂
    apply h
    rw [← h', ← h₂]
    exact ComplexShape.rel_π₂ c₁₂ c _ h₁
  · rw [K.d₃_eq_zero _ _ _ _ _ _ h₁]

lemma int₁₂_D₁ (j j' : J) :
    (int₁₂ K c₁₂).D₁ c j j' = K.D₁ c₁₂ c j j' + K.D₂ c₁₂ c j j' := by
  by_cases h₀ : c.Rel j j'
  · apply total₁₂.hom_ext
    intro i₁ i₂ i₃ h
    rw [Preadditive.comp_add, ι_D₁, ι_D₂, K.ιTotal₁₂_eq c₁₂ c i₁ i₂ i₃ j h _ rfl,
      Category.assoc, HomologicalComplex₂.ι_D₁]
    by_cases h₁ : c₁₂.Rel (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩)
      (c₁₂.next (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩))
    · rw [(K.int₁₂ c₁₂).d₁_eq c h₁ i₃ j']; swap
      · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₁ c₃ c h₁]
      dsimp
      simp only [HomologicalComplex₂.total_d, Preadditive.add_comp, smul_add,
        Preadditive.comp_add, Linear.comp_units_smul, HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc]
      congr 1
      · by_cases h₂ : c₁.Rel i₁ (c₁.next i₁)
        · rw [(K.X' i₃).d₁_eq _ h₂ _ _ (ComplexShape.next_π₁ c₂ c₁₂ h₂ i₂).symm,
            Linear.units_smul_comp, Category.assoc, smul_smul, K.d₁_eq c₁₂ c h₂ i₂ i₃ j']; swap
          · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₁ c₃ c h₁,
              ComplexShape.next_π₁ c₂ c₁₂ h₂ i₂]
          congr 2
          symm
          apply K.ιTotal₁₂_eq
        · rw [(K.X' i₃).d₁_eq_zero _ _ _ _ h₂, zero_comp, smul_zero,
            K.d₁_eq_zero _ _ _ _ _ _ h₂]
      · by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
        · rw [(K.X' i₃).d₂_eq _ _ h₂ _ (ComplexShape.next_π₂ c₁ c₁₂ i₁ h₂).symm,
            Linear.units_smul_comp, Category.assoc, smul_smul, K.d₂_eq c₁₂ c i₁ h₂ i₃ j']; swap
          · rw [← c.next_eq' h₀, ← h, ← ComplexShape.next_π₂ c₁ c₁₂ i₁ h₂,
              ComplexShape.next_π₁ c₃ c h₁ i₃]
          congr 2
          symm
          apply K.ιTotal₁₂_eq
        · rw [(K.X' i₃).d₂_eq_zero _ _ _ _ h₂, zero_comp, smul_zero,
            K.d₂_eq_zero _ _ _ _ _ _ h₂]
    · rw [(K.int₁₂ c₁₂).d₁_eq_zero _ _ _ _ h₁, K.d₁_eq_zero, K.d₂_eq_zero, zero_add, comp_zero]
      · intro h₂
        have H := ComplexShape.rel_π₂ c₁ c₁₂ i₁ h₂
        rw [c₁₂.next_eq' H] at h₁
        exact h₁ H
      · intro h₂
        have H := ComplexShape.rel_π₁ c₂ c₁₂ h₂ i₂
        rw [c₁₂.next_eq' H] at h₁
        exact h₁ H
  · rw [(K.int₁₂ c₁₂).D₁_shape _ _ _ h₀, K.D₁_shape _ _ _ _ h₀, K.D₂_shape _ _ _ _ h₀, zero_add]

lemma int₁₂_D₂ (j j' : J) : (int₁₂ K c₁₂).D₂ c j j' = K.D₃ c₁₂ c j j' :=
  total₁₂.hom_ext (fun i₁ i₂ i₃ h => by
    rw [ι_D₃, K.ιTotal₁₂_eq_assoc c₁₂ c i₁ i₂ i₃ j h _ rfl, HomologicalComplex₂.ι_D₂]
    by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
    · by_cases h₂ : ComplexShape.π c₁₂ c₃ c
        (ComplexShape.π c₁ c₂ c₁₂ ⟨i₁, i₂⟩, ComplexShape.next c₃ i₃) = j'
      · rw [(K.int₁₂ c₁₂).d₂_eq c _ h₁ j' h₂, Linear.comp_units_smul, int₁₂_X_d,
          HomologicalComplex₂.ιTotal_map_assoc, K.d₃_eq c₁₂ c i₁ i₂ h₁ j' (by rw [← h₂])]
        rfl
      · rw [(K.int₁₂ c₁₂).d₂_eq_zero' c _ h₁ j' h₂, comp_zero,
          K.d₃_eq_zero' c₁₂ c i₁ i₂ h₁ j' (fun h₃ => h₂ (by rw [← h₃]))]
    · rw [(K.int₁₂ c₁₂).d₂_eq_zero c _ i₃ j' h₁, comp_zero, K.d₃_eq_zero c₁₂ c i₁ i₂ i₃ j' h₁])

/-- The differential of `Tot(Tot₁₂)` is `D₁ + D₂ + D₃`. -/
@[simp, stacks 08BI "the differential of `Tot` is the sum of the three signed pieces"]
lemma total₁₂_d (j j' : J) :
    (K.total₁₂ c₁₂ c).d j j' = K.D₁ c₁₂ c j j' + K.D₂ c₁₂ c j j' + K.D₃ c₁₂ c j j' := by
  rw [HomologicalComplex₂.total_d, int₁₂_D₁, int₁₂_D₂]

end HomologicalComplex₃
