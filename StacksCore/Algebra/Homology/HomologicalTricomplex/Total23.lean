module

public import StacksCore.Algebra.Homology.HomologicalTricomplex

/-! # The total complex of a tricomplex, last two indices first

For a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃`, `K.total₂₃ c₂₃ c` is the total complex of
the bicomplex `K.int₂₃ c₂₃ : HomologicalComplex₂ C c₁ c₂₃`: Stacks' `Tot(Tot₂₃(A^{•, •, •}))`.
Its degree-`j` term is the coproduct of the `((K.X i₁).X i₂).X i₃` over the triples with
`π c₁ c₂₃ c (i₁, π c₂ c₃ c₂₃ (i₂, i₃)) = j`, with inclusions `ιTotal₂₃`, and its differential is
`D₁' + D₂' + D₃'` (`total₂₃_d`), the three pieces acting on a summand by the three differentials
of `K` up to the signs of the two `TotalComplexShape`s (`d₁'_eq`, `d₂'_eq`, `d₃'_eq`). The primes
distinguish these from their `total₁₂` counterparts in
`StacksCore.Algebra.Homology.HomologicalTricomplex.Total12`; the two are compared in
`StacksCore.Algebra.Homology.HomologicalTricomplex.Associator`.

The structure mirrors Mathlib's `HomologicalComplex.mapBifunctor₂₃` in
`Mathlib.Algebra.Homology.BifunctorAssociator`.
Adapted from Joël Riou's unmerged Mathlib pull request #10717 (`HomologicalTricomplex.lean`,
Copyright (c) 2024 Joël Riou, released under the Apache 2.0 license), modernized to the current
Mathlib API.
-/

@[expose] public section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C] [Preadditive C] {I₁ I₂ I₃ I₂₃ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

namespace HomologicalComplex₃

variable (K : HomologicalComplex₃ C c₁ c₂ c₃)
  (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J) [DecidableEq I₂₃] [DecidableEq J]
  [TotalComplexShape c₂ c₃ c₂₃] [TotalComplexShape c₁ c₂₃ c] [K.HasInt₂₃ c₂₃]

/-- The condition that one may obtain a total complex of a tricomplex
`K : HomologicalComplex₃ C c₁ c₂ c₃` in two steps by taking the total complex of the bicomplex
`K.int₂₃ c₂₃ : HomologicalComplex₂ C c₁ c₂₃`. -/
abbrev HasTotal₂₃ := (K.int₂₃ c₂₃).HasTotal c

variable [K.HasTotal₂₃ c₂₃ c]

/-- **Stacks 08BI**, `Tot(Tot₂₃(A^{•, •, •}))`: the total complex of a tricomplex
`K : HomologicalComplex₃ C c₁ c₂ c₃` as the total complex of the bicomplex
`K.int₂₃ c₂₃ : HomologicalComplex₂ C c₁ c₂₃`. -/
@[stacks 08BI "`Tot(Tot₂₃)`; any shapes"]
noncomputable abbrev total₂₃ : HomologicalComplex C c :=
  (K.int₂₃ c₂₃).total c

section

variable (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)

/-- The inclusion of a summand in the total complex `K.total₂₃ c₂₃ c` of a tricomplex. -/
noncomputable def ιTotal₂₃
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  (K.X i₁).ιTotal c₂₃ i₂ i₃ _ rfl ≫
    (K.int₂₃ c₂₃).ιTotal c i₁ (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩) j h

@[reassoc]
lemma ιTotal₂₃_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j)
    (i₂₃ : I₂₃) (h' : ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩ = i₂₃) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h = (K.X i₁).ιTotal c₂₃ i₂ i₃ i₂₃ h' ≫
    (K.int₂₃ c₂₃).ιTotal c i₁ i₂₃ j (by rw [← h', h]) := by
  subst h'
  rfl

/-- The inclusion of a summand in the total complex `K.total₂₃ c₂₃ c` of a tricomplex,
or zero. -/
noncomputable def ιTotal₂₃OrZero :
    ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  if h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j then
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h
  else 0

lemma ιTotal₂₃OrZero_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃OrZero c₂₃ c i₁ i₂ i₃ j = K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h := dite_eq_left h

lemma ιTotal₂₃OrZero_eq_zero
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) ≠ j) :
    K.ιTotal₂₃OrZero c₂₃ c i₁ i₂ i₃ j = 0 := dite_eq_right h

end

section

variable (i₁ i₁' : I₁) (h₁ : c₁.Rel i₁ i₁')
  (i₂ i₂' : I₂) (h₂ : c₂.Rel i₂ i₂')
  (i₃ i₃' : I₃) (h₃ : c₃.Rel i₃ i₃') (j : J)

/-- The first differential on a summand of the total complex `K.total₂₃ c₂₃ c` of a
tricomplex. -/
noncomputable def d₁' : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
    ((K.d i₁ (c₁.next i₁)).f i₂).f i₃ ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _

/-- The second differential on a summand of the total complex `K.total₂₃ c₂₃ c` of a
tricomplex. -/
noncomputable def d₂' : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
    ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) •
  ((K.X i₁).d i₂ (c₂.next i₂)).f i₃ ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _

/-- The third differential on a summand of the total complex `K.total₂₃ c₂₃ c` of a
tricomplex. -/
noncomputable def d₃' : ((K.X i₁).X i₂).X i₃ ⟶ (K.total₂₃ c₂₃ c).X j :=
  (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
    ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
      ((K.X i₁).X i₂).d i₃ (c₃.next i₃) ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _

lemma d₁'_eq_zero (h : ¬ c₁.Rel i₁ (c₁.next i₁)) : K.d₁' c₂₃ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₁']
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f,
    HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₂'_eq_zero (h : ¬ c₂.Rel i₂ (c₂.next i₂)) : K.d₂' c₂₃ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₂']
  rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.zero_f, zero_comp, smul_zero]

lemma d₃'_eq_zero (h : ¬ c₃.Rel i₃ (c₃.next i₃)) : K.d₃' c₂₃ c i₁ i₂ i₃ j = 0 := by
  dsimp [d₃']
  rw [HomologicalComplex.shape _ _ _ h, zero_comp, smul_zero]

section

variable {i₁ i₁'}
include h₁

lemma d₁'_eq' :
    K.d₁' c₂₃ c i₁ i₂ i₃ j = ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _ := by
  obtain rfl := c₁.next_eq' h₁
  rfl

lemma d₁'_eq_zero'
    (h : ComplexShape.π c₁ c₂₃ c (i₁', ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) ≠ j) :
    K.d₁' c₂₃ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₁'_eq' c₂₃ c h₁, ιTotal₂₃OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₁'_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁', ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.d₁' c₂₃ c i₁ i₂ i₃ j = ComplexShape.ε₁ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) •
        ((K.d i₁ i₁').f i₂).f i₃ ≫ ιTotal₂₃ K c₂₃ c i₁' i₂ i₃ j h := by
  rw [K.d₁'_eq' c₂₃ c h₁, ιTotal₂₃OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₂ i₂'}
include h₂

lemma d₂'_eq' :
    K.d₂' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
      K.ιTotal₂₃OrZero c₂₃ c _ _ _ _ := by
  obtain rfl := c₂.next_eq' h₂
  rfl

lemma d₂'_eq_zero'
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂', i₃)) ≠ j) :
    K.d₂' c₂₃ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₂'_eq' c₂₃ c i₁ h₂, ιTotal₂₃OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₂'_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂', i₃)) = j) :
    K.d₂' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₁ c₂ c₃ c₂₃ (i₂, i₃)) • ((K.X i₁).d i₂ i₂').f i₃ ≫
        ιTotal₂₃ K c₂₃ c i₁ i₂' i₃ j h := by
  rw [K.d₂'_eq' c₂₃ c i₁ h₂, ιTotal₂₃OrZero_eq _ _ _ _ _ _ _ h]

end

section

variable {i₃ i₃'}
include h₃

lemma d₃'_eq' :
    K.d₃' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ K.ιTotal₂₃OrZero c₂₃ c _ _ _ _ := by
  obtain rfl := c₃.next_eq' h₃
  rfl

lemma d₃'_eq_zero'
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃')) ≠ j) :
    K.d₃' c₂₃ c i₁ i₂ i₃ j = 0 := by
  rw [K.d₃'_eq' c₂₃ c i₁ i₂ h₃, ιTotal₂₃OrZero_eq_zero _ _ _ _ _ _ _ h, comp_zero, smul_zero]

lemma d₃'_eq
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃')) = j) :
    K.d₃' c₂₃ c i₁ i₂ i₃ j = (ComplexShape.ε₂ c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) *
      ComplexShape.ε₂ c₂ c₃ c₂₃ (i₂, i₃)) •
      ((K.X i₁).X i₂).d i₃ i₃' ≫ ιTotal₂₃ K c₂₃ c i₁ i₂ i₃' j h := by
  rw [K.d₃'_eq' c₂₃ c i₁ i₂ h₃, ιTotal₂₃OrZero_eq _ _ _ _ _ _ _ h]

end

end

section

variable {c₂₃ c}
variable {A : C} {j : J} (f : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (_ : ComplexShape.π c₁ c₂₃ c ⟨i₁, ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ = j),
      ((K.X i₁).X i₂).X i₃ ⟶ A)

/-- Constructor for morphisms from one of the objects constituting the total complex
`K.total₂₃ c₂₃ c` of a tricomplex. -/
noncomputable def total₂₃Desc : (K.total₂₃ c₂₃ c).X j ⟶ A :=
  (K.int₂₃ c₂₃).totalDesc (fun i₁ i₂₃ h => (K.X i₁).totalDesc
    (fun i₂ i₃ h' => f i₁ i₂ i₃ (by rw [h', h])))

@[reassoc (attr := simp)]
lemma ι_total₂₃Desc (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
    (h : ComplexShape.π c₁ c₂₃ c ⟨i₁, ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ total₂₃Desc K f = f i₁ i₂ i₃ h := by
  simp [ιTotal₂₃, total₂₃Desc]

end

variable {K c₂₃ c} in
@[ext]
lemma total₂₃.hom_ext {A : C} {j : J} {f g : (K.total₂₃ c₂₃ c).X j ⟶ A}
    (hfg : ∀ (i₁ : I₁) (i₂ : I₂) (i₃ : I₃)
      (h' : ComplexShape.π c₁ c₂₃ c ⟨i₁, ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩⟩ = j),
        K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h' ≫ f = K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h' ≫ g) :
    f = g :=
  HomologicalComplex₂.total.hom_ext c (fun i₁ i₂₃ h =>
    HomologicalComplex₂.total.hom_ext c₂₃ (fun i₂ i₃ h' => by
      have := hfg i₁ i₂ i₃ (by rw [h', h])
      rw [K.ιTotal₂₃_eq c₂₃ c i₁ i₂ i₃ j _ i₂₃ h', Category.assoc, Category.assoc] at this
      exact this))

/-- The first differential on the total complex `K.total₂₃ c₂₃ c` of a tricomplex. -/
noncomputable def D₁' (j j' : J) : (K.total₂₃ c₂₃ c).X j ⟶ (K.total₂₃ c₂₃ c).X j' :=
  K.total₂₃Desc (fun _ _ _ _ => K.d₁' _ _ _ _ _ _)

/-- The second differential on the total complex `K.total₂₃ c₂₃ c` of a tricomplex. -/
noncomputable def D₂' (j j' : J) : (K.total₂₃ c₂₃ c).X j ⟶ (K.total₂₃ c₂₃ c).X j' :=
  K.total₂₃Desc (fun _ _ _ _ => K.d₂' _ _ _ _ _ _)

/-- The third differential on the total complex `K.total₂₃ c₂₃ c` of a tricomplex. -/
noncomputable def D₃' (j j' : J) : (K.total₂₃ c₂₃ c).X j ⟶ (K.total₂₃ c₂₃ c).X j' :=
  K.total₂₃Desc (fun _ _ _ _ => K.d₃' _ _ _ _ _ _)

@[reassoc (attr := simp)]
lemma ι_D₁' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ K.D₁' c₂₃ c j j' = K.d₁' _ _ _ _ _ _ := by
  simp [D₁']

@[reassoc (attr := simp)]
lemma ι_D₂' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ K.D₂' c₂₃ c j j' = K.d₂' _ _ _ _ _ _ := by
  simp [D₂']

@[reassoc (attr := simp)]
lemma ι_D₃' (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j j' : J)
    (h : ComplexShape.π c₁ c₂₃ c (i₁, ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j) :
    K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j h ≫ K.D₃' c₂₃ c j j' = K.d₃' _ _ _ _ _ _ := by
  simp [D₃']

/-- If `j` is not related to `j'`, a target related to a source index in degree `j` is not `j'`. -/
private lemma ne_of_not_rel_of_eq {J : Type*} {c : ComplexShape J} {j j' x y : J}
    (h : ¬ c.Rel j j') (h' : x = j) (hr : c.Rel x y) : y ≠ j' := by
  rintro rfl
  exact h (h' ▸ hr)

lemma D₁'_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₁' c₂₃ c j j' = 0 := by
  apply total₂₃.hom_ext
  intro i₁ i₂ i₃ h'
  rw [ι_D₁', comp_zero]
  by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
  · exact K.d₁'_eq_zero' _ _ h₁ _ _ _
      (ne_of_not_rel_of_eq h h' (ComplexShape.rel_π₁ c₂₃ c h₁ _))
  · rw [K.d₁'_eq_zero _ _ _ _ _ _ h₁]

lemma D₂'_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₂' c₂₃ c j j' = 0 := by
  apply total₂₃.hom_ext
  intro i₁ i₂ i₃ h'
  rw [ι_D₂', comp_zero]
  by_cases h₁ : c₂.Rel i₂ (c₂.next i₂)
  · exact K.d₂'_eq_zero' _ _ _ h₁ _ _
      (ne_of_not_rel_of_eq h h' (ComplexShape.rel_π₂ c₁ c i₁ (ComplexShape.rel_π₁ c₃ c₂₃ h₁ i₃)))
  · rw [K.d₂'_eq_zero _ _ _ _ _ _ h₁]

lemma D₃'_shape (j j' : J) (h : ¬ c.Rel j j') : K.D₃' c₂₃ c j j' = 0 := by
  apply total₂₃.hom_ext
  intro i₁ i₂ i₃ h'
  rw [ι_D₃', comp_zero]
  by_cases h₁ : c₃.Rel i₃ (c₃.next i₃)
  · exact K.d₃'_eq_zero' _ _ _ _ h₁ _
      (ne_of_not_rel_of_eq h h' (ComplexShape.rel_π₂ c₁ c i₁ (ComplexShape.rel_π₂ c₂ c₂₃ i₂ h₁)))
  · rw [K.d₃'_eq_zero _ _ _ _ _ _ h₁]

lemma int₂₃_D₁ (j j' : J) :
    (int₂₃ K c₂₃).D₁ c j j' = K.D₁' c₂₃ c j j' :=
  total₂₃.hom_ext (fun i₁ i₂ i₃ h => by
    rw [ι_D₁', K.ιTotal₂₃_eq c₂₃ c i₁ i₂ i₃ j h _ rfl, Category.assoc, HomologicalComplex₂.ι_D₁]
    by_cases h₁ : c₁.Rel i₁ (c₁.next i₁)
    · by_cases h₂ : ComplexShape.π c₁ c₂₃ c (ComplexShape.next c₁ i₁,
        ComplexShape.π c₂ c₃ c₂₃ (i₂, i₃)) = j'
      · rw [(K.int₂₃ c₂₃).d₁_eq c h₁ _ _ h₂, Linear.comp_units_smul,
          int₂₃_d, HomologicalComplex₂.ιTotal_map_assoc]
        congr 2
        symm
        apply ιTotal₂₃OrZero_eq
      · rw [(K.int₂₃ c₂₃).d₁_eq_zero' c h₁ _ _ h₂, comp_zero, K.d₁'_eq_zero' c₂₃ c h₁ _ _ _ h₂]
    · rw [K.d₁'_eq_zero c₂₃ c i₁ i₂ i₃ j' h₁, (K.int₂₃ c₂₃).d₁_eq_zero _ _ _ _ h₁, comp_zero])

lemma int₂₃_D₂ (j j' : J) : (int₂₃ K c₂₃).D₂ c j j' = K.D₂' c₂₃ c j j' + K.D₃' c₂₃ c j j' := by
  by_cases h₀ : c.Rel j j'
  · apply total₂₃.hom_ext
    intro i₁ i₂ i₃ h
    rw [Preadditive.comp_add, ι_D₂', ι_D₃', K.ιTotal₂₃_eq c₂₃ c i₁ i₂ i₃ j h _ rfl,
      Category.assoc, HomologicalComplex₂.ι_D₂]
    by_cases h₁ : c₂₃.Rel (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩)
      (c₂₃.next (ComplexShape.π c₂ c₃ c₂₃ ⟨i₂, i₃⟩))
    · rw [(K.int₂₃ c₂₃).d₂_eq c i₁ h₁ j']; swap
      · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₂ c₁ c i₁ h₁]
      dsimp
      simp only [HomologicalComplex₂.total_d, Preadditive.add_comp, smul_add,
        Preadditive.comp_add, Linear.comp_units_smul, HomologicalComplex₂.ι_D₁_assoc,
        HomologicalComplex₂.ι_D₂_assoc]
      congr 1
      · by_cases h₂ : c₂.Rel i₂ (c₂.next i₂)
        · rw [(K.X i₁).d₁_eq _ h₂ _ _ (ComplexShape.next_π₁ c₃ c₂₃ h₂ i₃).symm,
            Linear.units_smul_comp, Category.assoc, smul_smul, K.d₂'_eq c₂₃ c i₁ h₂ i₃ j']; swap
          · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₂ c₁ c i₁ h₁,
              ComplexShape.next_π₁ c₃ c₂₃ h₂]
          congr 2
          symm
          apply K.ιTotal₂₃_eq
        · rw [(K.X i₁).d₁_eq_zero _ _ _ _ h₂, zero_comp, smul_zero, K.d₂'_eq_zero _ _ _ _ _ _ h₂]
      · by_cases h₂ : c₃.Rel i₃ (c₃.next i₃)
        · rw [(K.X i₁).d₂_eq _ _ h₂ _ (ComplexShape.next_π₂ c₂ c₂₃ i₂ h₂).symm,
            Linear.units_smul_comp, Category.assoc, smul_smul, K.d₃'_eq c₂₃ c i₁ i₂ h₂ j']; swap
          · rw [← c.next_eq' h₀, ← h, ComplexShape.next_π₂ c₁ c i₁ h₁,
              ComplexShape.next_π₂ c₂ c₂₃ i₂ h₂]
          congr 2
          symm
          apply K.ιTotal₂₃_eq
        · rw [(K.X i₁).d₂_eq_zero _ _ _ _ h₂, zero_comp, smul_zero, K.d₃'_eq_zero _ _ _ _ _ _ h₂]
    · rw [(K.int₂₃ c₂₃).d₂_eq_zero _ _ _ _ h₁, K.d₂'_eq_zero, K.d₃'_eq_zero, zero_add, comp_zero]
      · intro h₂
        have H := ComplexShape.rel_π₂ c₂ c₂₃ i₂ h₂
        rw [c₂₃.next_eq' H] at h₁
        exact h₁ H
      · intro h₂
        have H := ComplexShape.rel_π₁ c₃ c₂₃ h₂ i₃
        rw [c₂₃.next_eq' H] at h₁
        exact h₁ H
  · rw [(K.int₂₃ c₂₃).D₂_shape _ _ _ h₀, K.D₂'_shape _ _ _ _ h₀, K.D₃'_shape _ _ _ _ h₀, zero_add]

/-- The differential of `Tot(Tot₂₃)` is `D₁' + D₂' + D₃'`. -/
@[simp]
lemma total₂₃_d (j j' : J) :
    (K.total₂₃ c₂₃ c).d j j' = K.D₁' c₂₃ c j j' + K.D₂' c₂₃ c j j' + K.D₃' c₂₃ c j j' := by
  rw [HomologicalComplex₂.total_d, int₂₃_D₁, int₂₃_D₂, add_assoc]

end HomologicalComplex₃
