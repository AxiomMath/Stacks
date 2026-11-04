module

public import StacksCore.Algebra.Homology.HomologicalTricomplex.Total12
public import StacksCore.Algebra.Homology.HomologicalTricomplex.Total23

/-! # The two total complexes of a tricomplex agree

Stacks 08BI: for a triple complex `A^{•, •, •}` the total complex, with differential
`d₁ + (-1)^p d₂ + (-1)^{p + q} d₃` on the summand `A^{p, q, r}`, "is equal to"
`Tot(Tot₁₂(A))` and to `Tot(Tot₂₃(A))`, so one may combine the first two indices first or the
last two first.

In Lean the two-step total complexes are `K.total₁₂ c₁₂ c` and `K.total₂₃ c₂₃ c`, and the tag's
own `Tot` needs no third definition: `ιTotal₁₂_d_up_ℤ` shows that for `ℤ`-cochain tricomplexes
the differential of `total₁₂` is exactly `d₁ + (-1)^p d₂ + (-1)^{p + q} d₃` on each summand. The
content of the remark is then the isomorphism `totalAssociator : K.total₁₂ c₁₂ c ≅ K.total₂₃ c₂₃ c`,
which is the identity on each summand `((K.X i₁).X i₂).X i₃`. It holds for any six complex shapes
satisfying `ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c`, Mathlib's compatibility of the four
`TotalComplexShape`s, whose fields say precisely that the degrees agree and that the composite
signs of `total₁₂` and `total₂₃` agree on each summand; Mathlib provides the instance for
`c c c c c c` whenever `c` has `TensorSigns`, in particular for `up ℤ`.

Mathlib's `HomologicalComplex.mapBifunctorAssociator` is the same statement for the tricomplexes
`G(F₁₂(K₁, K₂), K₃)` and `F(K₁, G₂₃(K₂, K₃))` built from bifunctors. The proofs here follow the
same pattern: the isomorphism is defined degreewise by the universal property of the coproducts,
and commutes with each of the three pieces of the differential by one of the three sign axioms.
Adapted from Joël Riou's unmerged Mathlib pull request #10717 (`HomologicalTricomplex.lean`,
Copyright (c) 2024 Joël Riou, released under the Apache 2.0 license), modernized to the current
Mathlib API.
-/

@[expose] public section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C] [Preadditive C] {I₁ I₂ I₃ I₁₂ I₂₃ J : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

namespace HomologicalComplex₃

variable (K : HomologicalComplex₃ C c₁ c₂ c₃)
  (c₁₂ : ComplexShape I₁₂) (c₂₃ : ComplexShape I₂₃) (c : ComplexShape J)
  [DecidableEq I₁₂] [DecidableEq I₂₃] [DecidableEq J]
  [TotalComplexShape c₁ c₂ c₁₂] [TotalComplexShape c₂ c₃ c₂₃]
  [TotalComplexShape c₁₂ c₃ c] [TotalComplexShape c₁ c₂₃ c]
  [K.HasInt₁₂ c₁₂] [K.HasInt₂₃ c₂₃] [K.HasTotal₁₂ c₁₂ c] [K.HasTotal₂₃ c₂₃ c]
  [ComplexShape.Associative c₁ c₂ c₃ c₁₂ c₂₃ c]

/-- The associator isomorphism `K.total₁₂ c₁₂ c ≅ K.total₂₃ c₂₃ c` between the two ways to
obtain the total complex of a tricomplex, in each degree. -/
noncomputable def totalAssociatorX (j : J) : (K.total₁₂ c₁₂ c).X j ≅ (K.total₂₃ c₂₃ c).X j where
  hom := K.total₁₂Desc (fun i₁ i₂ i₃ h => K.ιTotal₂₃ c₂₃ c i₁ i₂ i₃ j
    (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]))
  inv := K.total₂₃Desc (fun i₁ i₂ i₃ h => K.ιTotal₁₂ c₁₂ c i₁ i₂ i₃ j
    (by rw [← h, ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c]))
  hom_inv_id := by
    apply total₁₂.hom_ext
    intro i₁ i₂ i₃ h
    rw [ι_total₁₂Desc_assoc, ι_total₂₃Desc, comp_id]
  inv_hom_id := by
    apply total₂₃.hom_ext
    intro i₁ i₂ i₃ h
    rw [ι_total₂₃Desc_assoc, ι_total₁₂Desc, comp_id]

section

variable (i₁ : I₁) (i₂ : I₂) (i₃ : I₃) (j : J)

@[reassoc (attr := simp)]
lemma ιTotal₁₂OrZero_totalAssociatorX_hom :
    K.ιTotal₁₂OrZero c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom =
      K.ιTotal₂₃OrZero c₂₃ c i₁ i₂ i₃ j := by
  by_cases h : ComplexShape.π c₁₂ c₃ c (ComplexShape.π c₁ c₂ c₁₂ (i₁, i₂), i₃) = j
  · dsimp [totalAssociatorX]
    rw [K.ιTotal₁₂OrZero_eq c₁₂ c i₁ i₂ i₃ j h, ι_total₁₂Desc,
      K.ιTotal₂₃OrZero_eq c₂₃ c i₁ i₂ i₃ j]
  · rw [K.ιTotal₁₂OrZero_eq_zero c₁₂ c i₁ i₂ i₃ j h, zero_comp,
      K.ιTotal₂₃OrZero_eq_zero c₂₃ c i₁ i₂ i₃ j]
    intro h'
    exact h (by rw [ComplexShape.assoc c₁ c₂ c₃ c₁₂ c₂₃ c, h'])

@[reassoc (attr := simp)]
lemma totalAssociatorX_hom_d₁' :
    K.d₁ c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom = K.d₁' c₂₃ c i₁ i₂ i₃ j := by
  simp [d₁, d₁', ComplexShape.associative_ε₁_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃]

@[reassoc (attr := simp)]
lemma totalAssociatorX_hom_d₂' :
    K.d₂ c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom = K.d₂' c₂₃ c i₁ i₂ i₃ j := by
  simp [d₂, d₂', ComplexShape.associative_ε₂_ε₁ c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃]

@[reassoc (attr := simp)]
lemma totalAssociatorX_hom_d₃' :
    K.d₃ c₁₂ c i₁ i₂ i₃ j ≫ (K.totalAssociatorX c₁₂ c₂₃ c j).hom = K.d₃' c₂₃ c i₁ i₂ i₃ j := by
  simp [d₃, d₃', ComplexShape.associative_ε₂_eq_mul c₁ c₂ c₃ c₁₂ c₂₃ c i₁ i₂ i₃]

end

@[reassoc]
lemma D₁_totalAssociatorX_hom (j j' : J) :
    K.D₁ c₁₂ c j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom =
      (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ K.D₁' c₂₃ c j j' := by
  apply total₁₂.hom_ext
  intro i₁ i₂ i₃ h
  simpa [totalAssociatorX] using K.totalAssociatorX_hom_d₁' c₁₂ c₂₃ c i₁ i₂ i₃ j'

@[reassoc]
lemma D₂_totalAssociatorX_hom (j j' : J) :
    K.D₂ c₁₂ c j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom =
      (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ K.D₂' c₂₃ c j j' := by
  apply total₁₂.hom_ext
  intro i₁ i₂ i₃ h
  simpa [totalAssociatorX] using K.totalAssociatorX_hom_d₂' c₁₂ c₂₃ c i₁ i₂ i₃ j'

@[reassoc]
lemma D₃_totalAssociatorX_hom (j j' : J) :
    K.D₃ c₁₂ c j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom =
      (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ K.D₃' c₂₃ c j j' := by
  apply total₁₂.hom_ext
  intro i₁ i₂ i₃ h
  simpa [totalAssociatorX] using K.totalAssociatorX_hom_d₃' c₁₂ c₂₃ c i₁ i₂ i₃ j'

@[reassoc]
lemma totalAssociatorX_hom_d (j j' : J) :
    (K.totalAssociatorX c₁₂ c₂₃ c j).hom ≫ (K.total₂₃ c₂₃ c).d j j' =
      (K.total₁₂ c₁₂ c).d j j' ≫ (K.totalAssociatorX c₁₂ c₂₃ c j').hom := by
  simp only [total₂₃_d, Preadditive.comp_add, total₁₂_d, Preadditive.add_comp,
    D₁_totalAssociatorX_hom, D₂_totalAssociatorX_hom, D₃_totalAssociatorX_hom]

/-- **Stacks 08BI**: the two ways of forming the total complex of a tricomplex agree,
`Tot(Tot₁₂(A)) ≅ Tot(Tot₂₃(A))`, by the isomorphism which is the identity on every summand. -/
@[stacks 08BI "`Tot(Tot₁₂) ≅ Tot(Tot₂₃)`, the identity on every summand, under `Associative`"]
noncomputable def totalAssociator : K.total₁₂ c₁₂ c ≅ K.total₂₃ c₂₃ c :=
  HomologicalComplex.Hom.isoOfComponents (K.totalAssociatorX c₁₂ c₂₃ c)
    (fun j j' _ => K.totalAssociatorX_hom_d c₁₂ c₂₃ c j j')

section upℤ

open ComplexShape

variable (A : HomologicalComplex₃ C (up ℤ) (up ℤ) (up ℤ)) [A.HasInt₁₂ (up ℤ)]
  [A.HasTotal₁₂ (up ℤ) (up ℤ)]

/-- **Stacks 08BI**, the tag's formula for the differential of the total complex of a `ℤ`-cochain
triple complex: on the summand `A^{p, q, r}` it is `d₁ + (-1)^p d₂ + (-1)^{p + q} d₃`. -/
@[stacks 08BI "the tag's `d₁ + (-1)^p d₂ + (-1)^{p + q} d₃` on `A^{p, q, r}`, over `ℤ`"]
theorem ιTotal₁₂_d_up_ℤ (p q r n : ℤ) (h : p + q + r = n) :
    A.ιTotal₁₂ (up ℤ) (up ℤ) p q r n h ≫ (A.total₁₂ (up ℤ) (up ℤ)).d n (n + 1) =
      ((A.d p (p + 1)).f q).f r ≫ A.ιTotal₁₂ (up ℤ) (up ℤ) (p + 1) q r (n + 1) (by dsimp; lia) +
        p.negOnePow •
          (((A.X p).d q (q + 1)).f r ≫ A.ιTotal₁₂ (up ℤ) (up ℤ) p (q + 1) r (n + 1)
            (by dsimp; lia)) +
        (p + q).negOnePow •
          (((A.X p).X q).d r (r + 1) ≫ A.ιTotal₁₂ (up ℤ) (up ℤ) p q (r + 1) (n + 1)
            (by dsimp; lia)) := by
  rw [total₁₂_d, Preadditive.comp_add, Preadditive.comp_add, ι_D₁, ι_D₂, ι_D₃,
    A.d₁_eq (up ℤ) (up ℤ) (i₁ := p) (i₁' := p + 1) rfl q r (n + 1) (by dsimp; lia),
    A.d₂_eq (up ℤ) (up ℤ) p (i₂ := q) (i₂' := q + 1) rfl r (n + 1) (by dsimp; lia),
    A.d₃_eq (up ℤ) (up ℤ) p q (i₃ := r) (i₃' := r + 1) rfl (n + 1) (by dsimp; lia)]
  simp

end upℤ

end HomologicalComplex₃
