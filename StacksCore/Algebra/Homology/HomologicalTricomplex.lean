module

public import StacksCore.Algebra.Homology.TotalComplex

/-! # Tricomplexes

Given a category `C` with zero morphisms and three complex shapes `c₁ : ComplexShape I₁`,
`c₂ : ComplexShape I₂`, `c₃ : ComplexShape I₃`, the type of tricomplexes
`HomologicalComplex₃ C c₁ c₂ c₃` is an abbreviation for
`HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁`, exactly as a bicomplex is a complex of
complexes: a tricomplex `K` has terms `((K.X i₁).X i₂).X i₃` and three differentials, the outer
`K.d i₁ i₁'` (Stacks' `d₁`), the middle `(K.X i₁).d i₂ i₂'` (`d₂`) and the inner
`((K.X i₁).X i₂).d i₃ i₃'` (`d₃`).

This is the "triple complex" of Stacks 08BI. The remark's content is that its total complex can
be formed in two steps in either order; the two intermediate bicomplexes are defined here, both
termwise so that they need only the coproducts they actually use:

* `int₂₃ K c₂₃ : HomologicalComplex₂ C c₁ c₂₃`, whose column `i₁` is the total complex
  `(K.X i₁).total c₂₃` of the bicomplex `K.X i₁`, with the outer differential mapped through
  `HomologicalComplex₂.total.map`; it exists under `HasInt₂₃`, "each `K.X i₁` has a total
  complex";
* `int₁₂ K c₁₂ : HomologicalComplex₂ C c₁₂ c₃`, obtained from the slices `K.X' i₃`, the
  bicomplexes in the first two indices at a fixed `i₃`: each slice is totalized and the third
  differential becomes the second differential of the result; it exists under `HasInt₁₂`, "each
  slice has a total complex".

The slices and the two integrations are reducible (`abbrev`): the summand inclusions of the
iterated total complexes compose morphisms whose middle objects agree only after unfolding them,
and keeping that unfolding reducible is what lets `rw` and `simp` work on such composites without
lowering the defeq transparency.

The two total complexes `Tot(Tot₁₂)` and `Tot(Tot₂₃)` and the comparison isomorphism between
them are in `StacksCore.Algebra.Homology.HomologicalTricomplex.Total12`, `.Total23` and
`.Associator`.

Adapted from Joël Riou's unmerged Mathlib pull request #10717 (`HomologicalTricomplex.lean`,
Copyright (c) 2024 Joël Riou, released under the Apache 2.0 license), modernized to the current
Mathlib API.
-/

@[expose] public section

open CategoryTheory Category Limits

variable {C : Type*} [Category* C] {I₁ I₂ I₃ I₁₂ I₂₃ : Type*}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c₃ : ComplexShape I₃}

variable (C c₁ c₂ c₃) in
/-- **Stacks 08BI**, the triple complex. Given a category `C` and three complex shapes `c₁`, `c₂`
and `c₃` on types `I₁`, `I₂` and `I₃`, a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃` is a
complex `K : HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁` of bicomplexes. -/
@[stacks 08BI "the triple complex, as a complex of bicomplexes, for any three complex shapes"]
abbrev HomologicalComplex₃ [HasZeroMorphisms C] :=
  HomologicalComplex (HomologicalComplex₂ C c₂ c₃) c₁

variable [Preadditive C]

namespace HomologicalComplex₃

variable (K : HomologicalComplex₃ C c₁ c₂ c₃)

@[reassoc (attr := simp)]
lemma d_f_f_comp_d_f_f (i₁ i₁' i₁'' : I₁) (i₂ : I₂) (i₃ : I₃) :
    ((K.d i₁ i₁').f i₂).f i₃ ≫ ((K.d i₁' i₁'').f i₂).f i₃ = 0 := by
  rw [← HomologicalComplex.comp_f, HomologicalComplex₂.d_f_comp_d_f, HomologicalComplex.zero_f]

section

variable (c₂₃ : ComplexShape I₂₃) [DecidableEq I₂₃] [TotalComplexShape c₂ c₃ c₂₃]

/-- Given a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃` and a complex shape `c₂₃` with
`TotalComplexShape c₂ c₃ c₂₃`, this is the condition that allows to "integrate" `K` in the last
two indices, to get a bicomplex in `HomologicalComplex₂ C c₁ c₂₃`. -/
abbrev HasInt₂₃ := ∀ (i₁ : I₁), (K.X i₁).HasTotal c₂₃

/-- Given a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃` and a complex shape `c₂₃` with
`TotalComplexShape c₂ c₃ c₂₃`, this is the bicomplex in `HomologicalComplex₂ C c₁ c₂₃` whose
column indexed by `i₁` is `(K.X i₁).total c₂₃`: Stacks' `Tot₂₃(A^{•, •, •})`. -/
@[simps, stacks 08BI "`Tot₂₃`, integrating the last two indices; termwise, for any shapes"]
noncomputable abbrev int₂₃ [K.HasInt₂₃ c₂₃] : HomologicalComplex₂ C c₁ c₂₃ where
  X i₁ := (K.X i₁).total c₂₃
  d i₁ i₁' := HomologicalComplex₂.total.map (K.d i₁ i₁') _
  shape i₁ i₁' h := by
    rw [K.shape _ _ h, HomologicalComplex₂.total.map_zero]
  d_comp_d' i₁ i₁' i₁'' _ _ := by
    rw [← HomologicalComplex₂.total.map_comp, K.d_comp_d, HomologicalComplex₂.total.map_zero]

end

section

/-- Given a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃`, this is the bicomplex in
`HomologicalComplex₂ C c₁ c₂` obtained by fixing the third index `i₃ : I₃`. -/
@[simps!]
abbrev X' (i₃ : I₃) : HomologicalComplex₂ C c₁ c₂ where
  X i₁ :=
    { X := fun i₂ => ((K.X i₁).X i₂).X i₃
      d := fun i₂ i₂' => ((K.X i₁).d i₂ i₂').f i₃ }
  d i₁ i₁' :=
    { f := fun i₂ => ((K.d i₁ i₁').f i₂).f i₃ }

/-- The third differential of a tricomplex, as a morphism `K.X' i₃ ⟶ K.X' i₃'` between the
slices. -/
@[simps]
def d' (i₃ i₃' : I₃) : K.X' i₃ ⟶ K.X' i₃' where
  f i₁ :=
    { f := fun i₂ => ((K.X i₁).X i₂).d i₃ i₃'
      comm' := fun _ _ _ => (HomologicalComplex.Hom.comm _ _ _).symm }
  comm' _ _ _ := by
    ext i₂
    exact (HomologicalComplex.Hom.comm _ _ _).symm

lemma shape_d' (i₃ i₃' : I₃) (h : ¬ c₃.Rel i₃ i₃') :
    K.d' i₃ i₃' = 0 := by
  ext i₁ i₂
  exact ((K.X i₁).X i₂).shape _ _ h

@[reassoc (attr := simp)]
lemma d'_comp_d' (i₃ i₃' i₃'' : I₃) : K.d' i₃ i₃' ≫ K.d' i₃' i₃'' = 0 := by
  ext i₁ i₂
  dsimp
  exact ((K.X i₁).X i₂).d_comp_d _ _ _

variable (c₁₂ : ComplexShape I₁₂) [DecidableEq I₁₂] [TotalComplexShape c₁ c₂ c₁₂]

/-- Given a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃` and a complex shape `c₁₂` with
`TotalComplexShape c₁ c₂ c₁₂`, this is the condition that allows to "integrate" `K` in the first
two indices, to get a bicomplex in `HomologicalComplex₂ C c₁₂ c₃`. -/
abbrev HasInt₁₂ := ∀ (i₃ : I₃), (K.X' i₃).HasTotal c₁₂

/-- Given a tricomplex `K : HomologicalComplex₃ C c₁ c₂ c₃` and a complex shape `c₁₂` with
`TotalComplexShape c₁ c₂ c₁₂`, this is the bicomplex in `HomologicalComplex₂ C c₁₂ c₃` whose row
indexed by `i₃` is `(K.X' i₃).total c₁₂`, the total complex of the slice at `i₃`, and whose second
differential is induced by the third differential of `K`: Stacks' `Tot₁₂(A^{•, •, •})`. -/
@[simps, stacks 08BI "`Tot₁₂`, integrating the first two indices; termwise, for any shapes"]
noncomputable abbrev int₁₂ [K.HasInt₁₂ c₁₂] : HomologicalComplex₂ C c₁₂ c₃ where
  X i₁₂ :=
    { X := fun i₃ => ((K.X' i₃).total c₁₂).X i₁₂
      d := fun i₃ i₃' => (HomologicalComplex₂.total.map (K.d' i₃ i₃') c₁₂).f i₁₂
      shape := fun i₃ i₃' h => by
        rw [K.shape_d' _ _ h, HomologicalComplex₂.total.map_zero, HomologicalComplex.zero_f]
      d_comp_d' := fun i₃ i₃' i₃'' _ _ => by
        rw [← HomologicalComplex.comp_f, ← HomologicalComplex₂.total.map_comp, K.d'_comp_d',
          HomologicalComplex₂.total.map_zero, HomologicalComplex.zero_f] }
  d i₁₂ i₁₂' :=
    { f := fun i₃ => ((K.X' i₃).total c₁₂).d i₁₂ i₁₂'
      comm' := fun i₃ i₃' _ =>
        ((HomologicalComplex₂.total.map (K.d' i₃ i₃') c₁₂).comm i₁₂ i₁₂').symm }
  shape i₁₂ i₁₂' h :=
    HomologicalComplex.Hom.ext (funext fun i₃ => ((K.X' i₃).total c₁₂).shape _ _ h)
  d_comp_d' i₁₂ i₁₂' i₁₂'' _ _ :=
    HomologicalComplex.Hom.ext (funext fun i₃ => ((K.X' i₃).total c₁₂).d_comp_d _ _ _)

end

end HomologicalComplex₃
