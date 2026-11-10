module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
import StacksCore.Tactic.StacksAttribute

/-! ## Double complexes

Stacks 012Y defines a double complex in an additive category `𝒜` as a system `(A^{p, q}, d₁, d₂)`
indexed by `ℤ × ℤ`, with `d₁^{p, q} : A^{p, q} → A^{p + 1, q}` and
`d₂^{p, q} : A^{p, q} → A^{p, q + 1}`, such that (1) `d₁ ∘ d₁ = 0`, (2) `d₂ ∘ d₂ = 0` and
(3) `d₁ ∘ d₂ = d₂ ∘ d₁`. The section then warns that some authors require the squares to
*anti*commute instead; Mathlib, like Stacks, has them commute.

Mathlib's `HomologicalComplex₂ C c₁ c₂` is `HomologicalComplex (HomologicalComplex C c₂) c₁`, a
complex of complexes for arbitrary complex shapes and any category with zero morphisms. Its first
index is the outer one — Mathlib's docstring calls `K.X p` a column — so the object in bidegree
`(p, q)` is `(K.X p).X q`, the tag's `d₁^{p, q}` is `(K.d p (p + 1)).f q`, and its `d₂^{p, q}` is
`(K.X p).d q (q + 1)`. Rule (1) is `HomologicalComplex₂.d_f_comp_d_f`, rule (2) is
`HomologicalComplex.d_comp_d` on each column, and rule (3) is `HomologicalComplex₂.d_comm`, which
states the same equation with its two sides swapped.

The tag's own presentation is `HomologicalComplex₂.DoubleComplex` below: the objects and the two
differentials as data and the three rules as fields, shaped like `HomologicalComplex` itself. It
is the same notion, not merely a source of bicomplexes: `DoubleComplex.equivHomologicalComplex₂`
is a bijection with `HomologicalComplex₂ C (up ℤ) (up ℤ)`. Its forward map builds the columns and
the outer complex with `CochainComplex.of`, which extends the differentials by zero away from
adjacent degrees, and each horizontal differential `d p (p + 1)` with `CochainComplex.ofHom` from
the components `d₁ p`; its inverse reads the data off a bicomplex. Mathlib has no such
Stacks-shaped constructor — `HomologicalComplex₂.ofGradedObject` takes differentials over all pairs
of indices together with separate vanishing hypotheses.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

add_to_stacks 012Y "any complex shapes, any category with zero morphisms; the first index is outer"
  HomologicalComplex₂
add_to_stacks 012Y "rule (1), `d₁ ∘ d₁ = 0`; rule (2) is `d_comp_d` on each column"
  HomologicalComplex₂.d_f_comp_d_f
add_to_stacks 012Y "rule (3), the squares commute; stated with its two sides swapped"
  HomologicalComplex₂.d_comm

add_to_stacks 0G6B "`DoubleComp(𝒜)` as complexes of complexes with outer index `p`, Mathlib's view"
  HomologicalComplex₂
add_to_stacks 0G6A "`DoubleComp(𝒜)` as complexes of complexes with outer index `q`: the flip"
  HomologicalComplex₂.flip

namespace HomologicalComplex₂

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- **Stacks 012Y.** A double complex: a `ℤ × ℤ`-indexed family of objects with a horizontal and
a vertical differential, such that `d₁ ∘ d₁ = 0`, `d₂ ∘ d₂ = 0` and the squares commute. -/
@[stacks 012Y "the tag's definition, as a structure shaped like `HomologicalComplex`", sga
  "4 XVII 0.4" "case |I| = 2"]
structure DoubleComplex (C : Type*) [Category* C] [HasZeroMorphisms C] where
  /-- The object in bidegree `(p, q)`. -/
  X : ℤ → ℤ → C
  /-- The horizontal differential `d₁^{p, q} : A^{p, q} → A^{p + 1, q}`. -/
  d₁ (p q : ℤ) : X p q ⟶ X (p + 1) q
  /-- The vertical differential `d₂^{p, q} : A^{p, q} → A^{p, q + 1}`. -/
  d₂ (p q : ℤ) : X p q ⟶ X p (q + 1)
  /-- Rule (1): `d₁^{p + 1, q} ∘ d₁^{p, q} = 0`. -/
  d₁_comp_d₁ (p q : ℤ) : d₁ p q ≫ d₁ (p + 1) q = 0 := by cat_disch
  /-- Rule (2): `d₂^{p, q + 1} ∘ d₂^{p, q} = 0`. -/
  d₂_comp_d₂ (p q : ℤ) : d₂ p q ≫ d₂ p (q + 1) = 0 := by cat_disch
  /-- Rule (3): `d₁^{p, q + 1} ∘ d₂^{p, q} = d₂^{p + 1, q} ∘ d₁^{p, q}`. -/
  comm (p q : ℤ) : d₂ p q ≫ d₁ p (q + 1) = d₁ p q ≫ d₂ (p + 1) q := by cat_disch

namespace DoubleComplex

variable (A : DoubleComplex C)

/-- The bicomplex of a double complex. The columns and the outer complex are `CochainComplex.of`,
which extends `d₂` and the horizontal differential by zero away from adjacent degrees; the
horizontal differential `d p (p + 1)` is `CochainComplex.ofHom` with components `d₁ p`. -/
@[implicit_reducible]
def toHomologicalComplex₂ : HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  CochainComplex.of (fun p => CochainComplex.of (A.X p) (A.d₂ p) (A.d₂_comp_d₂ p))
    (fun p => CochainComplex.ofHom (A.d₁ p) fun q => by
      simpa [CochainComplex.of_d] using (A.comm p q).symm)
    fun p => by
      ext q
      simpa using A.d₁_comp_d₁ p q

/-- The bicomplex of a double complex has the same objects. -/
@[simp]
lemma toHomologicalComplex₂_X_X (p q : ℤ) : (A.toHomologicalComplex₂.X p).X q = A.X p q := rfl

/-- The columns of the bicomplex of a double complex have differential `d₂`. -/
@[simp]
lemma toHomologicalComplex₂_X_d (p q : ℤ) :
    (A.toHomologicalComplex₂.X p).d q (q + 1) = A.d₂ p q := by
  simp [toHomologicalComplex₂, CochainComplex.of_d]

/-- The horizontal differential of the bicomplex of a double complex has components `d₁`. -/
@[simp]
lemma toHomologicalComplex₂_d_f (p q : ℤ) :
    (A.toHomologicalComplex₂.d p (p + 1)).f q = A.d₁ p q := by
  simp [toHomologicalComplex₂, CochainComplex.of_d]

end DoubleComplex

/-- The double complex of a bicomplex: its objects, the components of its differential, and the
differentials of its columns. The three rules are `d_f_comp_d_f`, `d_comp_d` on each column, and
`d_comm`. -/
@[implicit_reducible, simps]
def toDoubleComplex (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) : DoubleComplex C where
  X p q := (K.X p).X q
  d₁ p q := (K.d p (p + 1)).f q
  d₂ p q := (K.X p).d q (q + 1)
  d₁_comp_d₁ _ _ := K.d_f_comp_d_f _ _ _ _
  d₂_comp_d₂ p _ := (K.X p).d_comp_d _ _ _
  comm _ _ := (K.d_comm _ _ _ _).symm

/-- **Stacks 012Y**, identified with Mathlib: double complexes are exactly the bicomplexes
`HomologicalComplex₂ C (up ℤ) (up ℤ)`, over any category with zero morphisms. -/
@[simps, stacks 012Y "identified with `HomologicalComplex₂ C (up ℤ) (up ℤ)` by a bijection"]
def DoubleComplex.equivHomologicalComplex₂ (C : Type*) [Category* C] [HasZeroMorphisms C] :
    DoubleComplex C ≃ HomologicalComplex₂ C (up ℤ) (up ℤ) where
  toFun := DoubleComplex.toHomologicalComplex₂
  invFun := toDoubleComplex
  left_inv A := by
    rcases A with ⟨X, d₁, d₂, -, -, -⟩
    simp [toDoubleComplex, DoubleComplex.toHomologicalComplex₂]
  right_inv K := by
    refine HomologicalComplex.ext (funext fun p => HomologicalComplex.ext rfl fun q q' hqq' => ?_)
      fun p p' hpp' => ?_
    · obtain rfl : q + 1 = q' := hqq'
      simp
    · obtain rfl : p + 1 = p' := hpp'
      ext; simp

end HomologicalComplex₂
