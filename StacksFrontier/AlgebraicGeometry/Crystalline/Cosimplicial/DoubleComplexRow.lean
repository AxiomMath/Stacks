module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplex

/-!
# The rows of the double complex of a cochain complex of cosimplicial abelian groups

`Crystalline.cosimplicialDoubleComplexFunctor` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/DoubleComplex.lean` turns a cochain
complex `K` of cosimplicial abelian groups into a double complex over `ℤ` in both directions, by
taking the Moore complex of [Stacks, Tag 019I] in each exterior degree and then extending the
inner and the outer index along `ComplexShape.embeddingUpNat`.  Its *columns* are described
there, by `Crystalline.cosimplicialDoubleComplexColumnIso`.  Its *rows* — the complexes
`(cosimplicialDoubleComplexFunctor.obj K).flip.X b`, which the second degeneration of
`StacksFrontier/Algebra/Homology/TotalDegeneration.lean` and hence the hypotheses `hrows` and
`hrow0` of `...SmallSite.computes07LG_of_doubleComplex` are stated about — were not described at
all, because the flip has to be moved past *two* nested `ℕ`-to-`ℤ` extensions.

This module describes them.  The row `b` is, before any extension, simply the cochain complex

`a ↦ K^a(⦋b⦌)`

obtained by evaluating every cosimplicial group of `K` at the simplex `⦋b⦌`: the Moore complex
plays no role in the `b` direction beyond selecting that evaluation, since the `b`-th term of the
Moore complex of a cosimplicial object is its value at `⦋b⦌`.  So the row is
`Crystalline.cosimplicialRowComplex`, and
`Crystalline.cosimplicialDoubleComplexRowIso` identifies the row of the double complex with its
extension.

## Implementation notes

The flip is moved past the two extensions in one step rather than two.  Flipping a double complex
and reading off the row `b` is, definitionally, applying the degree-`b` evaluation functor
degreewise, so the outer extension is moved past it by
`HomologicalComplex.mapHomologicalComplexExtendIso` of
`StacksFrontier/Algebra/Homology/Embedding/ExtendMap.lean` — the statement that extending along an
embedding commutes with applying a functor degreewise — and the *inner* extension is then
absorbed by Mathlib's `ComplexShape.Embedding.extendFunctorCompEvalIso`, which says that
evaluating an extended complex in a degree of the image is evaluating the original complex, and
which applies degreewise through `NatIso.mapHomologicalComplex`.  No case analysis on the sign of
the index is needed for the rows in the image of the embedding, and the rows outside it vanish.

## Main definitions

* `Crystalline.cosimplicialRowComplex` — **the row `b` of `K`**, the cochain complex
  `a ↦ K^a(⦋b⦌)` indexed by `ℕ`.
* `Crystalline.cosimplicialDoubleComplexRowIso` — **the row `b` of the double complex is the
  `ℕ`-to-`ℤ` extension of the row `b` of `K`.**
* `Crystalline.cosimplicialDoubleComplexRowHomologyIso` — the induced identification of the
  cohomology in each degree.

## Main results

* `Crystalline.isZero_cosimplicialDoubleComplex_flip_X_X_of_neg` and
  `Crystalline.acyclic_cosimplicialDoubleComplex_flip_X_of_neg` — **the rows in negative degree
  vanish**, so the hypothesis `hrows` of `...SmallSite.computes07LG_of_doubleComplex` is only
  ever about the rows indexed by a positive natural number.
* `Crystalline.acyclic_cosimplicialDoubleComplex_flip_X` — a row whose `ℕ`-indexed complex is
  acyclic is acyclic, including in the degrees the extension adds.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial

universe u

namespace Crystalline

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)

/-- **The row `b` of a cochain complex of cosimplicial abelian groups**: the cochain complex
`a ↦ K^a(⦋b⦌)` obtained by evaluating every one of the cosimplicial groups at the simplex `⦋b⦌`,
with the differential of `K` read in that simplex.

It is indexed by `ℕ`; `Crystalline.cosimplicialDoubleComplexRowIso` identifies its `ℕ`-to-`ℤ`
extension with the row of `Crystalline.cosimplicialDoubleComplexFunctor.obj K`. -/
def cosimplicialRowComplex (b : ℕ) : CochainComplex AddCommGrpCat.{u} ℕ :=
  ((alternatingCofaceMapComplex AddCommGrpCat.{u} ⋙
    HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) b).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K

/-- The exterior degree `a` of the row `b` is the value of the cosimplicial group `K^a` at the
simplex `⦋b⦌`. -/
theorem cosimplicialRowComplex_X (b a : ℕ) :
    (cosimplicialRowComplex K b).X a = (K.X a).obj ⦋b⦌ := rfl

/-- The differential of the row `b` is the differential of `K` read in the simplex `⦋b⦌`. -/
theorem cosimplicialRowComplex_d (b a a' : ℕ) :
    (cosimplicialRowComplex K b).d a a' = (K.d a a').app ⦋b⦌ := rfl

/-- **The row `b` of the double complex is the `ℕ`-to-`ℤ` extension of the row `b` of `K`.**

Flipping the double complex and reading the row `b` is applying the degree-`b` evaluation
functor degreewise, so `HomologicalComplex.mapHomologicalComplexExtendIso` moves the outer
extension past it; the inner extension is then absorbed by
`ComplexShape.Embedding.extendFunctorCompEvalIso` applied degreewise. -/
def cosimplicialDoubleComplexRowIso (b : ℕ) :
    (cosimplicialDoubleComplexFunctor.obj K).flip.X (b : ℤ) ≅
      (cosimplicialRowComplex K b).extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.mapHomologicalComplexExtendIso
      (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) (b : ℤ))
      (((ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K))
      ComplexShape.embeddingUpNat).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapIso
      ((NatIso.mapHomologicalComplex
        (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso AddCommGrpCat.{u}
          (show ComplexShape.embeddingUpNat.f b = (b : ℤ) from rfl))
        (ComplexShape.up ℕ)).app
          (((alternatingCofaceMapComplex AddCommGrpCat.{u}).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj K))

/-- **The cohomology of the row `b` of the double complex is the cohomology of the row `b` of
`K`**, in each degree.  The extension from `ℕ` to `ℤ` adds no cohomology in a degree of the
image of the embedding. -/
def cosimplicialDoubleComplexRowHomologyIso (b j : ℕ) :
    ((cosimplicialDoubleComplexFunctor.obj K).flip.X (b : ℤ)).homology (j : ℤ) ≅
      (cosimplicialRowComplex K b).homology j :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ)
      (j : ℤ)).mapIso (cosimplicialDoubleComplexRowIso K b) ≪≫
    (cosimplicialRowComplex K b).extendHomologyIso ComplexShape.embeddingUpNat rfl

/-- **The rows of the double complex vanish in negative degree**, term by term: the inner
extension is zero outside the image of `ComplexShape.embeddingUpNat`. -/
theorem isZero_cosimplicialDoubleComplex_flip_X_X_of_neg {b : ℤ} (hb : b < 0) (a : ℤ) :
    IsZero (((cosimplicialDoubleComplexFunctor.obj K).flip.X b).X a) :=
  isZero_cosimplicialDoubleComplex_X_X_of_neg K a hb

/-- **A row of the double complex in negative degree is acyclic**, every one of its terms being
zero.  Together with `Crystalline.acyclic_cosimplicialDoubleComplex_flip_X` this means that the
acyclicity of the rows off `0` is a statement about the rows indexed by a positive natural
number only. -/
theorem acyclic_cosimplicialDoubleComplex_flip_X_of_neg {b : ℤ} (hb : b < 0) :
    ((cosimplicialDoubleComplexFunctor.obj K).flip.X b).Acyclic := by
  intro a
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ShortComplex.isZero_homology_of_isZero_X₂ (_ : ShortComplex AddCommGrpCat.{u})
    (isZero_cosimplicialDoubleComplex_flip_X_X_of_neg K hb a)

/-- **A row of the double complex is acyclic as soon as the corresponding `ℕ`-indexed row of `K`
is.**

As for the columns, the extension from `ℕ` to `ℤ` adds no cohomology: in a degree in the image of
the embedding the cohomology is that of `Crystalline.cosimplicialRowComplex`, and in a negative
degree the term itself vanishes. -/
theorem acyclic_cosimplicialDoubleComplex_flip_X (b : ℕ)
    (h : ∀ j : ℕ, IsZero ((cosimplicialRowComplex K b).homology j)) :
    ((cosimplicialDoubleComplexFunctor.obj K).flip.X (b : ℤ)).Acyclic := by
  intro m
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) m).mapIso
      (cosimplicialDoubleComplexRowIso K b))
  by_cases hm : 0 ≤ m
  · lift m to ℕ using hm
    exact IsZero.of_iso (h m)
      ((cosimplicialRowComplex K b).extendHomologyIso ComplexShape.embeddingUpNat
        (j := m) (j' := (m : ℤ)) rfl)
  · exact ShortComplex.isZero_homology_of_isZero_X₂ (_ : ShortComplex AddCommGrpCat.{u})
      (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat m
        (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega))

end Crystalline

end
