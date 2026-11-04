module

public import Mathlib.Algebra.Homology.Bifunctor
import StacksCore.Tactic.StacksAttribute

/-! ## The double complex `X ⊗ Y` of two complexes

Stacks 0A5J: given additive categories `𝒜`, `ℬ`, `𝒞`, a functor `⊗ : 𝒜 × ℬ → 𝒞` bilinear on
morphisms, and complexes `X` of `𝒜` and `Y` of `ℬ`, the double complex `K^{p, q} = X^p ⊗ Y^q`
whose first differential is induced by `d_X` and the identity of `Y^q`, and whose second is
induced by the identity of `X^p` and `d_Y`.

Mathlib's `CategoryTheory.Functor.mapBifunctorHomologicalComplex F c₁ c₂` is this construction,
functorially in both complexes: the tag's double complex is
`((F.mapBifunctorHomologicalComplex c₁ c₂).obj X).obj Y` for a curried functor
`F : C₁ ⥤ C₂ ⥤ D`, where `F` is `Functor.curry` of Stacks' `⊗ : 𝒜 × ℬ ⥤ 𝒞` (equivalently, `⊗`
is `Functor.uncurry.obj F`). It works for arbitrary complex shapes `c₁`, `c₂` in place of `ℤ`, and
under hypotheses strictly weaker than the tag's: only `HasZeroMorphisms` on the three categories
and `PreservesZeroMorphisms` for `F` in each variable, with no additivity at all. The result lives
in `HomologicalComplex₂ D c₁ c₂`, whose first index is the outer one, so `(K.d p p').f q` is the
tag's first differential and `(K.X p).d q q'` its second. The three `@[simps!]` lemmas tagged
below are the tag's three pieces of data: the term `K^{p, q}`, the first differential, and the
second differential, which the tag gives by "similarly".
-/

@[expose] public section

add_to_stacks 0A5J "curried `F`, zero morphisms only, any shapes, functorial in both complexes"
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
add_to_stacks 0A5J "the term `K^{p, q} = X^p ⊗ Y^q`"
  CategoryTheory.Functor.mapBifunctorHomologicalComplex_obj_obj_X_X
add_to_stacks 0A5J "the first differential, induced by `d_X` and the identity of `Y^q`"
  CategoryTheory.Functor.mapBifunctorHomologicalComplex_obj_obj_d_f
add_to_stacks 0A5J "the second differential, induced by the identity of `X^p` and `d_Y`"
  CategoryTheory.Functor.mapBifunctorHomologicalComplex_obj_obj_X_d
