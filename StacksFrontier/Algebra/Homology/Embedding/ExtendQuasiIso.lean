module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Extending a complex along an embedding preserves quasi-isomorphisms

Let `e : c.Embedding c'` be an embedding of complex shapes with `e.IsRelIff`. Mathlib's
`HomologicalComplex.quasiIso_extendMap_iff` says that `HomologicalComplex.extendMap φ e` is a
quasi-isomorphism exactly when `φ` is. This file restates that in the *functor* spelling,
`(e.extendFunctor C).map φ`, which is the form a consumer meets whenever the extension appears as
a functor rather than as a bare map on morphisms.

## Main results

* `HomologicalComplex.quasiIso_extendFunctor_map`: `(e.extendFunctor C).map φ` is a
  quasi-isomorphism when `φ` is.

## Implementation notes

The two spellings are connected by `ComplexShape.Embedding.extendFunctor_map`, the
`@[simps]`-generated lemma for `ComplexShape.Embedding.extendFunctor`, whose `map` field is
`HomologicalComplex.extendMap φ e` on the nose. Rewriting with it and appealing to Mathlib's
iff is the whole proof. Stating it with the functor as a variable, rather than forcing the
projection to reduce at each call site, is deliberate: call sites instantiate `e` and `C`
afterwards.

`HasZeroObject C` is the instance Mathlib's `quasiIso_extendMap_iff` needs beyond
`CategoryWithHomology C` — extension inserts zero objects in the degrees outside the image of
`e.f`, and the `iff` has to know those degrees are exact.

**A pitfall worth naming, because it is about how `QuasiIso` is threaded through hypotheses in this
development rather than about extension.** `QuasiIso` is a class, and the hypothesis below is an
instance binder. A `QuasiIso` fact that arrives as a *plain* argument — `(h : QuasiIso φ)` in some
caller's signature — is **not** in the instance cache, so the instance binder here will not
resolve from it and instance search fails with no mention of `h`. The caller must put it in scope
first, with `haveI := h`. The same applies to the downstream instances
`CategoryTheory.quasiIso_of_isIso` and `CategoryTheory.quasiIso_comp`, which is how a composite
with an isomorphism is normally discharged.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

/-- **Extending along an embedding of complex shapes preserves quasi-isomorphisms**, in the
functor spelling: if `φ` is a quasi-isomorphism then so is `(e.extendFunctor C).map φ`.

This is `HomologicalComplex.quasiIso_extendMap_iff` read through
`ComplexShape.Embedding.extendFunctor_map`, which identifies the functor's action on morphisms
with `HomologicalComplex.extendMap`. -/
theorem quasiIso_extendFunctor_map {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]
    [CategoryWithHomology C] (e : c.Embedding c') [e.IsRelIff]
    {K L : HomologicalComplex C c} (φ : K ⟶ L) [QuasiIso φ] :
    QuasiIso ((e.extendFunctor C).map φ) := by
  rw [ComplexShape.Embedding.extendFunctor_map]
  exact (HomologicalComplex.quasiIso_extendMap_iff φ e).2 inferInstance

end HomologicalComplex

end
