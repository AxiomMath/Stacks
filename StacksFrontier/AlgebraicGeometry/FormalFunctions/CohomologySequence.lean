module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# The long exact cohomology sequence of a short exact sequence of abelian sheaves

Let `(C, J)` be a site and let `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` be a short exact sequence of abelian
sheaves on it. For every object `U` of `C` the cohomology groups `H^n(U, ℱ)` fit into a long
exact sequence
`… → H^n(U, ℱ₁) → H^n(U, ℱ₂) → H^n(U, ℱ₃) → H^{n+1}(U, ℱ₁) → H^{n+1}(U, ℱ₂) → …`
whose connecting homomorphism is given by composition with the `Ext`-class of the sequence.

Cohomology here is Mathlib's `CategoryTheory.Sheaf.H'`: the group `H^n(U, ℱ)` is the `n`-th
`Ext`-group from the free abelian sheaf on `yoneda.obj U` to `ℱ`. For the site of opens of a
scheme `X` and `U = ⊤` this is `H^n(X, ℱ)`, the group appearing throughout the theorem on formal
functions; the sequence below is the "long exact cohomology sequence" invoked in the
Artin--Rees step of that theorem, applied to `0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0`.

## Main definitions

* `Stacks.Cohomology.LongExactSequence.freeYoneda`: the free abelian sheaf on `yoneda.obj U`,
  the object corepresenting cohomology over `U`.
* `Stacks.Cohomology.LongExactSequence.map`: the map `H^n(U, ℱ) → H^n(U, 𝒢)` induced by a
  morphism of abelian sheaves.
* `Stacks.Cohomology.LongExactSequence.δ`: the connecting homomorphism
  `H^{n₀}(U, ℱ₃) → H^{n₁}(U, ℱ₁)` of a short exact sequence, for `n₀ + 1 = n₁`.

## Main results

* `Stacks.Cohomology.LongExactSequence.exact_map_map`: exactness at `H^n(U, ℱ₂)`.
* `Stacks.Cohomology.LongExactSequence.exact_map_δ`: exactness at `H^{n₀}(U, ℱ₃)`.
* `Stacks.Cohomology.LongExactSequence.exact_δ_map`: exactness at `H^{n₁}(U, ℱ₁)`.
* `Stacks.Cohomology.LongExactSequence.ker_map_eq_range_map`: the kernel of
  `H^n(U, ℱ₂) → H^n(U, ℱ₃)` is the image of `H^n(U, ℱ₁) → H^n(U, ℱ₂)`. This is the form in
  which exactness is used in the Artin--Rees step of the theorem on formal functions, where it
  identifies `Ker(H^p(X, ℱ) → H^p(X, ℱ/I^n ℱ))` with `Im(H^p(X, I^n ℱ) → H^p(X, ℱ))`.

## Implementation notes

Cohomology over `U` is by definition an `Ext`-group out of a fixed object, so the sequence is
the covariant long exact `Ext`-sequence `CategoryTheory.Abelian.Ext.covariantSequence` of the
short exact sequence, specialised to that object. Nothing beyond that specialisation is needed:
in particular the connecting homomorphism is not constructed here, being composition with
`CategoryTheory.ShortComplex.ShortExact.extClass`.

Mathlib states the three exactness points as exactness of a `ShortComplex` of `AddCommGrpCat`;
they are transported to `Function.Exact` on the underlying maps, which is the form in which a
diagram chase uses them.

The universe `w'` of the `Ext`-groups is a free parameter, as it is for `Sheaf.H'`; the site's
morphism universe `v` is forced to be the one in which the sheaves take values, because
`Sheaf.H'` is defined only in that case.

## References

* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

universe w' v u

namespace Stacks.Cohomology.LongExactSequence

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

/-- The free abelian sheaf on the presheaf of sets `yoneda.obj U`. Cohomology over `U` is the
`Ext`-functor out of this object, so it is the object corepresenting `H^n(U, -)`.

This is the shape in which Mathlib's `CategoryTheory.Sheaf.H'` is defined; for the site of opens
of a scheme and `U = ⊤` the resulting groups are the `H^p(X, ℱ)` of the theorem on formal
functions, [Stacks, Tag 02OB]. -/
abbrev freeYoneda (U : C) : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj U ⋙ AddCommGrpCat.free)

variable {J}

/-- Cohomology over `U` is the `Ext`-group out of `freeYoneda J U`. -/
theorem h'_eq (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) (U : C) :
    Sheaf.H'.{w'} F n U = Ext.{w'} (freeYoneda J U) F n :=
  rfl

/-- The map `H^n(U, ℱ) → H^n(U, 𝒢)` on cohomology over `U` induced by a morphism of abelian
sheaves `ℱ ⟶ 𝒢`, namely composition with its degree-zero `Ext`-class.

This is the map appearing in the long exact cohomology sequence, [Stacks, Tag 0159]. -/
def map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G) (n : ℕ) (U : C) :
    Sheaf.H'.{w'} F n U →+ Sheaf.H'.{w'} G n U :=
  (Ext.mk₀ f).postcomp (freeYoneda J U) (add_zero n)

/-- `map` is the value at `U` of the map of cohomology presheaves induced by a morphism of
abelian sheaves, so it carries the restriction maps of the site along with it. -/
theorem map_eq_cohomologyPresheafFunctor_map {F G : Sheaf J AddCommGrpCat.{v}} (f : F ⟶ G)
    (n : ℕ) (U : C) :
    AddCommGrpCat.ofHom (map.{w'} f n U) =
      ((Sheaf.cohomologyPresheafFunctor.{w'} J n).map f).app (op U) :=
  rfl

variable (S : ShortComplex (Sheaf J AddCommGrpCat.{v})) (hS : S.ShortExact)

/-- The connecting homomorphism `H^{n₀}(U, ℱ₃) → H^{n₁}(U, ℱ₁)` of a short exact sequence of
abelian sheaves `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`, for `n₀ + 1 = n₁`: composition with the `Ext`-class of
the sequence.

This is the map denoted `δ` in the long exact cohomology sequence, [Stacks, Tag 0159]. For the
sequence `0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0` on a scheme it is the connecting map
`H^p(X, ℱ/I^n ℱ) → H^{p+1}(X, I^n ℱ)` of the Artin--Rees step of the theorem on formal
functions, [Stacks, Tag 02OB]. -/
def δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (U : C) :
    Sheaf.H'.{w'} S.X₃ n₀ U →+ Sheaf.H'.{w'} S.X₁ n₁ U :=
  hS.extClass.postcomp (freeYoneda J U) h

include hS

/-- **Exactness at `H^n(U, ℱ₂)`.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` the sequence `H^n(U, ℱ₁) → H^n(U, ℱ₂) → H^n(U, ℱ₃)` is exact.
[Stacks, Tag 0159]. -/
theorem exact_map_map (n : ℕ) (U : C) :
    Function.Exact (map.{w'} S.f n U) (map.{w'} S.g n U) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₂' (freeYoneda J U) hS n)

/-- **Exactness at `H^{n₀}(U, ℱ₃)`.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` and `n₀ + 1 = n₁` the sequence
`H^{n₀}(U, ℱ₂) → H^{n₀}(U, ℱ₃) → H^{n₁}(U, ℱ₁)` is exact. [Stacks, Tag 0159]. -/
theorem exact_map_δ (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (U : C) :
    Function.Exact (map.{w'} S.g n₀ U) (δ.{w'} S hS n₀ n₁ h U) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₃' (freeYoneda J U) hS n₀ n₁ h)

/-- **Exactness at `H^{n₁}(U, ℱ₁)`.** For a short exact sequence of abelian sheaves
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` and `n₀ + 1 = n₁` the sequence
`H^{n₀}(U, ℱ₃) → H^{n₁}(U, ℱ₁) → H^{n₁}(U, ℱ₂)` is exact. [Stacks, Tag 0159]. -/
theorem exact_δ_map (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (U : C) :
    Function.Exact (δ.{w'} S hS n₀ n₁ h U) (map.{w'} S.f n₁ U) := by
  exact (ShortComplex.ab_exact_iff_function_exact _).1
    (Ext.covariant_sequence_exact₁' (freeYoneda J U) hS n₀ n₁ h)

/-- **The kernel-image form of exactness at `H^n(U, ℱ₂)`.** For a short exact sequence of
abelian sheaves `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`,
`Ker(H^n(U, ℱ₂) → H^n(U, ℱ₃)) = Im(H^n(U, ℱ₁) → H^n(U, ℱ₂))`.

Applied to `0 → I^n ℱ → ℱ → ℱ/I^n ℱ → 0` on a scheme this is the identification
`Ker(H^p(X, ℱ) → H^p(X, ℱ/I^n ℱ)) = Im(H^p(X, I^n ℱ) → H^p(X, ℱ))` with which the Artin--Rees
step of the theorem on formal functions begins, [Stacks, Tag 02OB] part (1). -/
theorem ker_map_eq_range_map (n : ℕ) (U : C) :
    (map.{w'} S.g n U).ker = (map.{w'} S.f n U).range := by
  ext x
  simpa [AddMonoidHom.mem_ker, AddMonoidHom.mem_range] using exact_map_map S hS n U x

end Stacks.Cohomology.LongExactSequence

end
