module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.CategoryTheory.Triangulated.Generators
public import StacksCore.Tactic.StacksAttribute

/-! # A compact generator with the expected endomorphisms gives a derived equivalence

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let `N`
be a differential graded `(A, B)`-bimodule. [Stacks, Tag 09S7] says that if

1. `N` defines a compact object of `D(B, d)`,
2. an object `N'` of `D(B, d)` with `Hom_{D(B,d)}(N, N'[n]) = 0` for every `n ∈ ℤ` is zero, and
3. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` is an isomorphism for every `k ∈ ℤ`,

then `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence.

The three hypotheses enter as follows. Hypotheses (1) and (3) are exactly those of
[Stacks, Tag 09R9], so they make `- ⊗_A^𝐋 N` fully faithful. The functor has the right adjoint
`RHom(N, -)` unconditionally, by [Stacks, Tag 09LT], and both are exact. Hypothesis (2) says
that the class of `N` is a *weak generator* of `D(B, d)` in the sense of [Stacks, Tag 09SJ](3),
and that is what makes the kernel of `RHom(N, -)` zero: if `RHom(N, N')` is a zero object then
every morphism `N[n] ⟶ N'` vanishes, because the adjunction identifies it with a morphism
`A[n] ⟶ RHom(N, N')` and `A[n] ⊗_A^𝐋 N ≅ N[n]`. Then [Stacks, Tag 09J1] — a fully faithful
exact functor between triangulated categories whose right adjoint is exact and has zero kernel
is an equivalence — gives the conclusion.

## Main definitions

* `DifferentialGraded.Bimodule.derivedTensorEquivalence`: the equivalence
  `D(A, d) ≌ D(B, d)` of **Stacks 09S7**, whose quasi-inverse is the derived Hom functor
  `RHom(N, -)` of Tag 09LI.

## Main results

* `DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor`: **Stacks 09S7**, with the
  three hypotheses in the source's own shape.
* `DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator`:
  the same, with hypothesis (2) phrased as weak generation of `D(B, d)` by the class of `N`
  ([Stacks, Tag 09SJ](3)). This is the form in which the hypothesis is usually available, the
  class of the regular module being a weak generator of its own derived category
  (`DifferentialGradedModule.isWeakTriangulatedGenerator_q_regularModule`).
* `DifferentialGraded.Bimodule.rightOrthogonal_shiftClosure_of_isZero_derivedHom`: the one
  computation behind the application of Tag 09J1 — if `RHom(N, N')` is a zero object, then `N'`
  is right orthogonal to the translates of the class of `N`.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero`:
  weak generation by a single object `E`, in the vanishing form `Hom(E, K[n]) = 0` for all
  `n ∈ ℤ` implies `K = 0` that the source's hypothesis (2) uses.
* `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_of_iso`: weak generation
  by a single object only depends on its isomorphism class, which is what lets hypothesis (2) be
  checked on a quasi-isomorphic model of the generator.

## Implementation notes

*What "equivalence of triangulated categories" amounts to here.* The source's conclusion is that
`- ⊗_A^𝐋 N` is an `R`-linear equivalence of triangulated categories. The functor is exact
unconditionally and before any of the three hypotheses: it commutes with the translation by
`DifferentialGraded.Bimodule.derivedTensorFunctor_commShift` and preserves distinguished
triangles by `DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated`, both of which are
instances and are Tags 09LR and 09LS. So the content added by Tag 09S7 is that this already
exact functor is an equivalence, which is what is proved below; and the quasi-inverse is exact
too, being the right adjoint of an exact functor
(`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`, Tag 0A8D), as the proofs below use.

*What is not proved here.* The `R`-linearity of `- ⊗_A^𝐋 N` is **not** part of what is proved,
and the clause strings on the tag say so. The derived categories are `R`-linear
(`DifferentialGradedModule.instLinearDerivedCategory`), but `(- ⊗_A^𝐋 N).Linear R` is a separate
statement about the derived tensor functor, needing the `R`-linearity of tensoring with `N` on
the homotopy categories, which this development does not have: `Tag 09LM`'s functor is obtained
from a differential graded functor through
`DifferentialGraded.Bimodule.tensorDGFunctor` and the comparison equivalences of
`DifferentialGradedModule.homotopyCategoryEquivalence`, and none of those is known to be
`R`-linear here. Nothing below depends on `R`-linearity, and nothing below asserts it.

*Hypothesis (2), and why it is stated twice.* The source's "if `N' ∈ D(B,d)` and
`Hom_{D(B,d)}(N, N'[n]) = 0` for `n ∈ ℤ`, then `N' = 0`" is, for all `n : ℤ` and with `N' = 0`
read isomorphism-invariantly as `IsZero N'`, Definition [Stacks, Tag 09SJ](3) for the class of
`N`. The two spellings are interchanged by
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero`,
proved below from `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_iff`; the tagged
statement uses the source's spelling and the reusable one uses Mathlib's.

*Two pretriangulated structures on `K(A, d)`.* As in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedTensorFullyFaithful.lean`, the imports
bring both `DifferentialGradedModule.instPretriangulatedHomotopyCategory` and
`DifferentialGradedModule.instPretriangulatedHomotopyCategory'`; everything about `D(A, d)` in
this chapter is stated against the primed one, and that is the one given priority below.

## References

* [Stacks Project, Tag 09S7](https://stacks.math.columbia.edu/tag/09S7), the result proved here.
* [Stacks Project, Tag 09R9](https://stacks.math.columbia.edu/tag/09R9) for full faithfulness,
  [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT) for the adjunction,
  [Tag 09J1](https://stacks.math.columbia.edu/tag/09J1) for the criterion of equivalence,
  [Tag 09SJ](https://stacks.math.columbia.edu/tag/09SJ) for weak generators and
  [Tag 0A8D](https://stacks.math.columbia.edu/tag/0A8D) for the exactness of a right adjoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

namespace CategoryTheory.ObjectProperty

/-- If every morphism `E' ⟶ X` vanishes and `E ≅ E'`, then every morphism `E ⟶ X` vanishes. -/
private theorem eq_zero_of_iso_of_forall_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {E E' X : C} (e : E ≅ E') (h : ∀ g : E' ⟶ X, g = 0) (f : E ⟶ X) : f = 0 := by
  rw [← e.hom_inv_id_assoc f, h (e.inv ≫ f), comp_zero]

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasShift C ℤ]

/-- **Weak generation by one object, in its vanishing form.** A single object `E` of a category
with zero morphisms and a translation by `ℤ` is a weak generator ([Stacks, Tag 09SJ](3)) if and
only if every object `K` with `Hom(E, K[n]) = 0` for all `n : ℤ` is a zero object.

This is the contrapositive of `CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_iff`,
which states weak generation as "every nonzero `K` admits an integer `n` and a nonzero map
`E ⟶ K[n]`". -/
theorem isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero (E : C) :
    (ObjectProperty.singleton E).IsWeakTriangulatedGenerator ↔
      ∀ K : C, (∀ (n : ℤ) (f : E ⟶ K⟦n⟧), f = 0) → IsZero K := by
  rw [isWeakTriangulatedGenerator_iff]
  refine ⟨fun h K hK => ?_, fun h K hK => ?_⟩
  · by_contra hc
    obtain ⟨E', hE', n, f, hf⟩ := h K hc
    obtain rfl := (ObjectProperty.singleton_iff E E').1 hE'
    exact hf (hK n f)
  · refine ⟨E, (ObjectProperty.singleton_iff E E).2 rfl, ?_⟩
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hK (h K hc)

/-- **Weak generation by one object only depends on its isomorphism class.** If `E` is a weak
generator ([Stacks, Tag 09SJ](3)) and `E ≅ E'`, then `E'` is a weak generator: a morphism
`E ⟶ K[n]` factors as the isomorphism followed by a morphism out of `E'`, so the two vanishing
conditions of
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero`
are equivalent. -/
theorem isWeakTriangulatedGenerator_singleton_of_iso {E E' : C} (e : E ≅ E')
    (h : (ObjectProperty.singleton E).IsWeakTriangulatedGenerator) :
    (ObjectProperty.singleton E').IsWeakTriangulatedGenerator := by
  rw [isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero] at h ⊢
  intro K hK
  exact h K fun n => eq_zero_of_iso_of_forall_eq_zero e (hK n)

end CategoryTheory.ObjectProperty

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule CategoryTheory.ObjectProperty

universe u

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-- **The kernel of `RHom(N, -)` is right orthogonal to the translates of `N`.** Let `N` be a
differential graded `(A, B)`-bimodule and let `X` be an object of `D(B, d)` with `RHom(N, X)` a
zero object of `D(A, d)`. Then every morphism to `X` out of an object isomorphic to a translate
of the class of `N` vanishes.

A morphism `N[n] ⟶ X` is, under the adjunction of Tag 09LT and the identification
`A[n] ⊗_A^𝐋 N ≅ N[n]` of `DifferentialGraded.Bimodule.derivedTensorShiftRegularIso`, a morphism
`A[n] ⟶ RHom(N, X)`; there is only one of those, the target being a zero object, and the
correspondence is a bijection. -/
theorem rightOrthogonal_shiftClosure_of_isZero_derivedHom (N : Bimodule A B)
    {X : derivedCategory' B}
    (hX : IsZero ((derivedHomData A B N.rightModule N.leftAction).functor.obj X)) :
    ((ObjectProperty.singleton ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
      N.rightModule)).shiftClosure ℤ).rightOrthogonal X := by
  intro Y f hY
  obtain ⟨E, n, e, hE⟩ := hY
  obtain rfl := (ObjectProperty.singleton_iff _ E).1 hE
  exact eq_zero_of_iso_of_forall_eq_zero e
    (eq_zero_of_iso_of_forall_eq_zero (derivedTensorShiftRegularIso N n).symm fun g =>
      ((derivedTensorFunctor_adj_derivedHomFunctor N).homEquiv _ X).injective
        (hX.eq_of_tgt _ _)) f

/-- **Stacks 09S7, with hypothesis (2) as weak generation.** Let `(A, d)` and `(B, d)` be
differential graded algebras over a commutative ring `R` and let `N` be a differential graded
`(A, B)`-bimodule. Assume

1. the class of `N` in `D(B, d)` is a compact object,
2. the class of `N` is a weak generator of `D(B, d)` ([Stacks, Tag 09SJ](3)), and
3. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
   `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every `k : ℤ`.

Then `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence of categories. The functor is exact
before any hypothesis, by Tags 09LR and 09LS, so this is the equivalence of triangulated
categories; its `R`-linearity is not asserted.

Hypothesis (2) is interchangeable with the source's own form by
`CategoryTheory.ObjectProperty.isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero`;
`DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor` is this statement in that form.

By Tag 09R9 hypotheses (1) and (3) make the functor fully faithful; Tag 09LT gives the right
adjoint `RHom(N, -)`, which is exact by Tag 0A8D; its kernel is zero by hypothesis (2) through
`DifferentialGraded.Bimodule.rightOrthogonal_shiftClosure_of_isZero_derivedHom`; and Tag 09J1
turns that into the equivalence. -/
theorem isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : (ObjectProperty.singleton ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj
      N.rightModule)).IsWeakTriangulatedGenerator)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorFunctor N).IsEquivalence := by
  have hff := derivedTensorFunctor_fullyFaithful N h3
  have _ : (derivedTensorFunctor N).Full := hff.full
  have _ : (derivedTensorFunctor N).Faithful := hff.faithful
  let adj := derivedTensorFunctor_adj_derivedHomFunctor N
  have : (derivedHomData A B N.rightModule N.leftAction).functor.Additive :=
    adj.right_adjoint_additive
  let _ : (derivedHomData A B N.rightModule N.leftAction).functor.CommShift ℤ :=
    adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : (derivedHomData A B N.rightModule N.leftAction).functor.IsTriangulated :=
    adj.isTriangulated_rightAdjoint
  exact isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero _ _ adj
    fun X hX => h2 X (rightOrthogonal_shiftClosure_of_isZero_derivedHom N hX)

/-- **Stacks 09S7.** Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative
ring `R` and let `N` be a differential graded `(A, B)`-bimodule. Assume

1. the class of `N` in `D(B, d)` is a compact object,
2. an object `X` of `D(B, d)` with `Hom_{D(B,d)}(N, X[n]) = 0` for every `n : ℤ` is zero, and
3. the canonical map `H^k(A) → Hom_{D(B,d)}(N, N[k])` of
   `DifferentialGraded.Bimodule.cohomologyEndomorphismComparison` is bijective for every `k : ℤ`.

Then `- ⊗_A^𝐋 N : D(A, d) ⥤ D(B, d)` is an equivalence of categories.

The functor is exact with no hypothesis at all — it commutes with the translation by
`DifferentialGraded.Bimodule.derivedTensorFunctor_commShift` and preserves distinguished
triangles by `DifferentialGraded.Bimodule.derivedTensorFunctor_isTriangulated`, Tags 09LR and
09LS — so this is the source's equivalence of triangulated categories. What the clause string
excludes is the source's `R`-linearity of the functor, which is not proved here.

This is
`DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator`,
hypothesis (2) being weak generation of `D(B, d)` by the class of `N` ([Stacks, Tag 09SJ](3)). -/
@[stacks 09S7 "the equivalence of triangulated categories, not the R-linearity of the functor"]
theorem isEquivalence_derivedTensorFunctor (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    (derivedTensorFunctor N).IsEquivalence :=
  isEquivalence_derivedTensorFunctor_of_isWeakTriangulatedGenerator N
    ((isWeakTriangulatedGenerator_singleton_iff_forall_hom_eq_zero _).2 h2) h3

/-- **Stacks 09S7, as an equivalence with its quasi-inverse named.** Under the hypotheses of
`DifferentialGraded.Bimodule.isEquivalence_derivedTensorFunctor`, the derived tensor product
`- ⊗_A^𝐋 N` is one half of an equivalence `D(A, d) ≌ D(B, d)` whose other half is the derived
Hom functor `RHom(N, -) : D(B, d) ⥤ D(A, d)` of Tag 09LI, with the unit and counit of the
adjunction of Tag 09LT as the two structural isomorphisms.

The source asserts only that `- ⊗_A^𝐋 N` *is* an equivalence and leaves the quasi-inverse
unnamed; this records which functor it is. The unit is invertible by
`DifferentialGraded.Bimodule.isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor` (the heart of
Tag 09R9), and the counit is invertible at every object because the functor is fully faithful and
essentially surjective, so every object of `D(B, d)` lies in its essential image. Again only the
equivalence is claimed, not its `R`-linearity. -/
@[stacks 09S7 "the equivalence, with RHom(N, -) as quasi-inverse; not the R-linearity"]
def derivedTensorEquivalence (N : Bimodule A B)
    [IsCompactObject.{u} ((toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule)]
    (h2 : ∀ X : derivedCategory' B,
      (∀ (n : ℤ) (f : (toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q).obj N.rightModule ⟶
        X⟦n⟧), f = 0) → IsZero X)
    (h3 : ∀ k : ℤ, Function.Bijective (N.cohomologyEndomorphismComparison k)) :
    derivedCategory' A ≌ derivedCategory' B :=
  haveI : (derivedTensorFunctor N).IsEquivalence :=
    isEquivalence_derivedTensorFunctor N h2 h3
  haveI := isIso_unit_derivedTensorFunctor_adj_derivedHomFunctor N h3
  haveI : ∀ Y : derivedCategory' B,
      IsIso ((derivedTensorFunctor_adj_derivedHomFunctor N).counit.app Y) := fun Y =>
    (Adjunction.isIso_counit_app_iff_mem_essImage _).2
      ⟨(derivedTensorFunctor N).objPreimage Y,
        ⟨(derivedTensorFunctor N).objObjPreimageIso Y⟩⟩
  (derivedTensorFunctor_adj_derivedHomFunctor N).toEquivalence

end DifferentialGraded.Bimodule

end
