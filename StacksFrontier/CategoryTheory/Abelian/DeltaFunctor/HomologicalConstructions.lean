module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalUniversal
import StacksCore.Tactic.EgaSgaAttribute

/-! # Constructions of homological δ-functors

`Stacks.CategoryHomology.HomologicalDeltaFunctor` is the homological counterpart of Stacks
010Q, and `StacksFrontier/CategoryTheory/Abelian/DeltaFunctor/HomologicalUniversal.lean` equips it
with morphisms, coeffaceability and universality. This file adds the two pieces of API that a
*comparison* of two such δ-functors needs:

* the components of an isomorphism of δ-functors, as isomorphisms of functors;
* the δ-functor attached to an additive functor into chain complexes which carries short exact
  sequences to short exact sequences of complexes, namely its homology functors together with
  the connecting morphisms of the associated long exact sequence;
* the recognition of coeffaceability from an epimorphic cover by objects on which the positive
  degree functors vanish, which does not require the covering object to be projective.

## Main definitions

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.isoApp`: the degree-`n` component of an
  isomorphism of homological δ-functors, as an isomorphism `Hₙ ≅ Gₙ` of functors.
* `Stacks.CategoryHomology.HomologicalDeltaFunctor.ofChainComplexFunctor`: the homological
  δ-functor `X ↦ Hₙ(K(X))` attached to an additive `K : A ⥤ ChainComplex B ℕ` preserving short
  exactness.

## Main results

* `Stacks.CategoryHomology.HomologicalDeltaFunctor.Coeffaceable.of_exists_epi_isZero`: a
  homological δ-functor is coeffaceable as soon as every object admits an epimorphism onto it
  from an object killed by the functors of positive degree.

## Implementation notes

The source hypothesis is `[Abelian A]` alone, never `[Abelian A]` beside `[Preadditive A]`: with
both in scope the two spellings of `Preadditive Aᵒᵖ` are not interchangeable and the universality
API of `HomologicalUniversal.lean` becomes inapplicable for a hard type reason rather than a
transparency one.

`ofChainComplexFunctor` takes the preservation of short exactness as a hypothesis rather than
deriving it from exactness of `K`: the functors it is applied to in Stacks 08PG are proved to
preserve short exact sequences degreewise and directly, and an exactness hypothesis on a functor
into a category of complexes would have to be unpacked back into that statement anyway.

No `@[stacks]` attribute is placed here. Stacks' δ-functors are cohomological, and the
constructions below are the homological duals of bookkeeping that the source does not state
separately.

## References

* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 010T](https://stacks.math.columbia.edu/tag/010T)
* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

universe v v' u u'

namespace Stacks.CategoryHomology.HomologicalDeltaFunctor

section Preadditive

variable {A : Type u} [Category.{v} A] [Preadditive A] {B : Type u'} [Category.{v'} B]
  [Preadditive B] {H G : HomologicalDeltaFunctor A B}

/-- The degree-`n` component of an isomorphism of homological δ-functors, as an isomorphism of
functors `Hₙ ≅ Gₙ`. This is what makes a comparison of δ-functors usable: the inverse is the
degree-`n` component of the inverse, so the naturality squares of both directions are available
at every object. -/
@[simps]
def isoApp (α : H ≅ G) (n : ℕ) : H.functor n ≅ G.functor n where
  hom := α.hom.app n
  inv := α.inv.app n
  hom_inv_id := by rw [← comp_app, α.hom_inv_id, id_app]
  inv_hom_id := by rw [← comp_app, α.inv_hom_id, id_app]

end Preadditive

section Abelian

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u'} [Category.{v'} B] [Abelian B]

/-- **The homology δ-functor of a functor into chain complexes.** If `K : A ⥤ ChainComplex B ℕ`
is additive and carries short exact sequences of `A` to short exact sequences of complexes, then
the homology functors `X ↦ Hₙ(K(X))` together with the connecting morphisms of the long exact
homology sequence form a homological δ-functor. Every clause is the corresponding statement of
`CategoryTheory.ShortComplex.ShortExact` for the image sequence; the degree-zero clause
`epi_map_g` is the only one that is not, and it follows from surjectivity in degree zero of the
complexes by `HomologicalComplex.epi_homologyMap_of_epi_of_not_rel`. -/
@[ega "III 7.4.1" "more general"]
noncomputable def ofChainComplexFunctor (K : A ⥤ ChainComplex B ℕ) [K.Additive]
    (hK : ∀ {S : ShortComplex A}, S.ShortExact → (S.map K).ShortExact) :
    HomologicalDeltaFunctor A B where
  functor n := K ⋙ HomologicalComplex.homologyFunctor _ _ n
  additive n := inferInstance
  δ hS n := (hK hS).δ (n + 1) n rfl
  map_g_δ hS n := (hK hS).comp_δ (n + 1) n rfl
  δ_map_f hS n := (hK hS).δ_comp (n + 1) n rfl
  epi_map_g {S} hS := by
    have : Epi ((K.map S.g).f 0) :=
      ((hK hS).map_of_exact (HomologicalComplex.eval _ _ 0)).epi_g
    exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (K.map S.g) 0 (by intro j; simp)
  exact_map hS n := (hK hS).homology_exact₂ n
  exact_δ₁ hS n := (hK hS).homology_exact₃ (n + 1) n rfl
  exact_δ₂ hS n := (hK hS).homology_exact₁ (n + 1) n rfl
  δ_naturality hS hT φ n :=
    (HomologicalComplex.HomologySequence.δ_naturality (K.mapShortComplex.map φ) (hK hS) (hK hT)
      (n + 1) n rfl).symm

/-- The degree-`n` functor of
`Stacks.CategoryHomology.HomologicalDeltaFunctor.ofChainComplexFunctor` is homology of `K` in
degree `n`. Deliberately not a `simp` lemma: it rewrites a whole functor, which leaves later
goals no longer type-correct at `implicit` transparency. -/
lemma ofChainComplexFunctor_functor (K : A ⥤ ChainComplex B ℕ) [K.Additive]
    (hK : ∀ {S : ShortComplex A}, S.ShortExact → (S.map K).ShortExact) (n : ℕ) :
    (ofChainComplexFunctor K hK).functor n = K ⋙ HomologicalComplex.homologyFunctor _ _ n :=
  rfl

/-- The connecting morphism of
`Stacks.CategoryHomology.HomologicalDeltaFunctor.ofChainComplexFunctor` is the connecting
morphism of the long exact homology sequence. Not a `simp` lemma, for the same reason. -/
lemma ofChainComplexFunctor_δ (K : A ⥤ ChainComplex B ℕ) [K.Additive]
    (hK : ∀ {S : ShortComplex A}, S.ShortExact → (S.map K).ShortExact)
    {S : ShortComplex A} (hS : S.ShortExact) (n : ℕ) :
    (ofChainComplexFunctor K hK).δ hS n = (hK hS).δ (n + 1) n rfl :=
  rfl

/-- **Coeffaceability from an acyclic cover.** A homological δ-functor is coeffaceable as soon as
every object admits an epimorphism onto it from an object which the functors of positive degree
send to zero. The covering object is not required to be projective, which is what lets Stacks
08PG use the cover by free abelian presheaves on representables directly, rather than passing
through projectivity. -/
theorem Coeffaceable.of_exists_epi_isZero (H : HomologicalDeltaFunctor A B)
    (h : ∀ (X : A) (n : ℕ), ∃ (P : A) (π : P ⟶ X), Epi π ∧ IsZero ((H.functor (n + 1)).obj P)) :
    H.Coeffaceable where
  nonempty X n := by
    obtain ⟨P, π, hπ, hP⟩ := h X n
    exact ⟨{ P := P, π := π, epi := hπ, map_π := hP.eq_of_src _ _ }⟩

end Abelian

end Stacks.CategoryHomology.HomologicalDeltaFunctor
