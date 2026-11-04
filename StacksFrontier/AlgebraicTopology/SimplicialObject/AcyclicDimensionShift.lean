module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Dimension shifting along a short exact sequence with acyclic middle term

Let `A` be an abelian category. Then `SimplicialObject A = SimplexCategoryᵒᵖ ⥤ A` is abelian as
well, with kernels and cokernels computed degreewise, and the Moore complex functor
`AlgebraicTopology.alternatingFaceMapComplex A : SimplicialObject A ⥤ ChainComplex A ℕ` is
degreewise the identity on objects: the term of `s(X)` in degree `n` is `Xₙ` and the differential
is the alternating sum of the face maps. Consequently `s` is exact. Indeed, short exactness in
`ChainComplex A ℕ` is tested degree by degree, and in degree `n` the image under `s` of a short
complex `S` of simplicial objects is the evaluation of `S` at `op ⦋n⦌`, which is short exact
because evaluation functors on a functor category preserve finite limits and finite colimits.

Let now `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` be a short exact sequence of simplicial objects of `A` whose
middle term has acyclic Moore complex, i.e. `Hₙ(s(X₂)) = 0` for every `n`. Applying `s` gives a
short exact sequence of chain complexes, so there is a long exact homology sequence

`⋯ ⟶ Hₙ₊₁(s(X₂)) ⟶ Hₙ₊₁(s(X₃)) ⟶ Hₙ(s(X₁)) ⟶ Hₙ(s(X₂)) ⟶ ⋯`

in which the outer two terms vanish. The connecting morphism `δ : Hₙ₊₁(s(X₃)) ⟶ Hₙ(s(X₁))` is
therefore both a monomorphism and an epimorphism, hence an isomorphism: homology is shifted by
one degree when passing from `X₃` to `X₁`.

## Main results

* `AlgebraicTopology.shortExact_map_alternatingFaceMapComplex`: the Moore complex functor of an
  abelian category carries a short exact sequence of simplicial objects to a short exact
  sequence of chain complexes.
* `AlgebraicTopology.homologyIsoOfShortExactOfAcyclic`: the dimension shifting isomorphism
  `Hₙ₊₁(s(X₃)) ≅ Hₙ(s(X₁))` attached to a short exact sequence of simplicial objects whose
  middle term has acyclic Moore complex.
* `AlgebraicTopology.homologyIsoOfDegreewiseShortExactOfAcyclic`: the same isomorphism, with the
  short exact sequence presented as two composable morphisms that are degreewise short exact.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory Limits Opposite

open scoped Simplicial

namespace AlgebraicTopology

/-- The Moore complex functor of an abelian category carries a degreewise short exact sequence of
simplicial objects to a short exact sequence of chain complexes. Short exactness in
`ChainComplex A ℕ` is tested degreewise, and in degree `n` the image of `S` under the Moore
complex functor is the evaluation of `S` at `op ⦋n⦌`. -/
public theorem shortExact_map_alternatingFaceMapComplex_of_degreewise {A : Type u}
    [Category.{v} A] [Abelian A] (S : ShortComplex (SimplicialObject A))
    (h : ∀ Δ : SimplexCategoryᵒᵖ, (S.map ((evaluation SimplexCategoryᵒᵖ A).obj Δ)).ShortExact) :
    (S.map (alternatingFaceMapComplex A)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => h (op ⦋n⦌)

/-- The Moore complex functor of an abelian category is exact: it carries a short exact sequence
of simplicial objects to a short exact sequence of chain complexes. Exactness in a functor
category is detected by the evaluation functors, which are exact. -/
public theorem shortExact_map_alternatingFaceMapComplex {A : Type u} [Category.{v} A]
    [Abelian A] {S : ShortComplex (SimplicialObject A)} (hS : S.ShortExact) :
    (S.map (alternatingFaceMapComplex A)).ShortExact :=
  shortExact_map_alternatingFaceMapComplex_of_degreewise S
    fun Δ => hS.map_of_exact ((evaluation SimplexCategoryᵒᵖ A).obj Δ)

/-- Dimension shifting along a short exact sequence of simplicial objects whose middle term
has an acyclic Moore complex. -/
public noncomputable def homologyIsoOfShortExactOfAcyclic
    {A : Type u} [CategoryTheory.Category.{v} A] [CategoryTheory.Abelian A]
    (S : CategoryTheory.ShortComplex (CategoryTheory.SimplicialObject A))
    (hS : S.ShortExact)
    (hE : ∀ n : ℕ, CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.alternatingFaceMapComplex A).obj S.X₂).homology n))
    (n : ℕ) :
    ((AlgebraicTopology.alternatingFaceMapComplex A).obj S.X₃).homology (n + 1) ≅
      ((AlgebraicTopology.alternatingFaceMapComplex A).obj S.X₁).homology n :=
  (shortExact_map_alternatingFaceMapComplex hS).δIso (n + 1) n rfl (hE (n + 1)) (hE n)

/-- Dimension shifting along two composable morphisms of simplicial objects that are degreewise
short exact and whose middle term has an acyclic Moore complex. This is
`AlgebraicTopology.homologyIsoOfShortExactOfAcyclic` with the short exact sequence presented as
objects and morphisms rather than as a `CategoryTheory.ShortComplex.ShortExact`. -/
public noncomputable def homologyIsoOfDegreewiseShortExactOfAcyclic {A : Type u}
    [Category.{v} A] [Abelian A] {X₁ X₂ X₃ : SimplicialObject A} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hfg : f ≫ g = 0)
    (h : ∀ Δ : SimplexCategoryᵒᵖ,
      ((ShortComplex.mk f g hfg).map ((evaluation SimplexCategoryᵒᵖ A).obj Δ)).ShortExact)
    (hE : ∀ n : ℕ, IsZero (((alternatingFaceMapComplex A).obj X₂).homology n))
    (n : ℕ) :
    ((alternatingFaceMapComplex A).obj X₃).homology (n + 1) ≅
      ((alternatingFaceMapComplex A).obj X₁).homology n :=
  (shortExact_map_alternatingFaceMapComplex_of_degreewise _ h).δIso (n + 1) n rfl
    (hE (n + 1)) (hE n)

end AlgebraicTopology

end
