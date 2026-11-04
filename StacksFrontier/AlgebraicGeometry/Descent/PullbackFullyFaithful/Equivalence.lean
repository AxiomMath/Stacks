module

public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.Factorization
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackFullyFaithful.PullbackFunctorIso

/-!
# Pullback of descent data along a morphism admitting a reverse morphism

Let `f : X' ⟶ X` be a morphism of schemes over `S`. If there is also a morphism `X ⟶ X'`
over `S`, then pullback gives an equivalence between the categories of descent data relative
to `X / S` and to `X' / S`.

## Main results

* `AlgebraicGeometry.DescentData.selfPullbackFunctorIso`: pullback along a
  selfmap of `X` over `S` is isomorphic to the identity functor on descent data.
* `AlgebraicGeometry.pullbackFunctor_isEquivalence_of_exists_reverse`: pullback of descent
  data is an equivalence when a morphism in the reverse direction exists over the base.

## Implementation notes

Being a morphism over `S` is expressed by commutation with the two structure maps. The
conclusion uses `CategoryTheory.Functor.IsEquivalence`, so the specified pullback functor
itself, rather than an unrelated choice of equivalence, is shown to be an equivalence.

## References

* [Stacks Project, Tag 0242](https://stacks.math.columbia.edu/tag/0242)
* [Stacks Project, Tag 0243](https://stacks.math.columbia.edu/tag/0243)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentData

/-- Pullback of descent data along a selfmap `f : X ⟶ X` over `S` is isomorphic to the identity
functor on the category of descent data relative to `X ⟶ S`. -/
@[stacks 0242]
def selfPullbackFunctorIso {S X : Scheme.{u}} (a : X ⟶ S) (f : X ⟶ X) (hf : f ≫ a = a) :
    (pullbackFunctor a a (𝟙 S) f (by simpa using hf)).functor ≅ 𝟭 _ :=
  (pullbackFunctorIsoOfSpec (pullbackFunctor a a (𝟙 S) f (by simpa using hf))
    (identityPullbackFunctor a)).iso

end DescentData

/-- Pulling back along `f` and then along a reverse morphism `g` is isomorphic to the identity. -/
private def pullbackFunctorCompIsoId {S X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S)
    (f : X' ⟶ X) (g : X ⟶ X') (comm : f ≫ a = a') (hg : g ≫ a' = a) :
    (DescentData.pullbackFunctor a a' (𝟙 S) f (by simpa using comm)).functor ⋙
      (DescentData.pullbackFunctor a' a (𝟙 S) g (by simpa using hg)).functor ≅ 𝟭 _ :=
  (DescentData.pullbackFactorizationIso
    (DescentData.pullbackFunctor a a (𝟙 S) (g ≫ f) (by simp [comm, hg]))
    (DescentData.pullbackFunctor a a' (𝟙 S) f (by simpa using comm))
    (DescentData.pullbackFunctor a' a (𝟙 S) g (by simpa using hg))).symm ≪≫
    DescentData.selfPullbackFunctorIso a (g ≫ f) (by simp [comm, hg])

/-- Pullback of descent data along `f : X' ⟶ X` is an equivalence if there is a morphism
`X ⟶ X'` over the same base scheme. -/
@[stacks 0243]
theorem pullbackFunctor_isEquivalence_of_exists_reverse
    {S X X' : Scheme.{u}} (a : X ⟶ S) (a' : X' ⟶ S) (f : X' ⟶ X)
    (comm : f ≫ a = a') (h : ∃ g : X ⟶ X', g ≫ a' = a) :
    (DescentData.pullbackFunctor a a' (𝟙 S) f (by simpa using comm)).functor.IsEquivalence := by
  obtain ⟨g, hg⟩ := h
  exact (CategoryTheory.Equivalence.mk _ _ (pullbackFunctorCompIsoId a a' f g comm hg).symm
    (pullbackFunctorCompIsoId a' a g f hg comm)).isEquivalence_functor

end AlgebraicGeometry
