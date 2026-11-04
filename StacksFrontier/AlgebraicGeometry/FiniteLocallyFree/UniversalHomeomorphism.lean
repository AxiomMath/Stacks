module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat

/-!
# Flat universally injective surjections are finite locally free

A universally open, surjective and universally injective morphism is universally closed.
Consequently an affine, flat morphism which is locally of finite presentation, surjective and
universally injective is finite locally free.

## Main results

* `Stacks.Morphisms.universallyClosed_of_universallyOpen`: a universally open surjection which
  is universally injective is universally closed.
* `Stacks.Morphisms.isFiniteLocallyFree_of_flat_of_universallyInjective`: an affine flat
  morphism of finite presentation which is surjective and universally injective is finite
  locally free.

## References

* [Stacks Project, Tag 01UA](https://stacks.math.columbia.edu/tag/01UA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Morphisms

/-- An open bijection of topological spaces is a closed map. -/
theorem isClosedMap_of_isOpenMap_of_bijective {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hopen : IsOpenMap g) (hbij : Function.Bijective g) :
    IsClosedMap g := by
  intro C hC
  have h : g '' C = (g '' Cᶜ)ᶜ := by
    rw [← Set.image_compl_eq hbij, compl_compl]
  rw [h]
  exact (hopen _ hC.isOpen_compl).isClosed_compl

/-- A universally open, surjective and universally injective morphism is universally closed. -/
theorem universallyClosed_of_universallyOpen {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyOpen f] [Surjective f] [UniversallyInjective f] : UniversallyClosed f := by
  rw [universallyClosed_eq]
  intro X' S' i₁ i₂ f' hsq
  have hopen : UniversallyOpen f' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hsurj : Surjective f' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have hinj : UniversallyInjective f' := MorphismProperty.of_isPullback hsq.flip inferInstance
  exact isClosedMap_of_isOpenMap_of_bijective f'.isOpenMap ⟨f'.injective, hsurj.surj⟩

/-- An affine flat morphism of finite presentation which is surjective and universally
injective is finite locally free. -/
theorem isFiniteLocallyFree_of_flat_of_universallyInjective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsAffineHom f] [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [UniversallyInjective f] : IsFiniteLocallyFree f := by
  have hclosed : UniversallyClosed f := universallyClosed_of_universallyOpen f
  have hint : IsIntegralHom f :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hclosed, inferInstance⟩
  have hfin : IsFinite f :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mpr ⟨hint, inferInstance⟩
  exact (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation f).mpr
    ⟨hfin, inferInstance, inferInstance⟩

end Stacks.Morphisms

end
