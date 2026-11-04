module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.SetoidRepresentability

/-!
# A relative property of a 1-morphism of fibred setoids (Stacks 04TC)

Let `P` be a property of morphisms of algebraic spaces over `S` which is stable under base change
and local on the target for the fppf precoverage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in setoids over the big fppf site of `S`. Let `a` be the induced map of
isomorphism-class presheaves. Then `a` has `P` in the sense of Stacks 03XZ exactly when `f` has
`P` in the relative sense of Stacks 03YK.

## Main results

* `AlgebraicGeometry.Stack.isoClassMap_holdsOnEverySchemePoint_iff`: **Stacks 04TC**.

## Implementation notes

The source's proof is "combine Stacks 0459 and Stacks 045A", and that is exactly the proof here:
Stacks 045A compares `a` with the 1-morphism `𝒮_F ⟶ 𝒮_G` attached to it, and Stacks 0459 moves a
relative property across the comparison square of Stacks 04SY, whose horizontal arrows are the
equivalences `AlgebraicGeometry.Stack.isoClassBasedFunctor` and whose 2-cell is
`AlgebraicGeometry.Stack.isoClassComparisonIso`.

No hypothesis of the source is carried: representability of `a` is not assumed but derived from
representability of `f` by Stacks 04SY, as the source says.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 04SY](https://stacks.math.columbia.edu/tag/04SY)
* [Stacks Project, Tag 04TC](https://stacks.math.columbia.edu/tag/04TC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v

/-- **Stacks 04TC.** For a 1-morphism `f` of categories fibred in setoids over the big fppf site
of `S` whose induced map `a` of isomorphism-class presheaves is representable by algebraic
spaces, `a` has a property `P` in the sense of Stacks 03XZ exactly when `f` has `P` in the
relative sense of Stacks 03YK. -/
@[stacks 04TC]
theorem isoClassMap_holdsOnEverySchemePoint_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    {𝒳 𝒴 : CatFiberedInSetoids.{u, v, u + 1, u} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳.val.p.isoClassPresheaf ⟶ 𝒴.val.p.isoClassPresheaf)
    (ha : ∀ (U : BigFppfOver B S hS) (x : 𝒳.val.p.Fiber U),
      a.app (Opposite.op U) (Functor.isoClassMk 𝒳.val.p x) =
        Functor.isoClassMk 𝒴.val.p
          ((Functor.Fiber.mapOfComp 𝒳.val.p 𝒴.val.p
            (CatFiberedInGroupoids.homFunctor f)
            (CatFiberedInGroupoids.homFunctor_comp_p f) U).obj x))
    (hf : IsRepresentableByAlgebraicSpaces B S hS
      (CatFiberedInSetoids.inclusion.map f).hom) :
    Space.HasProperty B S hS P a
        ((isoClassMap_isRepresentableByAlgebraicSpaces_iff B S hS f a ha).mpr hf) ↔
      HasRelativeProperty B S hS P (CatFiberedInSetoids.inclusion.map f) hf := by
  have harep := (isoClassMap_isRepresentableByAlgebraicSpaces_iff B S hS f a ha).mpr hf
  have hX : Functor.IsEquivalence (isoClassBasedFunctor B S hS 𝒳).toFunctor :=
    (isoClassEquivalenceOver B S hS 𝒳).toEquivalence.isEquivalence_functor
  have hY : Functor.IsEquivalence (isoClassBasedFunctor B S hS 𝒴).toFunctor :=
    (isoClassEquivalenceOver B S hS 𝒴).toEquivalence.isEquivalence_functor
  exact (holdsOnEverySchemePoint_iff_hasRelativeProperty B S hS P a harep).trans
    (@hasRelativeProperty_iff_of_equivalences' B S hS
      (CatFiberedInSetoids.inclusion.obj 𝒳) (CatFiberedInSetoids.inclusion.obj 𝒴)
      (fibredCategory B S hS 𝒳.val.p.isoClassPresheaf)
      (fibredCategory B S hS 𝒴.val.p.isoClassPresheaf) P _ _
      (CatFiberedInSetoids.inclusion.map f) (associatedMap B S hS a).1
      (isoClassBasedFunctor B S hS 𝒳) (isoClassBasedFunctor B S hS 𝒴)
      (isoClassComparisonIso B S hS f a ha) hX hY
      ((isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS a).mp harep) hf)

end AlgebraicGeometry.Stack

end
