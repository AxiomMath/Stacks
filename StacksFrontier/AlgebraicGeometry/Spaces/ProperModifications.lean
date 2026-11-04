module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Modifications
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine

/-!
# Proper modifications of the spectrum of a local ring (Stacks 0AE2)

Let `A` be a Noetherian local ring and `U ⊂ Spec A` its punctured spectrum. The objects of
interest for resolving the singularity of `A` are the proper morphisms of algebraic spaces
`f : X → Spec A` which are isomorphisms over `U`. They form a category: the full subcategory of
the slice over `Spec A` cut out by those three conditions.

## Main definitions

* `AlgebraicGeometry.Space.puncturedSpectrumSubfunctor` is the punctured spectrum of `A` as a
  subfunctor of the functor of points of `Spec A`.
* `AlgebraicGeometry.Space.IsProperModification` is the conjunction of the three conditions and
  `AlgebraicGeometry.Space.ProperModification` is the category they define: **Stacks 0AE2**.

## Implementation notes

The condition is stated for an arbitrary represented target and an arbitrary subfunctor of its
functor of points; `AlgebraicGeometry.Space.ProperModification` specializes it to `Spec A` and
its punctured spectrum. Two of the three conditions — that the source is an algebraic space and
that the base change to the subfunctor is an isomorphism — are exactly
`AlgebraicGeometry.Space.IsModification`, the notion of Tag 0BGY, so only properness is added
here.

The punctured spectrum is described as a subfunctor by *factorization*: a scheme-valued point of
`Spec A` lies in it when the corresponding morphism of schemes factors through the open
immersion of the punctured spectrum. This is the functor of points of the open subscheme without
requiring the open subscheme itself to be an object of the chosen big fppf site, so no
site-size hypothesis on it is needed.

## References

* [Stacks Project, Tag 0AE2](https://stacks.math.columbia.edu/tag/0AE2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0AE2.** The punctured spectrum of a local ring `A`, as a subfunctor of the functor
of points of `Spec A` on a big fppf site: a point lies in it exactly when the corresponding
morphism of schemes factors through the open immersion of the punctured spectrum. -/
@[stacks 0AE2 "the punctured spectrum as a subfunctor"]
noncomputable def puncturedSpectrumSubfunctor (A : Type u) [CommRing A] [IsLocalRing A]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A))) :
    Subfunctor (yoneda.obj (baseTerminal B (Spec (.of A)) hS)) where
  obj T := {f | ∃ g : (BigFppfOver.toScheme B (Spec (.of A)) hS).obj T.unop ⟶
      (puncturedSpectrum A).toScheme,
    g ≫ (puncturedSpectrum A).ι =
      (BigFppfOver.toScheme B (Spec (.of A)) hS).map f}
  map := by
    intro T T' i f ⟨g, hg⟩
    refine ⟨(BigFppfOver.toScheme B (Spec (.of A)) hS).map i.unop ≫ g, ?_⟩
    simp only [Category.assoc, hg, ← Functor.map_comp]
    rfl

/-- **Stacks 0AE2.** A *proper modification* of a represented algebraic space `T` outside a
subfunctor `U` of its functor of points: an algebraic space over `T` whose structure morphism is
proper and whose base change to `U` is an isomorphism. -/
@[stacks 0AE2 "the three defining conditions"]
def IsProperModification (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) (U : Subfunctor (yoneda.obj T))
    (X : Over (yoneda.obj T)) : Prop :=
  IsModification B S hS U X ∧ IsProper B S hS X.hom

/-- **Stacks 0AE2.** The category of proper morphisms of algebraic spaces to `Spec A` which are
isomorphisms over the punctured spectrum of `A`. -/
@[stacks 0AE2 "the category they form"]
abbrev ProperModification (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A))) :=
  ObjectProperty.FullSubcategory
    (IsProperModification B (Spec (.of A)) hS (baseTerminal B (Spec (.of A)) hS)
      (puncturedSpectrumSubfunctor A B hS))

/-- **Stacks 0AE2.** The three conditions defining a proper modification, spelled out: the
source is an algebraic space, its structure morphism is proper, and the base change of that
morphism to the subfunctor is an isomorphism. -/
@[stacks 0AE2 "the conditions spelled out"]
theorem isProperModification_iff (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) (U : Subfunctor (yoneda.obj T)) (X : Over (yoneda.obj T)) :
    IsProperModification B S hS T U X ↔
      IsAlgebraicSpace B S hS X.left ∧ IsProper B S hS X.hom ∧
        IsIso (pullback.snd X.hom U.ι) :=
  ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

end AlgebraicGeometry.Space

end
