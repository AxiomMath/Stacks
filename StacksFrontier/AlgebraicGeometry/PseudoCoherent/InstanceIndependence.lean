module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel

/-!
# Pseudo-coherence does not depend on the choice of derived category

`HasDerivedCategory.{w} C` is the datum of a localization of the category of cochain complexes in
`C` at the quasi-isomorphisms whose morphisms live in `Type w`, so both the type
`DerivedCategory C` and the localization functor `DerivedCategory.Q` depend on it. Two such data,
possibly with different `w`, therefore give two *different* derived categories, and a predicate
stated for one of them is a priori a different predicate from the same one stated for the other.

This file proves that `AlgebraicGeometry.RingedSpace.IsPseudoCoherentFrom` does not in fact
depend on that choice, for an object of the form `Q K`: the uniqueness of localizations
(`CategoryTheory.Localization.uniq`) provides an equivalence `D₁ ≌ D₂` under which the two
localization functors correspond (`CategoryTheory.Localization.compUniqFunctor`), and
`m`-pseudo-coherence of `Q K` only refers to the derived category through the existence of an
isomorphism `Q L ≅ Q K`, which that equivalence transports.

## Main definitions

* `CategoryTheory.DerivedCategory.transferQObjIso`: an isomorphism `Q₁ K ≅ Q₁ L` between the
  images of two cochain complexes in one derived category gives one in any other.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_transfer`: `m`-pseudo-coherence of the
  object of the derived category represented by a complex does not depend on the chosen
  `HasDerivedCategory` instance, not even on its universe.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_Q_transfer`: the same for pseudo-coherence.

## Implementation notes

The point of this file is to make an induction possible that would otherwise be blocked. The
induction of Stacks 09VA shrinks the ambient ringed space, so an inductive step for
`i : Z ⟶ X` has to re-apply the inductive hypothesis to `i|_W : Z|_{i⁻¹W} ⟶ X|_W`; the family of
`HasDerivedCategory` instances carried as hypotheses on the open subspaces of `X` does not
contain instances for the open subspaces of `X|_W`. The cure is to carry
`∀ Y : RingedSpace, HasDerivedCategory.{w} (OXMod Y)` as an explicit hypothesis, which *is*
stable under shrinking, and to bridge between that universe and the universe of the instances in
the statement of Stacks 09VA. Universe-polymorphic recursion being forbidden in Lean, no `d ≠ d'`
statement can play the role of the induction hypothesis itself, so the bridge has to happen once,
outside the induction; that bridge is `isPseudoCoherentFrom_Q_transfer`.

Both instances are taken as explicit arguments rather than as instance arguments: a statement
mentioning two `HasDerivedCategory` instances for the same category cannot have both of them
found by instance search.

## References

* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Lemma 36.60.9 (09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' v u

namespace CategoryTheory.DerivedCategory

/-- **An isomorphism between the images of two cochain complexes in one derived category gives
one in any other.** The two localization functors correspond under the equivalence
`CategoryTheory.Localization.uniq` of the two localizations of the category of cochain complexes
at the quasi-isomorphisms, so the image of the given isomorphism under that equivalence is the
isomorphism asked for. -/
public def transferQObjIso {C : Type u} [Category.{v} C] [Abelian C]
    (inst₁ : HasDerivedCategory.{w} C) (inst₂ : HasDerivedCategory.{w'} C)
    (K L : CochainComplex C ℤ)
    (e : (@DerivedCategory.Q C _ _ inst₁).obj K ≅ (@DerivedCategory.Q C _ _ inst₁).obj L) :
    (@DerivedCategory.Q C _ _ inst₂).obj K ≅ (@DerivedCategory.Q C _ _ inst₂).obj L :=
  let F := (Localization.uniq (@DerivedCategory.Q C _ _ inst₁) (@DerivedCategory.Q C _ _ inst₂)
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))).functor
  let ε := Localization.compUniqFunctor (@DerivedCategory.Q C _ _ inst₁)
    (@DerivedCategory.Q C _ _ inst₂) (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
  (ε.app K).symm ≪≫ F.mapIso e ≪≫ ε.app L

end CategoryTheory.DerivedCategory

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- **`m`-pseudo-coherence of the object represented by a complex does not depend on the choice of
derived category.** `m`-pseudo-coherence of `Q K` asserts the existence of an
`m`-pseudo-coherent complex `L` — a condition on complexes, with no reference to the derived
category — together with an isomorphism `Q L ≅ Q K`, and
`CategoryTheory.DerivedCategory.transferQObjIso` carries that isomorphism from one derived
category to another. -/
public theorem isPseudoCoherentFrom_Q_transfer
    (inst₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (inst₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} X))
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) (m : ℤ)
    (h : @IsPseudoCoherentFrom X inst₁ ((@DerivedCategory.Q _ _ _ inst₁).obj K) m) :
    @IsPseudoCoherentFrom X inst₂ ((@DerivedCategory.Q _ _ _ inst₂).obj K) m := by
  obtain ⟨L, hL, ⟨e⟩⟩ := h
  exact ⟨L, hL, ⟨DerivedCategory.transferQObjIso inst₁ inst₂ L K e⟩⟩

/-- **Pseudo-coherence of the object represented by a complex does not depend on the choice of
derived category.** As for `isPseudoCoherentFrom_Q_transfer`: the condition asks for a
pseudo-coherent complex `L` and an isomorphism `Q L ≅ Q K`, and only the latter refers to the
derived category. -/
public theorem isPseudoCoherent_Q_transfer
    (inst₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (inst₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} X))
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (h : @IsPseudoCoherent X inst₁ ((@DerivedCategory.Q _ _ _ inst₁).obj K)) :
    @IsPseudoCoherent X inst₂ ((@DerivedCategory.Q _ _ _ inst₂).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := h
  exact ⟨L, hL, ⟨DerivedCategory.transferQObjIso inst₁ inst₂ L K e⟩⟩

end AlgebraicGeometry.RingedSpace

end
