module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorAmplitudeRestriction

/-!
# Tor amplitude over the base, read off the stalks with no representative chosen

`AlgebraicGeometry.HasTorAmplitudeOver` is defined by exhibiting *one* cochain complex
representing the given object of `D(𝒪_X)` and asking its relative stalk complexes to have Tor
amplitude in the given interval. The choice of representative is immaterial — that is
`AlgebraicGeometry.relativeStalkAmplitude_of_derivedIso` — so the predicate is equivalent to a
condition on the derived stalks themselves, with no complex quantified over. This file records
that equivalence.

The representative-free form is what a comparison with a condition on a *different* space can
consume: a derived stalk is the value of a functor on `D(𝒪_X)`, so it transports along any
isomorphism of objects and along any identification of the stalk functors, whereas a choice of
representing complex does not move.

## Main definitions

* `AlgebraicGeometry.RelativeStalkHasTorAmplitude`: for every point `x` of `X`, the derived
  stalk of `E` at `x`, read over the local ring of `S` at `f x` along the germ map of `f`, has
  Tor amplitude in `[a, b]`.

## Main results

* `AlgebraicGeometry.hasTorAmplitudeOver_iff_forall_stalk`: Tor amplitude in `[a, b]` over the
  base is exactly that condition.
* `AlgebraicGeometry.exists_hasTorAmplitudeOver_iff_exists_forall_stalk`: the same with the
  interval quantified existentially, which is the shape the relative conditions of Stacks 0DI0
  are stated at.

## Implementation notes

The forward direction carries the hypothesis along
`AlgebraicGeometry.relativeStalkComplexDerivedIso`, which identifies the class of the relative
stalk complex of a representative with the derived stalk of the represented object; the backward
direction chooses the representative `CategoryTheory.DerivedCategory.Q.objPreimage E`, which
exists because the localization functor is essentially surjective, and runs the same
identification in reverse. Neither direction uses anything about `f` beyond its germ maps, and
neither needs a K-flat representative: the interval is fixed and no tensor product is formed.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 36.21.3 (Tag 0DHY)](https://stacks.math.columbia.edu/tag/0DHY)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open StacksDraft.TorAmplitude
open AlgebraicGeometry.BaseChangeTorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The stalkwise form of Tor amplitude over the base.** For every point `x` of `X`, the
derived stalk of `E` at `x` — an object of `D(𝒪_{X, x})` — read over the local ring
`𝒪_{S, f x}` along the germ map `f.stalkMap x`, has Tor amplitude in `[a, b]`.

This is `AlgebraicGeometry.HasTorAmplitudeOver` with no representing complex chosen; the two are
identified by `AlgebraicGeometry.hasTorAmplitudeOver_iff_forall_stalk`. -/
public def RelativeStalkHasTorAmplitude (E : DerivedCategory X.Modules) (a b : ℤ) : Prop :=
  ∀ x : X, HasTorAmplitudeCanonicalLift.{u, u, u}
    ((ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.obj
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.obj E)) a b

/-- **Tor amplitude over the base is a condition on the derived stalks.** An object of `D(𝒪_X)`
has Tor amplitude in `[a, b]` relative to `f : X ⟶ S` exactly when each of its derived stalks,
read over the local ring of `S` at the image point, has Tor amplitude in `[a, b]`.

The definition of `AlgebraicGeometry.HasTorAmplitudeOver` exhibits a representing complex; the
class of its relative stalk complex at `x` is the derived stalk by
`AlgebraicGeometry.relativeStalkComplexDerivedIso`, and Tor amplitude depends only on the
isomorphism class (`StacksDraft.TorAmplitude.hasTorAmplitudeCanonicalLift_of_iso`). Backwards,
`CategoryTheory.DerivedCategory.Q.objPreimage` supplies a representative. -/
public theorem hasTorAmplitudeOver_iff_forall_stalk (E : DerivedCategory X.Modules) (a b : ℤ) :
    HasTorAmplitudeOver f E a b ↔ RelativeStalkHasTorAmplitude f E a b := by
  have e (K : CochainComplex X.Modules ℤ) (eK : DerivedCategory.Q.obj K ≅ E) (x : X) :=
    relativeStalkComplexDerivedIso f K x ≪≫
      (ModuleCat.restrictScalars (f.stalkMap x).hom).mapDerivedCategory.mapIso
        ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategory.mapIso eK)
  constructor
  · rintro ⟨K, ⟨eK⟩, hK⟩ x
    exact hasTorAmplitudeCanonicalLift_of_iso (e K eK x) a b (hK x)
  · intro h
    exact ⟨DerivedCategory.Q.objPreimage E, ⟨DerivedCategory.Q.objObjPreimageIso E⟩, fun x =>
      hasTorAmplitudeCanonicalLift_of_iso (e _ (DerivedCategory.Q.objObjPreimageIso E) x).symm
        a b (h x)⟩

/-- **Finite Tor dimension over the base is a condition on the derived stalks**, with one
interval serving every point. This is the existential form of
`AlgebraicGeometry.hasTorAmplitudeOver_iff_forall_stalk`; the interval stays outside the
quantifier over points on both sides. -/
public theorem exists_hasTorAmplitudeOver_iff_exists_forall_stalk
    (E : DerivedCategory X.Modules) :
    (∃ a b : ℤ, HasTorAmplitudeOver f E a b) ↔
      ∃ a b : ℤ, RelativeStalkHasTorAmplitude f E a b :=
  exists_congr fun a => exists_congr fun b => hasTorAmplitudeOver_iff_forall_stalk f E a b

end AlgebraicGeometry

end
