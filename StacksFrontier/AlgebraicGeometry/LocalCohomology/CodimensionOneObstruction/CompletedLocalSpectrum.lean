module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk

/-!
# The spectrum of the completed local ring of a scheme

Let `X` be a locally Noetherian scheme and `x` a point of it. The completion `𝒪^∧_{X, x}` of the
local ring at its maximal ideal is a faithfully flat `𝒪_{X, x}`-algebra, and composing `Spec` of
the completion map with the canonical morphism `Spec 𝒪_{X, x} ⟶ X` gives a flat morphism
`Spec 𝒪^∧_{X, x} ⟶ X` carrying the closed point to `x` and with image the set of points
specializing to `x`.

This is the base change that the second paragraph of [Stacks, Tag 0AWC] performs: the
obstruction to coherence of a direct image is formulated there in terms of the associated primes
of `𝒪^∧_{X, z}`, so the argument has to move from `X` to `Spec 𝒪^∧_{X, z}` and back.

## Main definitions

* `AlgebraicGeometry.Scheme.completedLocalRingCat` is `𝒪^∧_{X, x}` as an object of
  `CommRingCat`, so that its spectrum can be formed.
* `AlgebraicGeometry.Scheme.toCompletedLocalRing` is the completion map
  `𝒪_{X, x} ⟶ 𝒪^∧_{X, x}` as a morphism of `CommRingCat`.
* `AlgebraicGeometry.Scheme.fromSpecCompletedLocalRing` is the morphism
  `Spec 𝒪^∧_{X, x} ⟶ X`.

## Main results

* the completed local ring is a faithfully flat module over the local ring: this is
  `Module.FaithfullyFlat.of_flat_of_isLocalHom`, used directly.
* `AlgebraicGeometry.Scheme.fromSpecCompletedLocalRing_closedPoint`: the closed point of
  `Spec 𝒪^∧_{X, x}` maps to `x`.
* `AlgebraicGeometry.Scheme.flat_fromSpecCompletedLocalRing`: the morphism
  `Spec 𝒪^∧_{X, x} ⟶ X` is flat.
* `AlgebraicGeometry.Scheme.range_fromSpecCompletedLocalRing`: its image is the set of points
  specializing to `x`.

## Implementation notes

Faithful flatness is `Module.FaithfullyFlat.of_flat_of_isLocalHom` applied to the two Mathlib
instances for the completion of a Noetherian local ring, `AdicCompletion.flat_of_isNoetherian`
and the `IsLocalHom` instance of `AdicCompletion.algebraMap_isLocalHom_of_fg`; for a general
ideal contained in the Jacobson radical it is `AdicCompletion.faithfullyFlat_of_le_ringJacobson`,
[Stacks, Tag 00MC], already in this repository.

`AlgebraicGeometry.Scheme.completedLocalRing` is a `Type`, while `Spec` consumes an object of
`CommRingCat`; `completedLocalRingCat` is the `CommRingCat` packaging, kept reducible so that
the ring-theoretic instances on the completion remain available. A consequence is that the
coercion `↥(Spec (X.completedLocalRingCat x))` does not reduce to `PrimeSpectrum (𝒪^∧_{X, x})`
at the transparency `rw` uses, which is why `AlgebraicGeometry.Scheme.Hom.comp_apply` is applied
as a term, with the two factors of `fromSpecCompletedLocalRing` given explicitly, rather than
through `rw`.

Surjectivity of `Spec 𝒪^∧_{X, x} ⟶ Spec 𝒪_{X, x}` is faithful flatness through
`PrimeSpectrum.comap_surjective_of_faithfullyFlat`; flatness of `Spec 𝒪_{X, x} ⟶ X` is
`AlgebraicGeometry.flat_fromSpecStalk`.

## References

* [Stacks Project, Tag 0AWC](https://stacks.math.columbia.edu/tag/0AWC)
* [Stacks Project, Tag 00MC](https://stacks.math.columbia.edu/tag/00MC)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The completion `𝒪^∧_{X, x}` of the local ring of `X` at `x`, as an object of
`CommRingCat`. -/
abbrev completedLocalRingCat (X : Scheme.{u}) (x : X) : CommRingCat.{u} :=
  .of (X.completedLocalRing x)

/-- The completion map `𝒪_{X, x} ⟶ 𝒪^∧_{X, x}`, as a morphism of `CommRingCat`. -/
def toCompletedLocalRing (X : Scheme.{u}) (x : X) :
    X.presheaf.stalk x ⟶ X.completedLocalRingCat x :=
  CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x))

/-- The completion map of a Noetherian local ring is a local homomorphism. -/
instance isLocalHom_toCompletedLocalRing [IsLocallyNoetherian X] (x : X) :
    IsLocalHom (X.toCompletedLocalRing x).hom :=
  inferInstanceAs
    (IsLocalHom (algebraMap (X.presheaf.stalk x) (X.completedLocalRing x)))

/-- **The canonical morphism `Spec 𝒪^∧_{X, x} ⟶ X`**: the spectrum of the completion map
followed by the canonical morphism from the spectrum of the local ring. -/
def fromSpecCompletedLocalRing (X : Scheme.{u}) (x : X) :
    Spec (X.completedLocalRingCat x) ⟶ X :=
  Spec.map (X.toCompletedLocalRing x) ≫ X.fromSpecStalk x

/-- A point of `Spec 𝒪^∧_{X, x}` maps to `X` through the completion map and `fromSpecStalk`. -/
private theorem fromSpecCompletedLocalRing_apply (x : X) (s : Spec (X.completedLocalRingCat x)) :
    X.fromSpecCompletedLocalRing x s = X.fromSpecStalk x (Spec.map (X.toCompletedLocalRing x) s) :=
  Scheme.Hom.comp_apply _ _ _

/-- **The closed point of `Spec 𝒪^∧_{X, x}` maps to `x`.** The completion map is a local
homomorphism, so it pulls the maximal ideal of the completion back to the maximal ideal of the
local ring. -/
theorem fromSpecCompletedLocalRing_closedPoint [IsLocallyNoetherian X] (x : X) :
    X.fromSpecCompletedLocalRing x
        (IsLocalRing.closedPoint (X.completedLocalRingCat x)) = x :=
  (fromSpecCompletedLocalRing_apply x _).trans <| by
    rw [show (Spec.map (X.toCompletedLocalRing x))
          (IsLocalRing.closedPoint (X.completedLocalRingCat x))
        = IsLocalRing.closedPoint (X.presheaf.stalk x) from
      IsLocalRing.comap_closedPoint (X.toCompletedLocalRing x).hom]
    exact Scheme.fromSpecStalk_closedPoint

/-- **`Spec 𝒪^∧_{X, x} ⟶ X` is flat.** Both factors are: the completion of a Noetherian local
ring is a flat module over it, and `Spec 𝒪_{X, x} ⟶ X` is flat. -/
theorem flat_fromSpecCompletedLocalRing [IsLocallyNoetherian X] (x : X) :
    Flat (X.fromSpecCompletedLocalRing x) := by
  have h₁ : Flat (Spec.map (X.toCompletedLocalRing x)) :=
    Flat.SpecMap_iff.mpr (AdicCompletion.flat_of_isNoetherian _)
  have h₂ : Flat (X.fromSpecStalk x) := flat_fromSpecStalk X x
  exact Flat.comp _ _

/-- **`Spec 𝒪^∧_{X, x} ⟶ Spec 𝒪_{X, x}` is surjective**, the completion map being faithfully
flat. -/
theorem surjective_specMap_toCompletedLocalRing [IsLocallyNoetherian X] (x : X) :
    Function.Surjective (Spec.map (X.toCompletedLocalRing x)).base :=
  have : Module.FaithfullyFlat (X.presheaf.stalk x) (X.completedLocalRing x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := X.presheaf.stalk x) (B := X.completedLocalRing x)

/-- **The image of `Spec 𝒪^∧_{X, x} ⟶ X` is the set of points specializing to `x`.** The second
factor has that image, and the first is surjective. -/
theorem range_fromSpecCompletedLocalRing [IsLocallyNoetherian X] (x : X) :
    Set.range (X.fromSpecCompletedLocalRing x) = {y | y ⤳ x} := by
  rw [← Scheme.range_fromSpecStalk (x := x),
    show ⇑(X.fromSpecCompletedLocalRing x) =
      X.fromSpecStalk x ∘ Spec.map (X.toCompletedLocalRing x) from
      funext (fromSpecCompletedLocalRing_apply x),
    Set.range_comp, (X.surjective_specMap_toCompletedLocalRing x).range_eq, Set.image_univ]

end AlgebraicGeometry.Scheme

end
