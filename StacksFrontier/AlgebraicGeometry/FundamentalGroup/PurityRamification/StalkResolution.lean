module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.LowEmbeddingDimensionEtale
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ExcellentLocalResolution
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.NormalizedBlowUpChainProjective
public import StacksFrontier.RingTheory.Excellent.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring at the point of [Stacks, Tag 0EA3] has a resolution

In the proof of [Stacks, Tag 0EA3] one first observes that `𝒪_{X, x}` is an excellent local ring
([Stacks, Tag 07QU]) and then chooses a resolution of singularities of `Spec(𝒪_{X, x})`
([Stacks, Tag 0BGP]). This file records those two steps for a morphism `f : X ⟶ Spec(A)` locally
of finite type over an excellent ring `A`.

## Main results

* `AlgebraicGeometry.isExcellent_stalk_of_isExcellent_of_locallyOfFiniteType`: `𝒪_{X, x}` is
  excellent.
* `AlgebraicGeometry.exists_isResolution_stalk_of_locallyOfFiniteType`: if moreover `𝒪_{X, x}`
  is a normal domain of dimension two, `Spec(𝒪_{X, x})` has a resolution of singularities.
* `AlgebraicGeometry.exists_isResolution_isProjectiveMorphism_stalk_of_locallyOfFiniteType`: and
  one which is H-projective, as the source uses ("`W ⟶ Spec(𝒪_{X, x})` is projective (as a
  sequence of normalized blowing ups)").
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **[Stacks, Tag 07QU] at a point.** If `A` is excellent and `f : X ⟶ Spec(A)` is locally of
finite type, every local ring `𝒪_{X, x}` is excellent: it is essentially of finite type over
the local ring `𝒪_{Spec A, f x}`, a localization of `A`. -/
@[ega "IV 7.8.3" "(ii), special case"]
theorem isExcellent_stalk_of_isExcellent_of_locallyOfFiniteType {A : Type u} [CommRing A]
    (hA : IsExcellent A)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X) :
    IsExcellent (X.presheaf.stalk x) := by
  let R := (Spec (.of A)).presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let : Algebra A R := (StructureSheaf.toStalk A (f x)).hom.toAlgebra
  let : Algebra R B := (f.stalkMap x).hom.toAlgebra
  let : Algebra A B := (toStalkStalkMap f x).toAlgebra
  have : IsScalarTower A R B := IsScalarTower.of_algebraMap_eq' rfl
  have : (f x).asIdeal.IsPrime := (f x).isPrime
  have : IsLocalization.AtPrime R (f x).asIdeal := StructureSheaf.IsLocalization.to_stalk A (f x)
  have : Algebra.EssFiniteType A R := .of_isLocalization R (f x).asIdeal.primeCompl
  have : Algebra.EssFiniteType R B := LocallyOfFiniteType.stalkMap f x
  have : Algebra.EssFiniteType A B := Algebra.EssFiniteType.comp A R B
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType (R := A)).2 hA

/-- **The resolution chosen in the proof of [Stacks, Tag 0EA3].** If `A` is excellent,
`f : X ⟶ Spec(A)` is locally of finite type and `𝒪_{X, x}` is a normal domain of dimension two,
then `Spec(𝒪_{X, x})` has a resolution of singularities: `𝒪_{X, x}` is excellent, and an
excellent normal local domain of dimension two has one
(`AlgebraicGeometry.exists_isResolution_of_isExcellent_of_ringKrullDim_eq_two`, the local case of
[Stacks, Tag 0BGP]). -/
@[sga "6 X 7.17.5" "special case"]
theorem exists_isResolution_stalk_of_locallyOfFiniteType {A : Type u} [CommRing A]
    (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)] [IsNormalDomain (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2) :
    ∃ (W : Scheme.{u}) (g : W ⟶ Spec (.of (X.presheaf.stalk x))), IsResolution g :=
  exists_isResolution_of_isExcellent_of_ringKrullDim_eq_two _
    (isExcellent_stalk_of_isExcellent_of_locallyOfFiniteType hA f x) hdim

/-- **The resolution chosen in the proof of [Stacks, Tag 0EA3] is projective.** Under the
hypotheses of `AlgebraicGeometry.exists_isResolution_stalk_of_locallyOfFiniteType`, the
resolution can be chosen H-projective: it is a sequence of normalized blowups
(`AlgebraicGeometry.exists_isResolution_isProjectiveMorphism_of_isExcellent`). -/
theorem exists_isResolution_isProjectiveMorphism_stalk_of_locallyOfFiniteType {A : Type u}
    [CommRing A] (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] (x : X)
    [IsNoetherianRing (X.presheaf.stalk x)] [IsNormalDomain (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2) :
    ∃ (W : Scheme.{u}) (g : W ⟶ Spec (.of (X.presheaf.stalk x))),
      IsResolution g ∧ IsProjectiveMorphism g :=
  exists_isResolution_isProjectiveMorphism_of_isExcellent _
    (isExcellent_stalk_of_isExcellent_of_locallyOfFiniteType hA f x) hdim

end AlgebraicGeometry

end
