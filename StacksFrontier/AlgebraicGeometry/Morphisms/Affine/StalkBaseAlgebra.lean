module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution

/-!
# The local ring of `X` at `x` as an algebra over a localization of the base

For a morphism `f : X ⟶ Spec R` of schemes and a point `x : X`, the stalk map of `f` at `x`
together with `AlgebraicGeometry.Spec.stalkIso` makes `𝒪_{X, x}` an algebra over the
localization of `R` at the image point `f x`, and that algebra map is local. If `f` is flat it
is moreover faithfully flat, so that two discrete valuation rings related in this way form an
extension in the sense of Stacks 09E4.

## Main definitions

* `AlgebraicGeometry.localizationAtPrimeToStalk`: the local homomorphism
  `R_{f x} ⟶ 𝒪_{X, x}` obtained from the stalk map of `f`.
* `AlgebraicGeometry.stalkAlgebraOfSpecHom`: the resulting algebra structure.

## Main results

* `AlgebraicGeometry.faithfulSMul_stalkAlgebraOfSpecHom`: for `f` flat the algebra map is
  injective.
* `AlgebraicGeometry.isExtension_stalkAlgebraOfSpecHom`: for `f` flat with both local rings
  discrete valuation rings, `𝒪_{X, x}` is an extension of `R_{f x}`.

## Implementation notes

The hypothesis `[(f.base x).asIdeal.IsPrime]` has to be taken as an instance argument: the
point `f.base x` lives in `↥(Spec R)` rather than in `PrimeSpectrum R`, and typeclass synthesis
does not see through `Spec` to find `PrimeSpectrum.isPrime`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) (x : X)
  [(f.base x).asIdeal.IsPrime]

/-- The stalk map of `f : X ⟶ Spec R` at `x`, read through `AlgebraicGeometry.Spec.stalkIso`:
a ring map from `R` localized at the image of `x` to the local ring of `X` at `x`. -/
noncomputable def localizationAtPrimeToStalk :
    CommRingCat.of (Localization.AtPrime (f.base x).asIdeal) ⟶ X.presheaf.stalk x :=
  (Spec.stalkIso R (f.base x)).inv ≫ f.stalkMap x

/-- The local ring of `X` at `x` is an algebra over `R` localized at the image of `x`. -/
@[instance_reducible]
noncomputable def stalkAlgebraOfSpecHom :
    Algebra (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) :=
  (localizationAtPrimeToStalk f x).hom.toAlgebra

/-- The map `R_{f x} ⟶ 𝒪_{X, x}` is a local homomorphism. -/
instance isLocalHom_localizationAtPrimeToStalk :
    IsLocalHom (localizationAtPrimeToStalk f x).hom := by
  have : IsLocalHom (Spec.stalkIso R (f.base x)).inv.hom :=
    isLocalHom_toRingHom (f := (Spec.stalkIso R (f.base x)).symm.commRingCatIsoToRingEquiv)
  exact CommRingCat.isLocalHom_comp _ _

/-- The structure map of `AlgebraicGeometry.stalkAlgebraOfSpecHom` is
`AlgebraicGeometry.localizationAtPrimeToStalk`. -/
lemma algebraMap_stalkAlgebraOfSpecHom :
    letI := stalkAlgebraOfSpecHom f x
    algebraMap (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) =
      (localizationAtPrimeToStalk f x).hom := rfl

/-- The structure map of `AlgebraicGeometry.stalkAlgebraOfSpecHom` is a local
homomorphism. -/
lemma isLocalHom_algebraMap_stalkAlgebraOfSpecHom :
    letI := stalkAlgebraOfSpecHom f x
    IsLocalHom (algebraMap (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x)) :=
  isLocalHom_localizationAtPrimeToStalk f x

/-- For `f` flat the map `R_{f x} ⟶ 𝒪_{X, x}` is flat. -/
lemma flat_localizationAtPrimeToStalk [Flat f] :
    (localizationAtPrimeToStalk f x).hom.Flat := by
  rw [localizationAtPrimeToStalk, CommRingCat.hom_comp]
  exact (RingHom.Flat.of_bijective
    (Spec.stalkIso R (f.base x)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (Flat.stalkMap f x)

/-- For `f` flat the local ring `𝒪_{X, x}` is faithfully flat over `R_{f x}`, both being
local rings. -/
lemma faithfullyFlat_stalkAlgebraOfSpecHom [Flat f] :
    letI := stalkAlgebraOfSpecHom f x
    Module.FaithfullyFlat (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfSpecHom f x
  have : Module.Flat (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) :=
    flat_localizationAtPrimeToStalk f x
  have : IsLocalHom (algebraMap (Localization.AtPrime (f.base x).asIdeal)
      (X.presheaf.stalk x)) := isLocalHom_algebraMap_stalkAlgebraOfSpecHom f x
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- For `f` flat the map `R_{f x} ⟶ 𝒪_{X, x}` is injective. -/
lemma faithfulSMul_stalkAlgebraOfSpecHom [Flat f] :
    letI := stalkAlgebraOfSpecHom f x
    FaithfulSMul (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfSpecHom f x
  have := faithfullyFlat_stalkAlgebraOfSpecHom f x
  infer_instance

/-- If `f` is flat and both local rings are discrete valuation rings, then `𝒪_{X, x}` is an
extension of discrete valuation rings over the localization of `R` at the image of `x`. -/
lemma isExtension_stalkAlgebraOfSpecHom [Flat f]
    [IsDomain (Localization.AtPrime (f.base x).asIdeal)]
    [IsDiscreteValuationRing (Localization.AtPrime (f.base x).asIdeal)]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    letI := stalkAlgebraOfSpecHom f x
    IsDiscreteValuationRing.IsExtension
      (Localization.AtPrime (f.base x).asIdeal) (X.presheaf.stalk x) := by
  let := stalkAlgebraOfSpecHom f x
  have := faithfulSMul_stalkAlgebraOfSpecHom f x
  have := isLocalHom_algebraMap_stalkAlgebraOfSpecHom f x
  exact ⟨⟩

end AlgebraicGeometry
