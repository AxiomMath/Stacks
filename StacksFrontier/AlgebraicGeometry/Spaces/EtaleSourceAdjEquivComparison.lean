module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleSourceLocalization

/-!
# The two transpositions along `a^* ⊣ a_*` agree

Two bijections in this development transpose a morphism `a^*Ω_{X/Y} ⟶ C` of `𝒪_U`-modules into
a morphism out of `Ω_{X/Y}`, and they are not the same bijection:

* `AlgebraicGeometry.Space.modulePullbackAdjunction`, the adjunction of Stacks 03LU, whose right
  adjoint is `AlgebraicGeometry.Space.modulePushforward`;
* `AlgebraicGeometry.Space.etaleSourceAdjEquiv`, the first of the four bijections that make the
  étale-source localization of Stacks 04CU, whose right adjoint is
  `AlgebraicGeometry.Space.etaleSourcePushforward`, the direct image in the untransported shape
  of Stacks 03D6 part (1).

They share their left adjoint — both are stated at `AlgebraicGeometry.Space.modulePullback` —
and their right adjoints are identified by `AlgebraicGeometry.Space.modulePushforwardIso`. This
file proves that the two transpositions agree under that identification.

## Main results

* `AlgebraicGeometry.Space.etaleSourceAdjEquiv_comp_modulePushforwardIso`: the transposition of
  Stacks 04CU's first bijection, followed by the identification of the two direct images, is the
  transposition of the adjunction of Stacks 03LU.
* `AlgebraicGeometry.Space.homEquiv_eq_etaleSourceAdjEquiv_comp`: the same equation read in the
  other direction, as a description of the transposition of Stacks 03LU.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU), the adjunction.
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6), the direct image of
  modules in the shape the second bijection uses.
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7), the adjunction for a
  morphism of ringed topoi, which both are instances of.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the étale-source
  localization whose first bijection this compares.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U X Y : AlgebraicSpaces B S hS}

/-- **The two transpositions along `a^* ⊣ a_*` agree.**  Transposing a morphism
`k : a^*Ω_{X/Y} ⟶ C` by `AlgebraicGeometry.Space.etaleSourceAdjEquiv`, the first bijection of the
étale-source localization of Stacks 04CU, and then carrying the result along
`AlgebraicGeometry.Space.modulePushforwardIso` from the direct image of Stacks 03D6 part (1) to
`AlgebraicGeometry.Space.modulePushforward`, gives its transpose along the adjunction
`AlgebraicGeometry.Space.modulePullbackAdjunction` of Stacks 03LU. -/
theorem etaleSourceAdjEquiv_comp_modulePushforwardIso (a : U ⟶ X) (f : X ⟶ Y)
    (C : Modules.{u, u} B S hS U.1 U.2)
    (k : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) :
    etaleSourceAdjEquiv B S hS a f C k ≫ (modulePushforwardIso B S hS a).hom.app C =
      (modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS f) C k :=
  (Adjunction.homEquiv_ofNatIsoRight_apply
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
      (smallEtaleRingedToposModulesHom B S hS a))
    (modulePushforwardIso B S hS a) k).symm

/-- **The transposition of Stacks 03LU, read through the one of Stacks 04CU.**  This is
`AlgebraicGeometry.Space.etaleSourceAdjEquiv_comp_modulePushforwardIso` with the sides
exchanged. -/
theorem homEquiv_eq_etaleSourceAdjEquiv_comp (a : U ⟶ X) (f : X ⟶ Y)
    (C : Modules.{u, u} B S hS U.1 U.2)
    (k : (modulePullback B S hS a).obj (sheafOfDifferentials B S hS f) ⟶ C) :
    (modulePullbackAdjunction B S hS a).homEquiv (sheafOfDifferentials B S hS f) C k =
      etaleSourceAdjEquiv B S hS a f C k ≫ (modulePushforwardIso B S hS a).hom.app C :=
  (etaleSourceAdjEquiv_comp_modulePushforwardIso B S hS a f C k).symm

end AlgebraicGeometry.Space

end
