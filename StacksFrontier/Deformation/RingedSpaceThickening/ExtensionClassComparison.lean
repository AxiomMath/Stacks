module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentLiftingObstruction
public import StacksFrontier.Deformation.RingedSpaceThickening.PulledNaiveCotangentTwoTerm
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentExactSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Comparing the classes of two square-zero extensions along a morphism

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` and `g : (Y, 𝒪_Y) ⟶ (X, 𝒪_X)` be morphisms of ringed spaces,
`ℱ` an `𝒪_X`-module, `𝒢` an `𝒪_Y`-module and `c : ℱ → 𝒢` a `g`-map. A class
`ξ ∈ Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, ℱ)` and a class `ζ ∈ Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)` are compared in
`Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)`, and an `S`-morphism `Y' ⟶ X'` compatible with `g` and `c` exists
exactly when the two images agree. The map in which `ζ` is read is precomposition with the
canonical comparison `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`, which for the sequence of sheaves of rings
`g⁻¹f⁻¹𝒪_S ⟶ g⁻¹𝒪_X ⟶ 𝒪_Y` on `Y` is the base-change map. Here `g^*` is the degreewise pullback,
`𝖭𝖫_{Y/S}` is taken over the iterated inverse image `g⁻¹f⁻¹𝒪_S`, and the image of `ξ` is taken
directly as a class in `Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentComparison`: the canonical
  comparison `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`.
* `AlgebraicGeometry.RingedSpaceThickening.pulledExtGroup` and
  `AlgebraicGeometry.RingedSpaceThickening.relativeExtGroup`: the groups
  `Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)` and `Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)`.
* `AlgebraicGeometry.RingedSpaceThickening.restrictExtClass`: the map
  `Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢) ⟶ Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)`, precomposition with that
  comparison.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.exists_compatibleLift_iff_eq_restrictExtClass`: a
  compatible `S`-morphism `Y' ⟶ X'` exists if and only if `ξ = restrictExtClass g f G ζ`. It takes
  as hypotheses a bijection `e` between the compatible morphisms and the factorizations of the
  difference homomorphism `δ` through the degree `0` term, and the identity `hcompat` identifying
  `ξ - restrictExtClass g f G ζ` with the obstruction class of `δ`.

## References

* [Stacks Project, Tag 0GQ1](https://stacks.math.columbia.edu/tag/0GQ1)
* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the base-change map.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.SheafOfModules (naiveCotangentComplex inverseImageBaseRing inverseImageMiddleRing
  inverseImageFirstRingMap ringedSpaceStructureMap pulledNaiveCotangentComplex
  pulledNaiveCotangentComparison spaceBaseChangeNaiveCotangentMap)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S Y : RingedSpace.{u, u}}

/-- `𝖭𝖫_{Y/S}`, the naive cotangent complex of `𝒪_Y` over the iterated inverse image
`g⁻¹f⁻¹𝒪_S`. -/
abbrev relativeNaiveCotangentComplex (g : Y ⟶ X) (f : X ⟶ S) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology Y.carrier) Y.sheaf)) ℤ :=
  naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology Y.carrier)
    (inverseImageBaseRing g f) Y.sheaf
    (inverseImageFirstRingMap g f ≫ ringedSpaceStructureMap g)

/-- The canonical comparison `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`: the identification of `g^*𝖭𝖫_{X/S}` with the
base change of `𝖭𝖫_{g⁻¹𝒪_X/g⁻¹f⁻¹𝒪_S}`, followed by the canonical base-change map for
`g⁻¹f⁻¹𝒪_S ⟶ g⁻¹𝒪_X ⟶ 𝒪_Y`. -/
@[stacks 0GQ1 "the canonical comparison g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S} along which ζ is read, for the \
degreewise pullback; the derived pullback Lg^*𝖭𝖫_{X/S} of the source's statement is not used"]
def pulledNaiveCotangentComparison (g : Y ⟶ X) (f : X ⟶ S) :
    pulledNaiveCotangentComplex.{u} g f ⟶ relativeNaiveCotangentComplex g f :=
  (Stacks.SheafOfModules.pulledNaiveCotangentComparison.{u} g f).hom ≫
    spaceBaseChangeNaiveCotangentMap (inverseImageBaseRing g f) (inverseImageMiddleRing g)
      Y.sheaf (inverseImageFirstRingMap g f) (ringedSpaceStructureMap g)

section Derived

attribute [local instance] HasDerivedCategory.standard

variable (g : Y ⟶ X) (f : X ⟶ S)
  (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology Y.carrier) Y.sheaf))

/-- `Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)`, the group in which the two classes are compared. -/
abbrev pulledExtGroup : Type _ :=
  DerivedCategory.Q.obj (pulledNaiveCotangentComplex.{u} g f) ⟶
    ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧

/-- `Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢)`, the group the class `ζ` of the extension of `𝒪_Y` lives in. -/
abbrev relativeExtGroup : Type _ :=
  DerivedCategory.Q.obj (relativeNaiveCotangentComplex.{u} g f) ⟶
    ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧

/-- The map `Ext¹_{𝒪_Y}(𝖭𝖫_{Y/S}, 𝒢) ⟶ Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)`: precomposition with the
canonical comparison of the naive cotangent complexes. -/
@[stacks 0GQ1 "the map Ext¹(𝖭𝖫_{Y/S}, 𝒢) ⟶ Ext¹(g^*𝖭𝖫_{X/S}, 𝒢) in which ζ is read, the \
second of the two maps the source's proof constructs; the first, which goes through the \
derived pullback of 06YJ and the g-map c, is not constructed here"]
def restrictExtClass (ζ : relativeExtGroup g f G) : pulledExtGroup g f G :=
  DerivedCategory.Q.map (pulledNaiveCotangentComparison g f) ≫ ζ

/-- An `S`-morphism `Y' ⟶ X'` compatible with `g` and the `g`-map `c` exists if and only if
`ξ = restrictExtClass g f G ζ` in `Ext¹_{𝒪_Y}(g^*𝖭𝖫_{X/S}, 𝒢)`.

Here `δ : g^*(𝒥/𝒥²) ⟶ 𝒢` is a homomorphism out of the conormal term of the two-term structure
`AlgebraicGeometry.RingedSpaceThickening.pulledNaiveCotangentTwoTerm g f`. The theorem takes as
hypotheses a bijection `e` between the type `Lift` of compatible morphisms and the factorizations
of `δ` through the degree `0` term `g^*Ω`, and the identity `hcompat`: the difference
`ξ - restrictExtClass g f G ζ` is the obstruction class of `δ`. -/
@[stacks 0GQ1 "the equivalence, deduced from clause (1) of 08U8: the two Ext¹ classes agree \
exactly when a compatible S-morphism exists. The two-term structure of g^*𝖭𝖫_{X/S} is now \
constructed rather than assumed, by pulledNaiveCotangentTwoTerm. Two conditions remain inputs: \
(i) the bijection e between the compatible S-morphisms and the factorizations of the difference \
homomorphism — Steps 1 to 3 of 08U8, an input there too — and (ii) hcompat, the compatibility \
between the constructions in the proofs of 0GPZ and 08U8 whose statement and proof the source \
omits. The class read off from ξ is taken as its image in Ext¹(g^*𝖭𝖫_{X/S}, 𝒢); the first of \
the source's two maps is not constructed here"]
theorem exists_compatibleLift_iff_eq_restrictExtClass
    (δ : (pulledNaiveCotangentTwoTerm g f).conormal ⟶ G) {Lift : Type*}
    (e : Lift ≃ {θ : (pulledNaiveCotangentTwoTerm g f).base ⟶ G //
      (pulledNaiveCotangentTwoTerm g f).d ≫ θ = δ})
    (ξ : pulledExtGroup g f G) (ζ : relativeExtGroup g f G)
    (hcompat : ξ - restrictExtClass g f G ζ =
      (pulledNaiveCotangentTwoTerm g f).conormalExtClass G δ) :
    Nonempty Lift ↔ ξ = restrictExtClass g f G ζ := by
  refine Iff.trans (liftingObstruction_eq_zero_iff _ G δ e).symm ?_
  rw [liftingObstruction, ← hcompat]
  exact sub_eq_zero

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
