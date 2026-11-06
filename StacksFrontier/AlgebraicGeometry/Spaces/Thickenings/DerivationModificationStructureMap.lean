module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDerivation
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentials
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.PerturbedStructureMap

/-!
# Modifying the structure map of a morphism of algebraic spaces by a derivation

Let `X'` and `Y'` be algebraic spaces over a scheme `S` contained in a big fppf site, let
`a' : X' ⟶ Y'` be a morphism, and let `X ⊂ X'` be a closed subspace which is a **first order
thickening**.  The map `α = (a')^♯ + D` of [Stacks Project, Tag 04D0] is the structure map of
`a'` modified by a derivation `D` taking values in the defining ideal of `X ⊂ X'`.  This file
builds that modified morphism of small étale ringed topoi and proves the two properties of it
which do not refer to the derivation's origin:

* it is a morphism of **locally ringed** topoi, and
* the zero derivation returns `a'` itself.

Both are the small étale instance of the generic statements of
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/PerturbedStructureMap.lean`, whose
input is a `Stacks.Sites.RingSheafDerivation` along the inverse-image structure map
`(a')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`.  The square-zero condition on the values of such a derivation is
supplied here from the first order hypothesis, by
`AlgebraicGeometry.Space.mul_eq_zero_of_mem_definingIdealAt` — the same lemma through which the
*difference* of two lifts is a derivation in
`StacksFrontier/AlgebraicGeometry/Spaces/LiftDifferenceDerivation.lean`.  So a consumer only has to
produce the sectionwise family and check that its values lie in the defining ideal.

## Main definitions

* `AlgebraicGeometry.Space.ringSheafDerivationOfMemDefiningIdeal`: a sectionwise additive,
  Leibniz, natural family of maps into the structure sheaf of `X'` whose values lie in the
  defining ideal of a first order thickening is a `Stacks.Sites.RingSheafDerivation`.  The field
  the first order hypothesis discharges is the vanishing of the products of values.
* `AlgebraicGeometry.Space.derivationModificationHom`: the morphism of small étale ringed topoi
  of `a'` with its structure map modified by such a derivation — the `α = (a')^♯ + D` of
  [Stacks Project, Tag 04D0], read as a morphism of ringed topoi on the ambient spaces rather
  than through the identification of [Stacks Project, Tag 05ZM].

## Main results

* `AlgebraicGeometry.Space.derivationModificationHom_isLocallyRinged`: **the modified structure
  map is locally ringed**, with nothing assumed beyond the first order hypothesis.  This is
  [Stacks Project, Tag 04KJ] for `a'` — `smallEtaleRingedToposHom_isLocallyRinged`, which is
  unconditional — together with the perturbation theorem.
* `AlgebraicGeometry.Space.derivationModificationHom_zero`: **modifying by the zero derivation
  returns the morphism of ringed topoi of `a'`.**
* `AlgebraicGeometry.Space.derivationModificationHom_fSharpInverseImage_apply`: the value of the
  modified structure map on a section, which is what identifies it with the source's `α`.

## Implementation notes

The modification is taken in the **inverse-image** form `(a')^{-1}𝒪_{Y'} ⟶ 𝒪_{X'}`, which is
the form the source writes `α` in, and not in the direct-image form which is the field of
`AlgebraicGeometry.RingedToposHom`.  `AlgebraicGeometry.RingedToposHom.ofInverseImageSharp`
transposes, and `ofInverseImageSharp_fSharpInverseImage` reads the inverse-image form back off
the result, so nothing here has to mention the transpose.

What this file does **not** do is produce the derivation from the `𝒪_X`-linear map
`θ : a^*Ω_{Y/B} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04D0].  That passage is the composite of
Equation (0619) — `AlgebraicGeometry.Space.derivationDirectImageEquiv` — with the
identification of sheaves on `X` with sheaves on `X'` of [Stacks Project, Tag 05ZM], whose topos
half is `AlgebraicGeometry.Space.smallEtaleToposEquivOfIsThickening`; and the conormal module of
a first order thickening is its defining ideal by
`AlgebraicGeometry.Space.firstOrderConormalModuleIso`.  Those three are in the library and the
passage between them is not.

## References

* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
* [Stacks Project, Tag 04KJ](https://stacks.math.columbia.edu/tag/04KJ)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public section

open CategoryTheory
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X'.1)

/-- **A sectionwise family with values in the defining ideal of a first order thickening is a
derivation with square zero values.**  The three equations — additivity, the Leibniz rule with
the scalars acting through `f`, and compatibility with restriction — are the caller's; the
vanishing of the products of values is
`AlgebraicGeometry.Space.mul_eq_zero_of_mem_definingIdealAt`, and it is the only place the first
order hypothesis is used. -/
noncomputable def ringSheafDerivationOfMemDefiningIdeal
    (hZ : IsFirstOrderThickening B S hS X' Z.1)
    {R : Sheaf (SmallEtale.topology B S hS X'.1) CommRingCat.{u}}
    (f : R ⟶ (smallEtaleRingedTopos B S hS X').O)
    (d : ∀ U : (SmallEtale B S hS X'.1)ᵒᵖ,
      R.obj.obj U → (smallEtaleRingedTopos B S hS X').O.obj.obj U)
    (hmem : ∀ (U : (SmallEtale B S hS X'.1)ᵒᵖ) (x : R.obj.obj U),
      d U x ∈ definingIdealAt B S hS X' Z U)
    (hadd : ∀ (U : (SmallEtale B S hS X'.1)ᵒᵖ) (x y : R.obj.obj U),
      d U (x + y) = d U x + d U y)
    (hleib : ∀ (U : (SmallEtale B S hS X'.1)ᵒᵖ) (x y : R.obj.obj U),
      d U (x * y) = (f.hom.app U).hom x * d U y + (f.hom.app U).hom y * d U x)
    (hnat : ∀ {U V : (SmallEtale B S hS X'.1)ᵒᵖ} (h : U ⟶ V) (x : R.obj.obj U),
      (((smallEtaleRingedTopos B S hS X').O).obj.map h).hom (d U x) =
        d V ((R.obj.map h).hom x)) :
    Stacks.Sites.RingSheafDerivation f where
  toFun := d
  map_add' := hadd
  leibniz := hleib
  mul_eq_zero U x y := mul_eq_zero_of_mem_definingIdealAt B S hS Z hZ (hmem U x) (hmem U y)
  naturality := hnat

variable {Y' : AlgebraicSpaces B S hS} (a' : X' ⟶ Y')

/-- **The structure map of `a'` modified by a derivation**, as a morphism of the small étale
ringed topoi of `X'` and `Y'`: the `α = (a')^♯ + D` of [Stacks Project, Tag 04D0], with the same
underlying morphism of topoi as `a'`. -/
noncomputable abbrev derivationModificationHom
    (δ : Stacks.Sites.RingSheafDerivation
      (smallEtaleRingedToposHom B S hS a').fSharpInverseImage) :
    RingedToposHom (smallEtaleRingedTopos B S hS X') (smallEtaleRingedTopos B S hS Y') :=
  RingedToposHom.ofInverseImageSharp (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS Y')
    (smallEtaleRingedToposHom B S hS a').toToposHom δ.add

/-- The modified structure map has the same underlying morphism of topoi as `a'`. -/
@[simp]
theorem derivationModificationHom_toToposHom
    (δ : Stacks.Sites.RingSheafDerivation
      (smallEtaleRingedToposHom B S hS a').fSharpInverseImage) :
    (derivationModificationHom B S hS a' δ).toToposHom =
      (smallEtaleRingedToposHom B S hS a').toToposHom := rfl

/-- **The inverse-image form of the modified structure map is the sum.**  This is what identifies
`AlgebraicGeometry.Space.derivationModificationHom` with the source's `α = (a')^♯ + D`. -/
theorem derivationModificationHom_fSharpInverseImage
    (δ : Stacks.Sites.RingSheafDerivation
      (smallEtaleRingedToposHom B S hS a').fSharpInverseImage) :
    (derivationModificationHom B S hS a' δ).fSharpInverseImage = δ.add :=
  RingedToposHom.ofInverseImageSharp_fSharpInverseImage
    (X := smallEtaleRingedTopos B S hS X') (Y := smallEtaleRingedTopos B S hS Y')
    (smallEtaleRingedToposHom B S hS a').toToposHom δ.add

/-- **The value of the modified structure map on a section** is the sum of the value of `(a')^♯`
and the value of the derivation. -/
theorem derivationModificationHom_fSharpInverseImage_apply
    (δ : Stacks.Sites.RingSheafDerivation
      (smallEtaleRingedToposHom B S hS a').fSharpInverseImage)
    (U : (SmallEtale B S hS X'.1)ᵒᵖ)
    (x : ((inverseImageCommRingFunctor
      (smallEtaleRingedToposHom B S hS a').toToposHom).obj
        (smallEtaleRingedTopos B S hS Y').O).obj.obj U) :
    (((derivationModificationHom B S hS a' δ).fSharpInverseImage).hom.app U).hom x =
      (((smallEtaleRingedToposHom B S hS a').fSharpInverseImage).hom.app U).hom x +
        δ.toFun U x := by
  rw [derivationModificationHom_fSharpInverseImage]
  exact δ.add_apply U x

/-- **Modifying by the zero derivation returns the morphism of ringed topoi of `a'`.**  For
[Stacks Project, Tag 04D0] this is the statement that the map `θ = 0` does not move `a'`. -/
theorem derivationModificationHom_zero :
    derivationModificationHom B S hS a'
        (0 : Stacks.Sites.RingSheafDerivation
          (smallEtaleRingedToposHom B S hS a').fSharpInverseImage) =
      smallEtaleRingedToposHom B S hS a' :=
  RingedToposHom.ofInverseImageSharp_zero_add (smallEtaleRingedToposHom B S hS a')

/-- **The modified structure map is locally ringed**, with nothing assumed.  The morphism of
small étale ringed topoi of `a'` is locally ringed by [Stacks Project, Tag 04KJ]
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_isLocallyRinged`, unconditional),
and a section of `𝒪_{X'}` is invertible exactly when its translate by a square-zero section is,
so the two have the same cartesian units square.

This is the `isLocallyRinged` hypothesis that [Stacks Project, Tag 05ZN] consumes, for the
modified structure map of [Stacks Project, Tag 04D0]. -/
theorem derivationModificationHom_isLocallyRinged
    (δ : Stacks.Sites.RingSheafDerivation
      (smallEtaleRingedToposHom B S hS a').fSharpInverseImage) :
    (derivationModificationHom B S hS a' δ).IsLocallyRinged := by
  haveI : Limits.HasLimitsOfShape Limits.WalkingCospan
      (Sheaf (smallEtaleRingedTopos B S hS X').J (Type u)) :=
    Limits.HasFiniteLimits.out _
  haveI : Limits.HasPullback (RingedTopos.unitsιOf (smallEtaleRingedTopos B S hS X').O)
      (RingedTopos.forgetRingMap (derivationModificationHom B S hS a' δ).fSharpInverseImage) :=
    Limits.HasLimitsOfShape.has_limit _
  exact RingedToposHom.isLocallyRinged_add (X := smallEtaleRingedTopos B S hS X')
    (Y := smallEtaleRingedTopos B S hS Y') (smallEtaleRingedToposHom B S hS a')
    (smallEtaleRingedToposHom_isLocallyRinged B S hS a') δ

end AlgebraicGeometry.Space

end
