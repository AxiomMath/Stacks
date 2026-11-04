module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Composition
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionUnconditional
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of derived pullbacks, with no resolving datum left over

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
`StacksDraft.Ch20.Sec27Pullback.Tag0D5S` proves the composition formula for derived pullback
relative to two classes of complexes `P` on `Z` and `Q` on `Y` and five hypotheses about them.
This file discharges all five at the K-flat classes, so Tag 0D5S holds for the canonical derived
pullbacks `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback` with no hypothesis
  beyond the two morphisms.

The five inputs and their suppliers:

* `hP`, that the K-flat complexes of `𝒪_Z`-modules resolve every complex, is
  `Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat`;
* `hinvgf`, that degreewise pullback along `f ≫ g` inverts the quasi-isomorphisms between
  K-flat complexes, is
    `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat`;
* `hstab`, stability of K-flatness under degreewise pullback along `g`, is Tag 06YC, as
  `Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_unconditional`;
* `hεg` and `hεf`, invertibility of the two comparison maps on the K-flat classes, are
  `Stacks.DerivedPullback.Composition.isIso_app_of_resolving` at the same two suppliers.

## Main definitions

* `Stacks.DerivedPullback.Composition.derivedPullbackCompComparisonCanonical` is the canonical
  comparison
  `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` between the canonical derived pullbacks.
* `Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical` is the resulting natural
  isomorphism.

Everything below that mentions a derived category carries the `HasDerivedCategory` binders, so
it holds at an arbitrary model of the three categories rather than only at
`HasDerivedCategory.standard`: a consumer working at another model — the locally small one of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, say — reads these off directly.

## Main results

* `Stacks.DerivedPullback.Composition.isKFlat_pullback`: degreewise pullback carries the K-flat
  class on `Z` into the
  K-flat class on `Y`, read on the unbounded homotopy categories.
* `Stacks.DerivedPullback.Composition.isIso_derivedPullbackComparison_app_of_isKFlat`: the
  canonical comparison for
  `Lf^*` is invertible at every K-flat complex.
* `Stacks.DerivedPullback.Composition.isIso_derivedPullbackCompComparisonCanonical`: **Stacks
  0D5S**, with no
  hypotheses.

## Implementation notes

*Why the comparison keeps its parametric definition.*  Everything below instantiates the
declarations of `StacksDraft.Ch20.Sec27Pullback.Tag0D5S` rather than restating them, so there is
one comparison map in the development and the unconditional statement is literally about it.

*The orientation.*  `Stacks.DerivedPullback.Composition.modulePullbackComp` reads left to right
  along the composite,
`g^* ⋙ f^* ≅ (f ≫ g)^*`, and the comparison inherits that direction:
`Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*`.

*Crossing the two spellings of the sheaf of rings.*  `structureSheafRing Y`
and `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf` are `rfl`-equal but the first is a `def`, so
  the passage
is made inside term-mode proofs, where the conversion check runs at default transparency; this
is the same device as in `StacksDraft.Ch20.Sec27Pullback.Tag06YJ`.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

namespace Stacks.DerivedPullback.Composition

universe w₁ w₂ w₃ u

noncomputable section

variable {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **Stacks 06YC on the homotopy category.**  Degreewise pullback along `g` carries the K-flat
class on `Z` into the K-flat class on `Y`.

This is the hypothesis `hstab` of the composition formula.  Nothing happens on passage to the
homotopy category: the underlying complex of `K(g^*) K` is `g^*` of the underlying complex of
`K`, so the statement is Tag 06YC at `K.as`. -/
theorem isKFlat_pullback (K : HomotopyCategory (ModuleSheaves Z) (ComplexShape.up ℤ))
    (hK : Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Z K) :
    Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y
      (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) :=
  Stacks.SheafOfModules.KFlatPullback.kFlat_pullback_unconditional g K.as hK

section

variable [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]

/-- The canonical comparison `Q ⋙ Lf^* ⟶ K(f^*)` is invertible at every K-flat complex of
`𝒪_Y`-modules, at an arbitrary model of the two derived categories.

This is the hypotheses `hεg` and `hεf` of the composition formula: `isIso_app_of_resolving` at
the resolving datum of Tags 06YJ and 079W. -/
theorem isIso_derivedPullbackComparison_app_of_isKFlat
    (M : HomotopyCategory (ModuleSheaves Y) (ComplexShape.up ℤ))
    (hM : Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y M) :
    IsIso ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f).app M) :=
  isIso_app_of_resolving f (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
      (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Y)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat f) M hM

end

section

variable [HasDerivedCategory.{w₁} (ModuleSheaves X)] [HasDerivedCategory.{w₂} (ModuleSheaves Y)]
  [HasDerivedCategory.{w₃} (ModuleSheaves Z)]

/-- The canonical comparison `Lg^* ⋙ Lf^* ⟶ L(f ≫ g)^*` between the canonical derived
pullbacks of Stacks 06YJ, which exist for every morphism of ringed spaces, at an arbitrary
model of the three derived categories. -/
abbrev derivedPullbackCompComparisonCanonical :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ⟶
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g) :=
  derivedPullbackCompComparison f g
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))

/-- **Stacks 0D5S.**  The canonical comparison from the composite of the derived pullbacks along
`g` and `f` to the derived pullback along `f ≫ g` is an isomorphism, for arbitrary composable
morphisms of ringed spaces.

Every hypothesis of `isIso_derivedPullbackCompComparison` is met at the K-flat classes on `Z`
and on `Y`. -/
@[stacks 0D5S]
theorem isIso_derivedPullbackCompComparisonCanonical :
    IsIso (derivedPullbackCompComparisonCanonical f g) :=
  isIso_derivedPullbackCompComparison f g
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Z)
      (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Z)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat (f ≫ g))
    (isKFlat_pullback g)
    (isIso_derivedPullbackComparison_app_of_isKFlat g)
    (isIso_derivedPullbackComparison_app_of_isKFlat f)

/-- The natural isomorphism `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*` between the canonical derived pullbacks,
for arbitrary composable morphisms of ringed spaces. -/
def derivedPullbackCompIsoCanonical :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g ⋙
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g) :=
  derivedPullbackCompIso f g (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback (f ≫ g))
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison f)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison g)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison (f ≫ g))
    (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Z)
      (Stacks.Cohomology.KFlatDerivedPullback.IsKFlat Y)
    (Stacks.Cohomology.KFlatDerivedPullback.hasResolutions_isKFlat Z)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pullbackInvertsQuasiIso_isKFlat (f ≫ g))
    (isKFlat_pullback g)
    (isIso_derivedPullbackComparison_app_of_isKFlat g)
    (isIso_derivedPullbackComparison_app_of_isKFlat f)

/-- The underlying map of `derivedPullbackCompIsoCanonical` is the canonical comparison. -/
@[simp]
theorem derivedPullbackCompIsoCanonical_hom :
    (derivedPullbackCompIsoCanonical f g).hom = derivedPullbackCompComparisonCanonical f g :=
  rfl

end

end

end Stacks.DerivedPullback.Composition

end
