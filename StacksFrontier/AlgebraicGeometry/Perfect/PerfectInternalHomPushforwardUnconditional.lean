module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectInternalHomPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforwardDerivedTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0DJR: the derived direct image of a derived internal Hom, unconditionally

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` a perfect
object of `D(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with
support proper over `S`.  Then `Rf_*RSheafHom(E, 𝒢)` is a perfect object of `D(𝒪_S)`
([Stacks, Tag 0DJR]).  Nothing is carried here.

## Main results

* `Stacks.Cohomology.PerfectInternalHomPushforward.derivedSheafHomObjIsoDualTensor`:
  `E^∨ ⊗^L 𝒢 ≅ RSheafHom(E, 𝒢)` for perfect `E`, the second assertion of [Stacks, Tag 08DQ]
  through the canonical map of [Stacks, Tag 08I1], read at the derived tensor product of
  [Stacks, Tag 06YU] after the commutativity constraint of [Stacks, Tag 0FPT].
* `isPerfect_derivedPushforward_derivedSheafHom_of_flatProperSupport`:
  **[Stacks, Tag 0DJR].**

## The proof

The source's: choose the dual `E^∨`, which is perfect by [Stacks, Tag 08DQ]
(`Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace`), rewrite
`RSheafHom(E, 𝒢) = E^∨ ⊗^L 𝒢`
(`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfectSpace`), and apply
[Stacks, Tag 0DJQ]
(`Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect`,
at the canonical derived tensor product of [Stacks, Tag 06YU]).

## References

* [Stacks Project, Tag 0DJR](https://stacks.math.columbia.edu/tag/0DJR)
* [Stacks Project, Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open StrictlyPerfect
open Stacks.Cohomology.ProperSupportPerfection (derivedPushforwardOX)
open Stacks.Cohomology.PerfectPushforward (FlatProperSupportComplex)

namespace Stacks.Cohomology.PerfectInternalHomPushforward

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings StrictlyPerfect.structureModule

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`E^∨ ⊗^L 𝒢 ≅ RSheafHom(E, 𝒢)` for a perfect `E`** ([Stacks, Tag 08DQ]): the commutativity
constraint of [Stacks, Tag 0FPT], the comparison of the two canonical derived tensor products,
and the canonical map of [Stacks, Tag 08I1], which is invertible for perfect `E`. -/
def derivedSheafHomObjIsoDualTensor (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
        (Stacks.SheafOfModules.derivedDual X.toRingedSpace.sheaf E)).obj
        (DerivedCategory.Q.obj G) ≅ derivedSheafHomObj (X := X) E G :=
  (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso
      (Stacks.SheafOfModules.ringedSite X.toRingedSpace.sheaf)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf) _ _) ≪≫
    (AlgebraicGeometry.RingedSite.derivedTensorObjIso
      (Stacks.SheafOfModules.ringedSite X.toRingedSpace.sheaf) _ _).symm ≪≫
    @asIso _ _ _ _ (Stacks.SheafOfModules.derivedTensorDualToSheafHom X.toRingedSpace.sheaf E
      (DerivedCategory.Q.obj G))
      (Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfectSpace
        X.toRingedSpace E (DerivedCategory.Q.obj G) hE)

/-- **[Stacks, Tag 0DJR].**  Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of
finite type, `E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded complex of coherent
`𝒪_X`-modules, flat over `S`, with support proper over `S`.  Then `Rf_*RSheafHom(E, 𝒢)` is a
perfect object of `D(𝒪_S)`, with `Rf_*` the derived direct image
`Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX f`.

The source's proof: `E^∨` is perfect and `RSheafHom(E, 𝒢) ≅ E^∨ ⊗^L 𝒢` by [Stacks, Tag 08DQ]
(`derivedSheafHomObjIsoDualTensor`), and [Stacks, Tag 0DJQ] applies to `(E^∨, 𝒢)`. -/
@[stacks 0DJR]
theorem isPerfect_derivedPushforward_derivedSheafHom_of_flatProperSupport [IsNoetherian S]
    [LocallyOfFiniteType f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) (hG : FlatProperSupportComplex f G) :
    RingedSpace.IsPerfect (X := S.toRingedSpace)
      ((derivedPushforwardOX f).obj (derivedSheafHomObj (X := X) E G)) :=
  (Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect f
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf)
      _ G (Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace X.toRingedSpace E hE)
      hG).of_iso
    ((derivedPushforwardOX f).mapIso (derivedSheafHomObjIsoDualTensor E G hE))

end Stacks.Cohomology.PerfectInternalHomPushforward

end
