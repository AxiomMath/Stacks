module

public import StacksFrontier.AlgebraicGeometry.Perfect.TorDimension
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TorAmplitudeStalkwise
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 09U9 in the Stacks 08CG spelling of Tor amplitude

`AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk` proves Stacks 09U9 for a
derived tensor product given as a bifunctor on `D(O)`. This file restates it for the certificate
bundle `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` of Stacks 08CG.

## Main results

* `RingedSpace.CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_iff_forall_stalk`:
  the Stacks 09U9 equivalence for the Stacks 08CG predicate on `OXMod X`, for an arbitrary
  certificate and arbitrary stalk-level bifunctors. The unconditional Stacks 09U9, which carries
  the tag, is `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_forall_stalk`.

## Implementation notes

The restatement holds definitionally: `OXMod X` is
`SheafOfModules (StrictlyPerfect.structureSheafOfRings X)`, so
`AlgebraicGeometry.SheafOfModules.stalkFunctor` applies to it unchanged, and
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn` is
`CategoryTheory.DerivedCategory.HasTorAmplitudeIn` at the certificate's `derivedTensor` field.

## References

* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ x : X.carrier, HasDerivedCategory.{d'} (ModuleCat.{u}
    (TopCat.Presheaf.stalk (C := RingCat.{u}) (structureSheafOfRings X).obj x))]

/-- An object `E` of `D(𝒪_X)` has Tor amplitude in `[a, b]` with respect to the derived tensor
product carried by the certificate `D` exactly when, for every point `x`, the stalk `E_x` has
Tor amplitude in `[a, b]` with respect to `T' x` on `D(𝒪_{X, x})`, provided taking stalks carries
the sheaf-level derived tensor product to the stalk-level one (`hstalk`). -/
public theorem hasTorAmplitudeIn_iff_forall_stalk
    (D : CertifiedDerivedSheafTensoring.{d, u} X)
    (T' : ∀ x : X.carrier,
      DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings X).obj x)) ⥤
        DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
          (structureSheafOfRings X).obj x)) ⥤
          DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u})
            (structureSheafOfRings X).obj x)))
    (hstalk : ∀ (x : X.carrier) (E : DerivedCategory (OXMod.{u, u} X))
        (F : OXMod.{u, u} X),
      ((T' x).obj ((SheafOfModules.stalkFunctor (structureSheafOfRings X) x
            ).mapDerivedCategory.obj E)).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((SheafOfModules.stalkFunctor (structureSheafOfRings X) x).obj F)) ≅
        (SheafOfModules.stalkFunctor (structureSheafOfRings X) x).mapDerivedCategory.obj
          ((D.derivedTensor.obj E).obj ((DerivedCategory.singleFunctor _ 0).obj F)))
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    D.HasTorAmplitudeIn E a b ↔
      ∀ x : X.carrier, CategoryTheory.DerivedCategory.HasTorAmplitudeIn (T' x)
        ((SheafOfModules.stalkFunctor (structureSheafOfRings X) x).mapDerivedCategory.obj E)
        a b :=
  SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk (structureSheafOfRings X)
    D.derivedTensor T' hstalk E a b

end AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring

end
