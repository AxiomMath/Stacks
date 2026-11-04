module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.CoextendRestrictComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedHomAnyModel
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext

/-!
# Tag 0A71 with both derived functors constructed

Let `f : A →+* B` be a homomorphism of commutative rings. Tag 0A71 compares two derived
functors: `RHom(B, -) : D(A) ⥤ D(B)`, read in `D(A)` through restriction of scalars, and the
`A`-valued functor `RHom_A(B, -) : D(A) ⥤ D(A)`. In
`Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso` and
`Dualizing.derivedCoextendScalarsHomologyLinearEquivExt` they enter as *arbitrary* right derived
functors, presented by their universal properties. This file discharges that data: both
functors exist, by the K-injective existence lemma applied to coextension of scalars and to
`Hom_A(B, -)` respectively, and the comparison and the identification of its cohomology with Ext
are stated unconditionally at the constructed pair.

## Main definitions

* `Dualizing.AnyModel.derivedHomUnit` — the structural transformation exhibiting
  `Dualizing.AnyModel.derivedHom f` as a right derived functor of coextension of scalars.

## Main results

* `Dualizing.restrictDerivedHomIsoDerivedHomAlong` — **Tag 0A71**, first assertion, with no
  assumed functor: `φ_* RHom(B, -) = RHom_A(B, -)`, for the constructed
  `Dualizing.AnyModel.derivedHom f` and `Dualizing.derivedHomAlong f`, by the unique
  isomorphism compatible with the two derived units.
* `Dualizing.derivedHomHomologyLinearEquivExt` — **Tag 0A71**, the "in particular" clause, with
  no assumed functor: `R^q Hom(B, K) = Ext^q_A(B, K)`, `A`-linearly, naturally in `K` and
  normalized by the derived unit.

## Implementation notes

The target `RHom_A(B, -)` is `Dualizing.derivedHomAlong`, the total right derived functor of
`Hom_A(B, -)` read in `D(A)`; its existence is
`Dualizing.homAlongToDerivedCategory_hasPointwiseRightDerivedFunctor`, the K-injective existence
lemma applied to `Dualizing.homAlongToDerivedCategory`. The source `RHom(B, -)` is
`Dualizing.AnyModel.derivedHom`, the total right derived functor of coextension of scalars; its
existence is `Dualizing.AnyModel.coextendScalars_hasPointwiseRightDerivedFunctor`, the same
lemma applied to coextension of scalars. The model-generic `Dualizing.AnyModel.derivedHom` is
used rather than `Dualizing.derivedHom`, which is silently specialised to
`HasDerivedCategory.standard`, so that the statements below keep the arbitrary models and the
independent morphism universes of the parameterised forms they instantiate.

Both rings are taken in a single universe `u` and the modules in `max v u`, which is the setting
of the parameterised statements being instantiated; nothing else is specialised.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public section

open CategoryTheory

universe u v wA wB

namespace Dualizing

noncomputable section

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]

namespace AnyModel

/-- The structural transformation exhibiting `Dualizing.AnyModel.derivedHom f` as a right derived
functor of coextension of scalars: its total-derived unit. -/
def derivedHomUnit (f : A →+* B) :
    coextendScalarsToDerivedCategory.{u, v, wB} f ⟶
      DerivedCategory.Qh ⋙ AnyModel.derivedHom.{u, v, u, wA, wB} f :=
  (coextendScalarsToDerivedCategory.{u, v, wB} f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))

/-- The constructed derived Hom functor has the right-derived universal property for its
total-derived unit, in any chosen models of the two derived categories. Model-generic form of
`Dualizing.derivedHom_isRightDerivedFunctor`. -/
instance derivedHom_isRightDerivedFunctor (f : A →+* B) :
    (derivedHom.{u, v, u, wA, wB} f).IsRightDerivedFunctor
      (AnyModel.derivedHomUnit.{u, v, wA, wB} f)
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) := by
  dsimp [derivedHom, derivedHomUnit]
  infer_instance

end AnyModel

/-- **Stacks 0A71**, the displayed formula, with both derived functors constructed:
`φ_* RHom(B, K) = RHom_A(B, K)`, where `φ_* : D(B) ⥤ D(A)` is restriction of scalars.

Restricting the constructed derived coextension functor `Dualizing.AnyModel.derivedHom f` to
`D(A)` is the constructed `A`-valued derived Hom functor `Dualizing.derivedHomAlong f`, by the
unique isomorphism compatible with the two derived units. This is
`Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso` with all four of its parameters
discharged: `RH`, `β` by `Dualizing.derivedHomAlong`, `Dualizing.derivedHomAlongUnit`, and
`RF`, `α` by `Dualizing.AnyModel.derivedHom`, `Dualizing.AnyModel.derivedHomUnit`. -/
@[stacks 0A71 "derived Hom after restriction, with both derived functors constructed: \
RHom(B, -) is AnyModel.derivedHom, the total right derived functor of coextension of scalars, \
and RHom_A(B, -) is derivedHomAlong, that of Hom_A(B, -). Both rings in one universe, modules \
in max v u, arbitrary models of the two derived categories"]
def restrictDerivedHomIsoDerivedHomAlong (f : A →+* B) :
    { e : AnyModel.derivedHom.{u, v, u, wA, wB} f ⋙
          (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ≅
        derivedHomAlong.{u, v, wA} f //
      restrictedDerivedUnit f (AnyModel.derivedHom.{u, v, u, wA, wB} f)
            (AnyModel.derivedHomUnit.{u, v, wA, wB} f) ≫
          Functor.whiskerLeft DerivedCategory.Qh e.hom =
        derivedHomAlongUnit.{u, v, wA} f } :=
  restrictDerivedCoextendIsoDerivedHomAlong f (AnyModel.derivedHom.{u, v, u, wA, wB} f)
    (AnyModel.derivedHomUnit.{u, v, wA, wB} f)

/-- **Stacks 0A71**, the "in particular" clause, with the derived functor constructed:
`R^q Hom(B, K) = Ext^q_A(B, K)`.

The cohomology of the constructed derived coextension functor `Dualizing.AnyModel.derivedHom f`,
restricted to `A`-modules, is `Ext^q_A(B, K)`, `A`-linearly, naturally in `K` and normalized by
the derived unit. This is `Dualizing.derivedCoextendScalarsHomologyLinearEquivExt` with its
parameters `RF`, `α` discharged by `Dualizing.AnyModel.derivedHom` and
`Dualizing.AnyModel.derivedHomUnit`. -/
@[stacks 0A71 "cohomology as Ext, with the derived functor constructed: RHom(B, -) is \
AnyModel.derivedHom, the total right derived functor of coextension of scalars. Both rings in \
one universe, modules in max v u, arbitrary models of the two derived categories"]
def derivedHomHomologyLinearEquivExt (f : A →+* B) :
    HomologyExtComparison f (AnyModel.derivedHom.{u, v, u, wA, wB} f)
      (AnyModel.derivedHomUnit.{u, v, wA, wB} f) :=
  derivedCoextendScalarsHomologyLinearEquivExt f (AnyModel.derivedHom.{u, v, u, wA, wB} f)
    (AnyModel.derivedHomUnit.{u, v, wA, wB} f)

end

end Dualizing

end
