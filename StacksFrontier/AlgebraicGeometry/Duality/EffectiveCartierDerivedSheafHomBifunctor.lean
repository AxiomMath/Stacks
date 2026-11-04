module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.EffectiveCartierDerivedSheafHomPushforward
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor

/-!
# The comparison morphism of Tag 0B4B in the derived internal Hom bifunctor

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor with closed immersion `i : D ⟶ X`.
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDerivedSheafHomPushforward.lean` reduces
the isomorphism assertion of [Stacks, Tag 0B4B] to the assertion that

`α : Ri_*(𝒩[-1]) ⟶ R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)`

is an isomorphism, where the right-hand side is the *total right derived functor* of
`ℰom_{𝒪_X}(i_* 𝒪_D, -)` evaluated at `𝒪_X`. The computation of that object from the ideal
sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` happens in the *source* variable, so it needs the
right-hand side as a value of the derived internal Hom **bifunctor** `R ℰom(-, -)` of
[Stacks, Tag 08DH], where the source is an object of `D(𝒪_X)` that a resolution can be
substituted for. This file is that change of model.

## The two models of Tag 0A77

Both forms of [Stacks, Tag 0A77] are in the library, and they share a source:

* `…derivedModulePushforwardDerivedSheafHomExactSupportIso`, the right-derived-functor form
  `Ri_* R ℰom(𝒪_D, -) ≅ R ℰom_{𝒪_X}(i_* 𝒪_D, -)`, and
* `…derivedSheafHomExactSupportPushforwardNatIso`, the bifunctor form
  `Ri_* R ℰom(𝒪_D, -) ≅ R ℰom(Ri_* 𝒪_D, -)`.

Composing the first backwards with the second therefore identifies the two targets, with no new
mathematics: that is
`…derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom` below. The in-file note of
`EffectiveCartierDerivedSheafHom.lean` lists the computation of `R ℰom_{𝒪_X}(i_* 𝒪_D, 𝒪_X)` as
owed and names [Stacks, Tag 08I0] and the representation theorem [Stacks, Tag 08JH] as the
inputs; both are statements about the bifunctor, and this identification is what makes them
applicable to `α`.

## Main definitions

* `derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom`, in the namespace
  `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`: the identification
  `R ℰom_{𝒪_X}(i_* 𝒪_Z, -) ≅ R ℰom(Ri_* 𝒪_Z, -)` of the two models.
* `Stacks.Divisors.pushforwardNormalShiftToDerivedSheafHom`: the morphism `α` of
  [Stacks, Tag 0B4B] read in the bifunctor,
  `Ri_*(𝒩[-1]) ⟶ R ℰom(Ri_* 𝒪_D, 𝒪_X)`.
* `Stacks.Divisors.derivedSheafHomEvaluationAtOne`: the map `R ℰom(Ri_* 𝒪_D, 𝒪_X) ⟶ 𝒪_X`
  induced by the unit `𝒪_X ⟶ i_* 𝒪_D`, read in the bifunctor.

## Main results

* `Stacks.Divisors.isIso_normalShiftToDerivedSheafHomExactSupport_iff_derivedSheafHom` and
  `Stacks.Divisors.isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_derivedSheafHom`:
  the isomorphism assertion of [Stacks, Tag 0B4B] is equivalent to the assertion that the
  bifunctor form of `α` is an isomorphism.
* `Stacks.Divisors.pushforwardNormalShiftToDerivedSheafHom_comp_derivedSheafHomEvaluationAtOne`:
  the bifunctor form of `α`, followed by the evaluation at one, is still the morphism
  `ψ : Ri_*(𝒩[-1]) ⟶ 𝒪_X` determined by the normal extension class. This is the identity that
  transports the comparison morphism, now on the side where the ideal sequence can be used.

## References

* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 08DH](https://stacks.math.columbia.edu/tag/08DH)
* [Stacks Project, Tag 08I0](https://stacks.math.columbia.edu/tag/08I0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- **The two models of [Stacks, Tag 0A77] agree.** The total right derived functor
`R ℰom_{𝒪_X}(i_* 𝒪_Z, -)` of the internal Hom from the pushed-forward structure sheaf is the
derived internal Hom bifunctor `R ℰom(-, -)` of [Stacks, Tag 08DH] with its source variable at
`Ri_* 𝒪_Z`.

Both are identified with `Ri_* R ℰom(𝒪_Z, -)` by a form of [Stacks, Tag 0A77]; this is
the composite of the two identifications, and introduces nothing. It is what lets a computation
in the *source* variable — a resolution substituted for `i_* 𝒪_Z`, as in [Stacks, Tag 08I0] or
the representation theorem of [Stacks, Tag 08JH] — reach a statement about the right derived
functor. -/
def derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom :
    S.derivedHomSheafFromPushforwardStructureSheaf ≅
      (Stacks.SheafOfModules.derivedSheafHom S.X.sheaf).obj
        (op ((modulePushforward S.i).mapDerivedCategory.obj
          (RingedSite.derivedStructureSheaf (Stacks.SheafOfModules.ringedSite S.Z.sheaf)))) :=
  S.derivedModulePushforwardDerivedSheafHomExactSupportIso.symm ≪≫
    S.derivedSheafHomExactSupportPushforwardNatIso

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- The object `R ℰom(Ri_* 𝒪_D, 𝒪_X)` of `D(𝒪_X)`: the value of the derived internal Hom
bifunctor of [Stacks, Tag 08DH] at the derived pushforward of the structure sheaf of `D` and at
`𝒪_X`. This is the object the ideal sequence `0 ⟶ ℐ_D ⟶ 𝒪_X ⟶ i_* 𝒪_D ⟶ 0` computes. -/
abbrev derivedSheafHomPushforwardStructureSheaf : DerivedCategory X.Modules :=
  ((Stacks.SheafOfModules.derivedSheafHom (closedQuotient D).X.sheaf).obj
    (op ((modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
      (RingedSite.derivedStructureSheaf
        (Stacks.SheafOfModules.ringedSite (closedQuotient D).Z.sheaf))))).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))

/-- **The morphism `α` of [Stacks, Tag 0B4B] read in the derived internal Hom bifunctor:**

`Ri_*(𝒩[-1]) ⟶ R ℰom(Ri_* 𝒪_D, 𝒪_X)` in `D(𝒪_X)`.

This is `Stacks.Divisors.pushforwardNormalShiftToDerivedHomSheaf` followed by the identification
of the two models of [Stacks, Tag 0A77]. The source computes `R ℰom(Ri_* 𝒪_D, 𝒪_X)` from the
ideal sequence, which is a computation in the source variable of the bifunctor; this is the
form in which that computation can see the comparison morphism. -/
def pushforwardNormalShiftToDerivedSheafHom :
    (modulePushforward (closedQuotient D).i).mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor D.subscheme.Modules 1).obj
          ((Scheme.Modules.pullback D.subschemeι).obj (divisorSheaf D))) ⟶
      derivedSheafHomPushforwardStructureSheaf D :=
  pushforwardNormalShiftToDerivedHomSheaf D ≫
    (closedQuotient D).derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom.hom.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))

/-- The map `R ℰom(Ri_* 𝒪_D, 𝒪_X) ⟶ 𝒪_X` induced by the unit `𝒪_X ⟶ i_* 𝒪_D`, read in the
derived internal Hom bifunctor: the derived evaluation at one of [Stacks, Tag 0B6M] carried
across the identification of the two models of [Stacks, Tag 0A77]. -/
def derivedSheafHomEvaluationAtOne :
    derivedSheafHomPushforwardStructureSheaf D ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X) :=
  (closedQuotient D).derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom.inv.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)) ≫
    (closedQuotient D).derivedEvaluationAtOne.app
      ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))

/-- **The comparison morphism of [Stacks, Tag 0B4B] in the bifunctor, followed by the evaluation
at one, is `ψ`.** The morphism `Ri_*(𝒩[-1]) ⟶ 𝒪_X` determined by the normal extension class is
recovered from the bifunctor form of `α` exactly as it is from `α` itself; the two differ by the
identification of the two models of [Stacks, Tag 0A77], which cancels.

This is the identity that transports the comparison morphism of [Stacks, Tag 0B4B] — defined on
the `D` side as an adjunct — onto the side where the ideal sequence computes. -/
theorem pushforwardNormalShiftToDerivedSheafHom_comp_derivedSheafHomEvaluationAtOne :
    pushforwardNormalShiftToDerivedSheafHom D ≫ derivedSheafHomEvaluationAtOne D =
      pushforwardNormalShiftToStructureSheaf D := by
  rw [pushforwardNormalShiftToDerivedSheafHom, derivedSheafHomEvaluationAtOne]
  exact (Category.assoc _ _ _).trans
    ((congrArg (pushforwardNormalShiftToDerivedHomSheaf D ≫ ·)
      (Iso.hom_inv_id_app_assoc _ _ _)).trans
      (pushforwardNormalShiftToDerivedHomSheaf_comp_derivedEvaluationAtOne D))

/-- **The isomorphism assertion of [Stacks, Tag 0B4B] is equivalent to an assertion about the
derived internal Hom bifunctor.** The canonical comparison morphism
`𝒩[-1] ⟶ R ℰom(𝒪_D, 𝒪_X)` is an isomorphism if and only if its bifunctor form
`Ri_*(𝒩[-1]) ⟶ R ℰom(Ri_* 𝒪_D, 𝒪_X)` is.

This is `Stacks.Divisors.isIso_normalShiftToDerivedSheafHomExactSupport_iff` followed by the
identification of the two models of [Stacks, Tag 0A77]. -/
theorem isIso_normalShiftToDerivedSheafHomExactSupport_iff_derivedSheafHom :
    IsIso (normalShiftToDerivedSheafHomExactSupport D) ↔
      IsIso (pushforwardNormalShiftToDerivedSheafHom D) :=
  (isIso_normalShiftToDerivedSheafHomExactSupport_iff D).trans
    (isIso_comp_right_iff _ ((closedQuotient
      D).derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom.app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))).hom).symm

/-- **The isomorphism assertion of [Stacks, Tag 0B4B] for the comparison morphism written with
the normal sheaf** is equivalent to the same assertion about the derived internal Hom
bifunctor. -/
theorem isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff_derivedSheafHom :
    IsIso (normalSheafShiftToDerivedSheafHomExactSupport D) ↔
      IsIso (pushforwardNormalShiftToDerivedSheafHom D) :=
  (isIso_normalSheafShiftToDerivedSheafHomExactSupport_iff D).trans
    (isIso_comp_right_iff _ ((closedQuotient
      D).derivedHomSheafFromPushforwardStructureSheafIsoDerivedSheafHom.app
        ((DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X))).hom).symm

end Stacks.Divisors

end
