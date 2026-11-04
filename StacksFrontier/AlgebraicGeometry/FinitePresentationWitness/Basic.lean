module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.AffineStageDescent.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.UnitDual
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Basic

/-!
# Witnesses for finite presentation of a sheaf of modules

`SheafOfModules.IsFinitePresentation` is a hypothesis of a large family of results, and its
single field is an existential over `SheafOfModules.QuasicoherentData`, so nothing about the
class itself says that any sheaf of modules satisfies it. This file registers the structure
sheaf and the finite free sheaves as instances of the class, so that `inferInstance` answers
for them, and feeds those witnesses to consumers of the class in order to exhibit non-trivial
conclusions drawn through it.

## Main results

* `isFinitePresentation_unit`, `isFinitePresentation_free`: the structure sheaf of a scheme and
  the free sheaves on a finite index type are of finite presentation. These are the
  theorems `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit` and
  `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite`, registered as
  instances.
* `isFinitePresentation_dualSheaf_unitModule`: the dual of the structure sheaf is of finite
  presentation, through the identification `𝒪_X^∨ ≅ 𝒪_X`.
* `module_isReflexive_modStalk_unitModule`: every local ring of a scheme is a reflexive module
  over itself, obtained from Tag 0AY3 at `F = 𝒪_X`.
* `nonempty_localPresentation_unit`: the structure sheaf admits section-level presentation data
  near every point, obtained from Tag 01BN at `M = 𝒪_X`.
* `exists_isFinitePresentation_pullback_unit_of_isAffine`: the structure sheaf of an affine
  scheme descends to a Noetherian stage of finite type over the integers, obtained from Tag
  01ZR (1) at `F = 𝒪_S`.

## Implementation notes

The last three results exist to show that the hypothesis sets of their sources are satisfiable,
and that the first of them is satisfiable *jointly*: Tag 0AY3 as formalized in
`StacksFrontier/AlgebraicGeometry/ReflexiveStalk/Basic.lean` asks for finite presentation of
`F` **and** of `F^∨`, and dropping either binder makes the statement below fail to elaborate
with `synthInstanceFailed`, so neither is redundant and the pair is discharged here by two
different arguments. `𝒪_X` is a witness for both at once because its dual is itself
(`Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso`); the finite free sheaves witness the
single-hypothesis consumers but not this one, since no identification of the dual of
`SheafOfModules.free ι` is in the library.

`Stacks.AlgebraicGeometry.ReflexiveModules.unitModule` is the structure sheaf written at the
type `X.Modules`, which is the spelling the reflexivity chain uses; it is interchangeable with
`SheafOfModules.unit X.ringCatSheaf` at argument positions, which is why the instance registered
at the latter spelling also serves the former.

No `stacks` attribute is attached to any declaration here. Each of the three derived statements
is one particular instance of a tag that is already carried by the general theorem it is
obtained from — 0AY3 by `isReflexive_iff_forall_modStalk`, 01BN by
`Stacks.SheafOfModules.nonempty_localPresentation` and 01ZR (1) by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isFinitePresentation_pullback_iso_of_qcqs`
— and a specialisation of a tag to one object is not the tag.

## References

* [Stacks Project, Tag 01BD](https://stacks.math.columbia.edu/tag/01BD)
* [Stacks Project, Tag 01BN](https://stacks.math.columbia.edu/tag/01BN)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace Stacks.AlgebraicGeometry.FinitePresentationWitness

/-! ### The witnesses -/

/-- The free sheaf of modules on a finite index type is of finite presentation, as an instance.
This is `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite`. -/
instance isFinitePresentation_free (X : Scheme.{u}) (ι : Type u) [Finite ι] :
    (SheafOfModules.free (R := X.ringCatSheaf) ι).IsFinitePresentation :=
  ModuleLimits.isFinitePresentation_free_of_finite X ι

/-- The structure sheaf of a scheme, viewed as a module over itself, is of finite presentation,
as an instance. This is `Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_unit`. -/
instance isFinitePresentation_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  ModuleLimits.isFinitePresentation_unit X

/-- The dual of the structure sheaf is of finite presentation: it is the structure sheaf, by
`Stacks.AlgebraicGeometry.ReflexiveModules.unitDualIso`, and finite presentation only depends on
the isomorphism class. -/
instance isFinitePresentation_dualSheaf_unitModule (X : Scheme.{u}) :
    (dualSheaf (unitModule X)).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso (unitDualIso X).symm
    (ModuleLimits.isFinitePresentation_unit X)

/-! ### Conclusions drawn through consumers of the class -/

/-- **The local ring of a scheme at a point is a reflexive module over itself.** This is Tag
0AY3's equivalence, `Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_iff_forall_modStalk`,
applied to `F = 𝒪_X`, whose two finite-presentation hypotheses are discharged by
`isFinitePresentation_unit` and `isFinitePresentation_dualSheaf_unitModule`, and whose
reflexivity hypothesis is
`Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_unit`. -/
theorem module_isReflexive_modStalk_unitModule (X : Scheme.{u}) (x : X) :
    Module.IsReflexive (ringStalk X.sheaf x) (modStalk (unitModule X) x) :=
  (isReflexive_iff_forall_modStalk (unitModule X)).mp (isReflexive_unit X) x

/-- **The structure sheaf has section-level presentation data near every point.** This is Tag
01BN, `Stacks.SheafOfModules.nonempty_localPresentation`, applied to `M = 𝒪_X`. -/
theorem nonempty_localPresentation_unit (X : Scheme.{u}) (x : X) :
    Nonempty (Stacks.SheafOfModules.LocalPresentation
      (SheafOfModules.unit X.ringCatSheaf) x) :=
  Stacks.SheafOfModules.nonempty_localPresentation _ x

/-- **The structure sheaf of an affine scheme descends to a Noetherian stage.** This is Tag
01ZR (1) in the form
`AlgebraicGeometry.exists_isFinitePresentation_pullback_of_isAffine`, applied to `F = 𝒪_S`. -/
theorem exists_isFinitePresentation_pullback_unit_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    ∃ (T : Scheme.{u}) (q : S ⟶ T) (G : T.Modules),
      IsAffine T ∧ IsNoetherian T ∧ LocallyOfFiniteType (terminal.from T) ∧
        G.IsFinitePresentation ∧
          Nonempty ((SheafOfModules.unit S.ringCatSheaf : S.Modules) ≅
            (Scheme.Modules.pullback q).obj G) :=
  _root_.AlgebraicGeometry.exists_isFinitePresentation_pullback_of_isAffine S
    (SheafOfModules.unit S.ringCatSheaf)

end Stacks.AlgebraicGeometry.FinitePresentationWitness

end
