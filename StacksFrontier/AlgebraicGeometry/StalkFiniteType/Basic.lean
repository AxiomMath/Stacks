module

public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType

/-!
# A finite type sheaf of modules on a scheme has finite stalks, and Tag 05P2 (3) ⟹ (4)

The implication (3) ⟹ (4) of Stacks Tag 05P2 — a locally free sheaf of modules of finite type
on a scheme is finite locally free — was reduced in
`StacksFrontier/AlgebraicGeometry/StalkFreeBridge/StalkFree.lean` to a single statement about
stalks: for `M : X.Modules` with `M.IsFiniteType`, every stalk `M_x` is a finite
`𝒪_{X,x}`-module. See
`Stacks.StalkFreeBridge.isFiniteLocallyFree_of_isLocallyFree_of_finite_stalk`.

That statement is **already proved** in this repository, as `SheafOfModules.finite_stalk`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Support/FiniteType.lean`), where it is used to prove
Tag 056J. It is proved there by exhibiting generators — a finite type sheaf has local generators
on some open neighbourhood of `x`, and their germs span the stalk — rather than by the route
`StacksFrontier/AlgebraicGeometry/StalkFreeBridge/StalkFree.lean` sketched (transport the
`StalkFreeBridge.Comparison` identification of
vocabularies for a structure map which is only an epimorphism, then compose with Tag 01C9's
stalk comparisons). No such transport is needed.

This file supplies the one-line vocabulary match and closes the implication.

## Main results

* `Stacks.StalkFiniteType.finite_stalk`: for `M : X.Modules` on a scheme with `M.IsFiniteType`,
  the stalk `M_x` is a finite module over `𝒪_{X,x}`, in the `AlgebraicGeometry.Scheme.Modules`
  spelling of the stalk and with the module structure that
  `Stacks.StalkFreeBridge.instModuleStalk` provides. This is the statement
  `StacksFrontier/AlgebraicGeometry/StalkFreeBridge/StalkFree.lean` records as the only step missing
  from Tag 05P2 (3) ⟹ (4).
* `Stacks.StalkFiniteType.isFiniteLocallyFree_of_isLocallyFree_of_isFiniteType`: **Stacks Tag
  05P2, the implication (3) ⟹ (4).** A locally free sheaf of modules of finite type on a
  scheme is finite locally free, stated over the tagged class
  `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`.
* `Stacks.StalkFiniteType.finiteLocallyFree_of_isLocallyFree_of_isFiniteType`: the same
  conclusion for the repository's second, untagged copy of the class,
  `Stacks.FiniteLocallyFree.IsFiniteLocallyFree`, off which the Tag 05P2 consequences already
  proved hang.

## Implementation notes

`SheafOfModules.finite_stalk` is stated for a sheaf of modules over
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj R` for `R : TopCat.Sheaf CommRingCat X`,
with the module structure on the stalk given by Mathlib's
`PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier`. For a scheme
`X` and `R := X.sheaf` that base sheaf of rings is `X.ringCatSheaf` and that module structure is
the one `Stacks.StalkFreeBridge.instModuleStalk` names, so the two statements match without any
transport; this was checked by elaboration.

## References

* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.StalkFiniteType

variable {X : Scheme.{u}}

/-- **The stalk of a finite type sheaf of modules on a scheme is a finite module** over the
local ring at that point.

This is `SheafOfModules.finite_stalk` read at the `AlgebraicGeometry.Scheme.Modules` spelling,
with the module structure `Stacks.StalkFreeBridge.instModuleStalk`; the two agree on the nose.
It is the statement that `StalkFreeBridge/StalkFree.lean` records as the only step missing from
the implication (3) ⟹ (4) of Stacks Tag 05P2. -/
theorem finite_stalk (M : X.Modules) [M.IsFiniteType] (x : X) :
    Module.Finite (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  SheafOfModules.finite_stalk X.sheaf M x

/-- **Stacks Tag 05P2, the implication (3) ⟹ (4).** A locally free sheaf of modules of finite
type on a scheme is finite locally free.

Entry (3) of the tag is `IsLocallyFree ∧ IsFiniteType` and entry (4) is `IsFiniteLocallyFree`.
The geometric content — a free chart on each member of the covering family, together with the
shrinking argument run at the stalk which forces the rank there to be finite — is
`Stacks.StalkFreeBridge.isFiniteLocallyFree_of_isLocallyFree_of_finite_stalk`; what `IsFiniteType`
contributes is exactly `finite_stalk`. -/
theorem isFiniteLocallyFree_of_isLocallyFree_of_isFiniteType (M : X.Modules)
    [SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) M] [M.IsFiniteType] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) M :=
  StalkFreeBridge.isFiniteLocallyFree_of_isLocallyFree_of_finite_stalk M (finite_stalk M)

/-- Tag 05P2 (3) ⟹ (4) for the repository's second, untagged copy of finite local freeness,
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree`. The two classes have identical bodies; the
crossing is `Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree`. -/
theorem finiteLocallyFree_of_isLocallyFree_of_isFiniteType (M : X.Modules)
    [SheafOfModules.IsLocallyFree (R := X.ringCatSheaf) M] [M.IsFiniteType] :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := X.ringCatSheaf) M :=
  have := isFiniteLocallyFree_of_isLocallyFree_of_isFiniteType M
  StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree M

end Stacks.StalkFiniteType

end
