module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroExactness

/-!
# Extension by zero along a relocalization `C/V ⥤ C/U`

Let `R` be a sheaf of rings on a site `(C, J)` and let `f : V ⟶ U` be an arrow of `C`.
Restriction of sheaves of modules along the relocalization functor `Over.map f : C/V ⥤ C/U` is
`SheafOfModules.overMap R f`. It has a left adjoint, extension by zero, and that left adjoint
is exact.

Both statements come from the corresponding ones for a localization `C/W ⥤ C` — Stacks 03DI
and 03DJ — applied to the site `C/U` and its object `Over.mk f`, because `Over.map f` factors
as the equivalence `CategoryTheory.Over.iteratedSliceBackward : C/V ⥤ (C/U)/(Over.mk f)`
followed by the localization `Over.forget (Over.mk f) : (C/U)/(Over.mk f) ⥤ C/U`. That
factorization is an *equality* of restriction functors on sheaves of modules, namely
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward`, so the left adjoints agree up to the
equivalence `Stacks.SheafOfModules.sliceEquiv`, and an equivalence is exact.

## Main definitions

* `Stacks.Sites.ExtensionByZero.overMapExtensionByZeroIso`: extension by zero along
  `Over.map f` is, up to the slice equivalence, extension by zero along the localization of
  `C/U` at `Over.mk f`.

## Main results

* `Stacks.Sites.ExtensionByZero.overMap_isRightAdjoint`: restriction along `Over.map f` has a
  left adjoint.
* `Stacks.Sites.ExtensionByZero.overMap_extensionByZero_exact`: **that left adjoint is exact.**

## Implementation notes

`SheafOfModules.overMap R f` is Mathlib's restriction along `Over.map f`, whose structure map
is `Sheaf.pushforwardOverMapIso`; that map is the identity of `R.over V` on the nose, so the
statements below are phrased with `𝟙 (R.over V)`, which is the form a consumer splitting a
restriction with `SheafOfModules.pushforwardComp` produces.

Existence of the left adjoint has to be established before `SheafOfModules.pullback` can be
written down at all, so it precedes the comparison isomorphism and is what the latter's
`Adjunction.leftAdjointUniq` is applied to.

## References

* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
* [Stacks Project, Tag 03DJ](https://stacks.math.columbia.edu/tag/03DJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.ExtensionByZero

universe u

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  (R : Sheaf J RingCat.{u}) {U V : C} (f : V ⟶ U)
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Extension by zero along `Over.map f`, composed from the slice equivalence and extension by
zero along the localization of `C/U` at `Over.mk f`, is left adjoint to restriction along
`Over.map f`. The right adjoint is a composite because
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward` makes `SheafOfModules.overMap R f` one
on the nose. -/
noncomputable def overMapExtensionByZeroAdjunction :
    (Stacks.SheafOfModules.sliceEquiv R U (Over.mk f)).functor ⋙
        SheafOfModules.pullback.{u} (F := Over.forget (Over.mk f))
          (𝟙 ((R.over U).over (Over.mk f))) ⊣
      SheafOfModules.overMap.{u} R f :=
  (Stacks.SheafOfModules.sliceEquiv R U (Over.mk f)).toAdjunction.comp
    (SheafOfModules.pullbackPushforwardAdjunction (𝟙 ((R.over U).over (Over.mk f))))

/-- **Stacks 03DI for a relocalization.** Restriction of sheaves of modules along
`Over.map f : C/V ⥤ C/U` has a left adjoint. -/
@[stacks 03DI "extension by zero along a relocalization C/V ⥤ C/U"]
instance overMap_isRightAdjoint : (SheafOfModules.overMap.{u} R f).IsRightAdjoint :=
  (overMapExtensionByZeroAdjunction J R f).isRightAdjoint

/-- `overMap_isRightAdjoint` in the spelling a consumer that splits a restriction with
`SheafOfModules.pushforwardComp` produces: the structure map written as the identity of
`R.over V` rather than as `Sheaf.pushforwardOverMapIso`. The two are equal on the nose, but
instance search matches syntactically. -/
instance pushforward_overMap_isRightAdjoint :
    (SheafOfModules.pushforward.{u} (F := Over.map f) (S := R.over V) (R := R.over U)
      (𝟙 (R.over V))).IsRightAdjoint :=
  inferInstanceAs (SheafOfModules.overMap.{u} R f).IsRightAdjoint

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Extension by zero along `Over.map f` is `SheafOfModules.pullback` for the identity
structure map: the structure map of `SheafOfModules.overMap` is the identity of `R.over V` on
the nose. -/
theorem overMap_leftAdjoint_eq :
    (SheafOfModules.overMap.{u} R f).leftAdjoint =
      SheafOfModules.pullback.{u} (F := Over.map f) (S := R.over V) (R := R.over U)
        (𝟙 (R.over V)) :=
  rfl

/-- Extension by zero along `Over.map f` is, up to the slice equivalence, extension by zero
along the localization of `C/U` at `Over.mk f`: both are left adjoint to restriction along
`Over.map f`. -/
noncomputable def overMapExtensionByZeroIso :
    (SheafOfModules.overMap.{u} R f).leftAdjoint ≅
      (Stacks.SheafOfModules.sliceEquiv R U (Over.mk f)).functor ⋙
        SheafOfModules.pullback.{u} (F := Over.forget (Over.mk f))
          (𝟙 ((R.over U).over (Over.mk f))) :=
  Adjunction.leftAdjointUniq
    (Adjunction.ofIsRightAdjoint (SheafOfModules.overMap.{u} R f))
    (overMapExtensionByZeroAdjunction J R f)

/-- **Stacks 03DJ for a relocalization.** Extension by zero of sheaves of modules along
`Over.map f : C/V ⥤ C/U` is exact: it is the slice equivalence, which is exact, followed by
extension by zero along the localization of `C/U` at `Over.mk f`, which is exact by
Stacks 03DJ. -/
@[stacks 03DJ "extension by zero along a relocalization C/V ⥤ C/U is exact"]
theorem overMap_extensionByZero_exact :
    exactFunctor _ _ (SheafOfModules.overMap.{u} R f).leftAdjoint := by
  obtain ⟨hlim, hcolim⟩ := (exactFunctor_iff (SheafOfModules.pullback.{u}
    (F := Over.forget (Over.mk f)) (𝟙 ((R.over U).over (Over.mk f))))).mp
      (extensionByZero_exact (J.over U) (R.over U) (Over.mk f))
  exact (exactFunctor _ _).prop_of_iso (overMapExtensionByZeroIso J R f).symm
    ((exactFunctor_iff _).2 ⟨comp_preservesFiniteLimits _ _, comp_preservesFiniteColimits _ _⟩)

end Stacks.Sites.ExtensionByZero

end
