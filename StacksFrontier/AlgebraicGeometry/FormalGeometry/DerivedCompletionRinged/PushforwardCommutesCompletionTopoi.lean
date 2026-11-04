module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.PushforwardCompletionTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# The comparison map of [Stacks, Tag 0A0G], for a morphism of ringed topoi

[Stacks, Tag 0A0G] is stated for a morphism of ringed **topoi**
`f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)`. What the rest of this directory proves is the tag for a morphism
of ringed **sites**: `AlgebraicGeometry.RingedSite.Hom`, whose underlying datum is a continuous
functor `u : 𝒞 ⥤ 𝒟` in the direction opposite to the morphism it presents. That is strictly less
general — `AlgebraicGeometry.RingedToposSiteHom`, the type the site-level `Rf_*` is indexed by,
is the same two data with the morphism-of-sites property weakened to continuity, and so is a
*site-presented* morphism of ringed topoi, not an arbitrary one. The genuine notion in this
library is `AlgebraicGeometry.RingedToposHom`: a geometric morphism of the underlying topoi — an
adjoint pair with left exact inverse image — together with `f^♯`.

This file builds, at that genuine generality, the canonical comparison map the tag asserts to be
invertible, together with the universal property that characterises it. The two inputs are both
available at the topos level already:

* `Rf_*(K^∧)` is derived complete, because `K^∧` is and because `Rf_*` preserves derived
  completeness — [Stacks, Tag 099J] for an arbitrary morphism of ringed topoi, which is
  `AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete` of
  `PushforwardTopoi.lean`, proved there by the reduction to a morphism of ringed sites of
  [Stacks, Tag 03CR];
* the reflector adjunction of [Stacks, Tag 099F] on `D(𝒪)`, which depends only on the site
  presenting the topos and the sheaf of ideals, not on the morphism, and so is the same
  `AlgebraicGeometry.RingedSite.derivedCompletionAdjunction` the site-level file uses.

So the comparison map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is the adjunct of `Rf_*K ⟶ Rf_*(K^∧)` under that
reflector adjunction, exactly as at the site level, and it is again constructed as a mate, hence
natural in `K`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.derivedCompletionPushforwardComparison`: the canonical map
  `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` of [Stacks, Tag 0A0G], for an arbitrary morphism of ringed topoi.

## Main results

* `RingedToposHom.derivedCompletionUnit_comp_derivedCompletionPushforwardComparison`:
  the comparison map is the unique map compatible with the two completion units, which is how
  the source introduces it.
* `RingedToposHom.isIso_derivedCompletionPushforwardComparison_of_isIso_map_unit`
  and `...of_isDerivedComplete`: the two criteria for it to be invertible.

## References

* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Cohomology

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
  (I : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
  (I' : SheafOfModules.Submodule
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))

section Commutation

variable (hI : IdealCompatible f I I')
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I')).IsRightAdjoint]

include hI in
/-- `Rf_*(K^∧)` is derived complete: `K^∧` is derived complete, and `Rf_*` preserves derived
completeness by [Stacks, Tag 099J] for a morphism of ringed topoi. -/
theorem isDerivedComplete_derivedPushforward_derivedCompletion
    (K : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
        ((RingedSite.derivedCompletion X.toRingedSite I').obj K)) :=
  isDerivedComplete_derivedPushforward f I I' hI _
    (RingedSite.isDerivedComplete_derivedCompletion_obj X.toRingedSite I' K)

variable
  [(ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)).IsRightAdjoint]

/-- `K ↦ Rf_*(K^∧)`, read as a functor into the derived-complete objects of `D(𝒪)`, for a
morphism of ringed topoi. -/
def completedPushforwardOfDerivedCompletion :
    DerivedCategory (SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))) ⥤
      ObjectProperty.FullSubcategory
        (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I) :=
  ObjectProperty.lift _
    (RingedSite.derivedCompletion X.toRingedSite I' ⋙
      DerivedPushforward.derivedPushforward (X := X) (Y := Y) f)
    (isDerivedComplete_derivedPushforward_derivedCompletion f I I' hI)

/-- The natural map `Rf_*K ⟶ Rf_*(K^∧)`, that is `Rf_*` applied to the unit `K ⟶ K^∧` of derived
completion, for a morphism of ringed topoi. -/
def pushforwardDerivedCompletionUnit :
    DerivedPushforward.derivedPushforward (X := X) (Y := Y) f ⟶
      RingedSite.derivedCompletion X.toRingedSite I' ⋙
        DerivedPushforward.derivedPushforward (X := X) (Y := Y) f :=
  Functor.whiskerRight (RingedSite.derivedCompletionUnit X.toRingedSite I')
    (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f)

/-- The comparison map of [Stacks, Tag 0A0G] read in the derived-complete objects: the adjunct,
under the reflector adjunction of [Stacks, Tag 099F] on `D(𝒪)`, of the natural map
`Rf_*K ⟶ Rf_*(K^∧)`, for a morphism of ringed topoi. -/
def derivedCompletionPushforwardComparisonLift :
    DerivedPushforward.derivedPushforward (X := X) (Y := Y) f ⋙
        (ObjectProperty.ι
          (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)).leftAdjoint ⟶
      completedPushforwardOfDerivedCompletion f I I' hI :=
  Functor.whiskerRight (pushforwardDerivedCompletionUnit f I')
      (ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I)).leftAdjoint ≫
    Functor.whiskerLeft (completedPushforwardOfDerivedCompletion f I I' hI)
      (RingedSite.derivedCompletionAdjunction Y.toRingedSite I).counit

/-- **The canonical map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` of [Stacks, Tag 0A0G], for an arbitrary morphism
of ringed topoi.** It exists because `Rf_*(K^∧)` is derived complete, by [Stacks, Tag 099J] at
that generality, so the universal property of derived completion applies to the natural map
`Rf_*K ⟶ Rf_*(K^∧)`. Built as a mate, so that it is natural in `K`.

This is the map the tag asserts to be invertible. For a morphism of ringed *sites* its
invertibility at the tag's own data is
`RingedSite.isIso_derivedCompletionPushforwardComparison_inverseImageIdealSheaf_of_isFiniteType`
of `PushforwardCommutesCompletionLocalToGlobal.lean`. Here `ℐ` and `ℐ'` are an arbitrary pair of
sheaves of ideals subject only to `hI`, the relation of [Stacks, Tag 099J] between them, which is
where the construction already makes sense. -/
def derivedCompletionPushforwardComparison :
    DerivedPushforward.derivedPushforward (X := X) (Y := Y) f ⋙
        RingedSite.derivedCompletion Y.toRingedSite I ⟶
      RingedSite.derivedCompletion X.toRingedSite I' ⋙
        DerivedPushforward.derivedPushforward (X := X) (Y := Y) f :=
  Functor.whiskerRight (derivedCompletionPushforwardComparisonLift f I I' hI)
    (ObjectProperty.ι (RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I))

include hI in
/-- **The comparison map is the one the universal property of derived completion produces**, for a
morphism of ringed topoi: it is the unique map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` whose composite with the
unit `Rf_*K ⟶ (Rf_*K)^∧` is `Rf_*` applied to the unit `K ⟶ K^∧`. This is how the source
introduces the map, and it is what pins it down among all maps between the two sides. -/
theorem derivedCompletionUnit_comp_derivedCompletionPushforwardComparison
    (K : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))) :
    (RingedSite.derivedCompletionUnit Y.toRingedSite I).app
          ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K) ≫
        (derivedCompletionPushforwardComparison f I I' hI).app K =
      (DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
        ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K) :=
  (RingedSite.derivedCompletionAdjunction Y.toRingedSite I).unit_comp_map_comp_counit
    (B := (completedPushforwardOfDerivedCompletion f I I' hI).obj K)
    ((pushforwardDerivedCompletionUnit f I').app K)

include hI in
/-- **A criterion for `Rf_*` to commute with derived completion at `K`**, for a morphism of ringed
topoi: if `Rf_*` applied to the unit `K ⟶ K^∧` is invertible, then so is the comparison map
`(Rf_*K)^∧ ⟶ Rf_*(K^∧)`.

Indeed `Rf_*(K^∧)` is derived complete, so an invertible `Rf_*(K ⟶ K^∧)` makes `Rf_*K` derived
complete too, whence its unit `Rf_*K ⟶ (Rf_*K)^∧` is invertible; and the comparison map is the
second factor of that unit followed by itself in
`derivedCompletionUnit_comp_derivedCompletionPushforwardComparison`. -/
theorem isIso_derivedCompletionPushforwardComparison_of_isIso_map_unit
    {K : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))}
    (hK : IsIso ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
      ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K))) :
    IsIso ((derivedCompletionPushforwardComparison f I I' hI).app K) := by
  have hcomplete : RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K) :=
    (RingedSite.isDerivedComplete_iff_of_iso Y.toRingedSite I
      (asIso ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
        ((RingedSite.derivedCompletionUnit X.toRingedSite I').app K)))).mpr
      (isDerivedComplete_derivedPushforward_derivedCompletion f I I' hI K)
  have hunit : IsIso ((RingedSite.derivedCompletionUnit Y.toRingedSite I).app
      ((DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K)) :=
    RingedSite.isIso_derivedCompletionUnit_app Y.toRingedSite I hcomplete
  exact IsIso.of_isIso_fac_left
    (derivedCompletionUnit_comp_derivedCompletionPushforwardComparison f I I' hI K)

include hI in
/-- **The comparison map is invertible at a derived-complete object**, for a morphism of ringed
topoi: for `K` in `D_comp(𝒪', ℐ')` the canonical map `(Rf_*K)^∧ ⟶ Rf_*(K^∧)` is invertible, so
`Rf_*(K^∧) = Rf_*K = (Rf_*K)^∧` — the unit `K ⟶ K^∧` is invertible on a derived-complete `K`.

This is the degenerate regime, where both completions are the identity on the objects in
sight. -/
theorem isIso_derivedCompletionPushforwardComparison_of_isDerivedComplete
    {K : DerivedCategory (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)))}
    (hK : RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I' K) :
    IsIso ((derivedCompletionPushforwardComparison f I I' hI).app K) :=
  isIso_derivedCompletionPushforwardComparison_of_isIso_map_unit f I I' hI
    (by
      have := RingedSite.isIso_derivedCompletionUnit_app X.toRingedSite I' hK
      infer_instance)

end Commutation

end AlgebraicGeometry.RingedToposHom

end
