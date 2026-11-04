module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StronglyCartesian

/-!
# The quasi-coherent modules are fibred over the big fppf site

The projection from quasi-coherent modules on the schemes of the big fppf site over `S` to that
site is a fibred category. This is the first of the three conditions of Stacks 026F that
Stacks 03YM asserts for this projection; in the tree those conditions are the three fields of
`CategoryTheory.Functor.IsStack`, and the attribute below is scoped to this one accordingly.

The fibre over an object `U` of the big fppf site is the category of quasi-coherent modules on
the underlying scheme of `U`, and a cartesian lift of `f : V ⟶ U` at a module `F` is the unit
of the pullback–pushforward adjunction, read as an `f`-map `F → f_* f^* F`. That this `f`-map is
strongly cartesian is `Stacks.QCoh.isStronglyCartesian_iff` applied to the identity of `f^* F`;
existence of such a lift over every arrow at every object is the condition.

## Main results

* `Stacks.QCoh.projection_isFibered`: **Stacks 03YM, condition (1) of Stacks 026F**.

## Implementation notes

`Stacks.QCoh.projection` is read off a `Stacks.QCoh.CategoryData` obtained by choice, so its
action on arrows is pinned only up to the two identifications `projection_obj` and
`projection_map` that the data carry. `rawProjection` below is the functor written directly in
terms of the `f`-map description of the hom-sets, `rawProjection_eq` identifies it with
`Stacks.QCoh.projection`, and the argument is carried out for `rawProjection`, where the
hom-sets are the `Σ`-type of Stacks 04U2 on the nose.

## References

* [Stacks Project, Tag 03YM](https://stacks.math.columbia.edu/tag/03YM)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Stacks.QCoh

universe u

variable {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

private noncomputable abbrev catData : CategoryData B S hS :=
  Classical.choice (exists_categoryData (B := B) (S := S) (hS := hS))

private noncomputable abbrev rawHom (A C : Object B S hS) :=
  Equiv.cast (catData.hom_type A C)

/-- The projection written directly in terms of the `f`-map description of the hom-sets. -/
private noncomputable def rawProjection :
    Object B S hS ⥤ BigFppfOver B S hS where
  obj A := A.base
  map {A C} m := (rawHom A C m).1
  map_id A := by
    change (Equiv.cast (catData.hom_type A A) (𝟙 A)).1 = _
    rw [catData.identity]
    rfl
  map_comp {A C D} m n := by
    change (Equiv.cast (catData.hom_type A D) (m ≫ n)).1 = _
    rw [catData.composition]
    rfl

private lemma rawProjection_eq :
    projection (B := B) (S := S) (hS := hS) = rawProjection :=
  CategoryTheory.Functor.ext catData.projection_obj (fun _ _ m => catData.projection_map m)

private abbrev modulesOn (U : BigFppfOver B S hS) :=
  (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory

private abbrev ofModule {U : BigFppfOver B S hS} (M : modulesOn U) :
    rawProjection.Fiber U := ⟨⟨U, M.obj, M.property⟩, rfl⟩

private abbrev schemeFunctor := BigFppfOver.toScheme B S hS

private noncomputable def modulePullback {U V : BigFppfOver B S hS} (f : V ⟶ U) :
    modulesOn U ⥤ modulesOn V :=
  ObjectProperty.lift _ ((SheafOfModules.isQuasicoherent (schemeFunctor.obj U).ringCatSheaf).ι ⋙
    Scheme.Modules.pullback (schemeFunctor.map f)) (fun M =>
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
        (schemeFunctor.map f).toLRSHom.toShHom M.obj M.property)

/-- The unit of the pullback–pushforward adjunction, read as an `f`-map. -/
private noncomputable def moduleCartesianMap {U V : BigFppfOver B S hS}
    (f : V ⟶ U) (M : modulesOn U) :
    (ofModule ((modulePullback f).obj M)).val ⟶ (ofModule M).val :=
  (rawHom _ _).symm ⟨f, (Scheme.Modules.pullbackPushforwardAdjunction
    (schemeFunctor.map f)).unit.app M.obj⟩

private lemma moduleCartesianMap_isStronglyCartesian
    {U V : BigFppfOver B S hS} (f : V ⟶ U) (M : modulesOn U) :
    rawProjection.IsStronglyCartesian f (moduleCartesianMap f M) := by
  let m := moduleCartesianMap f M
  have h : (projection (B := B) (S := S) (hS := hS)).IsStronglyCartesian
      ((projection (B := B) (S := S) (hS := hS)).map m) m := by
    rw [isStronglyCartesian_iff]
    have hm : homEquivPullbackHom _ _ m =
        ⟨f, 𝟙 ((Scheme.Modules.pullback (schemeFunctor.map f)).obj M.obj)⟩ := by
      show (Equiv.sigmaCongrRight (fun g : V ⟶ U =>
        (Scheme.Modules.pullbackPushforwardAdjunction (schemeFunctor.map g)).homEquiv
          M.obj ((modulePullback f).obj M).obj |>.symm)
        (rawHom (ofModule ((modulePullback f).obj M)).val (ofModule M).val m)) = _
      dsimp only [m, moduleCartesianMap]
      rw [Equiv.apply_symm_apply]
      show (⟨f, (Scheme.Modules.pullbackPushforwardAdjunction (schemeFunctor.map f)).homEquiv _ _
        |>.symm
          ((Scheme.Modules.pullbackPushforwardAdjunction (schemeFunctor.map f)).unit.app M.obj)⟩ :
        Σ g : V ⟶ U, (Scheme.Modules.pullback (schemeFunctor.map g)).obj M.obj ⟶ _) = _
      -- `Adjunction.homEquiv_symm_unit` is instantiated at the spelling the goal uses before
      -- being rewritten with: its statement is `dsimp%`-normalised, so the functor in the
      -- second argument of `homEquiv` is a separate variable there and a keyed rewrite has to
      -- unfold `Scheme.Modules.pullbackPushforwardAdjunction` to tie it to the adjunction.
      have hunit : ((Scheme.Modules.pullbackPushforwardAdjunction
            (schemeFunctor.map f)).homEquiv M.obj
            ((Scheme.Modules.pullback (schemeFunctor.map f)).obj M.obj)).symm
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (schemeFunctor.map f)).unit.app M.obj) =
          𝟙 ((Scheme.Modules.pullback (schemeFunctor.map f)).obj M.obj) :=
        Adjunction.homEquiv_symm_unit _ M.obj
      exact Sigma.ext rfl (heq_of_eq hunit)
    rw [hm]
    -- The goal is `IsIso ⟨f, 𝟙 _⟩.snd`; instance search does not reduce the projection of an
    -- explicit pair, so the identity instance is supplied directly.
    exact IsIso.id _
  rw [rawProjection_eq] at h
  simpa only [rawProjection, m, moduleCartesianMap, Equiv.apply_symm_apply] using h

private lemma rawProjection_isFibered :
    (rawProjection (B := B) (S := S) (hS := hS)).IsFibered := by
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  rintro ⟨U, M, hM⟩ V f
  exact ⟨_, moduleCartesianMap f ⟨M, hM⟩, moduleCartesianMap_isStronglyCartesian f ⟨M, hM⟩⟩

/-- **Stacks 03YM, condition (1) of Stacks 026F**: the projection from quasi-coherent modules on
the schemes of the big fppf site over `S` to that site is a fibred category. A cartesian lift of
`f : V ⟶ U` at a module `F` on `U` is the unit `F ⟶ f_* f^* F` of the pullback–pushforward
adjunction, read as an `f`-map. -/
@[stacks 03YM "condition (1): the functor is a fibred category", sga "1 VIII 1.1" "special case"]
public theorem projection_isFibered (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (projection (B := B) (S := S) (hS := hS)).IsFibered := by
  rw [rawProjection_eq]
  exact rawProjection_isFibered

end Stacks.QCoh

end
