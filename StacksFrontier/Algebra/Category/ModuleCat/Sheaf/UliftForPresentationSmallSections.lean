module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Module.Shrink
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SectionUniverseLiftColimits

/-!
# Sheaves of modules with small sections are universe lifts

Let `R` be a sheaf of rings on a site and `S` a sheaf of `R`-modules whose sections lie in a
universe `max t m`. If every module of sections of `S` is `m`-small, then `S` is, up to
isomorphism, the universe lift `SheafOfModules.uliftForPresentation` of a sheaf of modules with
sections in `Type m`: shrink every module of sections to `Type m` and transport the restriction
maps. In particular a subobject of a universe lift is again a universe lift.

## Main definitions

* `SheafOfModules.shrinkSections`: for a sheaf of modules with `m`-small sections, the sheaf of
  modules with sections in `Type m` obtained by shrinking them.
* `SheafOfModules.uliftForPresentationShrinkSectionsIso`: its universe lift is the original
  sheaf of modules.

## Main results

* `SheafOfModules.small_sections_of_mono`: a sheaf of modules with a monomorphism into a
  universe lift has small sections.
* `SheafOfModules.exists_iso_uliftForPresentationMap_of_mono`: **a monomorphism into the
  universe lift of a sheaf of modules is the universe lift of a monomorphism.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v r m t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

section Shrink

variable (S : SheafOfModules.{max t m} R) [hS : ∀ X, Small.{m} (S.val.obj X)]

/-- The sections of `S` over `X`, shrunk to `Type m`, as a linear equivalence. -/
abbrev shrinkSectionsEquiv (X : Cᵒᵖ) : Shrink.{m} (S.val.obj X) ≃ₗ[R.obj.obj X] S.val.obj X :=
  Shrink.linearEquiv (R.obj.obj X) (S.val.obj X)

/-- The restriction maps of `S`, read on the shrunk sections. -/
def shrinkSectionsRestrict {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Shrink.{m} (S.val.obj X) →ₛₗ[(R.obj.map f).hom] Shrink.{m} (S.val.obj Y) :=
  ((shrinkSectionsEquiv S Y).symm.toLinearMap.comp (S.val.restrictₛₗ f)).comp
    (shrinkSectionsEquiv S X).toLinearMap

/-- `SheafOfModules.shrinkSectionsRestrict` is the restriction map of `S`, conjugated by the
shrinking equivalences. -/
lemma shrinkSectionsRestrict_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : Shrink.{m} (S.val.obj X)) :
    shrinkSectionsRestrict S f x =
      (shrinkSectionsEquiv S Y).symm (S.val.restrictₛₗ f (shrinkSectionsEquiv S X x)) := rfl

/-- The presheaf of modules of the shrunk sections of `S`. -/
def shrinkSectionsPresheaf : PresheafOfModules.{m} R.obj where
  obj X := ModuleCat.of (R.obj.obj X) (Shrink.{m} (S.val.obj X))
  map {X Y} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj Y) (Shrink.{m} (S.val.obj Y))))
    { toFun := shrinkSectionsRestrict S f
      map_add' := map_add _
      map_smul' := fun a x ↦ (shrinkSectionsRestrict S f).map_smulₛₗ a x }
  map_id X := by
    ext x
    change shrinkSectionsRestrict S (𝟙 X) x = x
    rw [shrinkSectionsRestrict_apply, S.val.restrictₛₗ_id]
    exact (shrinkSectionsEquiv S X).symm_apply_apply x
  map_comp f g := by
    ext x
    change shrinkSectionsRestrict S (f ≫ g) x =
      shrinkSectionsRestrict S g (shrinkSectionsRestrict S f x)
    simp only [shrinkSectionsRestrict_apply, LinearEquiv.apply_symm_apply,
      S.val.restrictₛₗ_comp]

/-- The universe lift of the shrunk sections of `S` is `S`, as presheaves of modules. -/
def uliftShrinkSectionsPresheafIso :
    (shrinkSectionsPresheaf S).uliftSections.{t} ≅ S.val :=
  PresheafOfModules.isoMk
    (fun X ↦ (ULift.moduleEquiv.trans (shrinkSectionsEquiv S X)).toModuleIso)
    (fun X Y f ↦ by
      ext x
      change shrinkSectionsEquiv S Y (shrinkSectionsRestrict S f
          (ULift.down (x : ULift.{t} (Shrink.{m} (S.val.obj X))))) =
        S.val.restrictₛₗ f (shrinkSectionsEquiv S X
          (ULift.down (x : ULift.{t} (Shrink.{m} (S.val.obj X)))))
      rw [shrinkSectionsRestrict_apply, LinearEquiv.apply_symm_apply])

/-- **The sheaf of modules of the shrunk sections** of a sheaf of modules whose sections are
small: its sections over `X` are `Shrink (S(X))`. -/
def shrinkSections : SheafOfModules.{m} R where
  val := shrinkSectionsPresheaf S
  isSheaf := Presheaf.isSheaf_of_isSheaf_comp J _ AddCommGrpCat.uliftFunctor.{t}
    ((Presheaf.isSheaf_of_iso_iff
      ((PresheafOfModules.toPresheaf R.obj).mapIso (uliftShrinkSectionsPresheafIso S))).2 S.isSheaf)

/-- **A sheaf of modules with small sections is the universe lift of its shrunk sections.** -/
def uliftForPresentationShrinkSectionsIso :
    uliftForPresentation.{u, v, r, m, t} (shrinkSections S) ≅ S :=
  (fullyFaithfulForget R).preimageIso (uliftShrinkSectionsPresheafIso S)

end Shrink

/-- A sheaf of modules with a monomorphism into the universe lift of a sheaf of modules with
sections in `Type m` has `m`-small sections: a monomorphism of sheaves of modules is injective on
sections. -/
theorem small_sections_of_mono {Y : SheafOfModules.{m} R} {S : SheafOfModules.{max t m} R}
    (i : S ⟶ uliftForPresentation.{u, v, r, m, t} Y) [Mono i] (X : Cᵒᵖ) :
    Small.{m} (S.val.obj X) := by
  refine small_of_injective (f := fun x : S.val.obj X ↦ ((i.val.app X).hom x).down) ?_
  intro x y h
  exact PresheafOfModules.injective_of_mono ((forget R).map i) X (ULift.ext _ _ h)

/-- **A monomorphism into the universe lift of a sheaf of modules is the universe lift of a
monomorphism**, up to isomorphism of its source. -/
theorem exists_iso_uliftForPresentationMap_of_mono {Y : SheafOfModules.{m} R}
    {S : SheafOfModules.{max t m} R} (i : S ⟶ uliftForPresentation.{u, v, r, m, t} Y) [Mono i] :
    ∃ (S' : SheafOfModules.{m} R) (i' : S' ⟶ Y) (_ : Mono i')
      (e : uliftForPresentation.{u, v, r, m, t} S' ≅ S),
      e.hom ≫ i = uliftForPresentationMap.{u, v, r, m, t} i' := by
  have := small_sections_of_mono i
  let e := uliftForPresentationShrinkSectionsIso.{u, v, r, m, t} S
  refine ⟨shrinkSections S, uliftForPresentationMapDown (e.hom ≫ i), ?_, e,
    (uliftForPresentationMap_down _).symm⟩
  refine (uliftForPresentationFunctor.{u, v, r, m, t} (R := R)).mono_of_mono_map ?_
  show Mono (uliftForPresentationMap.{u, v, r, m, t} _)
  rw [uliftForPresentationMap_down]
  infer_instance

end SheafOfModules

end
