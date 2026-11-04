module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.AffineIdentification
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf

/-!
# A first-order thickening is trivial exactly when its conormal sheaf vanishes

Let `i : Z ⟶ X` be a first-order thickening, that is, a closed immersion whose defining ideal
sheaf `ℐ` satisfies `ℐ² = 0`. Then `i` is an isomorphism if and only if its conormal sheaf
`𝒞_{Z/X}` is the zero sheaf of modules.

## Main results

* `Stacks.Conormal.isZero_idealSheaf_of_isIso`: the defining ideal sheaf of an isomorphism of
  schemes is zero.
* `Stacks.Conormal.isZero_immersionConormalSheaf_of_isIso`: the conormal sheaf of an isomorphism
  is zero.
* `Stacks.Conormal.ker_eq_bot_of_isZero_immersionConormalSheaf`: a closed immersion with
  square-zero defining ideal and vanishing conormal sheaf has trivial defining ideal.
* `Stacks.Conormal.isIso_iff_isZero_immersionConormalSheaf`: the criterion itself.

## Implementation notes

The conormal sheaf is `Stacks.Thickenings.immersionConormalSheaf`, the pullback along
`AlgebraicGeometry.Scheme.Hom.liftCoborder` of the defining ideal sheaf of that closed
factorization, as in [Stacks Project, Tag 01R2].

## References

* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 04FE](https://stacks.math.columbia.edu/tag/04FE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction
open Stacks.Thickenings

universe u

namespace Stacks.Conormal

variable {Z X : Scheme.{u}}

/-- The sections of a zero sheaf of modules over any open vanish. -/
private theorem isZero_val_obj {Y : Scheme.{u}}
    {N : SheafOfModules.{u} (structureSheafRing Y.toLocallyRingedSpace.toRingedSpace)}
    (h : IsZero N) (U : Y.Opens) : IsZero (N.val.obj (op U)) := by
  rw [IsZero.iff_id_eq_zero]
  have h2 := congrArg (fun f : N ⟶ N => f.val.app (op U)) (h.eq_of_src (𝟙 N) 0)
  simp only [SheafOfModules.id_val] at h2
  exact h2

/-- **The defining ideal sheaf of an isomorphism of schemes is zero.** -/
public theorem isZero_idealSheaf_of_isIso (j : Z ⟶ X) [IsIso j] :
    IsZero (Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom) := by
  have hψ : IsIso (structureSheafHom j.toLRSHom.toShHom) := by
    have : IsIso ((sheafToPresheaf _ _).map (structureSheafHom j.toLRSHom.toShHom)) := by
      rw [NatTrans.isIso_iff_isIso_app]
      intro V
      show IsIso ((forget₂ CommRingCat RingCat).map (j.app V.unop))
      infer_instance
    exact isIso_of_reflects_iso (structureSheafHom j.toLRSHom.toShHom) (sheafToPresheaf _ _)
  have hq : IsIso (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom)) := by
    have hval : IsIso (SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom j.toLRSHom.toShHom)).val := by
      have : IsIso ((PresheafOfModules.toPresheaf _).map
          (SheafOfModules.unitToPushforwardObjUnit
            (structureSheafHom j.toLRSHom.toShHom)).val) := by
        rw [NatTrans.isIso_iff_isIso_app]
        intro V
        exact (ConcreteCategory.isIso_iff_bijective _).2 ((ConcreteCategory.isIso_iff_bijective
          ((structureSheafHom j.toLRSHom.toShHom).hom.app V)).1 inferInstance)
      exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)
    have : IsIso ((SheafOfModules.forget _).map (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom))) := hval
    exact isIso_of_reflects_iso _ (SheafOfModules.forget _)
  exact IsZero.of_iso (isZero_zero _)
    (Limits.kernel.ofMono (SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom j.toLRSHom.toShHom)))

/-- **An isomorphism factors through the coborder of its range by an isomorphism.** For an
immersion `i` that is an isomorphism, `AlgebraicGeometry.Scheme.Hom.liftCoborder i` is an
isomorphism. -/
public theorem isIso_liftCoborder (i : Z ⟶ X) [IsImmersion i] [IsIso i] : IsIso i.liftCoborder := by
  have hsurj : Function.Surjective i.base := (Scheme.homeoOfIso (asIso i)).surjective
  have hU : i.coborderRange = ⊤ := by
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    show x ∈ coborder (Set.range i.base)
    simp [Set.range_eq_univ.mpr hsurj, coborder]
  have : IsIso i.coborderRange.ι := by
    rw [hU, ← Scheme.topIso_hom]
    infer_instance
  have h : IsIso (i.liftCoborder ≫ i.coborderRange.ι) := by
    rw [i.liftCoborder_ι]; infer_instance
  exact IsIso.of_isIso_comp_right i.liftCoborder i.coborderRange.ι

/-- **The conormal sheaf of an isomorphism is zero.** -/
public theorem isZero_immersionConormalSheaf_of_isIso (i : Z ⟶ X) [IsImmersion i] [IsIso i] :
    IsZero (Stacks.Thickenings.immersionConormalSheaf i) := by
  have : IsIso i.liftCoborder := isIso_liftCoborder i
  have hideal := isZero_idealSheaf_of_isIso i.liftCoborder
  have : Functor.IsLeftAdjoint (modulePullback i.liftCoborder.toLRSHom.toShHom) :=
    ⟨modulePushforward _, ⟨modulePullbackPushforwardAdjunction _⟩⟩
  exact Functor.map_isZero _ hideal

/-- **A square-zero defining ideal with vanishing conormal sheaf is trivial.** Let `i : Z ⟶ X` be
a closed immersion whose defining ideal sheaf has vanishing square. If the conormal sheaf of `i`
is zero then the defining ideal sheaf is zero. -/
public theorem ker_eq_bot_of_isZero_immersionConormalSheaf (i : Z ⟶ X) [IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) (h : IsZero (Stacks.Thickenings.immersionConormalSheaf i)) :
    i.ker = ⊥ := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  obtain ⟨I, e, he⟩ := exists_affineModel i U.1 U.2
  have hI : i.ker.ideal U = I := by
    rw [i.ker_apply U, ← Scheme.Hom.appLE_preimage_self i U.1]
    exact ker_appLE_eq_of_affineModel i U.1 U.2 I e he
  have hI2 : I ^ 2 = ⊥ := by
    rw [← hI]
    simpa using congrArg (fun J : X.IdealSheafData => J.ideal U) hsq
  have hpush : IsZero ((modulePushforward i.toLRSHom.toShHom).obj
      (Stacks.Thickenings.immersionConormalSheaf i)) := by
    have : (modulePushforward i.toLRSHom.toShHom).IsRightAdjoint :=
      modulePushforward_isRightAdjoint _
    exact Functor.map_isZero _ h
  have hcot : IsZero (ModuleCat.of Γ(X, U.1) I.Cotangent) :=
    IsZero.of_iso (isZero_val_obj hpush U.1)
      (affineConormalIsoCotangent i U.1 U.2 I e he).symm
  have hsub : Subsingleton I.Cotangent := ModuleCat.isZero_iff_subsingleton.mp hcot
  rw [hI, Scheme.IdealSheafData.ideal_bot]
  refine eq_bot_iff.mpr fun x hx => ?_
  exact hI2 ▸ (Ideal.toCotangent_eq_zero I ⟨x, hx⟩).mp (hsub.elim _ 0)

/-- **A first-order thickening is trivial exactly when its conormal sheaf vanishes.** For a closed
immersion `i : Z ⟶ X` whose defining ideal sheaf has vanishing square, `i` is an isomorphism if
and only if the conormal sheaf `𝒞_{Z/X}` of [Stacks Project, Tag 01R2] is the zero sheaf of
modules. -/
public theorem isIso_iff_isZero_immersionConormalSheaf (i : Z ⟶ X) [IsClosedImmersion i]
    (hsq : i.ker ^ 2 = ⊥) :
    IsIso i ↔ IsZero (Stacks.Thickenings.immersionConormalSheaf i) := by
  refine ⟨fun _ => isZero_immersionConormalSheaf_of_isIso i, fun h => ?_⟩
  exact IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    (ker_eq_bot_of_isZero_immersionConormalSheaf i hsq h)

end Stacks.Conormal

end
