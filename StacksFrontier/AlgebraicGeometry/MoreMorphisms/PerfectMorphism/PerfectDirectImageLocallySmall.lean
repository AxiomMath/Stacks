module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.MayerVietorisTorDimension
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PseudoCoherentPushforwardLocallySmall
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Derived direct image along a perfect proper morphism preserves perfectness, at the locally
small model

[Stacks, Tag 0B6G] says that for a perfect proper morphism `f : X ⟶ S` with `S` Noetherian,
`Rf_*` carries perfect objects of `D(𝒪_X)` to perfect objects of `D(𝒪_S)`. It is proved at
`HasDerivedCategory.standard` as
`Stacks.AlgebraicGeometry.PerfectProperDirectImage.isPerfect_derivedPushforward_of_isPerfect`;
this file transports it to the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which
`Stacks.Duality.derivedPushforward` and the duality statements live.

Perfectness of the object represented by a complex does not depend on the model
(`Stacks.Cohomology.PerfectComplexes.isPerfect_Q_transfer`), and at either model `Rf_*` of the
object represented by `K` is represented by `f_*I` for a K-injective resolution `K ⟶ I`.

No `@[stacks]` attribute: the tag is registered at the standard model.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe w w' u

namespace Stacks.Cohomology.PerfectComplexes

/-- **Perfectness of the object represented by a complex does not depend on the choice of
derived category.** -/
theorem isPerfect_Q_transfer {X : RingedSpace.{u, u}}
    (inst₁ : HasDerivedCategory.{w} (StrictlyPerfect.OXMod.{u, u} X))
    (inst₂ : HasDerivedCategory.{w'} (StrictlyPerfect.OXMod.{u, u} X))
    (K : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ)
    (h : @IsPerfect X inst₁ ((@DerivedCategory.Q _ _ _ inst₁).obj K)) :
    @IsPerfect X inst₂ ((@DerivedCategory.Q _ _ _ inst₂).obj K) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := h
  exact ⟨L, hL, ⟨DerivedCategory.transferQObjIso inst₁ inst₂ L K e⟩⟩

end Stacks.Cohomology.PerfectComplexes

namespace Stacks.AlgebraicGeometry.PerfectProperDirectImage

open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.PerfectComplexTriangles

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 0B6G] at the locally small model.** For a perfect proper morphism
`f : X ⟶ S` with `S` Noetherian, `Rf_*` carries a perfect object of the locally small `D(𝒪_X)`
to a perfect object of `D(𝒪_S)`. -/
@[sga "6 IV 3.3.2" "3.3.2.3, special case"]
theorem isPerfect_derivedPushforward_of_isPerfect_locallySmall [IsNoetherian S] [Perfect f]
    [IsProper f] (E : DerivedCategory X.Modules)
    (hE : IsPerfect (X := X.toRingedSpace) E) :
    IsPerfect (X := S.toRingedSpace) ((Stacks.Duality.derivedPushforward f).obj E) := by
  let K := DerivedCategory.Q.objPreimage E
  let eQ : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hstd : @IsPerfect S.toRingedSpace (HasDerivedCategory.standard S.Modules)
      ((derivedPushforwardModules f).obj
        ((@DerivedCategory.Q X.Modules _ _ (HasDerivedCategory.standard X.Modules)).obj K)) :=
    isPerfect_derivedPushforward_of_isPerfect f _
      (isPerfect_Q_transfer _ _ K (isPerfect_of_iso eQ.symm hE))
  obtain ⟨I, s, hI, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective X K
  let eStd := (derivedPushforwardModules f).mapIso
      ((@DerivedCategory.quotientCompQhIso X.Modules _ _
        (HasDerivedCategory.standard X.Modules)).app K).symm ≪≫
    @Stacks.Duality.derivedPushforwardObjIso X S f (HasDerivedCategory.standard X.Modules)
      (HasDerivedCategory.standard S.Modules) K I s hI hs
  let eLS := (Stacks.Duality.derivedPushforward f).mapIso
      (eQ.symm ≪≫ ((DerivedCategory.quotientCompQhIso X.Modules).app K).symm) ≪≫
    Stacks.Duality.derivedPushforwardObjIso f s hI hs
  exact isPerfect_of_iso eLS.symm (isPerfect_Q_transfer (HasDerivedCategory.standard S.Modules)
    (Scheme.Modules.hasDerivedCategory S) _
    (@isPerfect_of_iso S.toRingedSpace (HasDerivedCategory.standard S.Modules) _ _ eStd hstd))

end Stacks.AlgebraicGeometry.PerfectProperDirectImage

end
