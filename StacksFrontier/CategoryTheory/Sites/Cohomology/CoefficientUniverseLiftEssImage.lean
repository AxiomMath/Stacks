module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoefficientUniverseLift
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Logic.Small.Basic

/-!
# Abelian sheaves with small sections are universe lifts

Let `J` be a Grothendieck topology on which the universe lift of abelian groups from
`AddCommGrpCat.{w}` to `AddCommGrpCat.{max w t}` is compatible with sheafification. An abelian
sheaf at the large coefficient universe all of whose groups of sections are `w`-small is the
universe lift of a sheaf at the small one; more generally so is the sheafification of every
presheaf with `w`-small values. Consequently the essential image of the universe lift is closed
under subobjects and quotients.

## Main results

* `Stacks.Cohomology.CoefficientLift.shrinkFunctor`: a functor to `AddCommGrpCat.{max w t}` with
  `w`-small values, shrunk to `AddCommGrpCat.{w}`.
* `Stacks.Cohomology.CoefficientLift.exists_sheafCompose_iso_presheafToSheaf`: the
  sheafification of a presheaf with small values is a universe lift.
* `Stacks.Cohomology.CoefficientLift.exists_sheafCompose_iso_of_small`: so is a sheaf with small
  sections.
* `Stacks.Cohomology.CoefficientLift.exists_sheafCompose_iso_of_mono`,
  `Stacks.Cohomology.CoefficientLift.exists_sheafCompose_iso_of_epi`: subobjects and quotients of
  universe lifts are universe lifts.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w t v₁ u₁ u₂ v₂

namespace Stacks.Cohomology.CoefficientLift

section Shrink

variable {D : Type u₂} [Category.{v₂} D] (P : D ⥤ AddCommGrpCat.{max w t})
  [∀ U, Small.{w} (P.obj U)]

/-- A functor to `AddCommGrpCat.{max w t}` all of whose values are `w`-small, shrunk to a functor
to `AddCommGrpCat.{w}`. -/
def shrinkFunctor : D ⥤ AddCommGrpCat.{w} where
  obj U := AddCommGrpCat.of (Shrink.{w} (P.obj U))
  map f := AddCommGrpCat.ofHom <|
    (Shrink.addEquiv.symm.toAddMonoidHom.comp (P.map f).hom).comp Shrink.addEquiv.toAddMonoidHom
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

/-- The universe lift of the shrinking of `P` is `P`. -/
def shrinkFunctorUliftIso :
    shrinkFunctor.{w, t} P ⋙ AddCommGrpCat.uliftFunctor.{t, w} ≅ P :=
  NatIso.ofComponents (fun U ↦ (AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso)
    (fun f ↦ by
      ext x
      change Shrink.addEquiv (Shrink.addEquiv.symm ((P.map f) (Shrink.addEquiv x.down))) = _
      simp only [AddEquiv.apply_symm_apply]
      rfl)

end Shrink

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{max w t}]
  [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, w}]

/-- **The sheafification of a presheaf with small values is a universe lift.** -/
theorem exists_sheafCompose_iso_presheafToSheaf (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w t})
    [∀ U, Small.{w} (P.obj U)] :
    ∃ G : Sheaf J AddCommGrpCat.{w},
      Nonempty ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G ≅
        (presheafToSheaf J AddCommGrpCat.{max w t}).obj P) :=
  ⟨(presheafToSheaf J AddCommGrpCat.{w}).obj (shrinkFunctor.{w, t} P),
    ⟨((sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{t, w}
        (sheafificationAdjunction J AddCommGrpCat.{w})
        (sheafificationAdjunction J AddCommGrpCat.{max w t})).app _).symm ≪≫
      (presheafToSheaf J AddCommGrpCat.{max w t}).mapIso (shrinkFunctorUliftIso P)⟩⟩

/-- **An abelian sheaf with small sections is a universe lift.** -/
theorem exists_sheafCompose_iso_of_small (F : Sheaf J AddCommGrpCat.{max w t})
    (hF : ∀ U, Small.{w} (F.obj.obj U)) :
    ∃ G : Sheaf J AddCommGrpCat.{w},
      Nonempty ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G ≅ F) := by
  have := hF
  obtain ⟨G, ⟨e⟩⟩ := exists_sheafCompose_iso_presheafToSheaf.{w, t} J F.obj
  exact ⟨G, ⟨e ≪≫ (sheafificationIso F).symm⟩⟩

omit [HasSheafify J AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{max w t}]
  [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, w}] in
/-- The sections of a universe lift are small. -/
theorem small_sheafCompose_obj (G : Sheaf J AddCommGrpCat.{w}) (U : Cᵒᵖ) :
    Small.{w} (((sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G).obj.obj U) :=
  ⟨⟨G.obj.obj U, ⟨Equiv.ulift⟩⟩⟩

omit [HasSheafify J AddCommGrpCat.{w}]
  [J.PreservesSheafification AddCommGrpCat.uliftFunctor.{t, w}] in
/-- A subsheaf of a sheaf with small sections has small sections. -/
theorem small_of_mono {F F' : Sheaf J AddCommGrpCat.{max w t}} (i : F ⟶ F') [Mono i]
    (hF' : ∀ U, Small.{w} (F'.obj.obj U)) (U : Cᵒᵖ) : Small.{w} (F.obj.obj U) := by
  have : Mono ((sheafToPresheaf J _).map i) := inferInstance
  have hU : Mono (i.hom.app U) := (NatTrans.mono_iff_mono_app _).1 this U
  have := hF' U
  exact small_of_injective ((AddCommGrpCat.mono_iff_injective _).1 hU)

/-- **A subsheaf of a universe lift is a universe lift.** -/
theorem exists_sheafCompose_iso_of_mono {F : Sheaf J AddCommGrpCat.{max w t}}
    {G : Sheaf J AddCommGrpCat.{w}}
    (i : F ⟶ (sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G) [Mono i] :
    ∃ G' : Sheaf J AddCommGrpCat.{w},
      Nonempty ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G' ≅ F) :=
  exists_sheafCompose_iso_of_small.{w, t} J F
    (small_of_mono.{w, t} J i (small_sheafCompose_obj.{w, t} J G))

/-- **A quotient of a universe lift is a universe lift.** The kernel of the quotient map is a
subsheaf of a universe lift, hence a universe lift, and the lift preserves cokernels. -/
theorem exists_sheafCompose_iso_of_epi {F : Sheaf J AddCommGrpCat.{max w t}}
    {G : Sheaf J AddCommGrpCat.{w}}
    (p : (sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G ⟶ F) [Epi p] :
    ∃ G' : Sheaf J AddCommGrpCat.{w},
      Nonempty ((sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}).obj G' ≅ F) := by
  let L := sheafCompose J AddCommGrpCat.uliftFunctor.{t, w}
  have : PreservesFiniteColimits L := uliftSheafCompose_preservesFiniteColimits.{w, t} J
  obtain ⟨K, ⟨eK⟩⟩ := exists_sheafCompose_iso_of_mono.{w, t} J (kernel.ι p)
  let f : K ⟶ G := L.preimage (eK.hom ≫ kernel.ι p)
  refine ⟨cokernel f, ⟨PreservesCokernel.iso L f ≪≫ ?_⟩⟩
  have hf : L.map f = eK.hom ≫ kernel.ι p := L.map_preimage _
  refine cokernel.mapIso (L.map f) (kernel.ι p) eK (Iso.refl _) (by simp [hf]) ≪≫ ?_
  exact (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p)).coconePointUniqueUpToIso
    (cokernelIsCokernel _) |>.symm

end Stacks.Cohomology.CoefficientLift
