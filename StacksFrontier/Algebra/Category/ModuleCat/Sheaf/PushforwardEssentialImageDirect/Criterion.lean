module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImageDirect.ModuleDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Deformation.ToposThickening.RestrictScalarsEssentialImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardFullyFaithful.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The essential image of the direct image of modules along a closed immersion of ringed topoi

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi whose underlying morphism of
topoi is a closed immersion and whose structure map `i^# : O' ⟶ i_*O` is locally surjective, and
let `I ⊆ O'` be the kernel of `i^#`. An `O'`-module `G` is in the essential image of the direct
image `i_* : Mod(O) ⥤ Mod(O')` exactly when `I` annihilates `G`.

## Main results

* `Stacks.Sheaves.PushforwardEssentialImage.essImage_pushforwardModules_iff`: for a closed
  immersion of topoi `f` and a locally surjective `α : O' ⟶ f_*O`, a sheaf of `O'`-modules is in
  the essential image of `Stacks.Sheaves.PushforwardEssentialImage.pushforwardModules f O α`
  exactly when the sectionwise kernel of `α` annihilates it.
* `AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`:
  the same for a closed immersion of ringed topoi and its kernel ideal.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe w v u v' u'

namespace Stacks.Sheaves.PushforwardEssentialImage

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w})]

/-- Let `f` be a closed immersion of topoi, `O` a sheaf of rings on the source and
`α : O' ⟶ f_*O` a locally surjective map of sheaves of rings on the target. A sheaf of
`O'`-modules is in the essential image of the direct image `Mod(O) ⥤ Mod(O')` determined by `α`
exactly when the sectionwise kernel of `α` annihilates it. -/
theorem essImage_pushforwardModules_iff
    {f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w))}
    (hf : MorphismOfTopoi.IsClosedImmersion f) (O : Sheaf J RingCat.{w})
    {O' : Sheaf K RingCat.{w}} (α : O' ⟶ pushforwardRingSheaf f O)
    [Presheaf.IsLocallySurjective K α.hom] (G : SheafOfModules.{w} O') :
    (pushforwardModules f O α).essImage G ↔
      ∀ (U : Dᵒᵖ) (a : O'.obj.obj U), a ∈ RingHom.ker (α.hom.app U).hom →
        ∀ m : G.val.obj U, a • m = 0 := by
  have hfull : f.pushforward.Full := hf.1.1
  have hfaithful : f.pushforward.Faithful := hf.1.2
  refine ⟨smul_eq_zero_of_essImage_pushforwardModules α, fun hG ↦ ?_⟩
  obtain ⟨H, ⟨e⟩⟩ := Deformation.ToposThickening.essImage_restrictScalars_of_smul_eq_zero α G hG
  obtain ⟨F, ⟨e'⟩⟩ := essImage_pushforwardModuleFunctor H
    (moduleSheaf_mem_essImage_pushforward hf H)
  exact ⟨F, ⟨(SheafOfModules.restrictScalars α).mapIso e' ≪≫ e⟩⟩

end Stacks.Sheaves.PushforwardEssentialImage

namespace AlgebraicGeometry

open Stacks.Sheaves.PushforwardEssentialImage

/-- An `O'`-module is a direct image from the closed ringed subtopos if and only if the kernel
ideal of the structure map acts trivially on it. -/
theorem ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates
    (S : ClosedRingedImmersion.{v, u, v', u', w})
    (G : SheafOfModules.{w} S.targetRingSheaf) :
    S.hom.pushforwardModules.essImage G ↔
      ∀ (U : S.target.Cᵒᵖ) (a : S.targetRingSheaf.obj.obj U),
        a ∈ S.ideal.obj U → ∀ m : G.val.obj U, a • m = 0 := by
  have hls : Presheaf.IsLocallySurjective S.target.J S.hom.structureRingMap.hom :=
    S.structureRingMap_isLocallySurjective
  refine (essImage_pushforwardModules_iff S.isClosedImmersion _ S.hom.structureRingMap G).trans ?_
  refine ⟨fun h U a ha m ↦ h U a ?_ m, fun h U a ha m ↦ h U a ?_ m⟩
  · rwa [S.ideal_obj] at ha
  · rwa [S.ideal_obj]

end AlgebraicGeometry

end
