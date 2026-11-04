module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SmallEtaleSitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatShriek
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MethodeDeLa.PrimeToEllDictionary
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local constancy with finite projective values on Mathlib's small étale site

A sheaf of `Λ`-modules is locally constant with finite projective values
(`Stacks.ConstantSheaf.IsFiniteProjectiveLocallyConstant`) on Mathlib's small étale site exactly
when its restriction to the small étale site of Stacks 021B is, and the condition survives inverse
image along any morphism of schemes and restriction along any étale morphism.

## Main results

* `AlgebraicGeometry.SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff`
* `Stacks.EtaleCohomology.isFiniteProjectiveLocallyConstant_etaleModuleInverseImage`
* `Stacks.EtaleCohomology.isFiniteProjectiveLocallyConstant_etaleModuleRestriction`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry.SmallEtale

open Stacks.ConstantSheaf

attribute [local instance] Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize
attribute [local instance] Stacks.Sites.overPost_isDenseSubsite

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [Ring Λ]

/-- **Local constancy with finite projective values transports between the two small étale
sites.** The restriction along the embedding of a sheaf of `Λ`-modules on Mathlib's small étale
site is locally constant with finite projective values exactly when the sheaf is. -/
public theorem isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff
    (F : Sheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)) :
    IsFiniteProjectiveLocallyConstant Λ (topology B X.obj X.property)
        ((sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).inverse.obj F) ↔
      IsFiniteProjectiveLocallyConstant Λ X.obj.smallEtaleTopology F :=
  Stacks.Sites.forall_exists_cover_iff_of_isDenseSubsite
    (topology B X.obj X.property) X.obj.smallEtaleTopology (toEtaleSite B X.obj X.property)
    (T := fun V => ∃ E : ModuleCat.{max (u + 1) r} Λ, Module.Finite Λ E ∧ Module.Projective Λ E ∧
      Nonempty ((constantSheaf ((topology B X.obj X.property).over V) _).obj E ≅
        ((topology B X.obj X.property).overPullback _ V).obj
          ((sheafEquiv B X.obj X.property (ModuleCat.{max (u + 1) r} Λ)).inverse.obj F)))
    (T' := fun W => ∃ E : ModuleCat.{max (u + 1) r} Λ, Module.Finite Λ E ∧ Module.Projective Λ E ∧
      Nonempty ((constantSheaf (X.obj.smallEtaleTopology.over W) _).obj E ≅
        (X.obj.smallEtaleTopology.overPullback _ W).obj F))
    (fun g ⟨E, h1, h2, ⟨φ⟩⟩ => ⟨E, h1, h2, ⟨(mapPullbackConstantSheafIso _ _ g).app E ≪≫
      ((topology B X.obj X.property).overMapPullback _ g).mapIso φ⟩⟩)
    (fun g ⟨E, h1, h2, ⟨φ⟩⟩ => ⟨E, h1, h2, ⟨(mapPullbackConstantSheafIso _ _ g).app E ≪≫
      (X.obj.smallEtaleTopology.overMapPullback _ g).mapIso φ⟩⟩)
    (fun V => exists_congr fun E => and_congr_right fun _ => and_congr_right fun _ =>
      nonempty_constantSheaf_iso_overPullback_sheafPushforward_iff
        (topology B X.obj X.property) X.obj.smallEtaleTopology (toEtaleSite B X.obj X.property)
        (ModuleCat.{max (u + 1) r} Λ) V E F)

end AlgebraicGeometry.SmallEtale

open AlgebraicGeometry Stacks.ConstantSheaf

namespace Stacks.EtaleCohomology

attribute [local instance] AlgebraicGeometry.SmallEtale.hasWeakSheafify_over_moduleCat_ring
  AlgebraicGeometry.SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (Λ : Type r) [Ring Λ]

/-- **Local constancy with finite projective values survives inverse image** along any morphism of
schemes, on Mathlib's small étale site. -/
@[sga "6 IV 2.7" "special case"]
public theorem isFiniteProjectiveLocallyConstant_etaleModuleInverseImage {X Y : Scheme.{u}}
    (g : Y ⟶ X) (F : EtaleModules.{u, r} Λ X)
    (hF : IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F) :
    IsFiniteProjectiveLocallyConstant Λ Y.smallEtaleTopology
      ((etaleModuleInverseImage.{u, r} Λ g).obj F) := by
  have : Small.{u} ({X, Y} : Set Scheme.{u}) := inferInstance
  let B := BigEtaleSite.ofSet ({X, Y} : Set Scheme.{u})
  let X' : B.Scheme := B.obj X (BigEtaleSite.contains_ofSet _ (by simp))
  let Y' : B.Scheme := B.obj Y (BigEtaleSite.contains_ofSet _ (by simp))
  let g' : Y' ⟶ X' := ObjectProperty.homMk g
  have hB := (SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff B X' Λ F).2 hF
  have hP := isFiniteProjectiveLocallyConstant_smallEtaleSheafPullback B Λ g' _ hB
  refine (SmallEtale.isFiniteProjectiveLocallyConstant_sheafEquiv_inverse_iff B Y' Λ _).1 ?_
  exact isFiniteProjectiveLocallyConstant_congr _ _
    (etaleModulesToSmallEtalePullbackIso B Λ g' F).symm hP

/-- **Local constancy with finite projective values survives restriction** along an étale
morphism, on Mathlib's small étale site. -/
public theorem isFiniteProjectiveLocallyConstant_etaleModuleRestriction {X Y : Scheme.{u}}
    (g : Y ⟶ X) [Etale g] (F : EtaleModules.{u, r} Λ X)
    (hF : IsFiniteProjectiveLocallyConstant Λ X.smallEtaleTopology F) :
    IsFiniteProjectiveLocallyConstant Λ Y.smallEtaleTopology
      ((etaleModuleRestriction.{u, r} Λ g).obj F) :=
  isFiniteProjectiveLocallyConstant_congr _ _
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ g).app F)
    (isFiniteProjectiveLocallyConstant_etaleModuleInverseImage Λ g F hF)

end Stacks.EtaleCohomology

end
