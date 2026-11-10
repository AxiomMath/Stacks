module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsDirectSums
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.GeneralCoefficients
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowDescent
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackExactness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Inverse image is exact on `D(X_étale, Λ)`

Let `Λ` be a commutative ring and `f : X ⟶ Y` a morphism of schemes. The morphism of ringed topoi
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` of `Stacks.EtaleCohomology.EtaleCoefficients.ringedToposHom` has
structure sheaf the constant sheaf `Λ̲` on both sides, and the inverse image of the constant sheaf
`Λ̲` on `Y_étale` is the constant sheaf on `X_étale`. So the inverse image `f⁻¹Λ̲ ⟶ Λ̲` of its
structure map is an isomorphism, the pullback of sheaves of `Λ̲`-modules involves no change of
rings, and it is exact. This file records that and its consequences on the derived categories
`D(-_étale, Λ)`:

* `f⁻¹` carries `D^{≥n}` into `D^{≥n}` and `D^{≤n}` into `D^{≤n}`;
* `Rf_*` carries `D^{≥n}` into `D^{≥n}`.

These are the facts about the inverse and direct images that the reductions of the proofs of the
Künneth section use (Stacks, Tags 0F1H, 0F1I and 0F1J): the base change map
`(f')⁻¹Rg_* ⟶ Rh_*e⁻¹` and the canonical map of Tag 0F1J are natural transformations between
exact functors which do not lower degrees.

## Main results

All in the namespace `Stacks.EtaleCohomology.EtaleCoefficients`.

* `isIso_inverseImageStructureMap` — **the inverse image of the structure map is an
  isomorphism**: `f⁻¹Λ̲ ≅ Λ̲`, because both sides are left adjoint to global sections.
* `preservesFiniteLimits_pullbackTopos` — the pullback of sheaves of `Λ̲`-modules is exact.
* `isGE_pullback_obj`, `isLE_pullback_obj`, `isGE_pushforward_obj` — the boundedness statements.

That `f⁻¹` and `Rf_*` are exact functors of triangulated categories is
`Stacks.EtaleCohomology.EtaleCoefficients.pullback_isTriangulated` and
`Stacks.EtaleCohomology.EtaleCoefficients.pushforward_isTriangulated`.

## Implementation notes

The structure map of `ringedToposHom Λ f` is built from the sheafification unit of the constant
presheaf (`Stacks.EtaleCohomology.EtaleCoefficients.structureMap`). Its inverse image is compared
with the isomorphism `Stacks.ConstantSheaf.sheafPullbackConstantSheafIso`, the uniqueness of left
adjoints to global sections, through the characterization
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app`: both are the unique map whose
transpose to global sections is the unit of the constant sheaf adjunction on `X`, and for the
inverse image of the structure map that is `toSheafify_app_comp_structureMap_app`.

## References

* [Stacks Project, Tag 0F1J](https://stacks.math.columbia.edu/tag/0F1J)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 0D7T](https://stacks.math.columbia.edu/tag/0D7T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable (Λ : Type (u + 1)) [CommRing Λ]

/-! ### The inverse image of the structure map -/

section StructureMap

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Base change along `f` carries the terminal object `Y` of the small model of `Y_étale` to a
terminal object of the small model of `X_étale`: it preserves finite limits. -/
def baseChangeTerminalIsTerminal : IsTerminal ((baseChange f).obj (terminal Y)) :=
  (terminalIsTerminal Y).isTerminalObj (baseChange f) _

/-- The comparison of the base change of the terminal object with the terminal object. -/
def baseChangeTerminalIso : (baseChange f).obj (terminal Y) ≅ terminal X :=
  (baseChangeTerminalIsTerminal f).uniqueUpToIso (terminalIsTerminal X)

/-- **The inverse image of the structure map**, `f⁻¹Λ̲ ⟶ Λ̲`: the transpose of the structure map
`Λ̲ ⟶ f_*Λ̲` of `ringedToposHom Λ f` across the inverse image / direct image adjunction on sheaves
of commutative rings. It is the structure map of the ring-theoretic half
`StacksPullbackFactorization.auxHomH` of the morphism of ringed topoi. -/
abbrev inverseImageStructureMap :
    ((baseChange f).sheafPullback CommRingCat.{u + 1} (topology Y) (topology X)).obj
        (ringedTopos Λ Y).O ⟶ (ringedTopos Λ X).O :=
  (((baseChange f).sheafAdjunctionContinuous CommRingCat.{u + 1} (topology Y)
    (topology X)).homEquiv _ _).symm (structureMap Λ f)

/-- The composite adjunction `Λ ↦ f⁻¹Λ̲ ⊣ Γ(X, -)`: the constant sheaf adjunction on `Y`, then the
inverse image / direct image adjunction, with sections of the direct image over `Y` read as
sections over `X`. -/
abbrev constantPullbackAdjunction :
    constantSheaf (topology Y) CommRingCat.{u + 1} ⋙
        (baseChange f).sheafPullback CommRingCat.{u + 1} (topology Y) (topology X) ⊣
      (sheafSections (topology X) CommRingCat.{u + 1}).obj (op (terminal X)) :=
  ((constantSheafAdj (topology Y) CommRingCat.{u + 1} (terminalIsTerminal Y)).comp
      ((baseChange f).sheafAdjunctionContinuous CommRingCat.{u + 1} (topology Y)
        (topology X))).ofNatIsoRight
    (Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal (baseChange f) CommRingCat.{u + 1}
      (topology Y) (topology X) (baseChangeTerminalIso f))

/-- The transpose of the inverse image of the structure map to global sections over `X` is the
unit of the constant sheaf adjunction on `X`. -/
theorem constantPullbackAdjunction_homEquiv_inverseImageStructureMap :
    (constantPullbackAdjunction f).homEquiv _ _ (inverseImageStructureMap Λ f) =
      (constantSheafAdj (topology X) CommRingCat.{u + 1} (terminalIsTerminal X)).unit.app
        (CommRingCat.of Λ) := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  dsimp only [Equiv.trans_apply]
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  simp only [Functor.flip_obj_obj, ObjectProperty.ι_obj, Functor.comp_obj, constantSheafAdj,
    Adjunction.comp_unit_app, evaluation_obj_obj, Functor.const_obj_obj,
    constantPresheafAdj_unit_app, sheafificationAdjunction_unit_app, evaluation_obj_map,
    Category.id_comp, Functor.flip_obj_map, ObjectProperty.ι_map,
    Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal]
  have h₁ := toSheafify_app_comp_structureMap_app Λ f (op (terminal Y))
  have hn := (toSheafify (topology X) ((Functor.const _).obj (CommRingCat.of Λ))).naturality
    (baseChangeTerminalIso f).inv.op
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hn
  exact (h₁ =≫ _).trans hn.symm

/-- **The inverse image of the structure map is an isomorphism**, `f⁻¹Λ̲ ≅ Λ̲`. Both sheaves are
left adjoint to global sections over `X`, and the inverse image of the structure map is the
comparison `Stacks.ConstantSheaf.sheafPullbackConstantSheafIso` of the two left adjoints. -/
theorem isIso_inverseImageStructureMap : IsIso (inverseImageStructureMap Λ f) := by
  have h : inverseImageStructureMap Λ f =
      ((constantPullbackAdjunction f).leftAdjointUniq
        (constantSheafAdj (topology X) CommRingCat.{u + 1} (terminalIsTerminal X))).hom.app
          (CommRingCat.of Λ) := by
    apply ((constantPullbackAdjunction f).homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      constantPullbackAdjunction_homEquiv_inverseImageStructureMap]
  rw [h]
  infer_instance

/-- **The pullback of sheaves of `Λ̲`-modules along `f` is left exact.** The inverse image of the
structure map is an isomorphism, hence flat, and base change is a morphism of sites, so this is
`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_preservesFiniteLimits`. -/
@[sga "4 IV 13.7" "special case"]
instance preservesFiniteLimits_pullbackTopos :
    PreservesFiniteLimits (ringedToposHom Λ f).pullbackTopos :=
  (ringedToposHom Λ f).pullbackTopos_preservesFiniteLimits (isMorphismOfSites_ringedToposHom Λ f)
    (SheafOfModules.isFlatMapULift_of_isIso _ (isIso_inverseImageStructureMap Λ f))

/-- The pullback of sheaves of `Λ̲`-modules along `f` is right exact, being a left adjoint. -/
instance preservesFiniteColimits_pullbackTopos :
    PreservesFiniteColimits (ringedToposHom Λ f).pullbackTopos :=
  (ringedToposHom Λ f).pullbackTopos_preservesFiniteColimits

end StructureMap

/-! ### The inverse and direct images on `D(-_étale, Λ)` -/

section Derived

-- `derivedPullback` (`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/
-- AdjunctionForRingedTopoi.lean:394`) is stated for the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The inverse image `f⁻¹` on `D(-_étale, Λ)` preserves boundedness below.** It is computed by
the degreewise pullback of sheaves of `Λ̲`-modules, which is exact
(`preservesFiniteLimits_pullbackTopos`). -/
theorem isGE_pullback_obj (K : DerivedModules Λ Y) (n : ℤ) (hK : K.IsGE n) :
    ((pullback Λ f).obj K).IsGE n :=
  Stacks.Cohomology.CohomologicalDescent.isGE_derivedPullback_obj (ringedToposHom Λ f) K n hK

/-- **The inverse image `f⁻¹` on `D(-_étale, Λ)` preserves boundedness above.** -/
theorem isLE_pullback_obj (K : DerivedModules Λ Y) (n : ℤ) (hK : K.IsLE n) :
    ((pullback Λ f).obj K).IsLE n :=
  Stacks.Cohomology.CohomologicalDescent.isLE_derivedPullback_obj (ringedToposHom Λ f) K n hK

/-- **The derived direct image `Rf_*` on `D(-_étale, Λ)` preserves boundedness below**: it is
right adjoint to `f⁻¹`, which preserves boundedness above. -/
theorem isGE_pushforward_obj (K : DerivedModules Λ X) (n : ℤ) (hK : K.IsGE n) :
    ((pushforward Λ f).obj K).IsGE n :=
  Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction
    (ringedToposHom Λ f) (adjunction Λ f) (fun L m hL => isLE_pullback_obj Λ f L m hL) K n hK

end Derived

end Stacks.EtaleCohomology.EtaleCoefficients

end
