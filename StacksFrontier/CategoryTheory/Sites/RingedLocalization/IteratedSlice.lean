module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.Relocalization

/-!
# The iterated slice of a ringed site, as a morphism of ringed topoi

Let `(C, O)` be a ringed site, `U` an object of `C` and `a : V ⟶ U` a morphism of `C`.
Localizing twice gives the ringed site `((C/U)/(V/U), O|_{V/U})`, and the canonical equivalence
`(C/U)/(V/U) ≌ C/V` of Mathlib's `CategoryTheory.Over.iteratedSliceEquiv` identifies it with the
localization of `(C, O)` at `V`: the structure sheaves agree on the nose, both evaluating at a
further slice object as `O` on its underlying object of `C`.

This file records that identification as a morphism of ringed topoi
`(Sh((C/U)/(V/U)), O|_{V/U}) ⟶ (Sh(C/V), O|_V)`: the inverse image is restriction along
`Over.iteratedSliceForward (V/U)`, which is a continuous and cocontinuous functor of the localized
topologies, and the structure map is the identification of the restricted structure sheaf with the
iterated one. Through this morphism, the localization of `(C/U, O|_U)` at the object `V/U` is the
relocalization of `(C, O)` along `a`.

## Main definitions

* `AlgebraicGeometry.RingedSite.iteratedSliceMorphismOfTopoi`: the morphism of topoi
  `Sh((C/U)/(V/U)) ⟶ Sh(C/V)` induced by `Over.iteratedSliceForward (V/U)`.
* `AlgebraicGeometry.RingedSite.iteratedSliceRingedToposHom`: it as a morphism of ringed topoi.
* `AlgebraicGeometry.RingedSite.iteratedSliceRelocalizationComparison`: the comparison of the
  direct image of the localization at `V/U` with the direct image of the composite.

## Main results

* `AlgebraicGeometry.RingedSite.iteratedSliceInverseImage_eq`: the inverse image of the
  localization of `(C/U, O|_U)` at `V/U` is the inverse image of the relocalization of `(C, O)`
  along `a` followed by the inverse image of the iterated-slice morphism, strictly.
* `AlgebraicGeometry.RingedSite.iteratedSliceRelocalizationTriangle`: consequently the
  localization morphism at `V/U` is the iterated-slice morphism followed by the relocalization
  morphism along `a`, as a 2-isomorphism of ringed topoi.

## References

* [Stacks Project, Tag 04IY](https://stacks.math.columbia.edu/tag/04IY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) {U : X.C} (W : Over U)

/-- The morphism of topoi `Sh((C/U)/(V/U)) ⟶ Sh(C/V)` induced by
`Over.iteratedSliceForward (V/U)`. Its inverse image is restriction along that functor and its
direct image is the right adjoint of that restriction. -/
noncomputable def iteratedSliceMorphismOfTopoi :
    MorphismOfTopoi (Sheaf ((X.J.over U).over W) (Type u))
      (Sheaf (X.J.over W.left) (Type u)) where
  inverseImage := (Over.iteratedSliceForward W).sheafPushforwardContinuous _
    ((X.J.over U).over W) (X.J.over W.left)
  pushforward := (Over.iteratedSliceForward W).sheafPushforwardCocontinuous _
    ((X.J.over U).over W) (X.J.over W.left)
  adj := (Over.iteratedSliceForward W).sheafAdjunctionCocontinuous _
    ((X.J.over U).over W) (X.J.over W.left)
  preservesFiniteLimits := inferInstance

/-- The inverse image of the structure sheaf of the localization at `V`, along the
iterated-slice morphism of topoi, is the structure sheaf of the iterated localization: both
evaluate at a further slice object as `O` on its underlying object of `C`. -/
noncomputable def iteratedSliceInverseImageCommRingIso :
    (inverseImageCommRingFunctor (X.iteratedSliceMorphismOfTopoi W)).obj (X.over W.left).O ≅
      ((X.over U).over W).O :=
  restrictionCommRingIso ((X.J.over U).over W) (X.J.over W.left)
    (Over.iteratedSliceForward W) (X.over W.left).O

/-- The identification of the inverse image of `O|_V` with `O|_{V/U}` is the identity on
underlying sheaves of sets. -/
theorem iteratedSliceInverseImageCommRingIso_forget :
    (sheafCompose ((X.J.over U).over W) (forget CommRingCat.{u})).map
        (X.iteratedSliceInverseImageCommRingIso W).hom =
      𝟙 ((sheafCompose ((X.J.over U).over W) (forget CommRingCat.{u})).obj
        ((X.over U).over W).O) :=
  rfl

/-- The structure map of the iterated-slice morphism in direct-image form, the adjunct of
`iteratedSliceInverseImageCommRingIso` under the adjunction on sheaves of commutative rings. -/
noncomputable def iteratedSliceCommRingFsharpAdjoint :
    (X.over W.left).O ⟶
      (pushforwardCommRingFunctor (X.iteratedSliceMorphismOfTopoi W)).obj
        ((X.over U).over W).O :=
  (commRingImageAdjunction (X.iteratedSliceMorphismOfTopoi W)).homEquiv _ _
    (X.iteratedSliceInverseImageCommRingIso W).hom

/-- The iterated-slice identification, as a morphism of ringed topoi
`(Sh((C/U)/(V/U)), O|_{V/U}) ⟶ (Sh(C/V), O|_V)`. -/
noncomputable def iteratedSliceRingedToposHom :
    AlgebraicGeometry.RingedToposHom (ringedTopos ((X.over U).over W))
      (ringedTopos (X.over W.left)) where
  toToposHom := X.iteratedSliceMorphismOfTopoi W
  fSharp := X.iteratedSliceCommRingFsharpAdjoint W

/-- The underlying morphism of topoi of `iteratedSliceRingedToposHom` is
`iteratedSliceMorphismOfTopoi`. -/
@[simp]
theorem iteratedSliceRingedToposHom_toToposHom :
    (X.iteratedSliceRingedToposHom W).toToposHom = X.iteratedSliceMorphismOfTopoi W :=
  rfl

/-- The inverse-image form of the structure map of the iterated-slice morphism is the identity
on underlying sheaves of sets. -/
theorem forgetRing_iteratedSliceRingedToposHom_fSharpInverseImage :
    (ringedTopos ((X.over U).over W)).forgetRing.map
        (X.iteratedSliceRingedToposHom W).fSharpInverseImage =
      𝟙 ((ringedTopos ((X.over U).over W)).forgetRing.obj
        ((X.over U).over W).O) :=
  (congrArg
      (fun φ ↦ (sheafCompose ((X.J.over U).over W) (forget CommRingCat.{u})).map φ)
      (((commRingImageAdjunction
          (X.iteratedSliceMorphismOfTopoi W)).homEquiv _ _).symm_apply_apply
        (X.iteratedSliceInverseImageCommRingIso W).hom)).trans
    (X.iteratedSliceInverseImageCommRingIso_forget W)

/-- On underlying sheaves of sets, the structure map of the iterated-slice morphism is the unit
of its adjunction at the structure sheaf of the localization at `V`. -/
theorem forgetRing_iteratedSliceRingedToposHom_fSharp :
    (ringedTopos (X.over W.left)).forgetRing.map (X.iteratedSliceRingedToposHom W).fSharp =
      (X.iteratedSliceMorphismOfTopoi W).adj.unit.app
        ((ringedTopos (X.over W.left)).forgetRing.obj (X.over W.left).O) :=
  Adjunction.unit_app_eq_of_homEquiv_symm_eq_id _ _ _
    ((AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv
        (X.iteratedSliceRingedToposHom W)).symm.trans
      (X.forgetRing_iteratedSliceRingedToposHom_fSharpInverseImage W))

/-- The inverse image of the iterated-slice morphism is an equivalence. -/
instance isEquivalence_iteratedSliceInverseImage :
    (X.iteratedSliceMorphismOfTopoi W).inverseImage.IsEquivalence :=
  inferInstanceAs
    (((Over.iteratedSliceEquiv W).sheafCongr ((X.J.over U).over W) (X.J.over W.left)
      (Type u)).inverse).IsEquivalence

/-- The direct image of the iterated-slice morphism is an equivalence. -/
instance isEquivalence_iteratedSlicePushforward :
    (X.iteratedSliceMorphismOfTopoi W).pushforward.IsEquivalence :=
  Adjunction.isEquivalence_right_of_isEquivalence_left (X.iteratedSliceMorphismOfTopoi W).adj

/-- The direct image of the iterated-slice morphism of *ringed* topoi is an equivalence. -/
instance isEquivalence_iteratedSliceRingedToposHom_pushforward :
    (X.iteratedSliceRingedToposHom W).toToposHom.pushforward.IsEquivalence :=
  X.isEquivalence_iteratedSlicePushforward W

/-- The structure map of the iterated-slice morphism is invertible on underlying sheaves of
sets. -/
instance isIso_forgetFSharp_iteratedSliceRingedToposHom :
    IsIso (AlgebraicGeometry.RingedToposHom.forgetFSharp (X.iteratedSliceRingedToposHom W)) := by
  rw [show AlgebraicGeometry.RingedToposHom.forgetFSharp (X.iteratedSliceRingedToposHom W) =
      (X.iteratedSliceMorphismOfTopoi W).adj.unit.app
        ((X.over W.left).ringedTopos.forgetRing.obj (X.over W.left).O) from
    X.forgetRing_iteratedSliceRingedToposHom_fSharp W]
  exact NatIso.isIso_app_of_isIso (X.iteratedSliceMorphismOfTopoi W).adj.unit _

/-! ### The iterated slice as a relocalization -/

/-- The composite of the iterated-slice morphism with the relocalization along `W.hom`. -/
noncomputable abbrev iteratedSliceCompRelocalization :
    AlgebraicGeometry.RingedToposHom (ringedTopos ((X.over U).over W))
      (ringedTopos (X.over U)) :=
  AlgebraicGeometry.RingedToposHom.comp
    (X := ringedTopos ((X.over U).over W)) (Y := ringedTopos (X.over W.left))
    (Z := ringedTopos (X.over U))
    (X.relocalizationRingedToposHom W.hom) (X.iteratedSliceRingedToposHom W)

/-- The inverse image of the localization of `(C/U, O|_U)` at the object `V/U` is the inverse
image of the relocalization along `W.hom` followed by the inverse image of the iterated-slice
morphism, as a strict equality of functors. -/
theorem iteratedSliceInverseImage_eq :
    (X.iteratedSliceCompRelocalization W).toToposHom.inverseImage =
      ((X.over U).localizationRingedToposHom W).toToposHom.inverseImage :=
  X.overMap_inverseImage_iteratedSlice W.hom

/-- The comparison of the two direct images: the localization of `(C/U, O|_U)` at `V/U` and the
composite of the iterated-slice morphism with the relocalization along `W.hom` have the same
inverse image, so their direct images are canonically isomorphic by uniqueness of right
adjoints. -/
noncomputable def iteratedSliceRelocalizationComparison :
    ((X.over U).localizationRingedToposHom W).toToposHom.pushforward ≅
      (X.iteratedSliceCompRelocalization W).toToposHom.pushforward :=
  Adjunction.rightAdjointUniq
    (((X.over U).localizationRingedToposHom W).toToposHom.adj.ofNatIsoLeft
      (eqToIso (X.iteratedSliceInverseImage_eq W).symm))
    (X.iteratedSliceCompRelocalization W).toToposHom.adj

/-- On underlying sheaves of sets, the structure map of the composite of the iterated-slice
morphism with the relocalization along `W.hom` is the unit of the composite adjunction. -/
theorem forgetRing_iteratedSliceCompRelocalization_fSharp :
    (X.over U).ringedTopos.forgetRing.map (X.iteratedSliceCompRelocalization W).fSharp =
      ((X.overMapMorphismOfTopoi W.hom).adj.comp
          (X.iteratedSliceMorphismOfTopoi W).adj).unit.app
        ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) := by
  rw [AlgebraicGeometry.RingedToposHom.comp_fSharp_forget
      (X.relocalizationRingedToposHom W.hom) (X.iteratedSliceRingedToposHom W),
    X.forgetRing_relocalizationRingedToposHom_fSharp W.hom,
    X.forgetRing_iteratedSliceRingedToposHom_fSharp W]
  exact (Adjunction.comp_unit_app _ _ _).symm

/-- The comparison of the two inverse images is the identity at the structure sheaf. -/
theorem iteratedSliceInverseImageEqToIso_hom_app_structureSheaf :
    (eqToIso (X.iteratedSliceInverseImage_eq W).symm).hom.app
        ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) =
      𝟙 (((X.over U).over W).ringedTopos.forgetRing.obj ((X.over U).over W).O) := by
  rw [eqToIso.hom, CategoryTheory.eqToHom_app]
  rfl

/-- Transporting the adjunction of the localization at `W` along the equality of its inverse
image with the composite inverse image does not change its unit at the structure sheaf. -/
theorem iteratedSliceAdjunction_ofNatIsoLeft_unit_app :
    ((((X.over U).localizationRingedToposHom W).toToposHom.adj).ofNatIsoLeft
          (eqToIso (X.iteratedSliceInverseImage_eq W).symm)).unit.app
        ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) =
      ((X.over U).overMorphismOfTopoi W).adj.unit.app
        ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) :=
  (congrArg (fun m ↦ ((X.over U).overMorphismOfTopoi W).adj.unit.app _ ≫
      ((X.over U).overMorphismOfTopoi W).pushforward.map m)
    (X.iteratedSliceInverseImageEqToIso_hom_app_structureSheaf W)).trans
    ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _))

/-- The unit of the localization at `W`, followed by the comparison of the two direct images,
is the unit of the composite adjunction, at the underlying sheaf of sets of the structure
sheaf. -/
theorem unit_iteratedSliceRelocalizationComparison_hom_app :
    ((X.over U).overMorphismOfTopoi W).adj.unit.app
          ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) ≫
        (X.iteratedSliceRelocalizationComparison W).hom.app
          (((X.over U).over W).ringedTopos.forgetRing.obj ((X.over U).over W).O) =
      ((X.overMapMorphismOfTopoi W.hom).adj.comp
          (X.iteratedSliceMorphismOfTopoi W).adj).unit.app
        ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) := by
  rw [← X.iteratedSliceAdjunction_ofNatIsoLeft_unit_app W]
  exact Adjunction.unit_rightAdjointUniq_hom_app _ _ _

/-- As a 2-isomorphism of ringed topoi, localizing `(C/U, O|_U)` at the object `W` is the
iterated-slice identification followed by relocalizing `(C, O)` along `W.hom : W.left ⟶ U`. -/
noncomputable def iteratedSliceRelocalizationTriangle :
    AlgebraicGeometry.RingedToposHom.TwoIso
      (A := ((X.over U).over W).ringedTopos) (B := (X.over U).ringedTopos)
      ((X.over U).localizationRingedToposHom W)
      (X.iteratedSliceCompRelocalization W) where
  e := X.iteratedSliceRelocalizationComparison W
  commutes := by
    rw [show AlgebraicGeometry.RingedToposHom.forgetFSharp
          ((X.over U).localizationRingedToposHom W) =
        ((X.over U).overMorphismOfTopoi W).adj.unit.app
          ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) from
      (X.over U).forgetRing_localizationRingedToposHom_fSharp W,
      show AlgebraicGeometry.RingedToposHom.forgetFSharp
          (X.iteratedSliceCompRelocalization W) =
        ((X.overMapMorphismOfTopoi W.hom).adj.comp
            (X.iteratedSliceMorphismOfTopoi W).adj).unit.app
          ((X.over U).ringedTopos.forgetRing.obj (X.over U).O) from
      X.forgetRing_iteratedSliceCompRelocalization_fSharp W]
    exact X.unit_iteratedSliceRelocalizationComparison_hom_app W

end AlgebraicGeometry.RingedSite

end
