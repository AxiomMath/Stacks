module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChange
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangle
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow
import StacksCore.Tactic.StacksAttribute

/-!
# The augmentation of the standard resolution is epi, and `ε^*ε_* = id`

Let `C` be a site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on `C` and
let `𝒫_• ⟶ ℬ` be the standard resolution of Section 08UQ, read on the site `Δ × C` as the
augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` of [Stacks, Section 92.19]. This file proves that `ε` is
surjective on sections, hence locally surjective and an epimorphism, and deduces the
identification `ε^*ε_* ≅ id` of extension of scalars along `ε` applied to restriction of scalars
along `ε`.

## Main definitions

* `CategoryTheory.Sheaf.simplicialAugmentationRing`: the augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` on
  `Δ × C`, as a map of sheaves of (not necessarily commutative) rings.
* `CategoryTheory.Sheaf.resolutionAugmentationCounitIso`: the isomorphism `ε^*ε_* ≅ id`.
* `CategoryTheory.Sheaf.extendScalarsSimplicialCoefficientsIso`: that isomorphism at the
  coefficient module of Tag 09DH: `ε^*` of `π^{-1}ℱ` read as a sheaf of `𝒫`-modules is
  `π^{-1}ℱ`.

## Main results

* `CategoryTheory.Sheaf.simplicialAugmentation_surjective`: the augmentation `𝒫 ⟶ π^{-1}ℬ` is
  surjective on sections.
* `CategoryTheory.Sheaf.epi_augmentationCommRingMap` and
  `CategoryTheory.Sheaf.epi_simplicialAugmentationRing`: the augmentation is an epimorphism, of
  sheaves of commutative rings and of sheaves of rings on `Δ × C`.
* `CategoryTheory.Sheaf.fullyFaithful_restrictScalars_simplicialAugmentation`: restriction of
  scalars along the augmentation is fully faithful.
* `CategoryTheory.Sheaf.isIso_resolutionAugmentationCounit`: the counit of the adjunction
  `ε^* ⊣ ε_*` is an isomorphism.
* `CategoryTheory.Sheaf.pullbackTopos_simplicialAugmentation`: the pullback of sheaves of modules
  along the morphism of ringed topoi that `ε` presents is extension of scalars along `ε`.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), and the untagged prose
  preceding it, where `- ⊗^𝐋_{𝒫} π^{-1}ℬ` is introduced.
* [Stacks Project, Tag 08SR](https://stacks.math.columbia.edu/tag/08SR), the standard
  resolution.
* [Stacks Project, Tag 0930](https://stacks.math.columbia.edu/tag/0930), full faithfulness of
  restriction of scalars.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars
  and its adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.SimplicialModules (projectionTopology projectionCommRing projectionRingSheaf
  augmentationCommRingMap projection)

universe u

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-! ### The augmentation on `Δ × C` -/

/-- The augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` of Section 92.19, as a map of sheaves of rings on
`Δ × C`. -/
abbrev simplicialAugmentationRing :
    (sheafCompose (projectionTopology C J)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj (simplicialResolution J f) ⟶
      projectionRingSheaf J B :=
  (sheafCompose (projectionTopology C J) (forget₂ CommRingCat.{u} RingCat.{u})).map
    (augmentationCommRingMap J (resolutionCommAugmentation J f))

/-- The sections of the augmentation `𝒫 ⟶ π^{-1}ℬ` over an object `(n, U)` of `Δ × C` are the
sections over `U` of the degree-`n` augmentation `P_n ⟶ ℬ`. -/
theorem augmentationCommRingMap_hom_app (X : (SimplexCategory × C)ᵒᵖ) :
    (augmentationCommRingMap J (resolutionCommAugmentation J f)).hom.app X =
      (resolutionAugmentation J f (op X.unop.1)).hom.app (op X.unop.2) :=
  rfl

/-! ### Epi-ness -/

/-- The augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` of the standard resolution is surjective on sections. -/
theorem simplicialAugmentation_surjective (X : (SimplexCategory × C)ᵒᵖ) :
    Function.Surjective
      ((augmentationCommRingMap J (resolutionCommAugmentation J f)).hom.app X) :=
  resolutionAugmentation_surjective J f (op X.unop.1) (op X.unop.2)

/-- The augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` is locally surjective. -/
instance simplicialAugmentation_isLocallySurjective :
    Sheaf.IsLocallySurjective (augmentationCommRingMap J (resolutionCommAugmentation J f)) :=
  Presheaf.isLocallySurjective_of_surjective (projectionTopology C J) _
    (simplicialAugmentation_surjective J f)

/-- The augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` is an epimorphism of sheaves of commutative rings on
`Δ × C`. -/
instance epi_augmentationCommRingMap :
    Epi (augmentationCommRingMap J (resolutionCommAugmentation J f)) :=
  inferInstance

/-- The augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` is locally surjective as a map of sheaves of rings. -/
instance simplicialAugmentationRing_isLocallySurjective :
    Sheaf.IsLocallySurjective (simplicialAugmentationRing J f) :=
  Presheaf.isLocallySurjective_of_surjective (projectionTopology C J) _
    (simplicialAugmentation_surjective J f)

/-- The augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` is an epimorphism of sheaves of rings on `Δ × C`. -/
instance epi_simplicialAugmentationRing : Epi (simplicialAugmentationRing J f) :=
  inferInstance

/-! ### `ε^*ε_* ≅ id` -/

/-- Restriction of scalars along the augmentation `ε : 𝒫 ⟶ π^{-1}ℬ` is fully faithful. -/
theorem fullyFaithful_restrictScalars_simplicialAugmentation :
    Nonempty (SheafOfModules.restrictScalars.{u} (simplicialAugmentationRing J f)).FullyFaithful :=
  Stacks.SheafOfModules.ChangeOfRings.restrictScalars_fullyFaithful_of_isLocallySurjective.{u}
    (simplicialAugmentationRing J f)

/-- The counit of `ε^* ⊣ ε_*` is an isomorphism at the augmentation of the standard resolution:
the canonical map `π^{-1}ℬ ⊗_𝒫 ℱ_𝒫 ⟶ ℱ` is invertible for every sheaf of `π^{-1}ℬ`-modules
`ℱ`. -/
instance isIso_resolutionAugmentationCounit :
    IsIso (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction.{u}
      (simplicialAugmentationRing J f)).counit :=
  inferInstance

/-- The isomorphism `ε^*ε_* ≅ id`: reading a sheaf of `π^{-1}ℬ`-modules as a sheaf of
`𝒫`-modules through the augmentation and extending scalars back along the augmentation returns
it, naturally. -/
def resolutionAugmentationCounitIso :
    SheafOfModules.restrictScalars.{u} (simplicialAugmentationRing J f) ⋙
        Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} (simplicialAugmentationRing J f) ≅
      𝟭 (SheafOfModules.{u} (projectionRingSheaf J B)) :=
  asIso (Stacks.Sheaves.ModuleAdjunction.extendRestrictScalarsAdjunction.{u}
    (simplicialAugmentationRing J f)).counit

section Coefficients

variable [(projection C).IsCocontinuous (projectionTopology C J) J]

/-- `ε^*` of the coefficient module `CategoryTheory.Sheaf.simplicialCoefficients` of Tag 09DH,
which is `π^{-1}ℱ` read as a sheaf of `𝒫`-modules through the augmentation, is `π^{-1}ℱ`. -/
def extendScalarsSimplicialCoefficientsIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} (simplicialAugmentationRing J f)).obj
        (simplicialCoefficients J f F) ≅ projectionCoefficients J (B := B) F :=
  (resolutionAugmentationCounitIso J f).app (projectionCoefficients J (B := B) F)

end Coefficients

/-- The pullback of sheaves of modules along the morphism of ringed topoi that the augmentation
`ε` presents is extension of scalars `ε^*` along `ε`. -/
theorem pullbackTopos_simplicialAugmentation :
    (AlgebraicGeometry.RingedToposSiteHom.coefficientChange.{u, u, u} (projectionTopology C J)
        (augmentationCommRingMap J (resolutionCommAugmentation J f))).pullbackTopos =
      Stacks.Sheaves.ModuleAdjunction.extendScalars.{u} (simplicialAugmentationRing J f) :=
  AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_coefficientChange.{u}
    (augmentationCommRingMap J (resolutionCommAugmentation J f))

end CategoryTheory.Sheaf

end
