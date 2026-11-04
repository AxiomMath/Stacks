module

public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahClassDisplayed
public import StacksFrontier.Cotangent.SheavesOfRings.AugmentationLowerShriekAssembly
public import StacksFrontier.Cotangent.SheavesOfRings.SimplicialResolutionMooreQuasiIso

/-!
# The third term of the Atiyah triangle is `ℱ`

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it,
let `ℱ` be a sheaf of `ℬ`-modules and let `𝒫 ⟶ π^{-1}ℬ` be the augmentation of the standard
resolution.  [Stacks, Tag 09DH] displays the Atiyah triangle with its third term identified with
`ℱ`.  This file proves that identification, the hypothesis `e₃` of
`CategoryTheory.Sheaf.resolutionAtiyahClass`.

## Main results

* `CategoryTheory.Sheaf.nonempty_resolutionAtiyahLowerShriekCoefficientsIso`: [Stacks, Tag 09D2]
  at the coefficient module of the Atiyah triangle.
* `CategoryTheory.Sheaf.nonempty_resolutionAtiyahTriangleThirdTermIso`: the third term of the
  Atiyah triangle is `ℱ`.

## Implementation notes

The third term of `CategoryTheory.Sheaf.resolutionAtiyahTriangle` is the `Lπ_!` of Remark 09D3 —
derived extension of scalars `Lε^*` along the augmentation followed by the `Lπ_!` of Remark 09CY
— applied to the coefficient module `ε_*(π^{-1}ℱ)`.  It is the composite of two steps:

* the derived base change along the augmentation is dropped by
  `Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso`,
  the module-coefficient dévissage of [Stacks, Tag 09D2] at a complex bounded above by `0`, whose
  hypothesis `hθ` holds for the standard resolution by
  `CategoryTheory.Sheaf.quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap`;
* what remains, `Lπ_!(π^{-1}ℱ[0]) ≅ ℱ[0]`, is
  `Stacks.SimplicialModules.derivedProjectionLowerShriekRestrictionIso`, carried in by
  `CategoryTheory.Sheaf.resolutionAtiyahTriangleThirdTermIso`.

The coefficient module `ℱ[0]` of the Atiyah triangle, as a complex of simplicial `𝒫`-modules,
**is** `ε_*` of `π^{-1}ℱ[0]`: `CategoryTheory.Sheaf.resolutionCoefficientsSingleIso`, which is
Mathlib's `HomologicalComplex.singleMapHomologicalComplex` at restriction of scalars along the
augmentation.  The passage `Q(ℱ[0]) = (singleFunctor _ 0).obj ℱ` is
`DerivedCategory.Q_obj_single_obj`.

The statement is existential because
`Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso`
asserts that an isomorphism exists: it is proved by choosing a resolution of the coefficient
module by standard covers.  The isomorphism at a fixed such resolution, as an explicit
composite, is `CategoryTheory.Sheaf.atiyahTriangleThirdTermIso`
(`StacksFrontier/Cotangent/SheavesOfRings/AtiyahClassDefinite.lean`).

This is one of the two outer-term identifications [Stacks, Tag 09DH] performs, not the equation
itself: the displayed triangle also identifies the first term with `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`, which
is `CategoryTheory.Sheaf.nonempty_resolutionAtiyahTriangleFirstTermIso`.  Neither is it
[Stacks, Tag 09D2], whose statement quantifies over every object of `D(𝒫)`.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the displayed triangle
  whose third term this is.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), the lemma that removes
  the derived base change along the augmentation.
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3) and
  [Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), the two functors `Lπ_!`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.SheafOfModules (moduleSheaves)
open Stacks.SimplicialModules (projection projectionTopology projectionRing
  derivedProjectionLowerShriek augPushforwardC)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-- **The coefficient module of the Atiyah triangle, as a complex, is `ε_*` of `π^{-1}ℱ[0]`.**
Restriction of scalars along the augmentation carries `π^{-1}ℱ` placed in degree `0` to `ℱ`
placed in degree `0`, because it carries the zero object to the zero object; that is Mathlib's
`HomologicalComplex.singleMapHomologicalComplex`. -/
def resolutionCoefficientsSingleIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (HomologicalComplex.single
        (moduleSheaves.{u, u, u, u} (simplicialResolution J f))
        (ComplexShape.up ℤ) 0).obj (simplicialCoefficients J f F) ≅
      (augPushforwardC J (resolutionCommAugmentation J f)).obj
        ((HomologicalComplex.single
          (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
          (ComplexShape.up ℤ) 0).obj (projectionCoefficients J (B := B) F)) :=
  ((HomologicalComplex.singleMapHomologicalComplex
    (SheafOfModules.restrictScalars
      (Stacks.SimplicialModules.augRingMap J (resolutionCommAugmentation J f)))
    (ComplexShape.up ℤ) 0).app (projectionCoefficients J (B := B) F)).symm

/-- **[Stacks, Tag 09D2] at the coefficient module of the Atiyah triangle.**  The third term of
`CategoryTheory.Sheaf.resolutionAtiyahTriangle`, which is the `Lπ_!` of Remark 09D3 applied to
`ε_*(π^{-1}ℱ)`, is the `Lπ_!` of Remark 09CY applied to `π^{-1}ℱ[0]`: the derived extension of
scalars along the augmentation may be dropped. This is the hypothesis `h` of
`CategoryTheory.Sheaf.resolutionAtiyahTriangleThirdTermIso`. -/
theorem nonempty_resolutionAtiyahLowerShriekCoefficientsIso
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Nonempty ((resolutionAtiyahTriangle J f F).obj₃ ≅
      (derivedProjectionLowerShriek C J (targetRing J (B := B))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
            (ComplexShape.up ℤ) 0).obj (projectionCoefficients J (B := B) F)))) := by
  obtain ⟨e⟩ :=
    Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso
      J (resolutionCommAugmentation J f)
      (quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap J f)
      ((HomologicalComplex.single
        (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
        (ComplexShape.up ℤ) 0).obj (projectionCoefficients J (B := B) F))
  exact ⟨(resolutionLowerShriek J f).mapIso
      (DerivedCategory.Q.mapIso (resolutionCoefficientsSingleIso J f F)) ≪≫ e⟩

/-- **`e₃` of [Stacks, Tag 09DH]: the third term of the Atiyah triangle is `ℱ`.**

`CategoryTheory.Sheaf.resolutionAtiyahTriangleThirdTermIso` reduces it to [Stacks, Tag 09D2] at
the coefficient module, and that is
`CategoryTheory.Sheaf.nonempty_resolutionAtiyahLowerShriekCoefficientsIso`. -/
theorem nonempty_resolutionAtiyahTriangleThirdTermIso
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Nonempty ((resolutionAtiyahTriangle J f F).obj₃ ≅
      DerivedCategory.Q.obj
        ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
          (ComplexShape.up ℤ) 0).obj F)) :=
  (nonempty_resolutionAtiyahLowerShriekCoefficientsIso J f F).map
    (resolutionAtiyahTriangleThirdTermIso J f F)

end CategoryTheory.Sheaf

end
