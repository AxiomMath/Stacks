module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsTransitivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.UnderivedTensorInverseImage
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangleThirdTerm
public import StacksFrontier.Cotangent.SheavesOfRings.AugmentationDifferentialsUncurry
public import StacksFrontier.Cotangent.SheavesOfRings.TensorUncurry

/-!
# The first term of the Atiyah triangle is `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`, and the Atiyah class

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it,
let `ℱ` be a sheaf of `ℬ`-modules and let `P_• ⟶ ℬ` be the standard resolution of `ℬ` over `𝒜`.
[Stacks, Tag 09DH] displays the Atiyah triangle with its first term identified with
`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`. This file proves that such an identification exists — the hypothesis `e₁` of
`CategoryTheory.Sheaf.resolutionAtiyahClass` — with nothing assumed, and with the third-term
identification it proves that the displayed triangle

  `L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)⟦1⟧`

of [Stacks, Tag 09DH] is distinguished for some identifications of its outer terms, the last arrow
being the Atiyah class of [Stacks, Tag 09DI].

The first term of `CategoryTheory.Sheaf.resolutionAtiyahTriangle` is the `Lπ_!` of Remark 09D3 —
derived extension of scalars `Lε^*` along the augmentation followed by the `Lπ_!` of Remark 09CY —
applied to `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ε_*(π^{-1}ℱ)`, the first term of the sequence of Tag 09DG. The
transitivity `M ⊗_𝒫 ε_*𝒩 ≅ ε_*((M ⊗_𝒫 π^{-1}ℬ) ⊗_{π^{-1}ℬ} 𝒩)` writes it as
`ε_*(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)`, where `Ω_{P_•/𝒜} ⊗_{P_•} ℬ` is the simplicial module of
[Stacks, Tag 08SS]; the derived base change along the augmentation is then dropped by
[Stacks, Tag 09D2].

## Main definitions

* `CategoryTheory.Sheaf.atiyahFirstTermCoefficients`: the sheaf of `π^{-1}ℬ`-modules
  `Y₀ = (Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 π^{-1}ℬ) ⊗_{π^{-1}ℬ} π^{-1}ℱ` on `Δ × C`.
* `CategoryTheory.Sheaf.simplicialPrincipalPartsX₁Iso`:
  `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ ≅ ε_*(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)`.
* `CategoryTheory.Sheaf.resolutionDifferentialsSingleIso`: the same, at a sheaf placed in degree
  `0`.

## Main results

* `CategoryTheory.Sheaf.nonempty_resolutionAtiyahLowerShriekDifferentialsIso`: **[Stacks, Tag 09D2]
  at the first term**, which drops the derived base change along the augmentation.
* `CategoryTheory.Sheaf.nonempty_resolutionAtiyahTriangleFirstTermIso`: **`e₁`, with nothing
  assumed.**
* `CategoryTheory.Sheaf.exists_resolutionAtiyahDisplayedTriangle_distinguished` and
  `CategoryTheory.Sheaf.exists_resolutionAtiyahClass_mem_distinguished`: the displayed triangle and
  the Atiyah class for some identifications of the outer terms.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), Equation 92.19.0.2, the
  displayed triangle, and [Tag 09DI](https://stacks.math.columbia.edu/tag/09DI), Definition
  92.19.1, the Atiyah class, which is its last arrow.
* [Stacks Project, Tag 09DG](https://stacks.math.columbia.edu/tag/09DG), the short exact sequence
  the triangle is the image of.
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2), the lemma that removes the
  derived base change along the augmentation.
* [Stacks Project, Tag 09D3](https://stacks.math.columbia.edu/tag/09D3), the functor `Lπ_!` of the
  triangle, and [Tag 09CY](https://stacks.math.columbia.edu/tag/09CY), its second factor.
* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS), the cotangent complex of a
  homomorphism of sheaves of rings.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.SheafOfModules (moduleSheaves derivationsFunctor)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Sheaves.RingedToposModules (commRingSheaf commRingSheafMap extendScalars)
open Stacks.SimplicialModules (projection projectionTopology projectionRing projectionCommRing
  uncurryMod derivedProjectionLowerShriek augPushforwardC)
open Stacks.SimplicialModules.TensorUncurry (tensorUncurryIso)

universe u

namespace CategoryTheory.Sheaf

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B)

/-! ### `X₁` in the shape Tag 09D2 consumes -/

/-- **`Y₀ = (Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 π^{-1}ℬ) ⊗_{π^{-1}ℬ} π^{-1}ℱ`**, a sheaf of `π^{-1}ℬ`-modules on
`Δ × C`. -/
abbrev atiyahFirstTermCoefficients (F : SheafOfModules.{u} (targetRing J (B := B))) :
    SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))) :=
  (PresheafOfModules.sheafification (R := projectionRing C J (targetRing J (B := B)))
      (𝟙 _)).obj
    (Stacks.tensorObj (O := ((projectionCommRing J B)).obj)
      (projectionCoefficients J (B := B) F).val
      ((PresheafOfModules.restrictScalars
          (𝟙 (projectionRing C J (targetRing J (B := B))).obj)).obj
        ((SheafOfModules.forget _).obj
          ((extendAugmentationScalars J f).obj (simplicialDifferentials J f)))))

omit [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)] in
/-- **The first term of the sequence of principal parts is the sheafification of an objectwise
tensor product.** -/
theorem simplicialPrincipalPartsX₁_eq (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (simplicialPrincipalPartsShortComplex J f F).X₁ =
      (PresheafOfModules.sheafification
          (R := commRingSheaf (projectionTopology C J) ((simplicialResolution J f)).obj
            (Stacks.SheafOfModules.Tensor.ringSheaf (simplicialResolution J f)).property) (𝟙 _)).obj
        (Stacks.tensorObj
          ((PresheafOfModules.restrictScalars
            (commRingSheafMap (projectionTopology C J) (simplicialAugmentation J f).hom
              (Stacks.SheafOfModules.Tensor.ringSheaf (simplicialResolution J f)).property
              (Stacks.SheafOfModules.Tensor.ringSheaf (projectionCommRing J B)).property).hom).obj
            (projectionCoefficients J (B := B) F).val)
          (simplicialDifferentials J f).val) :=
  rfl

/-- **`Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ ≅ ε_*Y₀`**, the transitivity of the tensor product across the
augmentation, with nothing assumed on `ε`. -/
def simplicialPrincipalPartsX₁TransitivityIso
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (simplicialPrincipalPartsShortComplex J f F).X₁ ≅
      (SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).obj
        (atiyahFirstTermCoefficients J f F) :=
  eqToIso (simplicialPrincipalPartsX₁_eq J f F) ≪≫
    Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso
      (projectionTopology C J) (simplicialAugmentation J f).hom
      (Stacks.SheafOfModules.Tensor.ringSheaf (simplicialResolution J f)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf (projectionCommRing J B)).property
      (simplicialDifferentials J f) (projectionCoefficients J (B := B) F)

/-- **`Y₀` is the uncurrying of `Ω_{P_•/𝒜} ⊗_{P_•} ℱ`.** The first factor of `Y₀` is
`ε^*Ω_{𝒫/π^{-1}𝒜}`, which is the uncurrying of the base-changed simplicial differentials
(`CategoryTheory.Sheaf.extendAugmentationDifferentialsUncurryIso`), and uncurrying commutes with
tensoring by the inverse image of `ℱ` (`Stacks.SimplicialModules.TensorUncurry.tensorUncurryIso`).
-/
def atiyahFirstTermCoefficientsIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    atiyahFirstTermCoefficients J f F ≅ simplicialDifferentialsCoefficients J f F :=
  (PresheafOfModules.sheafification
        (R := projectionRing C J (targetRing J (B := B))) (𝟙 _)).mapIso
      ((Stacks.Cohomology.MixedDerivedTensor.tensorRightNatIso
          (O := ((projectionCommRing J B)).obj)
          ((SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 _)).mapIso
            (extendAugmentationDifferentialsUncurryIso
              (cotangentSimplicialModule.{u, u, u} J f)))).app
        (projectionCoefficients J (B := B) F).val) ≪≫
    tensorUncurryIso J F (cotangentSimplicialModule.{u, u, u} J f).object

/-- **`Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ ≅ ε_*(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)`**: the first term of the sequence of
principal parts of the standard resolution is `ε_*` of the uncurrying of the simplicial module
whose associated complex is `L_{ℬ/𝒜} ⊗_ℬ ℱ`. -/
def simplicialPrincipalPartsX₁Iso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (simplicialPrincipalPartsShortComplex J f F).X₁ ≅
      (SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).obj
        (simplicialDifferentialsCoefficients J f F) :=
  simplicialPrincipalPartsX₁TransitivityIso J f F ≪≫
    (SheafOfModules.restrictScalars (simplicialAugmentationRing J f)).mapIso
      (atiyahFirstTermCoefficientsIso J f F)

/-- **The first term of the sequence of principal parts, placed in degree `0`, is `ε_*` of
`(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)[0]`.** -/
def resolutionDifferentialsSingleIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (HomologicalComplex.single
        (moduleSheaves.{u, u, u, u} (simplicialResolution J f))
        (ComplexShape.up ℤ) 0).obj (simplicialPrincipalPartsShortComplex J f F).X₁ ≅
      (augPushforwardC J (resolutionCommAugmentation J f)).obj
        ((HomologicalComplex.single
          (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
          (ComplexShape.up ℤ) 0).obj (simplicialDifferentialsCoefficients J f F)) :=
  (HomologicalComplex.single (moduleSheaves.{u, u, u, u} (simplicialResolution J f))
      (ComplexShape.up ℤ) 0).mapIso (simplicialPrincipalPartsX₁Iso J f F) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (SheafOfModules.restrictScalars
        (Stacks.SimplicialModules.augRingMap J (resolutionCommAugmentation J f)))
      (ComplexShape.up ℤ) 0).app (simplicialDifferentialsCoefficients J f F)).symm

/-! ### `e₁` -/

/-- **[Stacks, Tag 09D2] at the first term of the Atiyah triangle.** The first term of
`CategoryTheory.Sheaf.resolutionAtiyahTriangle`, which is the `Lπ_!` of Remark 09D3 applied to
`Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ε_*(π^{-1}ℱ)`, is the `Lπ_!` of Remark 09CY applied to
`(Ω_{P_•/𝒜} ⊗_{P_•} ℱ)[0]`: the derived extension of scalars along the augmentation may be dropped.
-/
theorem nonempty_resolutionAtiyahLowerShriekDifferentialsIso
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Nonempty ((resolutionAtiyahTriangle J f F).obj₁ ≅
      (derivedProjectionLowerShriek C J (targetRing J (B := B))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single
            (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
            (ComplexShape.up ℤ) 0).obj (simplicialDifferentialsCoefficients J f F)))) := by
  obtain ⟨e⟩ :=
    Stacks.SimplicialModules.nonempty_derivedProjectionLowerShriek_augmentationBaseChange_iso
      J (resolutionCommAugmentation J f)
      (quasiIso_mooreAbSheafCochain_unitMap_augmentationCommRingMap J f)
      ((HomologicalComplex.single
        (SheafOfModules.{u} (projectionRing C J (targetRing J (B := B))))
        (ComplexShape.up ℤ) 0).obj (simplicialDifferentialsCoefficients J f F))
  exact ⟨(resolutionLowerShriek J f).mapIso
      (DerivedCategory.Q.mapIso (resolutionDifferentialsSingleIso J f F)) ≪≫ e⟩

/-- **`e₁` of [Stacks, Tag 09DH], with nothing assumed: the first term of the Atiyah triangle is
`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ`.** -/
theorem nonempty_resolutionAtiyahTriangleFirstTermIso
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    Nonempty ((resolutionAtiyahTriangle J f F).obj₁ ≅
      ((derivedTensorProductFunctor B).obj
          (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
        (DerivedCategory.Q.obj
          ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
            (ComplexShape.up ℤ) 0).obj F))) :=
  (nonempty_resolutionAtiyahLowerShriekDifferentialsIso J f F).map
    fun e => e ≪≫ derivedLowerShriekSimplicialDifferentialsIso J f F

/-! ### The displayed triangle and the Atiyah class, for some identifications -/

/-- **The displayed triangle, for some identifications of the outer terms.** For a homomorphism
`f : 𝒜 ⟶ ℬ` of sheaves of commutative rings on a site and a sheaf of `ℬ`-modules `ℱ`, there are
identifications of the two outer terms of the Atiyah triangle for which

`L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ ⟶ Lπ_!(P¹_{𝒫/π^{-1}𝒜}(ℱ)) ⟶ ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)⟦1⟧`

is a distinguished triangle in `D(ℬ)`: the triangle of [Stacks, Tag 09DH]. -/
theorem exists_resolutionAtiyahDisplayedTriangle_distinguished
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    ∃ (e₁ : (resolutionAtiyahTriangle J f F).obj₁ ≅
        ((derivedTensorProductFunctor B).obj
            (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
              (ComplexShape.up ℤ) 0).obj F)))
      (e₃ : (resolutionAtiyahTriangle J f F).obj₃ ≅
        DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
            (ComplexShape.up ℤ) 0).obj F)),
      Triangle.mk (e₁.inv ≫ (resolutionAtiyahTriangle J f F).mor₁)
          ((resolutionAtiyahTriangle J f F).mor₂ ≫ e₃.hom)
          (e₃.inv ≫ (resolutionAtiyahTriangle J f F).mor₃ ≫
            (shiftFunctor (DerivedCategory (SheafOfModules.{u} (targetRing J (B := B))))
              (1 : ℤ)).map e₁.hom) ∈
        distinguishedTriangles := by
  obtain ⟨e₁⟩ := nonempty_resolutionAtiyahTriangleFirstTermIso J f F
  obtain ⟨e₃⟩ := nonempty_resolutionAtiyahTriangleThirdTermIso J f F
  exact ⟨e₁, e₃, resolutionAtiyahClass_mem_distinguished J f F e₁ e₃⟩

/-- **The Atiyah class, for some identifications of the outer terms.** There are identifications of
the two outer terms of the Atiyah triangle for which `CategoryTheory.Sheaf.resolutionAtiyahClass`,
an arrow `ℱ ⟶ (L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ)⟦1⟧`, is the last arrow of the displayed distinguished triangle;
this is the Atiyah class of [Stacks, Tag 09DI].
-/
theorem exists_resolutionAtiyahClass_mem_distinguished
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    ∃ (e₁ : (resolutionAtiyahTriangle J f F).obj₁ ≅
        ((derivedTensorProductFunctor B).obj
            (DerivedCategory.Q.obj (cotangentComplex.{u, u, u} J f))).obj
          (DerivedCategory.Q.obj
            ((HomologicalComplex.single (Stacks.DerivedTensor.RingedSite.Modules B)
              (ComplexShape.up ℤ) 0).obj F)))
      (e₃ : (resolutionAtiyahTriangle J f F).obj₃ ≅
        DerivedCategory.Q.obj
          ((HomologicalComplex.single (SheafOfModules.{u} (targetRing J (B := B)))
            (ComplexShape.up ℤ) 0).obj F)),
      Triangle.mk (e₁.inv ≫ (resolutionAtiyahTriangle J f F).mor₁)
          ((resolutionAtiyahTriangle J f F).mor₂ ≫ e₃.hom)
          (resolutionAtiyahClass J f F e₁ e₃) ∈ distinguishedTriangles :=
  exists_resolutionAtiyahDisplayedTriangle_distinguished J f F

end CategoryTheory.Sheaf

end
