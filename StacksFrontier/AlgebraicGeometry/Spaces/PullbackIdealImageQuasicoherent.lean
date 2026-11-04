module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivityFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealImage
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The inverse-image ideal of a quasi-coherent sheaf of ideals is quasi-coherent

Let `g : X ⟶ X'` be a morphism of algebraic spaces over a scheme `S` and let `𝓘 ⊆ 𝒪_{X'}` be
a quasi-coherent sheaf of ideals.  The inverse-image ideal `g⁻¹𝓘 · 𝒪_X` is the image of the
morphism `g^*𝓘 ⟶ 𝒪_X` induced by the inclusion `𝓘 ⊆ 𝒪_{X'}`.  Its source is quasi-coherent,
the inverse image of a quasi-coherent module being quasi-coherent (Stacks 03GA), and so is its
target; the image of a morphism of quasi-coherent modules is quasi-coherent.  **So `g⁻¹𝓘 · 𝒪_X`
is again a quasi-coherent sheaf of ideals**, which is what makes it an admissible ideal for the
category `Coh(X, g⁻¹𝓘 · 𝒪_X)` of Stacks 089P.

## Main results

* `AlgebraicGeometry.Space.epi_toPullbackIdealImage` — the corestriction of `g^*𝓘 ⟶ 𝒪_X` to
  the inverse-image ideal is an epimorphism.
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_pullbackIdealImage` — **the inverse image
  ideal of a sheaf of ideals cartesian on affine charts is cartesian on affine charts.**
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_pullbackIdealImage` — the same, read as
  quasi-coherence on the small étale site.

## Implementation notes

`AlgebraicGeometry.Space.pullbackIdealImage` is the subsheaf of sections lying locally in the
pointwise image, not the abelian image of the category of modules, so the two are compared
first: the corestriction of `g^*𝓘 ⟶ 𝒪_X` to the subsheaf is locally surjective by definition,
hence an epimorphism (`Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective`), and the
inclusion of a subsheaf is a monomorphism, so the uniqueness of epi-mono factorisations
(`CategoryTheory.Limits.image.isoStrongEpiMono`) identifies the subsheaf with the image.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (g : X ⟶ X')
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)

/-- The corestriction of `g^*𝓘 ⟶ 𝒪_X` to the inverse-image ideal `g⁻¹𝓘 · 𝒪_X`. -/
def toPullbackIdealImage :
    ((modulePullback B S hS g).obj 𝓘.toSheafOfModules : Modules.{u, u} B S hS X.1 X.2) ⟶
      (pullbackIdealImage B S hS g 𝓘).toSheafOfModules :=
  ⟨Stacks.SheafOfModules.toLocalImage (pullbackIdealHom B S hS g 𝓘).val⟩

/-- The corestriction followed by the inclusion is `g^*𝓘 ⟶ 𝒪_X`. -/
theorem toPullbackIdealImage_ι :
    toPullbackIdealImage B S hS g 𝓘 ≫ (pullbackIdealImage B S hS g 𝓘).ι =
      pullbackIdealHom B S hS g 𝓘 :=
  SheafOfModules.hom_ext (Stacks.SheafOfModules.toLocalImage_ι _)

/-- The corestriction of `g^*𝓘 ⟶ 𝒪_X` to `g⁻¹𝓘 · 𝒪_X` is an epimorphism: every section of the
inverse-image ideal lies locally in the pointwise image, by definition. -/
theorem epi_toPullbackIdealImage : Epi (toPullbackIdealImage B S hS g 𝓘) := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s => ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ s.2
  rintro V i ⟨t, ht⟩
  exact ⟨t, Subtype.ext ht⟩

/-- **The inverse-image ideal `g⁻¹𝓘 · 𝒪_X` of a sheaf of ideals cartesian on affine charts is
cartesian on affine charts.**  It is the image of a morphism `g^*𝓘 ⟶ 𝒪_X` of modules cartesian
on affine charts: `g^*𝓘` is quasi-coherent by Stacks 03GA, and quasi-coherence is being
cartesian on affine charts by Stacks 03DX.  The inverse-image ideal is identified with the
abelian image by the uniqueness of epi-mono factorisations. -/
theorem isCartesianOnAffineCharts_pullbackIdealImage
    (hI : IsCartesianOnAffineCharts 𝓘.toSheafOfModules) :
    IsCartesianOnAffineCharts (pullbackIdealImage B S hS g 𝓘).toSheafOfModules := by
  let : Abelian (Modules.{u, u} B S hS X.1 X.2) := SheafOfModules.instAbelian _
  have hc := isCartesianOnAffineCharts_image_of_cartesian (pullbackIdealHom B S hS g 𝓘)
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _
      (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g _
        ((isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X'.1 X'.2 _).2 hI)))
    isCartesianOnAffineCharts_unit
  have := epi_toPullbackIdealImage B S hS g 𝓘
  have : StrongEpi (toPullbackIdealImage B S hS g 𝓘) :=
    strongEpi_of_epi (C := Modules.{u, u} B S hS X.1 X.2) _
  exact IsCartesianOnAffineCharts.of_iso
    (Abelian.imageIsoImage (C := Modules.{u, u} B S hS X.1 X.2) _ ≪≫
    (image.isoStrongEpiMono (toPullbackIdealImage B S hS g 𝓘) (pullbackIdealImage B S hS g 𝓘).ι
      (toPullbackIdealImage_ι B S hS g 𝓘)).symm) hc

/-- **The inverse-image ideal of a quasi-coherent sheaf of ideals is quasi-coherent.** -/
theorem isQuasicoherentOnSite_pullbackIdealImage
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) :
    (pullbackIdealImage B S hS g 𝓘).toSheafOfModules.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2 _).2
    (isCartesianOnAffineCharts_pullbackIdealImage B S hS g 𝓘
      ((isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X'.1 X'.2 _).1 hI))

end AlgebraicGeometry.Space

end
