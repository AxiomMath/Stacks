module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymMap
public import StacksFrontier.AlgebraicGeometry.ProjBundleSurjection.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalDatumExists

/-!
# The closed immersion of projective bundles of a quotient

Let `u : F ⟶ F'` be an epimorphism of quasi-coherent modules on a scheme `X`. The surjection
`Sym(u) : Sym(F) ⟶ Sym(F')` of symmetric algebras induces a morphism of relative homogeneous
spectra (`Stacks.AlgebraicGeometry.ProjBundleSurjection.map`), a closed immersion over `X`. This
file reads it on the presentation `Stacks.RelativeProj.projectiveBundle` of the projective bundle,
the one the chart bundles of a projective bundle of an algebraic space are built from, through the
comparison `Stacks.RelativeProj.bundlePresentationIso` of the two presentations.

## Main definitions

* `Stacks.RelativeProj.projectiveBundleMapOfEpi`: the morphism `𝐏(F') ⟶ 𝐏(F)`.

## Main results

* `Stacks.RelativeProj.projectiveBundleMapOfEpi_comp_toBase`: it lies over `X`.
* `Stacks.RelativeProj.isClosedImmersion_projectiveBundleMapOfEpi`: it is a closed immersion.

## References

* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SymGraded

universe u

namespace Stacks.RelativeProj

variable {X : Scheme.{u}} {F F' : X.Modules} [F.IsQuasicoherent] [F'.IsQuasicoherent]
  (u : F ⟶ F') [Epi u]

/-- `Sym(u)` of an epimorphism of quasi-coherent modules, as a homomorphism of the graded algebras
whose relative homogeneous spectra present `𝐏(F)` and `𝐏(F')`, is surjective on homogeneous
sections over the affine opens of the base. -/
theorem surjectiveOnAffineSections_symGradedHom :
    Stacks.AlgebraicGeometry.ProjBundleSurjection.SurjectiveOnAffineSections
      (schemeSheafGradedAlgebraHom u (isQuasicoherentPieces_of_isQuasicoherent F)
        (isQuasicoherentPieces_of_isQuasicoherent F')) :=
  Stacks.Chow.GenuineChern.surjectiveOnAffineSections_schemeSheafGradedAlgebraHom u _ _

/-- **The morphism of projective bundles `𝐏(F') ⟶ 𝐏(F)` of an epimorphism `u : F ⟶ F'`**: the
morphism of relative homogeneous spectra induced by `Sym(u)`, read on
`Stacks.RelativeProj.projectiveBundle`. -/
def projectiveBundleMapOfEpi : projectiveBundle X F' ⟶ projectiveBundle X F :=
  (bundlePresentationIso F').inv ≫
    Stacks.AlgebraicGeometry.ProjBundleSurjection.map (surjectiveOnAffineSections_symGradedHom u) ≫
      (bundlePresentationIso F).hom

/-- **The morphism of projective bundles of a quotient lies over the base.** -/
@[reassoc (attr := simp)]
theorem projectiveBundleMapOfEpi_comp_toBase :
    projectiveBundleMapOfEpi u ≫ projectiveBundleToBase X F = projectiveBundleToBase X F' := by
  rw [projectiveBundleMapOfEpi, Category.assoc, Category.assoc,
    bundlePresentationIso_hom_comp_toBase,
    Stacks.AlgebraicGeometry.ProjBundleSurjection.map_comp_toBase,
    bundlePresentationIso_inv_comp_toBase]

/-- **The morphism of projective bundles of a quotient is a closed immersion.** -/
instance isClosedImmersion_projectiveBundleMapOfEpi :
    IsClosedImmersion (projectiveBundleMapOfEpi u) := by
  have := Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_map
    (surjectiveOnAffineSections_symGradedHom u)
  unfold projectiveBundleMapOfEpi
  infer_instance

end Stacks.RelativeProj

end
