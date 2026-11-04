module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.SymMap
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Bundle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The closed immersion of projective bundles induced by a surjection

Let `g : 𝒢 ⟶ 𝒬` be an epimorphism of finite locally free modules on a scheme `X`. The induced
surjection `Sym(𝒢) ⟶ Sym(𝒬)` of symmetric algebras gives a closed immersion
`ι : 𝐏(𝒬) ⟶ 𝐏(𝒢)` over `X`, for the projective bundles `Stacks.Chow.bundle`.

## Main definitions

* `Stacks.Chow.GenuineChern.bundleEmbedding`: the closed immersion `𝐏(𝒬) ⟶ 𝐏(𝒢)`.

## Main results

* `Stacks.Chow.GenuineChern.isClosedImmersion_bundleEmbedding`: it is a closed immersion.
* `Stacks.Chow.GenuineChern.bundleEmbedding_comp_bundleProj`: it is a morphism over `X`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.SymGraded

universe u

namespace Stacks.Chow.GenuineChern

variable {X : Scheme.{u}} {G Q : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} Q]
  (g : G ⟶ Q) [Epi g]

/-- A finite locally free module is quasi-coherent. -/
instance (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    E.IsQuasicoherent :=
  Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E

/-- `Sym(g)` is surjective on homogeneous sections over affine opens. -/
theorem surjectiveOnAffineSections_bundle :
    Stacks.AlgebraicGeometry.ProjBundleSurjection.SurjectiveOnAffineSections
      (schemeSheafGradedAlgebraHom g (bundlePieces G) (bundlePieces Q)) :=
  surjectiveOnAffineSections_schemeSheafGradedAlgebraHom g _ _

/-- **The closed immersion `𝐏(𝒬) ⟶ 𝐏(𝒢)` induced by an epimorphism `𝒢 ⟶ 𝒬`.** -/
def bundleEmbedding : bundle Q ⟶ bundle G :=
  Stacks.AlgebraicGeometry.ProjBundleSurjection.map (surjectiveOnAffineSections_bundle g)

/-- **The induced morphism of projective bundles is a closed immersion.** -/
@[ega "II 3.6.4" "Case S = Sym(Q)"]
instance isClosedImmersion_bundleEmbedding : IsClosedImmersion (bundleEmbedding g) :=
  Stacks.AlgebraicGeometry.ProjBundleSurjection.isClosedImmersion_map _

/-- **The induced morphism of projective bundles is over the base.** -/
@[reassoc (attr := simp)]
theorem bundleEmbedding_comp_bundleProj : bundleEmbedding g ≫ bundleProj G = bundleProj Q :=
  Stacks.AlgebraicGeometry.ProjBundleSurjection.map_comp_toBase _

/-- Over the chart of an affine open of the base, the embedding is the chart map. -/
@[reassoc]
theorem chart_comp_bundleEmbedding (U : X.Opens) (hU : IsAffineOpen U) :
    (Stacks.SymGraded.schemeProjectiveBundle Q (bundlePieces Q)).chart U hU ≫ bundleEmbedding g =
      Stacks.AlgebraicGeometry.ProjBundleSurjection.chartMap
          (surjectiveOnAffineSections_bundle g) U hU ≫
        (Stacks.SymGraded.schemeProjectiveBundle G (bundlePieces G)).chart U hU :=
  Stacks.AlgebraicGeometry.ProjBundleSurjection.chart_comp_map _ U hU

end Stacks.Chow.GenuineChern

end
