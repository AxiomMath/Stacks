module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingTowerRecovery
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Composition
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# Projectivity of a tower of projective bundles over a quasi-compact base

Let `π : P ⟶ X` be a finite composition of projective space bundles `𝐏(ℰ) ⟶ X` of finite locally
free modules (`Stacks.Chow.IsProjectiveBundleTower`). Each layer is projective in the sense of
Stacks 01W8 (`AlgebraicGeometry.isProjective_schemeProjectiveBundleToBase`), the empty tower is the
identity, which is H-projective through `ℙ⁰_X ≅ X` and hence projective (Stacks 01W9), and over a
quasi-compact and quasi-separated base a composition of projective morphisms is projective
(Stacks 0C4P). Since every layer is proper, the intermediate bases stay quasi-compact and
quasi-separated, so `π` is projective whenever `X` is quasi-compact and quasi-separated.

## Main results

* `AlgebraicGeometry.isProjectiveMorphism_id`, `AlgebraicGeometry.isProjective_id` — the identity
  is H-projective and projective.
* `Stacks.Chow.isProjective_bundleProj` — the projection of the projective bundle of a finite
  locally free module is projective.
* `Stacks.Chow.IsProjectiveBundleTower.isProjective_of_compactSpace` — a tower of projective
  bundles over a quasi-compact and quasi-separated base is projective.

## References

* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 0C4P](https://stacks.math.columbia.edu/tag/0C4P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The identity is H-projective**: the inverse of `ℙ⁰_X ≅ X` is a closed immersion over `X`. -/
theorem isProjectiveMorphism_id (X : Scheme.{u}) : IsProjectiveMorphism (𝟙 X) :=
  ⟨0, (projectiveSpaceOver.zeroIsoBase X).inv, inferInstance,
    projectiveSpaceOver.zeroIsoBase_inv_comp_over X⟩

/-- **The identity is projective** (Stacks 01W8): it is H-projective (Stacks 01W9). -/
theorem isProjective_id (X : Scheme.{u}) : IsProjective (𝟙 X) :=
  (isProjectiveMorphism_id X).isProjective

end AlgebraicGeometry

namespace Stacks.Chow

/-- **The projection of the projective bundle of a finite locally free module is projective**
(Stacks 01W8): a finite locally free module is quasi-coherent and of finite type. -/
theorem isProjective_bundleProj {X : Scheme.{u}} (E : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    IsProjective (bundleProj E) := by
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have : E.IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree E
  exact isProjective_schemeProjectiveBundleToBase E

/-- **A tower of projective bundles over a quasi-compact and quasi-separated base is projective**
(Stacks 01W8). Induction on the tower: the identity is projective, each layer is projective, the
source of each layer is again quasi-compact and quasi-separated since the layer is proper, and a
composition of projective morphisms over a quasi-compact and quasi-separated base is projective
(Stacks 0C4P). -/
theorem IsProjectiveBundleTower.isProjective_of_compactSpace {C : ChowSituation.{u}}
    {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {d : ℕ}
    {T : SplittingMorphism C sX d} (hT : IsProjectiveBundleTower C sX d T) :
    CompactSpace X → QuasiSeparatedSpace X → IsProjective T.π := by
  induction hT with
  | id sX => exact fun _ _ ↦ isProjective_id _
  | compStep sX E m hE n T _ ih =>
    intro _ _
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
        (m + 1 + 1)
    have : IsProper (projectiveBundleStep C sX E m hE).π := inferInstance
    have : CompactSpace (projectiveBundleStep C sX E m hE).P :=
      compactSpace_of_isProper (projectiveBundleStep C sX E m hE).π
    have : QuasiSeparatedSpace (projectiveBundleStep C sX E m hE).P :=
      quasiSeparatedSpace_of_isProper (projectiveBundleStep C sX E m hE).π
    have hlayer : IsProjective (projectiveBundleStep C sX E m hE).π := isProjective_bundleProj E
    exact IsProjective.comp (ih inferInstance inferInstance) hlayer

end Stacks.Chow

end
