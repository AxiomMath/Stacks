module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceUniformBound
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSectionsAmplitudeDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedLimitsCohomology
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# `R lim_{D(𝒪_X)} Kₙ` has bounded-above affine cohomology

In the situation of [Stacks, Tag 0DIK], the tower `(Rjₙ,* Kₙ)` in `D(𝒪_X)` has a derived limit
`R lim_{D(𝒪_X)} Kₙ`, whose cohomology over the affine objects étale over `X` is bounded above.

## Main definitions

* `AlgebraicGeometry.Space.DerivedExistenceSystem.spaceTower`: the tower `(Rjₙ,* Kₙ)` read in
  `spaceDerivedCategory X` (the `Modules` spelling of `D(𝒪_X)`).

## Main results

* `AlgebraicGeometry.Space.DerivedExistenceSystem.isQuasicoherentOnSite_homology_spaceTower`: the
  terms of the tower lie in `D_QCoh(𝒪_X)`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.exists_spaceCohomologyVanishesAbove_spaceTower`:
  the terms of the tower are uniformly bounded above.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.exists_isDerivedLimit_spaceTower`:
  `R lim_{D(𝒪_X)} Kₙ` exists.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.exists_sectionsAmplitudeLE_of_isDerivedLimit`:
  there is `a` such that every derived limit of the tower, on every K-injective representative,
  has no cohomology over the affine étale charts of `X` in degrees `> a`.

## References

* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- **The tower `(Rjₙ,* Kₙ)` in `D(𝒪_X)`**, read in `spaceDerivedCategory X`. -/
def spaceTower : ℕᵒᵖ ⥤ spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left :=
  D.pushforwardTower

/-- The `n`-th term of `spaceTower` is `towerObj n`. -/
lemma spaceTower_obj (n : ℕ) : D.spaceTower.obj ⟨n⟩ = D.towerObj n := rfl

/-- The terms of the tower have quasi-coherent cohomology sheaves. -/
theorem isQuasicoherentOnSite_homology_spaceTower (n : ℕ) (q : ℤ) :
    ((spaceDerivedHomology D.B (limitBase D.system) D.containsLimitBase D.X.left q).obj
      (D.spaceTower.obj ⟨n⟩)).IsQuasicoherentOnSite :=
  D.isQuasicoherentOnSite_homology_towerObj n q

/-- The terms of the tower are bounded above uniformly in `n`. -/
theorem exists_spaceCohomologyVanishesAbove_spaceTower :
    ∃ b : ℤ, ∀ n : ℕ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase
      D.X.left b (D.spaceTower.obj ⟨n⟩) :=
  D.exists_isZero_homology_towerObj_gt_uniform

/-- `D(𝒪_X)` has countable products. -/
instance hasProduct_spaceTower : HasProduct fun n : ℕ => D.spaceTower.obj ⟨n⟩ := by
  have := hasProductsOfShape_nat_derivedCategory_modules D.B (limitBase D.system)
    D.containsLimitBase D.X.left.1 D.X.left.2
  infer_instance

/-- **`R lim_{D(𝒪_X)} Kₙ` exists.** -/
theorem exists_isDerivedLimit_spaceTower :
    ∃ L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      IsDerivedLimit D.spaceTower L :=
  exists_isDerivedLimit D.spaceTower

/-- **`R lim_{D(𝒪_X)} Kₙ` has bounded-above affine cohomology**: there is one `a` such that every
derived limit `L` of the tower, on every K-injective complex `I` representing it, has no cohomology
over the affine étale charts of `X` in degrees `> a`. -/
theorem exists_sectionsAmplitudeLE_of_isDerivedLimit :
    ∃ a : ℤ, ∀ L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left,
      IsDerivedLimit D.spaceTower L →
      ∀ (I : CochainComplex (Modules.{u, u} D.B (limitBase D.system) D.containsLimitBase
          D.X.left.1 D.X.left.2) ℤ), I.IsKInjective →
        ((spaceDerivedQ D.B (limitBase D.system) D.containsLimitBase D.X.left).obj I ≅ L) →
          SectionsAmplitudeLE D.B (limitBase D.system) D.containsLimitBase D.X.left a I := by
  obtain ⟨b, hb⟩ := D.exists_spaceCohomologyVanishesAbove_spaceTower
  exact ⟨b + 1, fun L ⟨p, δ, hL⟩ I hI e => sectionsAmplitudeLE_of_isDerivedLimit D.B
    (limitBase D.system) D.containsLimitBase D.X.left D.spaceTower L p ⟨δ, hL⟩ b
    D.isQuasicoherentOnSite_homology_spaceTower hb I hI e⟩

end DerivedExistenceSystem

end AlgebraicGeometry.Space
