module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceQuasicoherentLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedCoherator.AffineChartCase

/-!
# The derived limit of Situation 0DIK is bounded above

In Situation [Stacks, Tag 0DIK] let
`K = R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(R lim_{D(𝒪_X)} Kₙ)`.
[Stacks, Tag 0DIL] says that `K` lies in `D⁻_QCoh(𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedExistenceSystem.coherator`: a chosen coherator `DQ_X`, the right
  adjoint of `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, with adjunction
  `AlgebraicGeometry.Space.DerivedExistenceSystem.coheratorAdjunction`.
* `AlgebraicGeometry.Space.DerivedExistenceSystem.quasicoherentLimit`: the object
  `K = DQ_X(R lim_{D(𝒪_X)} Kₙ)` of `D_QCoh(𝒪_X)`.

## Main results

* `DerivedExistenceSystem.derivedLimit_isBoundedAbove`: [Stacks, Tag 0DIL] at every coherator
  and every derived limit.
* `DerivedExistenceSystem.isDerivedLimit_quasicoherentLimit`: `K` is a derived limit of
  `(Rjₙ,* Kₙ)` in `D_QCoh(𝒪_X)`.
* `DerivedExistenceSystem.exists_spaceCohomologyVanishesAbove_quasicoherentLimit`: `K` lies in
  `D⁻_QCoh(𝒪_X)`.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

/- The statements below read `D(𝒪_X)` at the standard model `spaceHasDerivedCategory`. The
small-Hom model `ChaoticComparison.sheafOfModules_hasDerivedCategory`, reachable in this import
context, is not that model, so instance search for the shift functors of `D(𝒪_X)` must not pick
it. -/
attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory

namespace DerivedExistenceSystem

variable (D : DerivedExistenceSystem.{u})

/-- The inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X` and the tower `(Rjₙ,* Kₙ)`
has a derived limit `L = R lim_{D(𝒪_X)} Kₙ`. For every coherator `DQ_X` and every such `L`,
`K = DQ_X(L)` is a derived limit of the tower in `D_QCoh(𝒪_X)` whose cohomology sheaves vanish
above some degree. Every derived limit of the tower in `D_QCoh(𝒪_X)` lies in `D⁻_QCoh(𝒪_X)`. -/
@[stacks 0DIL "K = R lim_{D_QCoh} K_n = DQ_X(R lim_{D(O_X)} K_n) lies in D^-_QCoh(O_X), for every \
  choice of coherator and of derived limits"]
theorem derivedLimit_isBoundedAbove :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.IsLeftAdjoint ∧
    (∃ L, IsDerivedLimit D.spaceTower L) ∧
    (∀ (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
        (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
          D.X.left).FullSubcategory)
      (_ : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)
      (L : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left),
      IsDerivedLimit D.spaceTower L →
        (∃ _ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩,
          IsDerivedLimit D.quasicoherentTower (DQ.obj L)) ∧
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase
          D.X.left c ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
            D.X.left).ι.obj (DQ.obj L))) ∧
    ∀ (_ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩)
      (K : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory),
      IsDerivedLimit D.quasicoherentTower K →
        ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase
          D.X.left c ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
            D.X.left).ι.obj K) :=
  D.derivedLimit_isBoundedAbove_of_affineCase (affineCoheratorCase _ _ _)

/-- The inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` is a left adjoint. -/
instance isLeftAdjoint_spaceQuasicoherentι :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).ι.IsLeftAdjoint :=
  D.derivedLimit_isBoundedAbove.1

/-- **A chosen coherator `DQ_X`**: the right adjoint of `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`. -/
abbrev coherator :
    spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
        D.X.left).FullSubcategory :=
  (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.rightAdjoint

/-- The adjunction `D_QCoh(𝒪_X) ⥤ D(𝒪_X) ⊣ DQ_X`. -/
def coheratorAdjunction :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣
      D.coherator :=
  Adjunction.ofIsLeftAdjoint _

/-- **The object `K = R lim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(R lim_{D(𝒪_X)} Kₙ)` of `D_QCoh(𝒪_X)`.** -/
abbrev quasicoherentLimit :
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase
      D.X.left).FullSubcategory :=
  D.coheratorLimit D.coherator

/-- `K` is a derived limit of the tower `(Rjₙ,* Kₙ)` in `D_QCoh(𝒪_X)`. -/
theorem isDerivedLimit_quasicoherentLimit :
    ∃ _ : HasProduct fun n : ℕ => D.quasicoherentTower.obj ⟨n⟩,
      IsDerivedLimit D.quasicoherentTower D.quasicoherentLimit :=
  (D.derivedLimit_isBoundedAbove.2.2.1 D.coherator D.coheratorAdjunction D.derivedLimit
    D.isDerivedLimit_derivedLimit).1

/-- **`K` lies in `D⁻_QCoh(𝒪_X)`.** -/
theorem exists_spaceCohomologyVanishesAbove_quasicoherentLimit :
    ∃ c : ℤ, SpaceCohomologyVanishesAbove D.B (limitBase D.system) D.containsLimitBase D.X.left c
      ((spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι.obj
        D.quasicoherentLimit) :=
  (D.derivedLimit_isBoundedAbove.2.2.1 D.coherator D.coheratorAdjunction D.derivedLimit
    D.isDerivedLimit_derivedLimit).2

end DerivedExistenceSystem

end AlgebraicGeometry.Space

end
