module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.SitesConormalComparison
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentInverseImageStalkSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentTowerPullbackDifferentials
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTowerPresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `NL_{X/Y}` is the two-term complex of the tower `f⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X`

Let `i : X ⟶ P` be a morphism of schemes which is surjective on stalks and let `g : P ⟶ Y` be
formally smooth, and write `f = i ≫ g`.  The three sheaves of rings `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X`
on `X` form a tower whose second map is locally surjective, so `i⁻¹𝒪_P` presents `𝒪_X` over
`i⁻¹g⁻¹𝒪_Y`, and `Stacks.SheafOfModules.towerNaiveCotangentComplex` is the two-term complex

`(I/I² ⟶ 𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y])`

of that presentation.  This file assembles the sites-level comparison of
`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentTowerPresentation` with the identification of
`NL_{X/Y}` with its iterated spelling and shows that the two are isomorphic in the derived
category of sheaves of `𝒪_X`-modules.

This is the scheme-level half of the core of [Stacks Project, Tag 0FV4] that does not yet mention
the geometric conormal sheaf or the geometric sheaf of relative differentials.  The tag itself is
**not** proved here: its right-hand side is the two-term complex of the conormal sequence of
[Stacks Project, Tag 01UZ], built from `Stacks.Conormal.conormalSheaf` and
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials`, and identifying the two terms above with
those is a separate matter.

## Main results

* `Stacks.NaiveCotangentTower.quasiIso_schemeTowerComparison`: the canonical chain map
  `NL(f⁻¹𝒪_Y-polynomials on the sections of i⁻¹𝒪_P ⟶ 𝒪_X) ⟶ (I/I² ⟶ 𝒪_X ⊗ Ω)` is a
  quasi-isomorphism.
* `Stacks.NaiveCotangentTower.schemeTowerIso`: the resulting isomorphism
  `NL_{X/Y} ≅ (I/I² ⟶ 𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y])` in `D(𝒪_X)`.

## Route

Three identifications are composed.

1. `Stacks.SheafOfModules.naiveCotangentComplexCompIsoOfEq` rewrites `NL_{X/Y}`, the naive
   cotangent complex of `𝒪_X` over `f⁻¹𝒪_Y`, as the naive cotangent complex of `𝒪_X` over the
   iterated inverse image `i⁻¹g⁻¹𝒪_Y`.  It is an isomorphism of complexes.
2. [Stacks Project, Tag 08TL], `Stacks.SheafOfModules.quasiIso_naiveCotangentComplexComparison`,
   identifies that with the naive cotangent complex of the polynomial presentation of `𝒪_X` on
   the sections of `i⁻¹𝒪_P`.
3. `Stacks.SheafOfModules.quasiIso_towerPresentationComparison` identifies that in turn with the
   two-term complex of the presentation `i⁻¹𝒪_P ⟶ 𝒪_X`, the hypothesis being that `i⁻¹𝒪_P` is
   formally smooth over `i⁻¹g⁻¹𝒪_Y` at every stalk — which is formal smoothness of `g`, read on
   stalks.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.Sites.FreeAlgebra
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.RelativeDifferentialStalk (algebraStalk)

universe u

noncomputable section

namespace Stacks.NaiveCotangentTower

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y)

/-- **The identification of `NL_{X/Y}` with the naive cotangent complex of the polynomial
presentation of `𝒪_X` on the sections of `i⁻¹𝒪_P`, over the iterated inverse image.** -/
def schemePresentationIso [SurjectiveOnStalks i] :
    Scheme.naiveCotangentComplex (i ≫ g) ≅
      naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g) ≫
          ringedSpaceStructureMap (ringedSpaceHom i)) :=
  naiveCotangentComplexCompIsoOfEq (ringedSpaceHom i) (ringedSpaceHom g)
    (ringedSpaceHom (i ≫ g)) rfl

/-- **The comparison of the polynomial presentation of `𝒪_X` on the sections of `i⁻¹𝒪_P` with
the two-term complex of the presentation `i⁻¹𝒪_P ⟶ 𝒪_X`.** -/
def schemeTowerComparison [SurjectiveOnStalks i] :=
  towerPresentationComparison (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i))

/-- **The comparison is a quasi-isomorphism for `g` formally smooth.**  Formal smoothness of `g`
makes `i⁻¹𝒪_P` formally smooth over `i⁻¹g⁻¹𝒪_Y` at every stalk. -/
theorem quasiIso_schemeTowerComparison [SurjectiveOnStalks i]
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    QuasiIso (schemeTowerComparison i g) :=
  quasiIso_towerPresentationComparison
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i))
    (fun x ↦ NaiveCotangentInverseImageStalkSmooth.formallySmooth_stalk_inverseImageFirstRingMap
      i g hg x)

/-- The polynomial presentation of `𝒪_X` on the sections of `i⁻¹𝒪_P` is locally surjective, in
the vocabulary of the inverse-image development. -/
instance isLocallySurjective_schemePresentation [SurjectiveOnStalks i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (presentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g) ≫
          ringedSpaceStructureMap (ringedSpaceHom i))
        (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageMiddleRing (ringedSpaceHom i)))
        (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom i)))).hom :=
  isLocallySurjective_presentation_towerGenerators
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g))
    (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g))
    (ringedSpaceStructureMap (ringedSpaceHom i))

/-- **[Stacks Project, Tag 08TL] for the polynomial presentation on the sections of `i⁻¹𝒪_P`.** -/
theorem quasiIso_schemePresentationComparison [SurjectiveOnStalks i] :
    QuasiIso (naiveCotangentComplexComparison.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g) ≫
        ringedSpaceStructureMap (ringedSpaceHom i))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i)))
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i)))) :=
  quasiIso_naiveCotangentComplexComparison _ _ _ _ _

/-! ### The isomorphism in the derived category -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- The comparison of [Stacks Project, Tag 08TL] is invertible in `D(𝒪_X)`. -/
theorem isIso_Q_map_schemePresentationComparison [SurjectiveOnStalks i] :
    IsIso (DerivedCategory.Q.map (naiveCotangentComplexComparison.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g) ≫
        ringedSpaceStructureMap (ringedSpaceHom i))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i)))
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i))))) :=
  have := quasiIso_schemePresentationComparison i g
  inferInstance

/-- The comparison with the two-term complex of the presentation `i⁻¹𝒪_P ⟶ 𝒪_X` is invertible in
`D(𝒪_X)` for `g` formally smooth. -/
theorem isIso_Q_map_schemeTowerComparison [SurjectiveOnStalks i]
    (hg : Stacks.Smooth.FormallySmoothScheme g) :
    IsIso (DerivedCategory.Q.map (schemeTowerComparison i g)) :=
  have := quasiIso_schemeTowerComparison i g hg
  inferInstance

/-- **`NL_{X/Y} ≅ (I/I² ⟶ 𝒪_X ⊗_{i⁻¹𝒪_P} Ω[i⁻¹𝒪_P / i⁻¹g⁻¹𝒪_Y])` in `D(𝒪_X)`.**  For `i`
surjective on stalks and `g` formally smooth, the naive
cotangent complex of `i ≫ g` is isomorphic in the derived category of sheaves of `𝒪_X`-modules to
the two-term complex of the presentation `i⁻¹𝒪_P ⟶ 𝒪_X`. -/
@[sga "6 VIII 2.2" "more general"]
def schemeTowerIso [SurjectiveOnStalks i]
    (hg : Stacks.Smooth.FormallySmoothScheme g) :=
  DerivedCategory.Q.mapIso (schemePresentationIso i g) ≪≫
    (@asIso _ _ _ _ _ (isIso_Q_map_schemePresentationComparison i g)).symm ≪≫
    (@asIso _ _ _ _ _ (isIso_Q_map_schemeTowerComparison i g hg))

end Derived

end Stacks.NaiveCotangentTower

end

end
