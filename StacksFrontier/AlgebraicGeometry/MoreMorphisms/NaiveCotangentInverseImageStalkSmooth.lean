module

public import Mathlib.RingTheory.RingHom.Smooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentSixTermFirstTerms
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalk.Kaehler
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentFormallySmoothVanishing
public import StacksFrontier.AlgebraicGeometry.SkyscraperPushforward.Basic

/-!
# The first ring map of the iterated tower is formally smooth on stalks

Let `i : X ⟶ P` and `g : P ⟶ Y` be morphisms of schemes.  The naive cotangent complex of the
composite, written in the iterated spelling of [Stacks Project, Tag 0E1Z], is built from the
tower of sheaves of rings `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P ⟶ 𝒪_X` on `X`, whose first map is
`Stacks.SheafOfModules.inverseImageFirstRingMap`.  **When `g` is formally smooth, the stalk of
that first map at every point of `X` is a formally smooth ring map.**

## Main results

* `Stacks.NaiveCotangentInverseImageStalkSmooth.stalkFunctor_map_inverseImageFirstRingMap`: the
  stalk at `x` of `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P` is, up to the two identifications of the stalk of an
  inverse image with a stalk at the image point, the stalk at `i x` of the structural map
  `g⁻¹𝒪_Y ⟶ 𝒪_P`.
* `Stacks.NaiveCotangentInverseImageStalkSmooth.formallySmooth_hom_stalk_inverseImageFirstRingMap`
  and
  `Stacks.NaiveCotangentInverseImageStalkSmooth.formallySmooth_stalk_inverseImageFirstRingMap`:
  for `g` formally smooth, the stalk of `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P` is formally smooth, as a ring
  homomorphism and as the algebra structure `Stacks.RelativeDifferentialStalk.algebraStalk`
  attaches to it.

## References

* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0E1Z](https://stacks.math.columbia.edu/tag/0E1Z)
* [Stacks Project, Tag 0D0L](https://stacks.math.columbia.edu/tag/0D0L)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.SheafOfModules (inverseImageBaseRing inverseImageBaseRingOnMiddle
  inverseImageMiddleRing inverseImageFirstRingMap ringedSpaceStructureMap)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)

universe u

namespace Stacks.NaiveCotangentInverseImageStalkSmooth

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (g : P ⟶ Y)

/-- **The stalk of `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P` is the stalk of `g⁻¹𝒪_Y ⟶ 𝒪_P` at the image point.**
The stalk at `x` of the first ring map of the iterated tower is the identification
`(i⁻¹g⁻¹𝒪_Y)_x ≅ (g⁻¹𝒪_Y)_{i x}`, followed by the stalk at `i x` of the structural map of `g`,
followed by the identification `(𝒪_P)_{i x} ≅ (i⁻¹𝒪_P)_x`. -/
theorem stalkFunctor_map_inverseImageFirstRingMap (x : X) :
    (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g)).hom =
      ((Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} i.base
            (inverseImageBaseRingOnMiddle (ringedSpaceHom g)) x).hom ≫
          (TopCat.Presheaf.stalkFunctor CommRingCat.{u} (i.base x)).map
            (ringedSpaceStructureMap (ringedSpaceHom g)).hom) ≫
        (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} i.base P.sheaf x).inv :=
  (Iso.eq_comp_inv _).mpr
    (Stacks.SkyscraperPushforward.stalkSheafPullbackIso_naturality CommRingCat.{u} i.base
      (ringedSpaceStructureMap (ringedSpaceHom g)) x)

/-- **The stalk of `i⁻¹g⁻¹𝒪_Y ⟶ i⁻¹𝒪_P` is a formally smooth ring map for `g` formally
smooth.**  The ring homomorphism obtained by taking stalks at a point `x` of `X` of the first
ring map of the iterated tower of [Stacks Project, Tag 0E1Z] is formally smooth. -/
theorem formallySmooth_hom_stalk_inverseImageFirstRingMap
    (hg : Stacks.Smooth.FormallySmoothScheme g) (x : X) :
    (CommRingCat.Hom.hom ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g)).hom)).FormallySmooth := by
  rw [stalkFunctor_map_inverseImageFirstRingMap i g x]
  refine RingHom.FormallySmooth.comp (RingHom.FormallySmooth.comp
    (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
      (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} i.base
        (inverseImageBaseRingOnMiddle (ringedSpaceHom g)) x).hom))
    (Stacks.Smooth.formallySmooth_stalk_inverseImageStructureMap g hg (i.base x)))
    (RingHom.FormallySmooth.of_bijective (ConcreteCategory.bijective_of_isIso
      (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} i.base P.sheaf x).inv))

/-- **The stalk of `i⁻¹𝒪_P` is a formally smooth algebra over the stalk of `i⁻¹g⁻¹𝒪_Y`.**  For
`g` formally smooth and every point `x` of `X`, the algebra structure that the first ring map of
the iterated tower of [Stacks Project, Tag 0E1Z] induces on stalks at `x`, namely
`Stacks.RelativeDifferentialStalk.algebraStalk`, is formally smooth. -/
theorem formallySmooth_stalk_inverseImageFirstRingMap
    (hg : Stacks.Smooth.FormallySmoothScheme g) (x : X) :
    letI := Stacks.RelativeDifferentialStalk.algebraStalk
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom g)).hom x
    Algebra.FormallySmooth
      (ToType ((inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom g)).presheaf.stalk x))
      (ToType ((inverseImageMiddleRing (ringedSpaceHom i)).presheaf.stalk x)) :=
  (formallySmooth_hom_stalk_inverseImageFirstRingMap i g hg x).toAlgebra

end Stacks.NaiveCotangentInverseImageStalkSmooth

end
