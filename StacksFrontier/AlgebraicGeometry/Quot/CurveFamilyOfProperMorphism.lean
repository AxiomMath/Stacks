module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource

/-!
# A proper flat morphism of schemes as a family of curves

A morphism of the big fppf site of the integers whose underlying morphism of schemes is flat,
proper and locally of finite presentation, and whose source has topological Krull dimension at
most one, is a family of curves in the sense of Stacks 0D4Z, given three space-level conditions
on the induced morphism of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.curveFamilyOfSchemeMorphism` assembles the family of curves.

## Implementation notes

Of the nine obligations of `AlgebraicGeometry.CurveFamily`, the seven scheme-level ones are
instances, four of the scheme-to-space transfers are the every-étale-chart comparison
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` of Stacks 03MJ applied to the
Stacks 04R3 étale-locality witnesses for flatness, finite type and finite presentation together
with `AlgebraicGeometry.Space.presheaf_universallyClosed_iff` of Stacks 03XD, and the
relative-dimension condition is
`AlgebraicGeometry.Space.relativeDimensionLE_schemeSpaceMap`.

The remaining three are taken as the hypotheses `hqc`, `hsep` and `hqsep`: quasi-compactness of
the induced morphism of algebraic spaces, the subject of Stacks 04XW
(`AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed`), and its separatedness and
quasi-separatedness, the subject of Stacks 03KY
(`AlgebraicGeometry.Space.separationProperties_of_relativelyRepresentable`).

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 03KY](https://stacks.math.columbia.edu/tag/03KY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A morphism of the big fppf site of the integers which is flat, proper and locally of finite
presentation on underlying schemes and whose source has topological Krull dimension at most one,
as a family of curves in the sense of Stacks 0D4Z.

Quasi-compactness (Stacks 04XW) and separatedness and quasi-separatedness (Stacks 03KY) of the
induced morphism of algebraic spaces are hypotheses. -/
def curveFamilyOfSchemeMorphism {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hqc : Space.IsQuasiCompact B integerBase hZ (schemeSpaceMap g).hom)
    (hsep : Space.IsSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hqsep : Space.IsQuasiSeparated B integerBase hZ (schemeSpaceMap g).hom)
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    CurveFamily B hZ where
  base := U
  total := schemeSpace T
  toBase := schemeSpaceMap g
  flat := (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
    Flat.isEtaleLocalOnSourceAndTarget g).2 hflat
  proper := by
    refine ⟨hsep, ⟨?_, hqc⟩, ?_⟩
    · exact (Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget g).2 inferInstance
    · have hrep : yoneda.relativelyRepresentable (yoneda.map g) :=
        Functor.relativelyRepresentable.map _ _
      exact (Space.presheaf_universallyClosed_iff B integerBase hZ
          (isAlgebraicSpace_yoneda B integerBase hZ T)
          (isAlgebraicSpace_yoneda B integerBase hZ U) hrep).1
        (Space.presheaf_yoneda_map_of_inverseImage B integerBase hZ
          (P := @UniversallyClosed.{u}) inferInstance g inferInstance)
  finitePresentation :=
    ⟨(Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
        LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget g).2 hlfp,
      hqc, hqsep⟩
  relativeDimensionLE :=
    Space.relativeDimensionLE_schemeSpaceMap B integerBase hZ g 1 (by simpa using hdim)

end AlgebraicGeometry

end
