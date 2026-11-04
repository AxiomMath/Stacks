module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreProperty
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSemistableGenus
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.AlgebraicGeometry.Quot.StableFamilyDualizingAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquareSubmodules
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.PrestableFibre
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# The relative dualizing sheaf of a family of curves, and surjectivity of `f^*f_*𝓛 ⟶ 𝓛`

Let `f : X ⟶ S` be a family of curves and `(ω^•_{X/S}, τ)` a relative dualizing complex of `f`
(Stacks 0E5X). The *relative dualizing sheaf* is `ω_{X/S} = H^{-1}(ω^•_{X/S})` (Stacks 0E6Q).
This file sets up the objects in the statement of Stacks 0E6Y: `ω_{X/S}`, the inverse image
`f⁻¹(U)` of an open `U` of the base as an open subspace of the total space, and the condition
that the counit `f^*f_*𝓛 ⟶ 𝓛` is surjective over `f⁻¹(U)` for some open `U` containing a given
point.

## Main definitions

* `AlgebraicGeometry.CurveFamily.dualizingSheafOfComplex`: `ω_{X/S} = H^{-1}(ω^•_{X/S})`.
* `AlgebraicGeometry.CurveFamily.preimageOpens`: the open subspace `f⁻¹(U)`.
* `AlgebraicGeometry.CurveFamily.IsCounitSurjectiveAbove`: `f^*f_*𝓛 ⟶ 𝓛` is surjective over
  `f⁻¹(U)` for some open `U ∋ s`.

## Implementation notes

A relative dualizing complex is taken as an argument rather than chosen: relative dualizing
complexes of a proper flat morphism of finite presentation are unique up to unique isomorphism, so
every statement about `ω_{X/S}` is a statement about each of them.

## References

* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E5X](https://stacks.math.columbia.edu/tag/0E5X)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- The *relative dualizing sheaf* `ω_{X/S} = H^{-1}(ω^•_{X/S})` of a family of curves, for a
relative dualizing complex `(ω^•_{X/S}, τ)` of the family (Stacks 0E5X, 0E6Q). -/
def dualizingSheafOfComplex (X : CurveFamily B hZ)
    (D : Space.RelativeDualizingComplex B.contains_terminal X.toBase X.proper X.flat
      X.finitePresentation) :
    Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2 :=
  (DerivedCategory.homologyFunctor _ (-1)).obj D.ω

/-- The inverse image `f⁻¹(U)` of an open `U` of the base of a family of curves, as a subfunctor
of the total space. -/
abbrev preimageOpens (X : CurveFamily B hZ)
    (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens) : Subfunctor X.total.1 :=
  (Space.subspaceOfOpens B integerBase hZ X.base U).preimage X.toBase.hom

/-- The inverse image of an open of the base is an open subspace of the total space. -/
theorem isOpenSubspace_preimageOpens (X : CurveFamily B hZ)
    (U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens) :
    Space.IsOpenSubspace B integerBase hZ (X.preimageOpens U) :=
  Space.isOpenSubspace_preimage B integerBase hZ X.toBase.hom _ (schemeSpace X.base).2 X.total.2
    (Space.isOpenSubspace_subspaceOfOpens B integerBase hZ X.base U)

/-- The counit `f^*f_*𝓛 ⟶ 𝓛` of the adjunction `f^* ⊣ f_*` of the structure morphism of a family
of curves. -/
abbrev pushforwardCounit (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) :
    (Space.modulePullback B integerBase hZ X.toBase).obj
        ((Space.modulePushforward B integerBase hZ X.toBase).obj L) ⟶ L :=
  (Space.modulePullbackAdjunction B integerBase hZ X.toBase).counit.app L

/-- **Condition (2) of Stacks 0E6Y.** For a module `𝓛` on the total space of a family of curves
`f : X ⟶ S` and a point `s` of the base, the counit `f^*f_*𝓛 ⟶ 𝓛` is surjective over `f⁻¹(U)`
for some open `U ∋ s` of the base: its pullback to the open subspace `f⁻¹(U)` is an epimorphism
of sheaves of modules. -/
def IsCounitSurjectiveAbove (X : CurveFamily B hZ)
    (L : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
    (s : (BigFppfOver.toScheme B integerBase hZ).obj X.base) : Prop :=
  ∃ U : ((BigFppfOver.toScheme B integerBase hZ).obj X.base).Opens, s ∈ U ∧
    Epi ((Space.modulePullback B integerBase hZ
      (Space.openSubspaceHom B integerBase hZ (X.preimageOpens U)
        (X.isOpenSubspace_preimageOpens U))).map (X.pushforwardCounit L))

end CurveFamily

namespace C1764Prereq

/-- A presentation of the fibre `X_s` of a family of curves is a cartesian square of algebraic
spaces over `Spec κ(s) ⟶ S`. -/
theorem isPullback_fibre {X : CurveFamily B hZ}
    {s : (BigFppfOver.toScheme B integerBase hZ).obj X.base} {V : BigFppfOver B integerBase hZ}
    {v : V ⟶ CurveFamily.residuePoint B hZ X s} {q : yoneda.obj V ⟶ X.total.obj}
    (hq : CurveFamily.IsFibrePresentation B hZ X s v q) :
    IsPullback (ObjectProperty.homMk q : schemeSpace V ⟶ X.total) (schemeSpaceMap v) X.toBase
      (schemeSpaceMap (CurveFamily.residuePointMap B hZ X s)) :=
  C1590Private.isPullback_homMk_of_isPullback _ v q hq

end C1764Prereq

end AlgebraicGeometry
