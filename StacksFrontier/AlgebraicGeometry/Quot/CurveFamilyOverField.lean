module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOfProperMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff

/-!
# The family of curves of a proper scheme over a field

A morphism of the big fppf site of `Spec(ℤ)` which is flat, proper and locally of finite
presentation, with source of dimension at most one, is a family of curves ([Stacks, Tag 0D4Z]); the
space-level quasi-compactness, separatedness and quasi-separatedness asked for by
`AlgebraicGeometry.curveFamilyOfSchemeMorphism` are those of the morphism of schemes.

A proper scheme `X` of dimension at most one over a field `k` is such a morphism `X ⟶ Spec k`
with nothing further assumed: flatness holds over a field, finite presentation follows from finite
type over a Noetherian base, and `X` lies in every big fppf site containing `Spec k`. This gives
the point `x₀ : Spec k ⟶ Curves` classifying `X`.

## Main definitions

* `AlgebraicGeometry.curveFamilyOfProperFlatMorphism`: a flat, proper morphism of finite
  presentation of the site, with source of dimension at most one, as a family of curves.
* `AlgebraicGeometry.curveFamilyOfScheme`: the family of curves `X ⟶ Spec k` of a proper scheme
  of dimension at most one over a field.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **A proper flat morphism of finite presentation as a family of curves.** A morphism of the big
fppf site of the integers which is flat, proper and locally of finite presentation, and whose
source has dimension at most one, is a family of curves ([Stacks, Tag 0D4Z]). -/
def curveFamilyOfProperFlatMorphism {T U : BigFppfOver B integerBase hZ} (g : T ⟶ U)
    (hflat : Flat ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B integerBase hZ).map g))
    (hdim : topologicalKrullDim ((BigFppfOver.toScheme B integerBase hZ).obj T) ≤ 1) :
    CurveFamily B hZ :=
  curveFamilyOfSchemeMorphism B hZ g hflat hproper hlfp
    (Space.isQuasiCompact_yoneda_map_of_quasiCompact B integerBase hZ g inferInstance)
    ((Space.isSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance)
    ((Space.isQuasiSeparated_yoneda_map_iff B integerBase hZ g).2 inferInstance) hdim

/-- A scheme of the site, as a scheme over the integers. -/
abbrev integerSiteObject {T : Scheme.{u}} (hT : B.Contains T) : BigFppfOver B integerBase hZ :=
  (schemeOverIntegers B).obj (B.obj hT)

/-- A morphism of schemes of the site, as a morphism of schemes over the integers. -/
abbrev integerSiteMap {T T' : Scheme.{u}} (hT : B.Contains T) (hT' : B.Contains T')
    (f : T ⟶ T') : integerSiteObject B hZ hT ⟶ integerSiteObject B hZ hT' :=
  (schemeOverIntegers B).map (ObjectProperty.homMk f)

end

/-- **The family of curves of a proper scheme `X` of dimension at most one over a field `k`**: its
structure morphism `X ⟶ Spec k`, in a big fppf site containing `Spec k`. This is the point
`x₀ : Spec k ⟶ Curves` classifying `X`. -/
def curveFamilyOfScheme {k : Type u} [Field k] (X : Over (Spec (.of k))) [IsProper X.hom]
    (B : BigFppfSite.{u}) (hZ : B.Contains integerBase) (hk : B.Contains (Spec (.of k)))
    (hdim : topologicalKrullDim X.left ≤ 1) : CurveFamily B hZ :=
  curveFamilyOfProperFlatMorphism B hZ
    (integerSiteMap B hZ (Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk) hk X.hom)
    (inferInstance : Flat X.hom) ‹_› (inferInstance : LocallyOfFinitePresentation X.hom) hdim

end AlgebraicGeometry

end
