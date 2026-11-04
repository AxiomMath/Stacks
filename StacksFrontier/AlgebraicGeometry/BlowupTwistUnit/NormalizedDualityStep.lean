module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.SingleQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.NormalizedComposition
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.Hull
public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.HullInstances
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksCore.Tactic.StacksAttribute

/-!
# The duality step for a blowup, from the normalization of the dualizing modules

Let `b : X' ⟶ X` be a morphism of quasi-compact quasi-separated schemes over a quasi-compact
quasi-separated base `S`, and let `ω_S^•` be an object of `D_QCoh(𝒪_S)`. Suppose `ω_X` and
`ω_{X'}` are modules whose associated complexes in degree zero are the twisted inverse images of
`ω_S^•` along the two structure morphisms:

`h^×(ω_S^•) ≅ ω_X[0]` and `(b ≫ h)^×(ω_S^•) ≅ ω_{X'}[0]`,

which is what it means for them to be *normalized relative to `ω_S^•`*. Then for a
quasi-coherent module `ℱ` on `X'` there is a bijection

`Hom_{X'}(ℱ, ω_{X'}) ≃ Hom_{D(𝒪_X)}(Rb_*(ℱ[0]), ω_X[0])`,

so that a map from `ℱ` to the dualizing module upstairs is the same thing as a map from its
derived direct image to the dualizing module downstairs. Nothing is assumed beyond the two
normalizations: the identification `ω_{X'} = b^×(ω_X)` follows from them by the composition
formula for right adjoints, and the bijection is then the adjunction `Rb_* ⊣ b^×` itself,
together with the full faithfulness of the degree-zero embedding of modules into the derived
category.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `singleHomEquiv`, `quasiCoherentHomEquiv` and `singleQcohHom`: morphisms of modules are
  morphisms of the degree-zero complexes they define, and morphisms of `D_QCoh` are morphisms of
  the underlying complexes.
* `normalizedUpperShriekIso`: **`b^×(ω_X) ≅ ω_{X'}`** from the two normalizations.
* `normalizedDualityHomEquiv`: **the duality bijection** displayed above.

## Implementation notes

*Which model of the derived category.* Everything is read at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, found by instance search, which is the
model at which
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`
provides the right adjoint of `Rb_*` — the only model at which that statement has content, Brown
representability needing direct sums indexed by the universe of the morphisms. No local instance
attribute pins a model, and none may: pinning
`CategoryTheory.HasDerivedCategory.standard` would silently change which functor
`Stacks.Duality.twistedInverseImage` is and leave the adjunction unavailable.

*Why the normalizations rather than the identification `ω_{X'} = b^×ω_X`.* The latter is the
input the duality step is usually quoted with, but it is not independent data: a dualizing module
is pinned only up to shift and an invertible twist, and what fixes `ω_X` for a scheme over `S` is
precisely the normalization relative to a complex on `S`. Taking the normalizations as the inputs
and deriving the identification is therefore the faithful reading, and it is what
`Stacks.Duality.twistedInverseImageObjIsoOfNormalizedObjOfQcqs` carries out.

*Degree-zero full faithfulness.* `CategoryTheory.DerivedCategory.singleFunctor` is full and
faithful, so a morphism of complexes concentrated in degree zero is a morphism of modules; this
is what keeps the conclusion a statement about maps of sheaves rather than about maps in a
derived category.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
* [Stacks Project, Remark 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

/-! ### Morphisms of modules and morphisms of complexes -/

/-- **A morphism of `𝒪_X`-modules is a morphism of the complexes they define in degree zero.**
The degree-zero embedding of modules into the derived category is full and faithful. -/
def singleHomEquiv {X : Scheme.{u}} (M N : X.Modules) :
    (M ⟶ N) ≃ ((DerivedCategory.singleFunctor X.Modules 0).obj M ⟶
      (DerivedCategory.singleFunctor X.Modules 0).obj N) :=
  (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.singleFunctor X.Modules 0)).homEquiv

/-- **A morphism of `D_QCoh(𝒪_X)` is a morphism of the underlying complexes.** `D_QCoh(𝒪_X)` is
a full subcategory of `D(𝒪_X)`. -/
def quasiCoherentHomEquiv {X : Scheme.{u}} (K L : quasiCoherentDerivedCategory X) :
    (K ⟶ L) ≃ (K.obj ⟶ L.obj) :=
  (Functor.FullyFaithful.ofFullyFaithful
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB
      (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)))).homEquiv

/-- **A morphism of quasi-coherent modules as a morphism of `D_QCoh(𝒪_X)`** between the
complexes they define in degree zero. -/
def singleQcohHom {X : Scheme.{u}} {M N : X.Modules} (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (φ : M ⟶ N) :
    singleQuasiCoherent M hM 0 ⟶ singleQuasiCoherent N hN 0 :=
  (quasiCoherentHomEquiv (singleQuasiCoherent M hM 0) (singleQuasiCoherent N hN 0)).symm
    (singleHomEquiv M N φ)

/-! ### The duality bijection of one morphism -/

section Duality

variable {S X X' : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
  (b : X' ⟶ X) (h : X ⟶ S) (ωS : quasiCoherentDerivedCategory S)
  (ωX : X.Modules) (hωX : ωX.IsQuasicoherent)
  (ωX' : X'.Modules) (hωX' : ωX'.IsQuasicoherent)

/-- **`b^×(ω_X) ≅ ω_{X'}` for dualizing modules normalized relative to the same complex on the
base.** This is `Stacks.Duality.twistedInverseImageObjIsoOfNormalizedObjOfQcqs`: the twisted
inverse image of a composite is the composite of the twisted inverse images, right adjoints being
unique up to canonical isomorphism, so the normalization along `b ≫ h` is the twisted inverse
image along `b` of the normalization along `h`. -/
def normalizedUpperShriekIso
    (nX : ((twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj ωS).obj ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj ωX)
    (nX' : ((twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj ωS).obj ≅
        (DerivedCategory.singleFunctor X'.Modules 0).obj ωX') :
    ((twistedInverseImage b
        (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
      (singleQuasiCoherent ωX hωX 0)).obj ≅
      (DerivedCategory.singleFunctor X'.Modules 0).obj ωX' :=
  twistedInverseImageObjIsoOfNormalizedObjOfQcqs b h ωS
    (singleQuasiCoherent ωX hωX 0) (singleQuasiCoherent ωX' hωX' 0) nX nX'

/-- **The duality bijection `Hom_{X'}(ℱ, ω_{X'}) ≃ Hom(Rb_*ℱ, ω_X)`** for dualizing modules
normalized relative to the same complex on the base.

A map `ℱ ⟶ ω_{X'}` is a map of the degree-zero complexes (`singleHomEquiv`), hence by
`normalizedUpperShriekIso` a map `ℱ[0] ⟶ b^×(ω_X[0])`, hence a map of `D_QCoh(𝒪_{X'})`
(`quasiCoherentHomEquiv`), and the adjunction `Rb_* ⊣ b^×` turns that into a map
`Rb_*(ℱ[0]) ⟶ ω_X[0]`. -/
def normalizedDualityHomEquiv
    (nX : ((twistedInverseImage h
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj ωS).obj ≅
        (DerivedCategory.singleFunctor X.Modules 0).obj ωX)
    (nX' : ((twistedInverseImage (b ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (b ≫ h))).obj ωS).obj ≅
        (DerivedCategory.singleFunctor X'.Modules 0).obj ωX')
    (F : X'.Modules) (hF : F.IsQuasicoherent) :
    (F ⟶ ωX') ≃
      ((quasiCoherentDerivedPushforward b
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
        (singleQuasiCoherent F hF 0) ⟶ singleQuasiCoherent ωX hωX 0) :=
  ((singleHomEquiv F ωX').trans
      ((Iso.homCongr (Iso.refl _)
          (normalizedUpperShriekIso b h ωS ωX hωX ωX' hωX' nX nX').symm).trans
        (quasiCoherentHomEquiv (singleQuasiCoherent F hF 0)
          ((twistedInverseImage b
            (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
              (singleQuasiCoherent ωX hωX 0))).symm)).trans
    (relativeDualizingComplexHomEquiv b
      (isQuasicoherent_homology_derivedPushforward_of_qcqs b)
      (singleQuasiCoherent ωX hωX 0) (singleQuasiCoherent F hF 0))

end Duality

end Stacks.BlowupTwistUnit

end
