module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.Composition

/-!
# Transporting a normalization along the composition formula for the twisted inverse image

Let `g : Z ⟶ X` and `f : X ⟶ Y` be morphisms of schemes and let `f^×`, `g^×` and `(g ≫ f)^×` be
the twisted inverse images of [Stacks, Tag 0A9E], that is the right adjoints of the restrictions
of derived direct image to the complexes with quasi-coherent cohomology. Fix an object `ω_Y^•`
of `D_QCoh(𝒪_Y)` and suppose two further objects are *normalized relative to it*:

`ω_X^• ≅ f^× ω_Y^•` and `ω_Z^• ≅ (g ≫ f)^× ω_Y^•`.

Then `g^× ω_X^• ≅ ω_Z^•`. The proof is one application of the composition formula
`(g ≫ f)^× ≅ f^× ⋙ g^×` of `Stacks.Duality.twistedInverseImageCompIso`, which is itself nothing
but uniqueness of right adjoints applied to `R(g ≫ f)_* ≅ Rg_* ⋙ Rf_*`.

This is the mathematical content of [Stacks, Tag 0AUD] — for a morphism `f : X ⟶ Y` of schemes
of finite type over a base carrying a dualizing complex, the right adjoint of `Rf_*` carries the
normalized complex downstairs to the normalized complex upstairs — carried out with the
*constructed* twisted inverse image of [Stacks, Tag 0A9E] in place of the upper shriek formalism
`Stacks.Duality.UpperShriek`, which in this repository is everywhere a parameter. Where
`Stacks.Duality.dualizingIsoRightAdjointObj` takes the formalism, the factorization comparison
and the identification of `f^!` with the right adjoint as inputs, nothing below is a hypothesis
beyond the two normalizations themselves: the only comparison used is the one this repository
constructs.

## Main definitions

All in the namespace `Stacks.Duality`.

* `twistedInverseImageObjIsoOfNormalized` — `g^× ω_X^• ≅ ω_Z^•` from the two normalizations.
* `twistedInverseImageObjIsoOfNormalizedOfQcqs` — the same with every input discharged for
  morphisms of quasi-compact quasi-separated schemes, where [Stacks, Tag 0A9E] is proved
  unconditionally as
  `Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`.

## Implementation notes

*Why this is the shape the consumers want.* A dualizing module normalized relative to a dualizing
module `ω_A` on an affine base, in the sense of [Stacks, Remark 0B4R], is given by an
isomorphism `ω_X ≅ f^×(ω_A)` with both sides in degree zero — this is
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`. For a blowup
`b : X' ⟶ X` of such an `X` the normalization of `ω_{X'}` is taken relative to the *same* `ω_A`,
along the composite `b ≫ f`. The statement below turns that pair of normalizations into
`b^× ω_X ≅ ω_{X'}`, which is the identity `ω_{X'} = b^!ω_X` that the duality step for a blowup
needs, and it needs no properness: `b` enters only through the composition formula.

*No properness and no finite type.* [Stacks, Tag 0AUD] states its hypotheses for a morphism of
`AlgebraicGeometry.FTS S` with `f` proper, because that is the situation in which the source has
`f^!` and knows it to be the right adjoint. Here the right adjoint itself is used throughout, so
the only hypotheses are the ones its existence needs.

## References

* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

section General

variable {Z X Y : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushgf : ∀ (K : quasiCoherentDerivedCategory Z) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward (g ≫ f)).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (g ≫ f) hpushgf).IsLeftAdjoint]

/-- **The twisted inverse image of a normalized complex is the normalized complex upstairs.**
Let `g : Z ⟶ X` and `f : X ⟶ Y` be morphisms along which derived direct image preserves
quasi-coherence of cohomology and whose restrictions to `D_QCoh` have right adjoints. If
`ω_X^• ≅ f^×ω_Y^•` and `ω_Z^• ≅ (g ≫ f)^×ω_Y^•`, then `g^×ω_X^• ≅ ω_Z^•`.

This is the content of [Stacks, Tag 0AUD]; the only comparison it uses is
`Stacks.Duality.twistedInverseImageCompIso`, the composition formula for the right adjoints. -/
def twistedInverseImageObjIsoOfNormalized (ωY : quasiCoherentDerivedCategory Y)
    {ωX : quasiCoherentDerivedCategory X} {ωZ : quasiCoherentDerivedCategory Z}
    (nX : ωX ≅ (twistedInverseImage f hpushf).obj ωY)
    (nZ : ωZ ≅ (twistedInverseImage (g ≫ f) hpushgf).obj ωY) :
    (twistedInverseImage g hpushg).obj ωX ≅ ωZ :=
  (twistedInverseImage g hpushg).mapIso nX ≪≫
    ((twistedInverseImageCompIso g f hpushg hpushf hpushgf).app ωY).symm ≪≫ nZ.symm

end General

section Qcqs

variable {Z X Y : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
  [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **`Stacks.Duality.twistedInverseImageObjIsoOfNormalized` with every input discharged.** For
morphisms `g : Z ⟶ X` and `f : X ⟶ Y` of quasi-compact and quasi-separated schemes, the
quasi-coherence of the cohomology of derived direct image is part (1) of [Stacks, Tag 08D5] and
the existence of the right adjoints is [Stacks, Tag 0A9E], both proved; so two normalizations
`ω_X^• ≅ f^×ω_Y^•` and `ω_Z^• ≅ (g ≫ f)^×ω_Y^•` give `g^×ω_X^• ≅ ω_Z^•` with no hypothesis
beyond the three schemes being quasi-compact and quasi-separated. -/
def twistedInverseImageObjIsoOfNormalizedOfQcqs (ωY : quasiCoherentDerivedCategory Y)
    {ωX : quasiCoherentDerivedCategory X} {ωZ : quasiCoherentDerivedCategory Z}
    (nX : ωX ≅ (twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωY)
    (nZ : ωZ ≅ (twistedInverseImage (g ≫ f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))).obj ωY) :
    (twistedInverseImage g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj ωX ≅ ωZ :=
  twistedInverseImageObjIsoOfNormalized g f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f)) ωY nX nZ

/-- **`Stacks.Duality.twistedInverseImageObjIsoOfNormalizedOfQcqs` with the normalizations read
in the ambient derived categories.** `D_QCoh` is a full subcategory of `D(𝒪_X)`, so an
isomorphism of its objects is the same thing as an isomorphism of the underlying objects of
`D(𝒪_X)`; this is the form in which a normalization is recorded by
`AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`, whose `normalizedIso`
field is an isomorphism `f^!(ω_A) ≅ ω_X` of `D(𝒪_X)` with `ω_X` placed in degree zero.

So for a blowup `g : Z ⟶ X` of a scheme `X` proper over an affine base `Y`, two normalizations
relative to the same complex on `Y` — one for `X` along `f` and one for `Z` along `g ≫ f` —
give `g^×ω_X^• ≅ ω_Z^•`. -/
def twistedInverseImageObjIsoOfNormalizedObjOfQcqs (ωY : quasiCoherentDerivedCategory Y)
    (ωX : quasiCoherentDerivedCategory X) (ωZ : quasiCoherentDerivedCategory Z)
    (nX : ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj ωY).obj ≅ ωX.obj)
    (nZ : ((twistedInverseImage (g ≫ f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (g ≫ f))).obj ωY).obj ≅ ωZ.obj) :
    ((twistedInverseImage g
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj ωX).obj ≅ ωZ.obj :=
  (ObjectProperty.ι _).mapIso
    (twistedInverseImageObjIsoOfNormalizedOfQcqs g f ωY
      (ObjectProperty.isoMk _ nX).symm (ObjectProperty.isoMk _ nZ).symm)

end Qcqs

end Stacks.Duality

end
