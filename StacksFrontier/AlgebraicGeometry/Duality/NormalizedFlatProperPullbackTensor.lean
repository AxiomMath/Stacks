module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedCohenMacaulayNagata
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedProperNagata
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical isomorphisms `ω_X^• = a(ω_Y^•) = Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}^•` for a flat proper `f`

In Situation [Stacks, Tag 0AU4], let `f : X ⟶ Y` be a flat proper morphism of schemes of finite
type over `S`, `a` the right adjoint of `Rf_*`, `ω_{X/Y}^• = a(𝒪_Y)` the relative dualizing
complex, and `ω_X^•`, `ω_Y^•` the dualizing complexes normalized relative to `ω_S^•` for the
upper shriek functors of Nagata compactifications. [Stacks, Remark 0B6W] gives canonical
isomorphisms

`ω_X^• = a(ω_Y^•) = Lf^* ω_Y^• ⊗ᴸ_{𝒪_X} ω_{X/Y}^•`

in `D(𝒪_X)`: the first is [Stacks, Tag 0AUD] (`Stacks.Duality.twistedInverseImageObjIsoNagata`),
the second comes from the discussion in [Stacks, Remark 0B6S]: `a = f^!` for proper `f`, and for
the perfect morphism `f` the map `μ_{f,K} : Lf^* K ⊗ᴸ f^! 𝒪_Y ⟶ f^! K` of [Stacks, Tag 0B6T] is an
isomorphism on `D⁺_QCoh(𝒪_Y)` ([Stacks, Tag 0B6U] (e)).

## Main definitions

* `Stacks.Duality.NormalizedOnOpens.twistedInverseImageObjIsoPullbackTensorOfFlat`: the second
  canonical isomorphism `a(K) ≅ Lf^* K ⊗ᴸ a(𝒪_Y)` for `K ∈ D⁺_QCoh(𝒪_Y)`.
* `Stacks.Duality.NormalizedOnOpens.isoPullbackTensorOfFlatNagata`: **[Stacks, Remark 0B6W]**,
  the composite `ω_X^• ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}^•`.

## References

* [Stacks Project, Tag 0B6W](https://stacks.math.columbia.edu/tag/0B6W)
* [Stacks Project, Tag 0B6S](https://stacks.math.columbia.edu/tag/0B6S)
* [Stacks Project, Tag 0AUD](https://stacks.math.columbia.edu/tag/0AUD)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

namespace NormalizedOnOpens

variable {X Y S : Scheme.{u}} {f : X ⟶ Y} {q : Y ⟶ S} {p : X ⟶ S} (hpe : f ≫ q = p)
  (hp : IsFiniteTypeOverNoetherian p) (hq : IsFiniteTypeOverNoetherian q)
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S}

/-- **[Stacks, Remark 0B6W], the second canonical isomorphism.** For a flat proper morphism
`f : X ⟶ Y` of schemes of finite type over a Noetherian `S`, with `a` the right adjoint of
`Rf_*`, there is a canonical isomorphism `a(K) ≅ Lf^* K ⊗ᴸ a(𝒪_Y)` for `K ∈ D⁺_QCoh(𝒪_Y)`: through
`a = f^!` (at the Nagata compactification of `f`) it is the inverse of `μ_{f,K}`
([Stacks, Tag 0B6U] (e)). -/
@[stacks 0B6W "the second canonical isomorphism a(ω_Y^•) = Lf^* ω_Y^• ⊗ ω_{X/Y}^•"]
def twistedInverseImageObjIsoPullbackTensorOfFlat [IsProper f] [Flat f]
    (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K.obj ≅
      ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K.obj)).obj
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          (DerivedPushforward.derivedStructureSheaf Y)) :=
  haveI := hq.source_noetherian
  haveI := hp.source_noetherian
  haveI hf := isShriekable_of_isProper hq (f := f)
  haveI := locallyOfFinitePresentation_left
    (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
  haveI : Flat (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id f)).left := inferInstanceAs (Flat f)
  haveI : Perfect (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y)
    (Category.comp_id f)).left := inferInstance
  haveI := isIso_upperShriekCompareWithPullback
    (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
    (nagataCompactification f hf) K.obj K.property
  ((UpperShriek.shriekOfIsoOfIsProper nagataCompactification f hf).app K).symm ≪≫
    (asIso (upperShriekCompareWithPullbackCanonical
      (ftsHomOf f hf.separatedFiniteType (isSeparatedFiniteType_id Y) (Category.comp_id f))
      (nagataCompactification f hf) K.obj)).symm ≪≫
    ((quasiCoherentDerivedTensor X).obj ((quasiCoherentDerivedPullback' f).obj K.obj)).mapIso
      ((UpperShriek.shriekOfIsoOfIsProper nagataCompactification f hf).app
        (derivedStructureSheafPlus Y))

/-- **[Stacks, Remark 0B6W].** Let `f : X ⟶ Y` be a flat proper morphism of schemes of finite type
over `S`, where `S` is Noetherian with a dualizing complex `ω_S^•`, and `ω_X^•`, `ω_Y^•` the
dualizing complexes normalized relative to `ω_S^•`. With `a` the right adjoint of `Rf_*` and
`ω_{X/Y}^• = a(𝒪_Y)` the relative dualizing complex, the canonical isomorphism
`ω_X^• ≅ a(ω_Y^•) ≅ Lf^* ω_Y^• ⊗ᴸ ω_{X/Y}^•` in `D(𝒪_X)`: the inverse of
`Stacks.Duality.twistedInverseImageObjIsoNagata` ([Stacks, Tag 0AUD]) followed by
`twistedInverseImageObjIsoPullbackTensorOfFlat`. -/
@[stacks 0B6W "ω_X^• = a(ω_Y^•) = Lf^* ω_Y^• ⊗ ω_{X/Y}^• in D(O_X)"]
def isoPullbackTensorOfFlatNagata
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj) [IsProper f] [Flat f]
    (𝒦X : NormalizedOnOpens UpperShriek.nagata hp ωS)
    (𝒦Y : NormalizedOnOpens UpperShriek.nagata hq ωS) :
    haveI := hq.source_noetherian
    haveI := hp.source_noetherian
    𝒦X.complex.obj ≅ ((quasiCoherentDerivedTensor X).obj
        ((quasiCoherentDerivedPullback' f).obj 𝒦Y.complex.obj)).obj
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y)) :=
  (twistedInverseImageObjIsoNagata hpe hωS 𝒦X 𝒦Y).symm ≪≫
    twistedInverseImageObjIsoPullbackTensorOfFlat hq 𝒦Y.complex

end NormalizedOnOpens

end Stacks.Duality

end
