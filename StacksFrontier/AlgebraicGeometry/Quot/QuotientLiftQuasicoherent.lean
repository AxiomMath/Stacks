module

public import StacksFrontier.Deformation.ToposThickening.QuotientLiftDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional

/-!
# Quasi-coherence of the lifts of a quotient across a thickening of algebraic spaces

Let `X_T ⟶ X_{T'}` be a first order thickening of algebraic spaces, read as a first order
thickening of small étale ringed topoi sitting in a strict square over a thickening of bases, let
`ℱ'` be a quasi-coherent `𝒪_{X_{T'}}`-module flat over the base and let `𝒦 ⊂ ℱ = ℱ'|_{X_T}` be the
kernel of a quasi-coherent quotient `𝒬`. A lift `𝒦' ⊂ ℱ'` of the quotient in the sense of ringed
topoi (`Deformation.ToposThickening.IsQuotientLift`) has quasi-coherent quotient `ℱ'/𝒦'`, as soon
as `𝒬 ⊗ f^*𝒥` is quasi-coherent: `ℱ'/𝒦'` is an extension of `i_*𝒬` by `i_*(𝒬 ⊗ f^*𝒥)`
(`Deformation.ToposThickening.exists_shortExact_cokernel_of_isQuotientLift`), the direct image
along the affine morphism `X_T ⟶ X_{T'}` preserves quasi-coherence (Stacks 07U8), and
quasi-coherent modules on an algebraic space are closed under extensions (Stacks 03M1).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_isQuotientLift`.

## References

* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening
open Stacks.Sheaves.RingedToposModules.RingedToposHom (pullbackModules)

universe u vS uS wS vS' uS' wS'

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S₀ : Scheme.{u}} {hS₀ : B.Contains S₀}
  {XT XT' : AlgebraicSpaces B S₀ hS₀} (g : XT ⟶ XT')
  {S : RingedTopos.{vS, uS, wS}} {S' : RingedTopos.{vS', uS', wS'}}
  [S.J.HasSheafCompose (forget RingCat.{wS})] [S'.J.HasSheafCompose (forget RingCat.{wS'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{wS} RingCat.{wS})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{wS'} RingCat.{wS'})]
  [S.J.HasSheafCompose (forget AddCommGrpCat.{wS})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{wS'})]
  [HasWeakSheafify S.J AddCommGrpCat.{wS}] [S.J.WEqualsLocallyBijective AddCommGrpCat.{wS}]
  (t : RingedToposHom S S') (f : RingedToposHom (smallEtaleRingedTopos B S₀ hS₀ XT) S)
  (f' : RingedToposHom (smallEtaleRingedTopos B S₀ hS₀ XT') S')
  (hi : FirstOrderThickening (smallEtaleRingedToposHom B S₀ hS₀ g)) (ht : FirstOrderThickening t)
  (comm : f'.comp (smallEtaleRingedToposHom B S₀ hS₀ g) = t.comp f)

include comm in
/-- **A lift of a quasi-coherent quotient across a thickening of algebraic spaces is
quasi-coherent**, provided `𝒬 ⊗ f^*𝒥` is quasi-coherent and `X_T ⟶ X_{T'}` is affine. -/
theorem isQuasicoherentOnSite_cokernel_of_isQuotientLift (hg : IsAffineHom B S₀ hS₀ g.hom)
    (F' : Modules.{u, u} B S₀ hS₀ XT'.1 XT'.2)
    (hstrict : (MorphismOfThickenings.ofFirstOrderThickenings (smallEtaleRingedToposHom B S₀ hS₀ g)
      t f f' hi ht comm).IsStrict)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat
      ((SheafOfModules.restrictScalars
        ((sheafCompose (smallEtaleRingedTopos B S₀ hS₀ XT').J
          (forget₂ CommRingCat.{u} RingCat.{u})).map f'.fSharpInverseImage)).obj F'))
    (K : Subobject ((modulePullback B S₀ hS₀ g).obj F'))
    (hQ : (cokernel K.arrow).IsQuasicoherentOnSite)
    (hJ : ((baseIdealTensor t f ht).obj (cokernel K.arrow)).IsQuasicoherentOnSite)
    {K' : Subobject F'} (hK' : IsQuotientLift (smallEtaleRingedToposHom B S₀ hS₀ g) f' F' K K') :
    (cokernel K'.arrow).IsQuasicoherentOnSite := by
  obtain ⟨ι, p, w, hSES⟩ := exists_shortExact_cokernel_of_isQuotientLift
    (smallEtaleRingedToposHom B S₀ hS₀ g) t f f' hi ht comm F' K hstrict hflat hK'
  have hpush : ∀ G : Modules.{u, u} B S₀ hS₀ XT.1 XT.2, G.IsQuasicoherentOnSite →
      ((smallEtaleRingedToposHom B S₀ hS₀ g).pushforwardModules.obj G).IsQuasicoherentOnSite := by
    intro G hG
    rw [pushforwardModules_eq_modulePushforward]
    exact isQuasicoherentOnSite_modulePushforward_isAffineHom B S₀ hS₀ g hg G hG
  exact (isClosedUnderExtensions_quasicoherentSheaves_schemeUniverse B S₀ hS₀ XT'.1
    XT'.2).prop_X₂_of_shortExact hSES (hpush _ hJ) (hpush _ hQ)

end AlgebraicGeometry.Space

end
