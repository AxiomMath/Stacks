module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChartTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOverBaseChangeAlgebraIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardAlgebraFunctorFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackChartSectionTranspose
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecBounded

/-!
# Stacks 081V in its corrected form

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 081V
asserts that `f ↦ f_* 𝒪_Y` is an anti-equivalence between the algebraic spaces `Y` affine over
`X` and the quasi-coherent sheaves of `𝒪_X`-algebras, and that it is compatible with arbitrary
base change.

As literally stated the anti-equivalence is refuted in this development:
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`
shows that a quasi-coherent algebra with at least `B.cutoff` sections over some étale chart is no
direct image, algebraic spaces living on a big fppf site with a cardinal cutoff while sheaves of
algebras are unbounded (the same bound is implicit in the set-theoretic conventions of the
Stacks project).  The corrected form takes as target the quasi-coherent algebras whose
sections over every étale chart are fewer than the cutoff,
`AlgebraicGeometry.Space.BoundedQuasicoherentAlgebra`; every direct image of an affine morphism
lies there, and `AlgebraicGeometry.Space.essImage_boundedPushforwardAlgebraFunctor_iff` shows
nothing is lost.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_boundedPushforwardAlgebraFunctor`: the direct image
  `f ↦ f_* 𝒪_Y` is an anti-equivalence onto the bounded quasi-coherent algebras.
* `AlgebraicGeometry.Space.isIso_affineOverBaseChangeAlgebraHom`: for `g : Y ⟶ X` and `Z`
  affine over `X`, the comparison `g^* (f_* 𝒪_Z) ⟶ f'_* 𝒪_{Y ×_X Z}` is an isomorphism.
* `AlgebraicGeometry.Space.quasicoherentAffineOverBaseChangeNatIso`: the anti-equivalence
  commutes with arbitrary base change, as a natural isomorphism of functors to the
  quasi-coherent `𝒪_Y`-algebras.
* `AlgebraicGeometry.Space.boundedAffineAlgebraAntiEquivalence`: the bounded anti-equivalence as
  a term of `AlgebraicGeometry.Space.BoundedAffineAlgebraAntiEquivalence`.
* `AlgebraicGeometry.Space.affineAlgebraAntiEquivalence_bounded`: the corrected Stacks 081V,
  both clauses together.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct-image functor of Stacks 081V is an equivalence onto the bounded quasi-coherent
algebras. -/
theorem isEquivalence_boundedPushforwardAlgebraFunctor (X : AlgebraicSpaces B S hS) :
    (boundedPushforwardAlgebraFunctor B S hS X).IsEquivalence :=
  have := full_boundedPushforwardAlgebraFunctor B S hS X
  have := (faithful_boundedPushforwardAlgebraFunctor_iff B S hS X).2
    (faithful_affinePushforwardAlgebraFunctor B S hS X)
  have := essSurj_boundedPushforwardAlgebraFunctor B S hS X
  { }

/-- The bounded anti-equivalence of Stacks 081V, with its functor the direct image. -/
def boundedAffineAlgebraAntiEquivalence : BoundedAffineAlgebraAntiEquivalence B S hS :=
  boundedAffineAlgebraAntiEquivalenceOfIsEquivalence
    (isEquivalence_boundedPushforwardAlgebraFunctor B S hS)

variable {X Y : AlgebraicSpaces B S hS}

/-- For `g : Y ⟶ X` and `Z` affine over `X`, the comparison `g^* (f_* 𝒪_Z) ⟶ f'_* 𝒪_{Y ×_X Z}` of
`AlgebraicGeometry.Space.affineOverBaseChangeAlgebraHom` is an isomorphism of `𝒪_Y`-algebras. -/
theorem isIso_affineOverBaseChangeAlgebraHom (g : Y ⟶ X) (Z : AffineOver B S hS X) :
    IsIso (affineOverBaseChangeAlgebraHom B S hS g Z) :=
  isIso_affineOverBaseChangeAlgebraHom_of_chart B S hS g Z
    (fun d s => underlyingModuleAlgebraPullbackModulePullbackIso_chartSection B S hS g
      (pushforwardAlgebra B S hS Z.obj) d s)
    (fun d => affineOverBaseChangeChartRingHom B S hS g Z d)
    (fun d s => affineOverBaseChangeChartRingHom_apply B S hS g Z d s)
    (fun d hU hV => isPushout_affineOverBaseChangeChartRingHom B S hS g Z d hU hV)

/-- The anti-equivalence of Stacks 081V commutes with arbitrary base change: for `g : Y ⟶ X`,
the direct image on the algebraic spaces affine over `X` followed by pullback of
quasi-coherent algebras along `g` is naturally isomorphic to base change along `g` followed by
the direct image on the algebraic spaces affine over `Y`; the component at `Z` is the comparison
`g^* (f_* 𝒪_Z) ≅ f'_* 𝒪_{Y ×_X Z}`. -/
def quasicoherentAffineOverBaseChangeNatIso (g : Y ⟶ X) :
    quasicoherentPushforwardAlgebraFunctor B S hS X ⋙ quasicoherentAlgebraPullback B S hS g ≅
      (affineOverBaseChangeFunctor B S hS g).op ⋙ quasicoherentPushforwardAlgebraFunctor B S hS Y :=
  quasicoherentAffineOverBaseChangeNatIsoOfIsIso B S hS g
    (isIso_affineOverBaseChangeAlgebraHom B S hS g)

/-- For every algebraic space `X`, the direct image
`f ↦ f_* 𝒪_Y` is an anti-equivalence from the algebraic spaces affine over `X` onto the
quasi-coherent `𝒪_X`-algebras with fewer than the big fppf site's cutoff many sections over every
étale chart; and for every morphism `g : Y ⟶ X` of algebraic spaces the direct image commutes with
base change along `g`, naturally in the affine space. -/
@[stacks 081V "corrected form: f ↦ f_* 𝒪_Y is an anti-equivalence from the algebraic spaces \
affine over X onto the quasi-coherent 𝒪_X-algebras with fewer than the big fppf site's cutoff \
many sections over every étale chart (the unrestricted target is refuted by \
not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart, and the bounded algebras \
are exactly the essential image by essImage_boundedPushforwardAlgebraFunctor_iff), and it \
commutes with arbitrary base change g : Y ⟶ X, naturally in the affine space"]
theorem affineAlgebraAntiEquivalence_bounded :
    (∀ X : AlgebraicSpaces B S hS, (boundedPushforwardAlgebraFunctor B S hS X).IsEquivalence) ∧
      ∀ {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X),
        Nonempty (quasicoherentPushforwardAlgebraFunctor B S hS X ⋙
            quasicoherentAlgebraPullback B S hS g ≅
          (affineOverBaseChangeFunctor B S hS g).op ⋙
            quasicoherentPushforwardAlgebraFunctor B S hS Y) :=
  ⟨isEquivalence_boundedPushforwardAlgebraFunctor B S hS,
    fun g => ⟨quasicoherentAffineOverBaseChangeNatIso B S hS g⟩⟩

end AlgebraicGeometry.Space

end
