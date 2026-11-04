module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentSinglePushforwardSpelling
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.PointBlowupHigherDirectImages

/-!
# `Rb_*(ℱ[0]) = (b_*ℱ)[0]` for a blowup in a closed point of a surface

Let `W` be an integral Noetherian scheme with `topologicalKrullDim W = 2`, let `w ∈ W` be a
closed point and let `b : W' ⟶ W` be the blowing up of `W` in the reduced point `{w}`. For a
quasi-coherent `𝒪_{W'}`-module `ℱ` the higher direct images `R^q b_*ℱ` vanish for every `q ≥ 2`
with no further hypothesis, by
`AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt`;
so the single vanishing `R^1b_*ℱ = 0` makes `ℱ` right acyclic for `b_*` and therefore

`Rb_*(ℱ[0]) ≅ (b_*ℱ)[0]`.

This file records that implication and carries the resulting isomorphism across to
`D_QCoh(𝒪_W)` at the locally small model, which is the shape the duality adjunction of
[Stacks, Tag 0A9E] — and hence the field
`Stacks.BlowupTwistUnit.NormalizedTopFormData.pushforwardIso` of the induction of
[Stacks, Tag 0B4T] — is written in. **No derived category remains in the hypotheses**: what is
left of that field, for a module given up to isomorphism, is the vanishing of `R^1b_*` and the
computation of `b_*` itself.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `rightAcyclic_pushforward_blowUpToBase_vanishingIdeal_singleton`: **`R^1b_*ℱ = 0` makes a
  quasi-coherent `ℱ` right acyclic for `b_*`**, the range `q ≥ 2` being automatic.
* `standardDerivedPushforwardSingleIso`: **`Rb_*(ℱ[0]) ≅ (b_*ℱ)[0]` in `D(𝒪_W)`** at
  `CategoryTheory.HasDerivedCategory.standard`.
* `standardDerivedPushforwardSingleIsoOfIso`: the same with the target read through an
  identification `b_*ℱ ≅ 𝒢` of the direct image with a module given on the base.
* `quasiCoherentDerivedPushforwardSingleIso`: **`Rb_*(ℱ[0]) ≅ 𝒢[0]` in `D_QCoh(𝒪_W)`** at the
  locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, again along such an
  identification — the form in which the dichotomy of [Stacks, Tag 0B3T] delivers the top forms
  upstairs.

## Implementation notes

*The two models.* The vanishing
`AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt`,
`CategoryTheory.Functor.rightAcyclic` and `Stacks.DeRham.pushforwardSingleToDerived`
are all written at `CategoryTheory.HasDerivedCategory.standard`, while
`Stacks.Duality.quasiCoherentDerivedPushforward` is written at the locally small model, the
adjunction of [Stacks, Tag 0A9E] needing the morphisms to live in a fixed universe. The first
three statements below therefore live in a section where the global locally small instances are
erased and the standard model installed — the sanctioned pattern, as in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Boundedness/PointBlowupHigherDirectImages.lean`
— and the crossing is
`Stacks.Duality.StandardModel.isoSingleQuasiCoherentOfStandardIso`, which is the bridge built for
exactly this purpose. Because the three are `def`s and `theorem`s whose statements mention the
model only through instance arguments, their elaborated types pin the standard model and the
bridge applies to them outside the section.

*Why right acyclicity and not a concentration argument.* `Rb_*(ℱ[0])` could be identified with
`(b_*ℱ)[0]` by showing its cohomology concentrated in degree zero and then invoking
[Stacks, Tag 0118]; that produces an isomorphism, but not the *canonical* comparison
`b_*ℱ ⟶ Rb_*ℱ`. Right acyclicity gives the canonical one, which is what makes the result usable
in a diagram, and the criterion [Stacks, Tag 0G9N] is available.

**No `@[stacks]` attribute is placed.** The vanishing in degrees `q ≥ 2` is registered where it
is proved, the acyclicity criterion is [Stacks, Tag 015C] and the comparison is
[Stacks, Tag 0G9N], both registered at their own statements; what is below is their instance at
one morphism, and an input of the induction of [Stacks, Tag 0B4T].

## References

* [Stacks Project, Tag 0G9N](https://stacks.math.columbia.edu/tag/0G9N)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality

universe u

namespace Stacks.BlowupTwistUnit

section Standard

attribute [-instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

attribute [local instance] HasDerivedCategory.standard

variable {W : Scheme.{u}} [AlgebraicGeometry.IsIntegral W] [IsNoetherian W]

/-- **`R^1b_*ℱ = 0`** for the blowing up `b : W' ⟶ W` of a scheme in the reduced closed point
`{w}`, as a predicate on `ℱ`.

The right derived functors of `b_*` are read at `CategoryTheory.HasDerivedCategory.standard`,
so a statement can ask for the predicate without naming a model. -/
abbrev IsZeroFirstDirectImageBlowUp (w : W) (hw : IsClosed ({w} : Set W))
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules) : Prop :=
  IsZero (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightDerivedPlus 1).obj F)

omit [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W] in
/-- **The vanishing of `R^1b_*` is invariant under isomorphism of the module.** Stated here, with
the predicate, because transporting it outside this section would read `R^1b_*` at the locally
small model and the predicate is pinned at the standard one. -/
theorem isZeroFirstDirectImageBlowUp_of_iso (w : W) (hw : IsClosed ({w} : Set W))
    {F F' : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules}
    (hF : IsZeroFirstDirectImageBlowUp w hw F) (e : F' ≅ F) :
    IsZeroFirstDirectImageBlowUp w hw F' :=
  hF.of_iso (((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightDerivedPlus 1).mapIso e)

/-- **A quasi-coherent module with vanishing `R^1b_*` is right acyclic for `b_*`**, for the
blowing up `b : W' ⟶ W` of an integral Noetherian scheme of dimension two in a closed point.

For a left exact functor right acyclicity is the vanishing of all the higher right derived
functors (part (2) of [Stacks, Tag 015C]), and `b_*` is left exact, being a right adjoint. Above
degree one the vanishing is
`AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt`,
which needs nothing but the dimension of `W`; so only degree one is a hypothesis. -/
theorem rightAcyclic_pushforward_blowUpToBase_vanishingIdeal_singleton
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules)
    [F.IsQuasicoherent]
    (h1 : IsZeroFirstDirectImageBlowUp w hw F) :
    (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).rightAcyclic F := by
  refine ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus _ F).2 inferInstance).2 ?_
  intro i hi
  by_cases hone : i = 1
  · subst hone
    exact h1
  · exact isZero_rightDerivedPlus_pushforward_blowUp_vanishingIdeal_singleton_of_one_lt
      hdim w hw F i (by omega)

/-- **`Rb_*(ℱ[0]) ≅ (b_*ℱ)[0]` in `D(𝒪_W)`** for the blowing up `b : W' ⟶ W` of an integral
Noetherian scheme of dimension two in a closed point and a quasi-coherent `ℱ` with
`R^1b_*ℱ = 0`.

The canonical comparison `(b_*ℱ)[0] ⟶ Rb_*(ℱ[0])` is
`Stacks.DeRham.pushforwardSingleToDerived`, invertible at a quasi-coherent right acyclic module
by `Stacks.DeRham.TwistDerived.isIso_pushforwardSingleToDerived`, which is [Stacks, Tag 0G9N] at
the complex `ℱ[0]`; the acyclicity is
`Stacks.BlowupTwistUnit.rightAcyclic_pushforward_blowUpToBase_vanishingIdeal_singleton`. -/
def standardDerivedPushforwardSingleIso
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules)
    [F.IsQuasicoherent]
    (h1 : IsZeroFirstDirectImageBlowUp w hw F) :
    (derivedPushforward (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj
        ((DerivedCategory.singleFunctor
          (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds W))).Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj
        ((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj F) :=
  haveI := Stacks.DeRham.TwistDerived.isIso_pushforwardSingleToDerived
    (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) F
    (rightAcyclic_pushforward_blowUpToBase_vanishingIdeal_singleton hdim w hw F h1)
  (asIso (Stacks.DeRham.pushforwardSingleToDerived
    (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) F)).symm

/-- **`Rb_*(ℱ[0]) ≅ 𝒢[0]` in `D(𝒪_W)`** for a module `𝒢` on the base identified with `b_*ℱ`:
`Stacks.BlowupTwistUnit.standardDerivedPushforwardSingleIso` followed by the degree-zero
embedding of the given identification.

The composition is performed here, inside the section that installs the standard model, because
the degree-zero embedding itself is model-dependent: outside the section the single functor on
`W` is the locally small one and the two do not compose. -/
def standardDerivedPushforwardSingleIsoOfIso
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules)
    [F.IsQuasicoherent]
    (h1 : IsZeroFirstDirectImageBlowUp w hw F) (G : W.Modules)
    (e : (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj F ≅ G) :
    (derivedPushforward (AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj
        ((DerivedCategory.singleFunctor
          (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{w}, hw⟩ : Closeds W))).Modules 0).obj F) ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj G :=
  standardDerivedPushforwardSingleIso hdim w hw F h1 ≪≫
    (DerivedCategory.singleFunctor W.Modules 0).mapIso e

end Standard

/-! ### The isomorphism in `D_QCoh` at the locally small model -/

variable {W : Scheme.{u}} [AlgebraicGeometry.IsIntegral W] [IsNoetherian W]

/-- **`Rb_*(ℱ[0]) ≅ (b_*ℱ)[0]` in `D_QCoh(𝒪_W)`** at the locally small model, for the blowing up
`b : W' ⟶ W` of an integral Noetherian scheme of dimension two in a closed point and a
quasi-coherent `ℱ` with `R^1b_*ℱ = 0`.

This is `Stacks.BlowupTwistUnit.standardDerivedPushforwardSingleIso` carried across the two
models and the two spellings of `Rf_*` by
`Stacks.Duality.StandardModel.isoSingleQuasiCoherentOfStandardIso`. It is the shape the field
`Stacks.BlowupTwistUnit.NormalizedTopFormData.pushforwardIso` asks for. -/
def quasiCoherentDerivedPushforwardSingleIso [CompactSpace W]
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (F : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).Modules)
    (hF : F.IsQuasicoherent)
    (h1 : IsZeroFirstDirectImageBlowUp w hw F)
    (G : W.Modules) (hG : G.IsQuasicoherent)
    (e : (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))).obj F ≅ G) :
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs
        (AlgebraicGeometry.blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
          (⟨{w}, hw⟩ : Closeds W))))).obj (singleQuasiCoherent F hF 0) ≅
      singleQuasiCoherent G hG 0 :=
  haveI := hF
  StandardModel.isoSingleQuasiCoherentOfStandardIso
    (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))) _ F hF G hG 0
    (standardDerivedPushforwardSingleIsoOfIso hdim w hw F h1 G e)

end Stacks.BlowupTwistUnit

end
