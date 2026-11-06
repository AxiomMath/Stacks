module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDifferentialsTriangle
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftPairActionSection

/-!
# The difference of two lifts is characterised by its transpose on universal differentials

Let `G ⊂ X'` be a thickening of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, let `q : Y' ⟶ Bb` be a morphism and let `b' : X' ⟶ Y'` be a morphism.
`AlgebraicGeometry.Space.definingIdealHomOfDerivation` attaches to a `Bb`-derivation `D` of
`(b')^{-1}𝒪_{Y'}` with values in the defining ideal of the thickening the morphism of
`𝒪_{X'}`-modules

`(b')^*Ω_{Y'/Bb} ⟶ 𝓘`,

and `AlgebraicGeometry.Space.liftPairActionSection` and
`AlgebraicGeometry.Space.liftPairGlobalSection` — the difference of two lifts of
[Stacks Project, Tag 0618] — are that morphism at the derivation which is the difference of the
two structure maps.

**This file gives that morphism its value lemma.**  It is built as the inverse of a composite of
three bijections, and the recorded obstruction to using it is that a bijection assembled from
universal properties cannot describe its own values.  The way round is not to compute the
inverse but to read the *forward* composite off it: a morphism out of `(b')^*Ω_{Y'/Bb}`,
transposed along the adjunction `(b')^* ⊣ (b')_*` of [Stacks Project, Tag 03LU], is a morphism
out of `Ω_{Y'/Bb}`, and such a morphism is determined by its effect on the universal
differentials `d_{Y'/Bb}(t)` of the local sections of `𝒪_{Y'}` — which is exactly the
uniqueness half of [Stacks Project, Tag 04CT],
`AlgebraicGeometry.Space.sheafOfDifferentials_hom_ext`.

## Main results

* `AlgebraicGeometry.Space.etaleSourceAdjEquiv_definingIdealHomOfDerivation`: the transpose of
  the morphism attached to `D` is the morphism `Ω_{Y'/Bb} ⟶ (b')_*𝓘` that the universal property
  of [Stacks Project, Tag 04CT] attaches to the transposed derivation.
* `AlgebraicGeometry.Space.definingIdealHomOfDerivation_transpose_app_d`: **the value lemma** —
  that transpose carries the universal differential `d_{Y'/Bb}(t)` of a local section `t` of
  `𝒪_{Y'}` to the value at `t` of the transposed derivation.
* `AlgebraicGeometry.Space.eq_definingIdealHomOfDerivation_of_transpose_app_d`: **the
  characterisation** — a morphism `(b')^*Ω_{Y'/Bb} ⟶ 𝓘` whose transpose does that *is* the
  morphism attached to `D`.  So the morphism is pinned by a statement about local sections of
  `𝒪_{Y'}`, with no bijection left to invert.
* `AlgebraicGeometry.Space.liftPairActionSectionOfDerivation_eq_of_transpose_app_d` and
  `AlgebraicGeometry.Space.liftPairGlobalSectionOfDerivation_eq_of_transpose_app_d`: the same
  characterisation carried to the two shapes the lifting problem consumes — the morphism
  `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}` and the global section of the acting sheaf of [Stacks Project,
  Tag 061D].

## Implementation notes

**Why the forward direction is free and the inverse is not.**
`AlgebraicGeometry.Space.definingIdealHomOfDerivation` is
`(etaleSourceAdjEquiv).symm ((differentialsHomEquiv).symm ((etaleSourceTransposeEquiv).symm D))`.
Applying `AlgebraicGeometry.Space.etaleSourceAdjEquiv` to it is `Equiv.apply_symm_apply`, and
`AlgebraicGeometry.Space.differentialsHomEquiv_symm_app_d` then reads the resulting morphism on
universal differentials in one step.  Neither move inspects the inverse of anything: the two
`Equiv.symm`s are cancelled rather than computed, which is why all five declarations here check
in under a second where a direct computation of the values of the composite does not.

**What this does not do.**  The value lemma is stated at the local sections of `𝒪_{Y'}`, on the
small étale site of `Y'`.  Reading it at an étale *scheme* chart of `Y'` — which is what the
chart-level acting group
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftingSheafAction` is indexed by — needs in
addition the compatibility of the source comparison
`AlgebraicGeometry.Space.ChartLiftPresentation.chartSourceIso` with the two universal
differentials, and that is a separate statement about [Stacks Project, Tag 04CU] and
[Stacks Project, Tag 04CS] which is not proved anywhere.  So this file is one half of what
`AlgebraicGeometry.Space.IsLiftDifferenceOfTranslate` needs and not the whole of it; see the
module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftChartDifferenceFamily`.

**A correction.**  That module documentation says a value lemma is owed for *both* halves of the
composite, naming `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv` as the
second.  The second is already proved, as
`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv_apply`
(`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSectionValue`); only the
half proved here was missing, and what remains after both is the compatibility of
`chartSourceIso` just described, which is a statement about neither bijection.

No `@[stacks]` attribute is claimed.  [Stacks Project, Tag 0618] is registered where the
derivation and the morphism are built, and the uniqueness half of [Stacks Project, Tag 04CT] at
`AlgebraicGeometry.Space.sheafOfDifferentials_hom_ext`; a characterisation of an existing
construction asserts no tag.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
* [Stacks Project, Tag 08TQ](https://stacks.math.columbia.edu/tag/08TQ)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X' Y' Bb : AlgebraicSpaces B S hS} {G : Subfunctor X'.1}
  (hG : IsThickening B S hS X' G) (b' : X' ⟶ Y') (q : Y' ⟶ Bb)

/-! ### The transpose of the morphism attached to a derivation -/

/-- **The transpose of the morphism attached to a derivation.**  Transposing
`AlgebraicGeometry.Space.definingIdealHomOfDerivation` along the adjunction
`(b')^* ⊣ (b')_*` of [Stacks Project, Tag 03LU] returns the morphism
`Ω_{Y'/Bb} ⟶ (b')_*𝓘` which the universal property of [Stacks Project, Tag 04CT] attaches to the
transpose of `D` along [Stacks Project, Tag 08TQ].

This is `Equiv.apply_symm_apply`: the outermost of the three bijections composed in the
definition is cancelled rather than computed. -/
theorem etaleSourceAdjEquiv_definingIdealHomOfDerivation
    (D : PresheafOfModulesOfCommRing.Derivation' (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')) (liftPairBaseMap B S hS b' q).hom) :
    etaleSourceAdjEquiv B S hS b' q (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules
        (definingIdealHomOfDerivation B S hS hG b' q D) =
      (differentialsHomEquiv B S hS q
          ((etaleSourcePushforward B S hS b').obj
            (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules)).symm
        ((etaleSourceTransposeEquiv B S hS b' q
          (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm D) :=
  Equiv.apply_symm_apply _ _

/-- **The value lemma for the difference morphism of [Stacks Project, Tag 0618].**  The
transpose of the morphism attached to `D` carries the universal differential `d_{Y'/Bb}(t)` of a
local section `t` of `𝒪_{Y'}` to the value at `t` of the transpose of `D`.

This is the characterising equation of the universal property of [Stacks Project, Tag 04CT],
`AlgebraicGeometry.Space.differentialsHomEquiv_symm_app_d`, read at the transposed derivation. -/
theorem definingIdealHomOfDerivation_transpose_app_d
    (D : PresheafOfModulesOfCommRing.Derivation' (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')) (liftPairBaseMap B S hS b' q).hom)
    (W : (SmallEtale B S hS Y'.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y').obj.obj W) :
    (((etaleSourceAdjEquiv B S hS b' q
            (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules
            (definingIdealHomOfDerivation B S hS hG b' q D)).val).app W).hom
        ((universalDerivation B S hS q).d t) =
      ((etaleSourceTransposeEquiv B S hS b' q
        (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm D).d t :=
  (congrArg (fun m => ((m.val).app W).hom ((universalDerivation B S hS q).d t))
      (etaleSourceAdjEquiv_definingIdealHomOfDerivation B S hS hG b' q D)).trans
    (differentialsHomEquiv_symm_app_d B S hS q _ _ W t)

/-! ### The characterisation -/

/-- **The difference morphism of [Stacks Project, Tag 0618] is characterised by its transpose on
universal differentials.**  A morphism `ψ : (b')^*Ω_{Y'/Bb} ⟶ 𝓘` whose transpose carries
`d_{Y'/Bb}(t)` to the value at `t` of the transpose of `D`, for every local section `t` of
`𝒪_{Y'}`, is `AlgebraicGeometry.Space.definingIdealHomOfDerivation` at `D`.

So the morphism is pinned by a statement about local sections, and no consumer has to invert the
composite of three bijections it is defined by.  The proof is the uniqueness half of
[Stacks Project, Tag 04CT], `AlgebraicGeometry.Space.sheafOfDifferentials_hom_ext`, applied to
the two transposes, followed by injectivity of the transposition. -/
theorem eq_definingIdealHomOfDerivation_of_transpose_app_d
    (D : PresheafOfModulesOfCommRing.Derivation' (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')) (liftPairBaseMap B S hS b' q).hom)
    (ψ : (modulePullback B S hS b').obj (sheafOfDifferentials B S hS q) ⟶
      (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules)
    (h : ∀ (W : (SmallEtale B S hS Y'.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y').obj.obj W),
      (((etaleSourceAdjEquiv B S hS b' q
            (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules ψ).val).app W).hom
          ((universalDerivation B S hS q).d t) =
        ((etaleSourceTransposeEquiv B S hS b' q
          (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm D).d t) :
    ψ = definingIdealHomOfDerivation B S hS hG b' q D :=
  (etaleSourceAdjEquiv B S hS b' q
      (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).injective
    (sheafOfDifferentials_hom_ext B S hS q fun W t =>
      (h W t).trans
        (definingIdealHomOfDerivation_transpose_app_d B S hS hG b' q D W t).symm)

/-! ### The two shapes the lifting problem consumes -/

/-- **The characterisation at the shape of a section of the acting sheaf of [Stacks Project,
Tag 061D]**: the morphism `a^*Ω_{Y'/Bb} ⟶ 𝒞_{X/X'}` attached to `D` is computed from any
morphism `ψ` satisfying the characterising equation, by the composition comparison of
[Stacks Project, Tag 03LU] and the inverse image along the inclusion of the thickening. -/
theorem liftPairActionSectionOfDerivation_eq_of_transpose_app_d
    (D : PresheafOfModulesOfCommRing.Derivation' (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')) (liftPairBaseMap B S hS b' q).hom)
    (ψ : (modulePullback B S hS b').obj (sheafOfDifferentials B S hS q) ⟶
      (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules)
    (h : ∀ (W : (SmallEtale B S hS Y'.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y').obj.obj W),
      (((etaleSourceAdjEquiv B S hS b' q
            (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules ψ).val).app W).hom
          ((universalDerivation B S hS q).d t) =
        ((etaleSourceTransposeEquiv B S hS b' q
          (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm D).d t) :
    liftPairActionSectionOfDerivation B S hS hG b' q D =
      (modulePullbackCompIso B S hS (IsThickening.inclusion B S hS hG) b').inv.app
          (sheafOfDifferentials B S hS q) ≫
        (modulePullback B S hS (IsThickening.inclusion B S hS hG)).map ψ :=
  congrArg
    (fun k => (modulePullbackCompIso B S hS (IsThickening.inclusion B S hS hG) b').inv.app
        (sheafOfDifferentials B S hS q) ≫
      (modulePullback B S hS (IsThickening.inclusion B S hS hG)).map k)
    (eq_definingIdealHomOfDerivation_of_transpose_app_d B S hS hG b' q D ψ h).symm

/-- **The characterisation at the shape of a global section of the acting sheaf of
[Stacks Project, Tag 061D]**, which is where
`AlgebraicGeometry.Space.liftPairGlobalSection` and hence
`AlgebraicGeometry.Space.chartLiftPairGlobalSection` live. -/
theorem liftPairGlobalSectionOfDerivation_eq_of_transpose_app_d
    (D : PresheafOfModulesOfCommRing.Derivation' (liftDifferenceCoefficients B S hS ⟨G, hG.1⟩
      (liftPairSecondSharp B S hS b')) (liftPairBaseMap B S hS b' q).hom)
    (ψ : (modulePullback B S hS b').obj (sheafOfDifferentials B S hS q) ⟶
      (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules)
    (h : ∀ (W : (SmallEtale B S hS Y'.1)ᵒᵖ) (t : (structureRingSheaf B S hS Y').obj.obj W),
      (((etaleSourceAdjEquiv B S hS b' q
            (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules ψ).val).app W).hom
          ((universalDerivation B S hS q).d t) =
        ((etaleSourceTransposeEquiv B S hS b' q
          (definingIdealSheaf B S hS X' ⟨G, hG.1⟩).toSheafOfModules).symm D).d t) :
    liftPairGlobalSectionOfDerivation B S hS hG b' q D =
      (smallEtaleInternalHomSectionsEquiv B S hS G.toFunctor hG.1.1
          ((modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ b')).obj
            (sheafOfDifferentials B S hS q))
          (conormalModule B S hS X' ⟨G, hG.1⟩)).symm
        ((modulePullbackCompIso B S hS (IsThickening.inclusion B S hS hG) b').inv.app
            (sheafOfDifferentials B S hS q) ≫
          (modulePullback B S hS (IsThickening.inclusion B S hS hG)).map ψ) :=
  congrArg
    (smallEtaleInternalHomSectionsEquiv B S hS G.toFunctor hG.1.1
      ((modulePullback B S hS (IsThickening.inclusion B S hS hG ≫ b')).obj
        (sheafOfDifferentials B S hS q))
      (conormalModule B S hS X' ⟨G, hG.1⟩)).symm
    (liftPairActionSectionOfDerivation_eq_of_transpose_app_d B S hS hG b' q D ψ h)

end AlgebraicGeometry.Space

end
