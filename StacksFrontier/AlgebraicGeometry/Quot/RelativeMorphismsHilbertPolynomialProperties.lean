/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismsHilbertPolynomial
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismSeparatedFinitePresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerFiniteProjectiveModel
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# `Mor^{P, ℳ}_Q(Z, X) ⟶ Q` is separated and locally of finite presentation

Let `z : Z ⟶ Q` be flat, proper and of finite presentation, `x : X ⟶ Q` separated and of finite
presentation, `ℳ` an invertible module on `Z ×_Q X` and `P : ℤ → ℤ`.  This file proves the open
and closed immersion of Stacks 0DPQ, and from it the two parts of Stacks 0DPR which follow from
Stacks 0DPN, as in the first sentence of the proof of Stacks 0DPR:

* `Mor^{P, ℳ}_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion (Stacks 0DPQ, the case
  `I = ℤ`, `E_i = ℳ^{⊗ i}`): the base change along the graph of the open and closed substack
  `Coh^{P, ℳ} ⊆ Coh_{Z ×_Q X / Q}` of Stacks 0DNF, whose twisted Euler characteristics are locally
  constant by the finite projective models of Stacks 0A1Q;
* `Mor^{P, ℳ}_Q(Z, X) ⟶ Q` is separated, being a monomorphism followed by the separated
  `Mor_Q(Z, X) ⟶ Q` (Stacks 0DPM), hence quasi-separated;
* `Mor^{P, ℳ}_Q(Z, X) ⟶ Q` is locally of finite presentation, being an open immersion followed by
  the locally finitely presented `Mor_Q(Z, X) ⟶ Q` (Stacks 0DPN): an étale chart of
  `Mor^{P, ℳ}_Q(Z, X)` is one of `Mor_Q(Z, X)`.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_and_isClosedImmersion_relativeHomHilbertPolynomial_ι`.
* `AlgebraicGeometry.Space.isSeparated_relativeHomHilbertPolynomial_comp`.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_relativeHomHilbertPolynomial_comp`.

## References

* [Stacks Project, Tag 0DPR](https://stacks.math.columbia.edu/tag/0DPR)
* [Stacks Project, Tag 0DPQ](https://stacks.math.columbia.edu/tag/0DPQ)
* [Stacks Project, Tag 0DPN](https://stacks.math.columbia.edu/tag/0DPN)
* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

section Charts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A property holding on every étale chart of `p` holds on every étale chart of `ι ≫ p` for an
étale `ι`**: an étale chart of the source of `ι` composed with `ι` is an étale chart of the source
of `p`. -/
theorem holdsOnEveryEtaleChart_comp_of_presheaf_etale (P : MorphismProperty Scheme.{u})
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (ι : F ⟶ G)
    (hι : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ι) (p : G ⟶ H)
    (hp : HoldsOnEveryEtaleChart B S hS P p) : HoldsOnEveryEtaleChart B S hS P (ι ≫ p) := by
  intro U V a b h ha hb hsq
  refine hp U V (a ≫ ι) b h (MorphismProperty.comp_mem _ _ _ ha hι) hb ?_
  rw [hsq, Category.assoc]

end Charts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q} {x : X ⟶ Q}
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)
    (hsep : IsSeparated B S hS x) (hxfp : IsFinitePresentation B S hS x)
    (hfp : IsFinitePresentation B S hS z) (hflat : IsFlat B S hS z)
    (hproper : IsProper B S hS z)
    (M : Modules.{u, u} B S hS (graphAmbient B S hS z x hZ hX hQ).1
      (graphAmbient B S hS z x hZ hX hQ).2)
    [hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS (graphAmbient B S hS z x hZ hX hQ).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        (graphAmbient B S hS z x hZ hX hQ).1 (graphAmbient B S hS z x hZ hX hQ).2).O)).property M]
    (P : ℤ → ℤ)

/-- **`Mor^{P, ℳ}_Q(Z, X) ⟶ Mor_Q(Z, X)` is an open and closed immersion** (Stacks 0DPQ, the case
`I = ℤ`, `E_i = ℳ^{⊗ i}`): it is the base change along the graph of
`Coh^{P, ℳ}_{Z ×_Q X / Q} ⊆ Coh_{Z ×_Q X / Q}`, cut out by open and closed subsets of the test
schemes (Stacks 0DNF). -/
theorem isOpenImmersion_and_isClosedImmersion_relativeHomHilbertPolynomial_ι :
    IsOpenImmersion B S hS
        (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).ι ∧
      IsClosedImmersion B S hS
        (relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).ι :=
  isOpenImmersion_and_isClosedImmersion_graphPreimage_hilbertCondition_ι B S hS Z X Q z x hZ hX
    hQ hsep hfp hflat hproper hxfp
    (fun m h => @CoherentObject.hasHilbertPolynomial_of_coherentHom B S hS _ M hM P _ _ m h)
    (CoherentSituation.isOpenAndClosedCondition_hasHilbertPolynomial
      (D := (structureSheafQuotSituation (graphAmbientMap B S hS z x hZ hX hQ)
        (isFinitePresentation_graphAmbientMap z x hZ hX hQ hfp hxfp)).toCoherentSituation) M
        (hL := hM) P).isCutOutOnTestSchemes

/-- **`Mor^{P, ℳ}_Q(Z, X) ⟶ Q` is separated**: the inclusion into `Mor_Q(Z, X)` is a monomorphism,
and `Mor_Q(Z, X) ⟶ Q` is separated by Stacks 0DPM. -/
theorem isSeparated_relativeHomHilbertPolynomial_comp :
    IsSeparated B S hS ((relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).ι ≫
      relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  isSeparated_comp B S hS _ _
    (AlgebraicGeometry.Space.isSeparated_of_mono (B := B) (S := S) (hS := hS) _ inferInstance)
    (isSeparated_relativeHomProjection hZ hX hQ hsep hxfp hfp hflat hproper)

/-- **`Mor^{P, ℳ}_Q(Z, X) ⟶ Q` is locally of finite presentation**: it is an open immersion
followed by `Mor_Q(Z, X) ⟶ Q`, which is locally of finite presentation by Stacks 0DPN. -/
theorem isLocallyOfFinitePresentation_relativeHomHilbertPolynomial_comp :
    IsLocallyOfFinitePresentation B S hS
      ((relativeHomHilbertPolynomial hZ hX hQ hsep hxfp hfp hflat hproper M P).ι ≫
        relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  holdsOnEveryEtaleChart_comp_of_presheaf_etale _ _
    (presheaf_etale_of_isOpenImmersion B S hS
      (isOpenImmersion_and_isClosedImmersion_relativeHomHilbertPolynomial_ι hZ hX hQ hsep hxfp hfp
        hflat hproper M P).1) _
    (isSeparated_and_isLocallyOfFinitePresentation_relativeHomProjection_unconditional hZ hX hQ
      hsep hxfp hfp hflat hproper).2

end AlgebraicGeometry.Space

end
