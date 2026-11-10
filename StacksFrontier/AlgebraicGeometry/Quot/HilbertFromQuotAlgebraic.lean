module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertQuotFunctorEquality
public import StacksFrontier.AlgebraicGeometry.Quot.IsomorphismLocusInRelativeMorphisms
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorModelSmall
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeMorphismAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian

/-!
# Stacks 0D01, 0D1C, 0DPP and 0DPE from the algebraicity of `Quot_{𝒪_X/X/B}`

Each of the four tags is, in the source, a short deduction from Stacks 09TU for the structure
sheaf: the Hilbert functor is `Quot_{𝒪_X/X/B}` (Stacks 0D00), the relative morphism functor is an
open subspace of a Hilbert functor (Stacks 0D1A, 0D1B), the isomorphism locus is open in it
(Stacks 05XD), and the image of an open immersion is open in a Hilbert functor. This file carries
out those deductions with the *first* clause of Stacks 09TU for `𝒪_X` as the only input: every
model of `Quot_{𝒪_X/X/B}` of a separated morphism of finite presentation is an algebraic space.
The second clause of Stacks 09TU — local finite presentation of `Quot_{𝒪_X/X/B} ⟶ B` — is derived
from the first by
`AlgebraicGeometry.Space.QuotSitePresheafModel.isLocallyOfFinitePresentation_toBase`, because
`𝒪_X` is of finite presentation.

## Main results

* `AlgebraicGeometry.Space.exists_hilbertPresheafModel_of_quotAlgebraic`: Stacks 0D01 from the
  algebraicity of `Quot_{𝒪_X/X/B}`.
* `AlgebraicGeometry.Space.hasHilbertModelsOver_of_quotAlgebraic`: the hypothesis of the proof of
  Stacks 0D1C, from the same input over the base.
* `AlgebraicGeometry.Space.isAlgebraicSpace_relativeHom_of_quotAlgebraic` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_relativeHomProjection_of_quotAlgebraic`:
  Stacks 0D1C.
* `AlgebraicGeometry.Space.isOpenSubspace_isomSubfunctor_of_quotAlgebraic`: Stacks 0DPP.
* `AlgebraicGeometry.Space.exists_hilbertModels_isOpenImmersion_of_quotAlgebraic`: Stacks 0DPE.

## References

* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 0D1C](https://stacks.math.columbia.edu/tag/0D1C)
* [Stacks Project, Tag 0DPP](https://stacks.math.columbia.edu/tag/0DPP)
* [Stacks Project, Tag 0DPE](https://stacks.math.columbia.edu/tag/0DPE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The structure sheaf of an algebraic space is of finite presentation. -/
theorem isFinitePresentationOnSite_structureSheafModule (X : AlgebraicSpaces B S hS) :
    (structureSheafModule B S hS X).IsFinitePresentationOnSite :=
  SheafOfModules.isFinitePresentationOnSite_unit

/-- **Stacks 0D01 from the algebraicity of `Quot_{𝒪_X/X/B}`.** For `f : X ⟶ Y` of finite
presentation and separated, if the models of `Quot_{𝒪_X/X/Y}` are algebraic spaces (the first
clause of Stacks 09TU for `𝒪_X`), then the Hilbert functor `Hilb_{X/Y}` has a model which is an
algebraic space locally of finite presentation over `Y`.

A model of the Quot presheaf exists
(`AlgebraicGeometry.Space.QuotSituation.exists_quotSitePresheafModel`), its morphism to `Y` is
locally of finite presentation by the second clause of Stacks 09TU, and
`Hilb_{X/Y} = Quot_{𝒪_X/X/Y}` over `Y` by Stacks 0D00. -/
theorem exists_hilbertPresheafModel_of_quotAlgebraic {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfp : IsFinitePresentation B S hS f.hom) (hsep : IsSeparated B S hS f.hom)
    (hquot : ∀ N : QuotSitePresheafModel (structureSheafQuotSituation f hfp),
      IsAlgebraicSpace B S hS N.presheaf) :
    ∃ M : HilbertPresheafModel f,
      IsAlgebraicSpace B S hS M.presheaf ∧ IsLocallyOfFinitePresentation B S hS M.toBase := by
  obtain ⟨N, -, -⟩ := (structureSheafQuotSituation f hfp).exists_quotSitePresheafModel
  obtain ⟨e, he⟩ := exists_hilbertPresheafIso_quotSitePresheaf f hfp
  exact exists_hilbertPresheafModel_isAlgebraicSpace (structureSheafQuotSituation f hfp) f hfp
    hsep N (hquot N)
    (N.isLocallyOfFinitePresentation_toBase (hquot N)
      (isFinitePresentationOnSite_structureSheafModule X)) e he

/-- **The hypothesis of the proof of Stacks 0D1C, from the algebraicity of `Quot_{𝒪_W/W/Q}`**
for every separated morphism of finite presentation `W ⟶ Q`. -/
theorem hasHilbertModelsOver_of_quotAlgebraic {Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : IsAlgebraicSpace B S hS Q)
    (hquot : ∀ (W : AlgebraicSpaces B S hS) (f : W ⟶ (⟨Q, hQ⟩ : AlgebraicSpaces B S hS))
      (hfp : IsFinitePresentation B S hS f.hom), IsSeparated B S hS f.hom →
        ∀ N : QuotSitePresheafModel (structureSheafQuotSituation f hfp),
          IsAlgebraicSpace B S hS N.presheaf) :
    HasHilbertModelsOver hQ :=
  fun W f hfp hsep => exists_hilbertPresheafModel_of_quotAlgebraic f hfp hsep (hquot W f hfp hsep)

section RelativeHom

variable {Z X Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (z : Z ⟶ Q) (x : X ⟶ Q)
    (hZ : IsAlgebraicSpace B S hS Z) (hX : IsAlgebraicSpace B S hS X)
    (hQ : IsAlgebraicSpace B S hS Q)

/-- **Stacks 0D1C, algebraicity, from the algebraicity of the Quot functors of structure sheaves
over `Q`.** -/
theorem isAlgebraicSpace_relativeHom_of_quotAlgebraic (hx_fp : IsFinitePresentation B S hS x)
    (hx_sep : IsSeparated B S hS x) (hz_fp : IsFinitePresentation B S hS z)
    (hz_flat : IsFlat B S hS z) (hz_proper : IsProper B S hS z) :
    IsAlgebraicSpace B S hS (relativeHom B S hS Z X Q z x hZ hX hQ) :=
  isAlgebraicSpace_relativeHom z x hZ hX hQ hx_fp hx_sep hz_fp hz_flat hz_proper

/-- **Stacks 0D1C, local finite presentation over the base, from the algebraicity of the Quot
functors of structure sheaves over `Q`.** -/
theorem isLocallyOfFinitePresentation_relativeHomProjection_of_quotAlgebraic
    (hx_fp : IsFinitePresentation B S hS x) (hx_sep : IsSeparated B S hS x)
    (hz_fp : IsFinitePresentation B S hS z) (hz_flat : IsFlat B S hS z)
    (hz_proper : IsProper B S hS z) :
    IsLocallyOfFinitePresentation B S hS
      (relativeHomProjection B S hS Z X Q z x hZ hX hQ) :=
  isLocallyOfFinitePresentation_relativeHomProjection z x hZ hX hQ hx_fp hx_sep hz_fp hz_flat
    hz_proper

/-- **Stacks 0DPP from the algebraicity of the Quot functors of structure sheaves over `Q`.**
With `Z ⟶ Q` of finite presentation, flat and proper and `X ⟶ Q` of finite presentation and
proper, the subfunctor `Isom_Q(Z, X) ⊆ Mor_Q(Z, X)` of isomorphisms is an open subspace. -/
theorem isOpenSubspace_isomSubfunctor_of_quotAlgebraic (hx_fp : IsFinitePresentation B S hS x)
    (hx_proper : IsProper B S hS x) (hz_fp : IsFinitePresentation B S hS z)
    (hz_flat : IsFlat B S hS z) (hz_proper : IsProper B S hS z) :
    IsOpenSubspace B S hS (isomSubfunctor B S hS Z X Q z x hZ hX hQ) :=
  isOpenSubspace_isomSubfunctor B S hS Z X Q z x hZ hX hQ hz_fp hz_flat hz_proper hx_proper
    (isAlgebraicSpace_relativeHom_of_quotAlgebraic z x hZ hX hQ hx_fp hx_proper.1 hz_fp hz_flat
      hz_proper)

end RelativeHom

/-- **Stacks 0DPE from the algebraicity of `Quot_{𝒪_X/X/A}` and `Quot_{𝒪_Y/Y/A}`.** Let
`π : X ⟶ Y` be an open immersion of algebraic spaces separated and of finite presentation over
`A`. Then the Hilbert functors of `X` and `Y` over `A` have models which are algebraic spaces,
and `π` induces an open immersion between them. -/
theorem exists_hilbertModels_isOpenImmersion_of_quotAlgebraic {X Y A : AlgebraicSpaces B S hS}
    {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A} (hπ : π ≫ bY = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (hXfp : IsFinitePresentation B S hS bX.hom)
    (hXsep : IsSeparated B S hS bX.hom) (hYfp : IsFinitePresentation B S hS bY.hom)
    (hYsep : IsSeparated B S hS bY.hom)
    (hquotX : ∀ N : QuotSitePresheafModel (structureSheafQuotSituation bX hXfp),
      IsAlgebraicSpace B S hS N.presheaf)
    (hquotY : ∀ N : QuotSitePresheafModel (structureSheafQuotSituation bY hYfp),
      IsAlgebraicSpace B S hS N.presheaf) :
    ∃ (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY),
      IsAlgebraicSpace B S hS MX.presheaf ∧ IsAlgebraicSpace B S hS MY.presheaf ∧
        IsOpenImmersion B S hS (hilbertModelMap hπ hopen hYsep MX MY) := by
  obtain ⟨MX, hMX, -⟩ := exists_hilbertPresheafModel_of_quotAlgebraic bX hXfp hXsep hquotX
  obtain ⟨MY, hMY, -⟩ := exists_hilbertPresheafModel_of_quotAlgebraic bY hYfp hYsep hquotY
  exact ⟨MX, MY, hMX, hMY, isOpenImmersion_hilbertModelMap hπ hopen hYsep MX MY⟩

end AlgebraicGeometry.Space

end
