module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfFiniteLocallyFreeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFppfLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.QuotientStackSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphism
import StacksFrontier.AlgebraicGeometry.Stacks.AffineMorphismStability
import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalSchemePoint
import StacksFrontier.AlgebraicGeometry.Stacks.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FppfDescentIngredients
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFieldValuedPoint
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented
import StacksFrontier.AlgebraicGeometry.Stacks.SchemePointBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE
import StacksFrontier.AlgebraicGeometry.Stacks.SeparationBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine
import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap

/-!
# Well-nigh affine stacks and affine finite locally free groupoids (Stacks 0DUM)

An algebraic stack `𝒳` over a scheme `S` of a big fppf site is well-nigh affine (Stacks 0DUL)
exactly when it is the quotient stack `[U/R]` of a groupoid scheme `(U, R, s, t, c)` with `U` and
`R` affine and `s, t : R ⟶ U` finite locally free; and then `𝒳` is quasi-compact, quasi-DM and
separated. This file carries the quasi-compactness assertion outright and the quasi-DM and
separatedness assertions from the presentation of condition (2).

## Main definitions

* `AlgebraicGeometry.Stack.representedGroupoid`: the groupoid in algebraic spaces over `S`
  presented by a groupoid scheme whose object and arrow schemes are objects of the site.
* `AlgebraicGeometry.Stack.HasAffineFiniteLocallyFreeGroupoidPresentation`: condition (2) of
  **Stacks 0DUM**.

## Main results

* `AlgebraicGeometry.Stack.isQuasiCompactStack_of_isWellNighAffine`: **Stacks 0DUM**, the
  quasi-compactness assertion.
* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_representedGroupoid_isFiniteLocallyFree`:
  **Stacks 0DUM**, the quasi-DM assertion, read off condition (2).
* `AlgebraicGeometry.Stack.isSeparatedOver_of_representedGroupoid_isFiniteLocallyFree` and
  `AlgebraicGeometry.Stack.isAbsolutelySeparated_of_representedGroupoid_isFiniteLocallyFree`:
  **Stacks 0DUM**, the separatedness assertion over the base scheme of the site and in the
  source's unqualified, absolute sense.
* `AlgebraicGeometry.Stack.isWellNighAffine_of_isAffineHom`: **Stacks 0DUN**, clause (2).
* `AlgebraicGeometry.Stack.isAffineSpace_of_isWellNighAffine`: **Stacks 0DUN**, clause (1).

## Implementation notes

Condition (2) is rendered with the library's quotient stack
`AlgebraicGeometry.Stack.quotientStack` (**Stacks 044Q**), which consumes a groupoid in
algebraic spaces (**Stacks 043W**). A groupoid scheme `(U, R, s, t, c)` whose object and arrow
schemes are objects of the site gives one through
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.ofComposable`: its object and arrow spaces are the
represented algebraic spaces of `U` and `R`, and its source and target are the Yoneda images of
`s` and `t`, which by full faithfulness of Yoneda is the same data. The composition is taken as a
morphism of presheaves of composable pairs rather than as a morphism of the scheme fibre product,
which asks no containment of that fibre product in the site and makes the three consequences
below apply to more presentations, not fewer. Finite local freeness is the library's
`Stacks.Morphisms.IsFiniteLocallyFree` (**Stacks 02KA**) of the underlying morphisms of schemes,
not a weakening of it.

Quasi-compactness needs nothing beyond the surjective 1-morphism from an affine scheme that
Stacks 0DUL provides.

Quasi-DM and separatedness are the three cancellations of **Stacks 0DTY**, parts (4) and (6),
applied to the presenting groupoid. What finite local freeness supplies is the four properties of
morphisms of algebraic spaces those parts test: flatness and local finite presentation of `s` and
`t` by **Stacks 02KB**, local quasi-finiteness because a finite morphism of schemes is locally
quasi-finite, and properness because a finite morphism of schemes is proper — each transported to
the represented morphism of algebraic spaces by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map_iff` and
`AlgebraicGeometry.Space.isProper_yoneda_map`. Separatedness of the object space over the base
scheme, which part (6) also asks for, is separatedness of a morphism out of an affine scheme.

Clause (2) of **Stacks 0DUN** is the source's own argument. An affine scheme `U` of the site
presenting `𝒳` is read as a scheme-valued point of `𝒳` through
`CategoryTheory.Over.iteratedSliceBackward`, which is an equivalence over the site, so the four
properties of the presentation transport to it; the base change `𝒳' ×_𝒳 U` is then represented
over `U` by an algebraic space whose structural morphism is affine, and affineness tested at the
affine object `U` against the identity section makes that structural morphism the projection of
an affine scheme `W` of the site. The apex of the base-change square is therefore equivalent over
the site to the algebraic stack of `W`, and the four properties of the presentation are inherited
by its projection to `𝒳'` — surjectivity by **Stacks 04ZU**, flatness by **Stacks 06PY**, and
finiteness and relative finite presentation by **Stacks 045C** in the longhand form of
`AlgebraicGeometry.Stack.relativeProperty_baseChange`, since no base-change stability or
target-locality instance for those two properties of morphisms of algebraic spaces is available.

Clause (1) reads the presentation as a morphism of algebraic spaces. Both the affine scheme `U`
and `𝒳` itself are represented by algebraic spaces, so Stacks 04SW turns the presenting
1-morphism into a morphism `h_U ⟶ F` of the representing presheaves. It is surjective by Stacks
04ZS; it is finite because over an affine object of the site a section of `F` names a
scheme-valued point of `𝒳` (Stacks 04SW again) whose base change Stacks 04SD identifies with the
fibre product of `h_U ⟶ F` along that section; it is flat by the equivalence of conditions (2)
and (3) of Stacks 06FM; and it is locally of finite presentation because local finite
presentation of morphisms of algebraic spaces is local on the target for the fppf topology, so
the relative condition of Stacks 03YK on the presentation may be read off the base changes along
scheme-valued points. Finite, flat and locally of finite presentation is finite locally free by
Stacks 0416, so the presentation is a surjective finite locally free chart of `F`, and the
spectrum of the ring of invariant functions of its kernel pair represents `F` by Stacks 03BM:
this is `AlgebraicGeometry.Space.isAffineSpace_of_isFiniteLocallyFree_affineChart`. The route is
the second one the source offers for clause (1), through Stacks 03BM rather than through
Stacks 07VS, and the groupoid of the kernel pair is formed here rather than taken from
condition (2) of Stacks 0DUM.

## References

* [Stacks Project, Tag 0DUL](https://stacks.math.columbia.edu/tag/0DUL)
* [Stacks Project, Tag 0DUM](https://stacks.math.columbia.edu/tag/0DUM)
* [Stacks Project, Tag 0DUN](https://stacks.math.columbia.edu/tag/0DUN)
* [Stacks Project, Tag 0CHQ](https://stacks.math.columbia.edu/tag/0CHQ)
* [Stacks Project, Tag 0DTY](https://stacks.math.columbia.edu/tag/0DTY)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 0416](https://stacks.math.columbia.edu/tag/0416)
* [Stacks Project, Tag 04YB](https://stacks.math.columbia.edu/tag/04YB)
* [Stacks Project, Tag 04SD](https://stacks.math.columbia.edu/tag/04SD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-compactness -/

/-- **Stacks 0DUM, the quasi-compactness assertion.** A well-nigh affine algebraic stack is
quasi-compact: the algebraic stack of the affine scheme that Stacks 0DUL provides is
quasi-compact, and it surjects onto `𝒳`. -/
@[stacks 0DUM "a well-nigh affine algebraic stack is quasi-compact"]
theorem isQuasiCompactStack_of_isWellNighAffine
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    IsQuasiCompactStack.{u, w} B S hS 𝒳.val 𝒳.property := by
  obtain ⟨U, hU, f, hsurj, -⟩ := h𝒳
  exact isQuasiCompactStack_of_isSurjective.{u, w} B S hS f
    (isQuasiCompactStack_schemeStack_of_isAffine.{u, w} B S hS U hU) hsurj

/-! ### The groupoid presented by a groupoid scheme of the site -/

/-- The groupoid in algebraic spaces over `S` presented by a groupoid scheme `(U, R, s, t, c)`
whose object and arrow schemes are objects of the big fppf site: its object and arrow spaces are
the represented algebraic spaces of `U` and `R`, and its source and target are the Yoneda images
of `s` and `t`. -/
noncomputable abbrev representedGroupoid {U R : BigFppfOver B S hS} (s t : R ⟶ U)
    (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
      (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
      ((yoneda.map t).app T) fun p => c.app T p)) :
    GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS) :=
  GroupoidInAlgebraicSpaces.ofComposable
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
    ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩
    (ObjectProperty.homMk (yoneda.map s)) (ObjectProperty.homMk (yoneda.map t)) c hG

/-- **Stacks 0DUM, condition (2).** An algebraic stack over `S` has an *affine finite locally
free groupoid presentation* when it is equivalent over the site to the quotient stack of a
groupoid scheme whose object and arrow schemes are affine objects of the site and whose source
and target are finite locally free. -/
@[stacks 0DUM "condition (2): a presentation by an affine groupoid scheme with finite locally \
free source and target"]
abbrev HasAffineFiniteLocallyFreeGroupoidPresentation
    (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (U R : BigFppfOver B S hS) (s t : R ⟶ U)
      (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
        (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
      (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
        ((yoneda.map t).app T) fun p => c.app T p)),
    IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) ∧
          Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t) ∧
            Nonempty (StacksRepresentableCFG.EquivalenceOver
              (quotientStack (representedGroupoid B S hS s t c hG)).p 𝒳.val.val.p)

/-! ### The four properties of algebraic spaces supplied by finite local freeness -/

/-- The represented morphism of algebraic spaces of a finite locally free morphism of the site is
flat: finite local freeness is flatness together with finiteness and local finite presentation by
Stacks 02KB, and flatness is étale local on the source and target. -/
private theorem isFlat_yonedaMap_of_isFiniteLocallyFree {U R : BigFppfOver B S hS} (s : R ⟶ U)
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s)) :
    Space.IsFlat B S hS (yoneda.map s) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget s).2
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map s)).1 hs).2.1

/-- The represented morphism of algebraic spaces of a finite locally free morphism of the site is
locally of finite presentation, by Stacks 02KB and the étale locality on the source and target of
local finite presentation. -/
private theorem isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree
    {U R : BigFppfOver B S hS} (s : R ⟶ U)
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s)) :
    Space.IsLocallyOfFinitePresentation B S hS (yoneda.map s) :=
  (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget s).2
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map s)).1 hs).2.2

/-- The represented morphism of algebraic spaces of a finite locally free morphism of the site is
locally quasi-finite: a finite morphism of schemes is locally of finite type and locally
quasi-finite, and that conjunction is étale local on the source and target. -/
private theorem isLocallyQuasiFinite_yonedaMap_of_isFiniteLocallyFree
    {U R : BigFppfOver B S hS} (s : R ⟶ U)
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s)) :
    Space.IsLocallyQuasiFinite B S hS (yoneda.map s) := by
  have hfin : IsFinite ((BigFppfOver.toScheme B S hS).map s) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map s)).1 hs).1
  refine (Space.holdsOnEveryEtaleChart_yoneda_map_iff B S hS
    isEtaleLocalOnSourceAndTarget_locallyOfFiniteType_inf_locallyQuasiFinite s).2 ?_
  exact ⟨(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).1 hfin |>.2,
    (IsFinite.iff_isProper_and_locallyQuasiFinite _).1 hfin |>.2⟩

/-- The represented morphism of algebraic spaces of a finite locally free morphism of the site is
proper: a finite morphism of schemes is proper, and properness of a morphism of the site passes
to its Yoneda image. -/
private theorem isProper_yonedaMap_of_isFiniteLocallyFree {U R : BigFppfOver B S hS} (s : R ⟶ U)
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s)) :
    Space.IsProper B S hS (yoneda.map s) := by
  have hfin : IsFinite ((BigFppfOver.toScheme B S hS).map s) :=
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map s)).1 hs).1
  exact Space.isProper_yoneda_map B S hS s
    ((IsFinite.iff_isProper_and_locallyQuasiFinite _).1 hfin |>.1)

/-- The structure morphism to the base scheme of the algebraic space represented by an affine
object of the site is separated: it is the Yoneda image of the unique morphism of the site to the
base object, and a morphism of schemes out of an affine scheme is separated. -/
private theorem isSeparated_toTerminalSpace_of_isAffine (U : BigFppfOver B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (f : (schemeSpace U : AlgebraicSpaces B S hS) ⟶
      Space.terminalSpace B S hS) :
    Space.IsSeparated B S hS f.hom := by
  have hf : f.hom = yoneda.map ((Over.mkIdTerminal : IsTerminal
      (Space.baseTerminal B S hS)).from U) :=
    (Space.baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _
  rw [hf]
  refine (Space.isSeparated_yoneda_map_iff B S hS _).2 ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  infer_instance

/-! ### Quasi-DM and separatedness from the presentation -/

section Presentation

variable (𝒳 : AlgebraicStacks.{u, w} B S hS) {U R : BigFppfOver B S hS} (s t : R ⟶ U)
  (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
    (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
  (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
    ((yoneda.map t).app T) fun p => c.app T p))

/-- **Stacks 0DUM, the quasi-DM assertion.** An algebraic stack equivalent over the site to the
quotient stack of a groupoid scheme of the site with finite locally free source and target is
quasi-DM.

This is Stacks 0DTY, part (4): finite local freeness makes the source and target flat, locally of
finite presentation and locally quasi-finite, and the cancellation of the source projection of
the square of the object space makes `(t, s)` locally quasi-finite. Affineness of the object and
arrow schemes is not used. -/
@[stacks 0DUM "a well-nigh affine algebraic stack is quasi-DM, read off condition (2)"]
theorem isAbsolutelyQuasiDM_of_representedGroupoid_isFiniteLocallyFree
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (ht : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack (representedGroupoid B S hS s t c hG)).p 𝒳.val.val.p)) :
    AlgebraicStacks.IsAbsolutelyQuasiDM.{u, w} B S hS hZ 𝒳 :=
  isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_source_target.{u, w}
    (representedGroupoid B S hS s t c hG) 𝒳 hZ hequiv
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isLocallyQuasiFinite_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isLocallyQuasiFinite_yonedaMap_of_isFiniteLocallyFree B S hS t ht)

/-- **Stacks 0DUM, the separatedness assertion over the base scheme of the site.** An algebraic
stack equivalent over the site to the quotient stack of a groupoid scheme of the site with affine
object scheme and finite locally free source and target is separated over `S`.

This is Stacks 0DTY, part (6): finite local freeness makes the source and target flat, locally of
finite presentation and proper, the object scheme being affine makes the object space separated
over `S`, and the cancellation of the separated source projection of the square of the object
space makes `(t, s)` proper. -/
@[stacks 0DUM "a well-nigh affine algebraic stack is separated over the base scheme of the \
site, read off condition (2)"]
theorem isSeparatedOver_of_representedGroupoid_isFiniteLocallyFree
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (ht : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack (representedGroupoid B S hS s t c hG)).p 𝒳.val.val.p)) :
    IsSeparatedOver.{u, w} B S hS 𝒳 :=
  isSeparatedOver_of_isProper_source_target.{u, w}
    (representedGroupoid B S hS s t c hG) 𝒳 hequiv
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isProper_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isProper_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isSeparated_toTerminalSpace_of_isAffine B S hS U hU _)

/-- **Stacks 0DUM, the separatedness assertion.** An algebraic stack equivalent over the site to
the quotient stack of a groupoid scheme of the site with affine object scheme and finite locally
free source and target is separated in the source's unqualified, absolute sense of Stacks 050D,
part (7), provided the algebraic stack of the base scheme of the site is separated.

Separatedness over the base scheme is the previous clause; the absolute notion is strictly
stronger, and `hBase` is the one further input Stacks 0DTY needs to reach it. -/
@[stacks 0DUM "a well-nigh affine algebraic stack is separated in the source's unqualified \
(absolute) sense, read off condition (2)"]
theorem isAbsolutelySeparated_of_representedGroupoid_isFiniteLocallyFree
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (hBase : AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ
      (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))))
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hs : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s))
    (ht : Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t))
    (hequiv : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (quotientStack (representedGroupoid B S hS s t c hG)).p 𝒳.val.val.p)) :
    AlgebraicStacks.IsAbsolutelySeparated.{u, w} B S hS hZ 𝒳 :=
  isAbsolutelySeparated_of_isProper_source_target.{u, w}
    (representedGroupoid B S hS s t c hG) 𝒳 hZ hBase hequiv
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isFlat_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isLocallyOfFinitePresentation_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isProper_yonedaMap_of_isFiniteLocallyFree B S hS s hs)
    (isProper_yonedaMap_of_isFiniteLocallyFree B S hS t ht)
    (isSeparated_toTerminalSpace_of_isAffine B S hS U hU _)

end Presentation

/-! ### Affine morphisms preserve well-nigh affineness -/

/-- **Stacks 0DUN, clause (2).** If `𝒳` is a well-nigh affine algebraic stack over `S` and
`f : 𝒳' ⟶ 𝒳` is an affine 1-morphism of algebraic stacks over `S`, then `𝒳'` is well-nigh
affine.

The affine scheme `U` presenting `𝒳` is read as a scheme-valued point of `𝒳`; the base change of
`f` along it is represented by an algebraic space over `U` whose structural morphism is affine, so
tested at `U` itself it is the projection of an affine scheme `W` of the site. The apex of the
base-change square is then the algebraic stack of `W`, and its projection to `𝒳'` is surjective,
flat, finite and of finite presentation because the presentation of `𝒳` is. -/
@[stacks 0DUN "clause (2): the source of an affine 1-morphism of algebraic stacks whose target \
is well-nigh affine is well-nigh affine"]
theorem isWellNighAffine_of_isAffineHom {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (f : 𝒳' ⟶ 𝒳)
    (hf : AlgebraicStacks.IsAffineHom B S hS f)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳) :
    IsWellNighAffine.{u, w} B S hS 𝒳' := by
  classical
  obtain ⟨U, hU, gpres, hsurj, hflat, hfin, hfp⟩ := h𝒳
  -- Read the presentation on the big fppf site of `U` instead of the slice of the site over `U`.
  have hbe : Functor.IsEquivalence (Over.iteratedSliceBackward U) :=
    (Over.iteratedSliceEquiv U).isEquivalence_inverse
  set kU : schemeSliceStack.{u, w} B S hS U ⟶ schemeStack.{u, w} B S hS U :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (⟨Over.iteratedSliceBackward U, Over.iteratedSliceBackward_forget U⟩ :
        (schemeSliceStack.{u, w} B S hS U).val.val ⥤ᵇ
          (schemeStack.{u, w} B S hS U).val.val)) with hkU
  have hkUe : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor kU.hom) := hbe
  have hid𝒳 : Functor.IsEquivalence (BasedFunctor.id 𝒳.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳.val.val.obj))
  have hid𝒳' : Functor.IsEquivalence (BasedFunctor.id 𝒳'.val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (𝟭 𝒳'.val.val.obj))
  set g : schemeSliceStack.{u, w} B S hS U ⟶ 𝒳 := kU ≫ gpres with hg
  obtain ⟨hreppres, hfinbody⟩ := hfin
  obtain ⟨-, hfpbody⟩ := hfp
  have hsurjg : IsSurjective B S hS g :=
    isSurjective_comp_of_isEquivalence B S hS kU gpres hkUe hsurj
  have hflatg : AlgebraicStacks.IsFlat B S hS g :=
    AlgebraicStacks.isFlat_comp_of_isEquivalence B S hS kU gpres hkUe hflat
  have hrepg : IsRepresentableByAlgebraicSpaces B S hS g.hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS g.hom.hom gpres.hom.hom
      kU.hom.hom (BasedFunctor.id 𝒳.val.val) (Iso.refl _)).1 hreppres
  have hfing := relativeProperty_of_equivalences B S hS
    (fun _ _ m => Space.IsFinite B S hS m.hom) g.hom.hom gpres.hom.hom kU.hom.hom
    (BasedFunctor.id 𝒳.val.val) (Iso.refl _) hfinbody
  have hfpg := relativeProperty_of_equivalences B S hS
    (fun _ _ m => Space.IsFinitePresentation B S hS m.hom) g.hom.hom gpres.hom.hom kU.hom.hom
    (BasedFunctor.id 𝒳.val.val) (Iso.refl _) hfpbody
  -- The base change of `f` along that point, and the affine scheme representing it.
  obtain ⟨F, hF, ⟨e⟩⟩ := hf.1 U (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
  have haff : Space.IsAffineHom B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.affineMorphismProperty B S hS) U F hF).1
      (hf.2 U (CatFiberedInGroupoids.homFunctor g.hom)
        (CatFiberedInGroupoids.homFunctor_comp_p g.hom) F hF ⟨e⟩)
  obtain ⟨W, pW, qW, hpb⟩ := haff ⟨U, hU⟩ (𝟙 (yoneda.obj U))
  set W' : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj W with hW'
  have iW : yoneda.obj W' ≅ (OverShriek.relocalizePresheafFunctor U.hom).obj F :=
    hpb.isoIsPullback _ _ IsPullback.of_id_fst
  -- The base-change square, and its apex read as the algebraic stack of `W`.
  set Q := twoFibreProductSquareAlgebraicStacks B S hS f g with hQ
  have hQtfp : Bicategory.IsTwoFibreProduct Q :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f g
  have eQ : StacksRepresentableCFG.EquivalenceOver Q.pt.val.val.p
      (presheafOfCategories
        ((OverShriek.relocalizePresheafFunctor U.hom).obj F ⋙ typeToCat)).p :=
    (twoFibreProductSwapEquivalenceOver B S hS f.hom g.hom).symm.trans
      (relocalizeFibreEquivalence B S hS U f.hom
        (CatFiberedInGroupoids.homFunctor g.hom) F e)
  have eWQ : StacksRepresentableCFG.EquivalenceOver
      (schemeStack.{u, w} B S hS W').val.val.p Q.pt.val.val.p :=
    ((PresheafOfCategories.sliceElementsEquivalenceOver W').trans
      (PresheafOfCategories.equivalenceOverOfIso iW)).trans eQ.symm
  set kW : schemeStack.{u, w} B S hS W' ⟶ Q.pt :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      (⟨eWQ.hom.functor, eWQ.hom.w⟩ :
        (schemeStack.{u, w} B S hS W').val.val ⥤ᵇ Q.pt.val.val)) with hkW
  have hkWe : Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor kW.hom) :=
    eWQ.isEquivalence_hom_functor
  -- The four properties of the presentation are inherited by `W ⟶ 𝒳'`.
  have hrepQ : IsRepresentableByAlgebraicSpaces B S hS Q.fst.hom.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, u, u + 1} B S hS
      (schemeSliceStack.{u, w} B S hS U).val 𝒳.val 𝒳'.val g.hom f.hom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f.hom g.hom) hrepg
  have hrepkW : IsRepresentableByAlgebraicSpaces B S hS (kW ≫ Q.fst).hom.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS (kW ≫ Q.fst).hom.hom
      Q.fst.hom.hom kW.hom.hom (BasedFunctor.id 𝒳'.val.val) (Iso.refl _)).1 hrepQ
  refine ⟨W', W.property, kW ≫ Q.fst, ?_, ?_, ⟨hrepkW, ?_⟩, ⟨hrepkW, ?_⟩⟩
  · exact isSurjective_comp_of_isEquivalence B S hS kW Q.fst hkWe
      (isSurjective_of_isTwoFibreProduct B S hS Q.swap
        (Bicategory.isTwoFibreProduct_swap hQtfp) hsurjg)
  · exact AlgebraicStacks.isFlat_comp_of_isEquivalence B S hS kW Q.fst hkWe
      (AlgebraicStacks.isFlat_baseChange B S hS g f Q hQtfp hflatg)
  · exact relativeProperty_of_equivalences B S hS
      (fun _ _ m => Space.IsFinite B S hS m.hom) (kW ≫ Q.fst).hom.hom Q.fst.hom.hom
      kW.hom.hom (BasedFunctor.id 𝒳'.val.val) (Iso.refl _)
      (relativeProperty_baseChange.{u, u, u + 1} B S hS
        (fun _ _ m => Space.IsFinite B S hS m.hom)
        (schemeSliceStack.{u, w} B S hS U).val 𝒳.val 𝒳'.val g.hom f.hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom g.hom) hfing)
  · exact relativeProperty_of_equivalences B S hS
      (fun _ _ m => Space.IsFinitePresentation B S hS m.hom) (kW ≫ Q.fst).hom.hom Q.fst.hom.hom
      kW.hom.hom (BasedFunctor.id 𝒳'.val.val) (Iso.refl _)
      (relativeProperty_baseChange.{u, u, u + 1} B S hS
        (fun _ _ m => Space.IsFinitePresentation B S hS m.hom)
        (schemeSliceStack.{u, w} B S hS U).val 𝒳.val 𝒳'.val g.hom f.hom
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f.hom g.hom)
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          f.hom g.hom) hfpg)

/-! ### Affineness of a well-nigh affine algebraic space -/

/-- The morphism of representing presheaves induced by a 1-morphism between two categories
fibred in groupoids represented by algebraic spaces is a finite morphism of algebraic spaces as
soon as the 1-morphism is finite in the relative sense of Stacks 03YK.

Over an affine object `Z` of the site, a section of the representing presheaf of the target is a
scheme-valued point by Stacks 04SW, the algebraic space representing the base change of the
1-morphism along it is finite over `Z`, and Stacks 04SD identifies it with the fibre product of
the induced morphism along that section. -/
private theorem isFinite_representingMap_of_relativeFinite
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (hfin : ∀ (Z : BigFppfOver B S hS)
      (y : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒞.val.obj)
      (_hy : y ⋙ 𝒞.val.p = Over.map Z.hom)
      (T : (BigFppfOver B Z.left.1 Z.left.2)ᵒᵖ ⥤ Type u)
      (hT : IsAlgebraicSpace B Z.left.1 Z.left.2 T),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map Z.hom) 𝒜.val.p 𝒞.val.p y
          (CatFiberedInGroupoids.homFunctor a))
        (presheafOfCategories (T ⋙ typeToCat)).p) →
      Space.IsFinite B S hS
        (algebraicSpaceMap B S hS Z
          ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj ⟨T, hT⟩)).hom) :
    Space.IsFinite B S hS (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
  intro Z hZ ξ
  obtain ⟨T, hT, ⟨eT⟩⟩ := ha Z
    (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS Z G eG ξ))
    (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS Z G eG ξ))
  have hpbalg : IsAlgebraicSpace B S hS
      (pullback ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a)) :=
    isAlgebraicSpace_pullback B S hS ξ _ (isAlgebraicSpace_yoneda B S hS Z) hF hG
  -- the base change of the induced morphism along `ξ` is the lower-shriek extension of `T`
  have e := arrowIsoRelocalizeFibrePullbackOfPullback B S hS Z a
    (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS Z G eG ξ))
    (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS Z G eG ξ))
    F G eF eG ξ (representingMap_schemePointMap B S hS Z G eG ξ) _ rfl hpbalg T eT hT
  obtain ⟨iL, iR, hw⟩ :
      ∃ (iL : (OverShriek.relocalizePresheafFunctor Z.hom).obj T ≅
          pullback ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a))
        (iR : yoneda.obj Z ≅ yoneda.obj Z),
        iL.hom ≫ pullback.fst ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a) =
          OverShriek.relocalizeToYoneda Z.hom T ≫ iR.hom :=
    ⟨(ObjectProperty.ι _).mapIso (Arrow.leftFunc.mapIso e.symm),
      (ObjectProperty.ι _).mapIso (Arrow.rightFunc.mapIso e.symm),
      congrArg InducedCategory.Hom.hom (Arrow.w e.inv)⟩
  -- the structural morphism of that extension is the morphism Stacks 03YK tests
  set j := (spacesOverSmallerBaseFunctorForgetIso B Z.left.1 S Z.left.2 hS Z.hom).app ⟨T, hT⟩
  have hstruct : j.hom ≫ OverShriek.relocalizeToYoneda Z.hom T =
      (algebraicSpaceMap B S hS Z
        ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj ⟨T, hT⟩)).hom := by
    apply (cancel_epi j.inv).mp
    simp only [Iso.inv_hom_id_assoc]
    ext W s
    exact (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B Z.left.1 S Z.left.2 hS
      Z.hom ⟨T, hT⟩ W s).symm
  obtain ⟨V, p, i₀, hVaff, hpfin, hpb0⟩ :=
    hfin Z (CatFiberedInGroupoids.homFunctor (schemePointMap B S hS Z G eG ξ))
      (CatFiberedInGroupoids.homFunctor_comp_p (schemePointMap B S hS Z G eG ξ)) T hT ⟨eT⟩
      Z hZ iR.inv
  refine ⟨V, p, (i₀ ≫ j.hom ≫ iL.hom) ≫
    pullback.snd ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a), hVaff, hpfin, ?_⟩
  have hcomm : (j.hom ≫ iL.hom) ≫ pullback.fst ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a) =
      (algebraicSpaceMap B S hS Z
        ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj
          ⟨T, hT⟩)).hom ≫ iR.hom := by
    rw [Category.assoc, hw, ← hstruct, Category.assoc]
  have hisosq : IsPullback (j.hom ≫ iL.hom)
      (algebraicSpaceMap B S hS Z
        ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj ⟨T, hT⟩)).hom
      (pullback.fst ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a)) iR.hom :=
    IsPullback.of_horiz_isIso ⟨hcomm⟩
  have hchain := (hpb0.paste_horiz hisosq).paste_horiz
    (IsPullback.of_hasPullback ξ (representingMap B S hS 𝒜 𝒞 F G eF eG a)).flip
  have hbot : (iR.inv ≫ iR.hom) ≫ ξ = ξ := by rw [Iso.inv_hom_id, Category.id_comp]
  rw [hbot] at hchain
  exact hchain

/-- The morphism of representing presheaves induced by a 1-morphism between two categories
fibred in groupoids represented by algebraic spaces is locally of finite presentation as soon
as the 1-morphism is of finite presentation in the relative sense of Stacks 03YK.

Local finite presentation of morphisms of algebraic spaces is local on the target for the fppf
topology, so the condition on the base changes along scheme-valued points of the target is
exactly the condition on the induced morphism. -/
private theorem isLocallyOfFinitePresentation_representingMap_of_relativeFinitePresentation
    {𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (a : 𝒜 ⟶ 𝒞)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a.hom)
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒜.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver 𝒞.val.p
      (presheafOfCategories (G ⋙ typeToCat)).p)
    (hfp : ∀ (Z : BigFppfOver B S hS)
      (y : BigFppfOver B Z.left.1 Z.left.2 ⥤ 𝒞.val.obj)
      (_hy : y ⋙ 𝒞.val.p = Over.map Z.hom)
      (T : (BigFppfOver B Z.left.1 Z.left.2)ᵒᵖ ⥤ Type u)
      (hT : IsAlgebraicSpace B Z.left.1 Z.left.2 T),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map Z.hom) 𝒜.val.p 𝒞.val.p y
          (CatFiberedInGroupoids.homFunctor a))
        (presheafOfCategories (T ⋙ typeToCat)).p) →
      Space.IsFinitePresentation B S hS
        (algebraicSpaceMap B S hS Z
          ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj ⟨T, hT⟩)).hom) :
    Space.IsLocallyOfFinitePresentation B S hS
      (representingMap B S hS 𝒜 𝒞 F G eF eG a) := by
  have hbase := Space.isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS
  have _ : MorphismProperty.RespectsIso
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS k.hom) := hbase.respectsIso
  exact prop_representingMap_of_relativeProperty B S hS
    (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (k : X ⟶ Y) =>
      Space.IsLocallyOfFinitePresentation B S hS k.hom)
    a F G hF hG eF eG
    (fun _ _ hX hY k h => Space.prop_homMk_of_forall_yoneda.{u, u + 1} B S hS
      (fun ⦃X Y : AlgebraicSpaces B S hS⦄ (m : X ⟶ Y) =>
        Space.IsLocallyOfFinitePresentation B S hS m.hom) hX hY k h) ha
    (fun Z y hy T hT he => (hfp Z y hy T hT he).1)

/-- **Stacks 0DUN, clause (1).** A well-nigh affine algebraic stack over `S` which is an
algebraic space is affine: every algebraic space `F` representing it over the site is affine.

The affine scheme `U` presenting `𝒳` represents an algebraic stack as well, so Stacks 04SW turns
the presentation into a morphism `h_U ⟶ F` of algebraic spaces over `S`. It is surjective
because the presentation is surjective on points, finite because the presentation is finite in
the relative sense of Stacks 03YK, flat because the presentation is flat, and locally of finite
presentation because the presentation is of finite presentation; so it is a surjective finite
locally free chart of `F` by Stacks 0416, and the ring of invariant functions of its kernel
pair makes `F` affine by Stacks 03BM. -/
@[stacks 0DUN "clause (1): a well-nigh affine algebraic stack which is an algebraic space is \
affine"]
theorem isAffineSpace_of_isWellNighAffine (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsWellNighAffine.{u, w} B S hS 𝒳)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (eF : StacksRepresentableCFG.EquivalenceOver 𝒳.val.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsAffineSpace B S hS F := by
  obtain ⟨U, hU, gpres, hsurj, hflat, hfin, hfp⟩ := h𝒳
  obtain ⟨hrep, hfinbody⟩ := hfin
  obtain ⟨-, hfpbody⟩ := hfp
  have hUalg : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have hsurjm := isSurjective_representingMap_of_isSurjective B S hS (yoneda.obj U) F
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eF gpres hsurj
  have hfinm := isFinite_representingMap_of_relativeFinite B S hS gpres.hom hrep
    (yoneda.obj U) F hUalg hF
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eF hfinbody
  have hflatm := isFlat_representingMap_of_isFlat.{u, w} B S hS (yoneda.obj U) F hUalg hF
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eF gpres hflat
  have hlfpm := isLocallyOfFinitePresentation_representingMap_of_relativeFinitePresentation
    B S hS gpres.hom hrep (yoneda.obj U) F hUalg hF
    (PresheafOfCategories.sliceElementsEquivalenceOver U) eF hfpbody
  -- the presentation is a surjective finite locally free chart of `F`
  have hflf := (Space.isFiniteLocallyFree_presheaf_iff B S hS hUalg hF _).mpr
    ⟨hfinm, hflatm, hlfpm⟩
  have hsurjpre :=
    (Space.presheafSurjective_iff_isSurjective_yoneda B S hS F hF U _).mpr hsurjm
  exact Space.isAffineSpace_of_isFiniteLocallyFree_affineChart B S hS hF U hU _ hsurjpre hflf

end AlgebraicGeometry.Stack

end
