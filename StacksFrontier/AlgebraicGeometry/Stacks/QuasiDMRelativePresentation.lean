module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordPresentationTheorem
public import StacksFrontier.AlgebraicGeometry.Stacks.NoetherianPointsAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalUnramified
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFlatCoverDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFppfDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationSourceOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationTrivialImplications
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack

/-!
# Quasi-DM 1-morphisms and locally quasi-finite flat covers (Stacks 06UE)

**Stacks 06UE.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks is quasi-DM exactly when each of
its base changes `𝒳 ×_𝒴 𝒱 ⟶ 𝒱` along an algebraic space `𝒱` admits a surjective, flat, locally
finitely presented, locally quasi-finite cover by an algebraic space, and exactly when one such
cover exists over one algebraic space `𝒱` covering `𝒴` surjectively, flatly and in a locally
finitely presented way.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.HasQuasiFiniteFlatSpaceCover`: an algebraic stack
  admits a surjective, flat, locally finitely presented, locally quasi-finite 1-morphism to it
  from an algebraic space.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMOver_of_isRepresentableByAlgebraicSpace`:
  **Stacks 050E**, part (3), at the structure 1-morphism — an algebraic stack representable by
  an algebraic space is quasi-DM over its base.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_tfae_hasQuasiFiniteFlatSpaceCover`:
  **Stacks 06UE**.

## Implementation notes

Local quasi-finiteness of a cover is read as `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, the
notion of Properties of Stacks, Section 04XB. A 1-morphism to an algebraic stack whose source is
representable by an algebraic space is representable by algebraic spaces
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack`), so this is the
notion the source attaches to the covers of **Stacks 06UE**; Lemma 101.23.1 of the source is
what says it agrees there with the general Definition 101.23.2 of a locally quasi-finite
1-morphism of algebraic stacks. The same reading is used for the chart of **Stacks 06MF** in
`AlgebraicGeometry.Stack.HasQuasiDMPresentation`, which this file's substantial direction
consumes.

Two hypotheses are carried that the source does not state.

* `hZ`, that the ambient big fppf site contains the terminal scheme. The absolute quasi-DM
  condition of **Stacks 050D**, part (6), is read over `Spec(ℤ)`, so every consumer of it needs
  that object in the site; the same hypothesis appears in **Stacks 06MB** and **06MF**.
* `hPresentation`, the substantial direction of **Stacks 06MF**
  (`AlgebraicGeometry.Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM`), which is carried
  there too: it is the structure theorem building a flat locally quasi-finite chart near every
  finite type point, whose proof runs through **Stacks 06MD**, **06ME**, **06G2** and **06G3**,
  none of which is in this library. It is used only for (1) ⟹ (2); the implications
  (2) ⟹ (3) and (3) ⟹ (1) are unconditional.

## References

* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
* [Stacks Project, Tag 06MB](https://stacks.math.columbia.edu/tag/06MB)
* [Stacks Project, Tag 06MF](https://stacks.math.columbia.edu/tag/06MF)
* [Stacks Project, Tag 06TZ](https://stacks.math.columbia.edu/tag/06TZ)
* [Stacks Project, Tag 06UE](https://stacks.math.columbia.edu/tag/06UE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic stack over `S` *has a locally quasi-finite flat cover by an algebraic space*
when there is an algebraic stack representable by an algebraic space with a surjective, flat,
locally finitely presented and locally quasi-finite 1-morphism to it.

Surjectivity, flatness and local finite presentation are the stack-level properties of
**Stacks 04ZS**, **06PW** and **06Q2**, part (1); local quasi-finiteness is the Section 04XB
notion `AlgebraicGeometry.Stack.IsLocallyQuasiFinite`, which applies because such a 1-morphism
is representable by algebraic spaces. -/
abbrev HasQuasiFiniteFlatSpaceCover (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  ∃ (𝒰 : Stack.AlgebraicStacks.{u, w} B S hS)
    (_h𝒰 : IsRepresentableByAlgebraicSpace B S hS 𝒰.val) (p : 𝒰 ⟶ 𝒵),
    IsSurjective B S hS p ∧ IsFlat B S hS p ∧ IsLocallyOfFinitePresentation B S hS p ∧
      Stack.IsLocallyQuasiFinite B S hS p.hom

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Condition (2) of Stacks 06UE.** Every base change of `f` along an algebraic space over
`𝒴` has a locally quasi-finite flat cover by an algebraic space. -/
abbrev HasQuasiFiniteFlatSpaceCoverOnEveryBaseChange (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (𝒱 : Stack.AlgebraicStacks.{u, w} B S hS),
    IsRepresentableByAlgebraicSpace B S hS 𝒱.val → ∀ g : 𝒱 ⟶ 𝒴,
      HasQuasiFiniteFlatSpaceCover B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt

/-- **Condition (3) of Stacks 06UE.** Some algebraic space surjective, flat and locally of
finite presentation over `𝒴` carries a base change of `f` with a locally quasi-finite flat cover
by an algebraic space. -/
abbrev HasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ (𝒱 : Stack.AlgebraicStacks.{u, w} B S hS)
    (_h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val) (g : 𝒱 ⟶ 𝒴),
    IsSurjective B S hS g ∧ IsFlat B S hS g ∧ IsLocallyOfFinitePresentation B S hS g ∧
      HasQuasiFiniteFlatSpaceCover B S hS
        (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt

/-- **Stacks 050E, part (3), at the structure 1-morphism.** An algebraic stack over `S` which is
representable by an algebraic space is quasi-DM over `S`: its structure 1-morphism is
representable by algebraic spaces, hence DM, hence quasi-DM. -/
theorem isQuasiDMOver_of_isRepresentableByAlgebraicSpace
    (𝒱 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒱 : IsRepresentableByAlgebraicSpace B S hS 𝒱.val) :
    Stack.IsQuasiDMOver B S hS 𝒱 :=
  isQuasiDM_of_isDM B S hS
    (Stack.isUnramified_relativeDiagonal_of_isRepresentableByAlgebraicSpaces B S hS
      (Stack.structureMorphism B S hS 𝒱)
      (Stack.isRepresentableByAlgebraicSpaces_of_isAlgebraicStack B S hS
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).property h𝒱
        (Stack.structureMorphism B S hS 𝒱).hom))

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 06UE, (1) ⟹ (2).** If `f : 𝒳 ⟶ 𝒴` is quasi-DM then every base change of `f` along
an algebraic space over `𝒴` has a locally quasi-finite flat cover by an algebraic space.

The base change `𝒳 ×_𝒴 𝒱 ⟶ 𝒱` is quasi-DM by **Stacks 050F**, the algebraic space `𝒱` is
quasi-DM over `S` by **Stacks 050E**, part (3), so `𝒳 ×_𝒴 𝒱` is quasi-DM over `S` by
**Stacks 050K** and quasi-DM by **Stacks 050N**, part (2); the chart is then the one
**Stacks 06MF** produces, carried here as `hPresentation`. -/
theorem hasQuasiFiniteFlatSpaceCoverOnEveryBaseChange_of_isQuasiDM
    (hPresentation : Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS hZ)
    (f : 𝒳 ⟶ 𝒴) (hf : IsQuasiDM B S hS f) :
    HasQuasiFiniteFlatSpaceCoverOnEveryBaseChange B S hS f := by
  intro 𝒱 h𝒱 g
  have hbc : IsQuasiDM B S hS (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd :=
    isQuasiDM_baseChange B S hS f g hf
  have hover : Stack.IsQuasiDMOver B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).pt := by
    have hcomp := isQuasiDM_comp B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS f g).snd
      (Stack.structureMorphism B S hS 𝒱) hbc
      (isQuasiDMOver_of_isRepresentableByAlgebraicSpace B S hS 𝒱 h𝒱)
    rwa [Stack.comp_structureMorphism] at hcomp
  obtain ⟨W, p, hpS, hpF, hpL, hpQ⟩ := hPresentation _
    (isAbsolutelyQuasiDM_of_isQuasiDMOver B S hS hZ _ hover)
  exact ⟨Stack.schemeStack.{u, w} B S hS W,
    Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS W, p,
    hpS, hpF, hpL, hpQ⟩

/-- **Stacks 06UE, (2) ⟹ (3).** Every algebraic stack has a smooth surjective chart by a scheme
of the site, and a smooth 1-morphism is flat and locally of finite presentation, so the
universal condition (2) applied to that chart is condition (3). -/
theorem hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange_of_onEveryBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : HasQuasiFiniteFlatSpaceCoverOnEveryBaseChange B S hS f) :
    HasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS f := by
  obtain ⟨U, a, haSmooth, haSurj⟩ := Stack.exists_smooth_surjective_schemeStack B S hS 𝒴
  exact ⟨Stack.schemeStack.{u, w} B S hS U,
    Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U, a, haSurj,
    isFlat_of_isSmooth B S hS a haSmooth,
    isLocallyOfFinitePresentation_of_isSmooth B S hS a haSmooth,
    hf _ (Stack.isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) a⟩

include hZ in
/-- **Stacks 06UE, (3) ⟹ (1).** A locally quasi-finite flat cover of `𝒳 ×_𝒴 𝒱` by an algebraic
space makes `𝒳 ×_𝒴 𝒱` quasi-DM by **Stacks 06MB**, part (2), hence `𝒳 ×_𝒴 𝒱 ⟶ 𝒱` quasi-DM by
**Stacks 050N**, parts (2) and (6); the separation axioms descend along the surjective flat
locally finitely presented `𝒱 ⟶ 𝒴` by **Stacks 06TZ**. -/
theorem isQuasiDM_of_hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange (f : 𝒳 ⟶ 𝒴)
    (hf : HasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS f) :
    IsQuasiDM B S hS f := by
  obtain ⟨𝒱, h𝒱, g, hgS, hgF, hgL, 𝒰, h𝒰, p, hpS, hpF, hpL, hpQ⟩ := hf
  refine isQuasiDM_of_isQuasiDM_baseChange B S hS f g h𝒱 hgS hgF hgL ?_
  refine Stack.isQuasiDM_of_isQuasiDMOver B S hS _ ?_
  exact (isAbsolutelyQuasiDM_iff_isQuasiDMOver B S hS hZ _).1
    (isAbsolutelyQuasiDM_of_isLocallyQuasiFinite_flatCover B S hS hZ p h𝒰 hpS hpF hpL hpQ)

/-- **Stacks 06UE.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` the following
are equivalent: `f` is quasi-DM; every base change of `f` along an algebraic space over `𝒴` has
a surjective, flat, locally finitely presented, locally quasi-finite cover by an algebraic
space; and some algebraic space surjective, flat and locally of finite presentation over `𝒴`
carries a base change of `f` with such a cover.

The hypothesis `hPresentation` is the substantial direction of **Stacks 06MF**, carried in this
library; it is used only for (1) ⟹ (2). -/
@[stacks 06UE "granted the substantial direction of Tag 06MF, the quasi-DM presentation
  theorem, as the hypothesis `hPresentation`, and granted the containment of the terminal
  scheme in the site as the hypothesis `hZ`, which the absolute quasi-DM condition of
  Tag 050D part (6) needs. Only (1) implies (2) uses `hPresentation`"]
theorem isQuasiDM_tfae_hasQuasiFiniteFlatSpaceCover
    (hPresentation : Stack.ExistsQuasiDMPresentationOfIsAbsolutelyQuasiDM.{u, w} B S hS hZ)
    (f : 𝒳 ⟶ 𝒴) :
    [IsQuasiDM B S hS f,
      HasQuasiFiniteFlatSpaceCoverOnEveryBaseChange B S hS f,
      HasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS f].TFAE := by
  tfae_have 1 → 2 :=
    hasQuasiFiniteFlatSpaceCoverOnEveryBaseChange_of_isQuasiDM B S hS hZ hPresentation f
  tfae_have 2 → 3 :=
    hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange_of_onEveryBaseChange B S hS f
  tfae_have 3 → 1 :=
    isQuasiDM_of_hasQuasiFiniteFlatSpaceCoverOnSomeFlatBaseChange B S hS hZ f
  tfae_finish

end AlgebraicGeometry.Stack.AlgebraicStacks

end
