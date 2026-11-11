module

public import StacksFrontier.CategoryTheory.Abelian.RightDerivedVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FppfEtaleComparison.ModuleHigherVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartBaseChangePresieve
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyBridge

/-!
# Vanishing of the higher direct images of modules along a representable morphism of spaces

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`.  The direct image of Stacks 03LU,
`AlgebraicGeometry.Space.modulePushforward`, is not visibly a restriction along a continuous
functor of sites, so no criterion for the vanishing of its right derived functors applies to it
directly.  `AlgebraicGeometry.Space.modulePushforwardChartIso` identifies it, for representable
`f`, with `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, which *is*
`CategoryTheory.SheafOfModules.pushforward` of the structure map of small-chart base change.

This file makes that identification usable for vanishing statements and runs the presieve
criterion
`Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`
through it, on the small étale sites of two algebraic spaces.  Composed with the
affine-base-change input of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartBaseChangePresieve.lean`, that produces the
hypothesis `AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage` — the hypothesis `h03DW`
— from the vanishing of the cohomology of a quasi-coherent module over an affine
étale chart, which is the output of the Čech criterion of [Stacks, Tag 03F9] and is the only
thing left carried here.

## Main definitions

* `AlgebraicGeometry.Space.AffineChartModuleSectionsVanishing`: the carried 03F9 step in its
  module form — a quasi-coherent `𝒪_F`-module has no higher derived *module* sections over an
  affine étale chart, for every algebraic space `F`.
* `AlgebraicGeometry.Space.AffineChartSheafCohomologyVanishing`: the same at the abelian-sheaf
  level, `CategoryTheory.Sheaf.H'`, which is the level a Čech argument works at.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_iff_smallBaseChange`:
  **the vanishing of `R^n f_*` is the same question for the two direct images**, transported
  across `AlgebraicGeometry.Space.modulePushforwardChartIso`.
* `AlgebraicGeometry.Space.isZero_rightDerived_smallBaseChangeModulePushforward_of_presieve` and
  `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_presieve`: **the presieve
  criterion on the small étale sites of two algebraic spaces**, concluded for the base-change
  direct image and for the direct image of Stacks 03LU respectively.
* `AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_affineChartVanishing` and
  `AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isZero_H'`: **the keystone
  `h03DW` from the carried 03F9 step**, in its module and its abelian-sheaf form.
* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isZero_H'`: **Stacks 073H
  with the 03F9 step as its only carried hypothesis** — for an affine morphism of algebraic
  spaces, a quasi-coherent `𝓕` and `0 < n`, `R^n f_* 𝓕 = 0`.

## Implementation notes

*Why `0 < n` and quasi-coherence appear.*
`AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage`
is false at `n = 0`: there it asserts that `f'_*(𝓕|_V)` itself vanishes.  The two hypotheses of
the statements below are exactly the source's — `0 < n` and quasi-coherence of `𝓕` — and both
are used: quasi-coherence of the restriction `𝓕|_{V ×_Y X}`, through
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`, and `0 < n` are what the
carried 03F9 step consumes.  Nothing here is proved at `n = 0`.

*The three spellings of one category, and why each has to be named.*  The `𝒪_F`-modules occur
here under two names that are equal by `rfl` and that instance search nevertheless keeps apart,
`AlgebraicGeometry.Space.Modules` being
`CategoryTheory.SheafOfModules (AlgebraicGeometry.RingedSite.ringSheaf
(AlgebraicGeometry.Space.smallEtaleRingedSite …))` while
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward` is typed through
`AlgebraicGeometry.Space.smallEtaleRingSheaf`.  Both reduce to the same sheaf of rings
(`AlgebraicGeometry.Space.ringedSite_ringSheaf_eq`), but `smallEtaleRingedSite` is a plain `def`
and so the two are *different keys* in the instance discrimination tree.  Three consequences,
each of which is a line below:

* `HasInjectiveResolutions` has to be introduced by a type *ascription* at each spelling that
  occurs in the statement; the ascription is checked at default transparency and goes through,
  while instance search left to itself reaches
  `Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives`, which pins the module universe
  to `max (u + 1) ?w` and reports `stuck at solving universe constraint max (u + 1) ?w =?= u`.
* `CategoryTheory.SheafOfModules.evaluation.{u}` has to carry its module universe explicitly.
  The sheaf of rings pins only the *ring* universe, so without it the module universe is still a
  metavariable when `CategoryTheory.Functor.rightDerived` asks for `HasInjectiveResolutions`,
  and the same blocked search follows.
* The `Functor.Additive` instance for `smallBaseChangeModulePushforward` below is stated at that
  functor's own spelling, which is what the statements need.  The transport lemma needs it at
  the `Modules` spelling instead — the category of the isomorphism
  `modulePushforwardChartIso` is the one `modulePushforward` is typed in — and no instance
  declaration can serve both: the category is an indexed argument of
  `CategoryTheory.Functor.Additive`, and writing the declaration's type with a type ascription
  on the functor does not help, since the ascription is erased and the category is read off the
  functor's own type.  It is supplied instead through the named instance argument
  `(hG := ⟨rfl⟩)`: `Functor.Additive` is `Prop`-valued, its one field holds by `rfl` for a
  direct image of sheaves of modules, and proof irrelevance makes the result interchangeable
  with any other proof.

`attribute [local instance 5000] SheafOfModules.instAbelian` is required, as it is in the other
modules of this tree that form derived functors of `𝒪_F`-modules; see the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModuleCohomologyBridge.lean` for what it
fixes.  `AlgebraicGeometry.Space.isContinuous_smallBaseChange` is a local instance here as it is
in `StacksFrontier/AlgebraicGeometry/Spaces/ModulePushforwardChartComparison.lean`.

No `@[stacks]` attribute is claimed.  Every statement below either transports a vanishing or
carries the 03F9 step as an explicit hypothesis; in particular
`isZero_rightDerived_modulePushforward_of_isZero_H'` is Stacks 073H with that hypothesis still
carried, while Stacks 073H itself is now registered, with no qualifier, on
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite`.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 073H](https://stacks.math.columbia.edu/tag/073H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] AlgebraicGeometry.Space.isContinuous_smallBaseChange

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

alias smallBaseChangeModulePushforward_additive :=
  AlgebraicGeometry.Space.additive_smallBaseChangeModulePushforward

attribute [instance] smallBaseChangeModulePushforward_additive

/-- **For a representable morphism the two direct images of modules have the same higher
vanishing.**  `R^n f_* 𝓖 = 0` for the direct image of Stacks 03LU exactly when it vanishes for
the base-change direct image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward`.

This is `CategoryTheory.Functor.isZero_rightDerived_natIso_iff` at the isomorphism
`AlgebraicGeometry.Space.modulePushforwardChartIso` of Stacks 03LU with chart base change.  It
is what lets a criterion stated for `CategoryTheory.SheafOfModules.pushforward` — every
criterion in this tree is — conclude about the direct image of Stacks 03LU. -/
theorem isZero_rightDerived_modulePushforward_iff_smallBaseChange (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (n : ℕ)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have : HasInjectiveResolutions (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :=
      hasInjectiveResolutions_modules B S hS X.1 X.2
    (IsZero (((modulePushforward B S hS f).rightDerived n).obj G) ↔
      IsZero (((smallBaseChangeModulePushforward.{u, u} B S hS f hf).rightDerived n).obj G)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  exact Functor.isZero_rightDerived_natIso_iff (hG := ⟨rfl⟩)
    (modulePushforwardChartIso B S hS f hf) n G

/-- **The presieve criterion for the vanishing of a higher direct image, on the small étale
sites of two algebraic spaces.**  If every étale chart `V` of `Y` carries a covering presieve
whose members `W` have `R^p Γ(W ×_Y X, 𝓖) = 0`, then `R^p f_* 𝓖 = 0` for the base-change direct
image.

This is `Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve`
at the continuous functor `AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4) and
the structure map `AlgebraicGeometry.Space.smallBaseChangeSharp`, with all of its instance
hypotheses discharged; enough injectives is
`AlgebraicGeometry.Space.enoughInjectives_modules`, carried at the spelling of the sheaf of
rings the criterion is typed through. -/
theorem isZero_rightDerived_smallBaseChangeModulePushforward_of_presieve (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (p : ℕ)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    have : HasInjectiveResolutions (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :=
      hasInjectiveResolutions_modules B S hS X.1 X.2
    (∀ V : SmallEtale B S hS Y.1, ∃ R : Presieve V,
        Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 V ∧
          ∀ ⦃W : SmallEtale B S hS Y.1⦄ (g : W ⟶ V), R g →
            IsZero (((SheafOfModules.evaluation.{u} (smallEtaleRingSheaf B S hS X.1 X.2)
              (op ((smallBaseChange B S hS f hf).obj W))).rightDerived p).obj G)) →
      IsZero (((smallBaseChangeModulePushforward.{u, u} B S hS f hf).rightDerived p).obj G) := by
  intro _ h
  have : EnoughInjectives (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :=
    enoughInjectives_modules B S hS X.1 X.2
  exact Stacks.Cohomology.ModuleDirectImageOnACover.isZero_rightDerived_pushforward_of_presieve
    (smallBaseChange B S hS f hf) (smallEtaleRingSheaf B S hS X.1 X.2)
    (smallEtaleRingSheaf B S hS Y.1 Y.2) (smallBaseChangeSharp B S hS f hf) p G h

/-- **The presieve criterion, concluded for the direct image of Stacks 03LU.**  The same
hypothesis gives `R^p f_* 𝓖 = 0` for `AlgebraicGeometry.Space.modulePushforward`.

This is the previous theorem followed by
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_iff_smallBaseChange`, and it is
the form `AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage` asks for. -/
theorem isZero_rightDerived_modulePushforward_of_presieve (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (p : ℕ)
    (G : Modules.{u, u} B S hS X.1 X.2) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    have : HasInjectiveResolutions (SheafOfModules.{u} (smallEtaleRingSheaf B S hS X.1 X.2)) :=
      hasInjectiveResolutions_modules B S hS X.1 X.2
    (∀ V : SmallEtale B S hS Y.1, ∃ R : Presieve V,
        Sieve.generate R ∈ SmallEtale.topology B S hS Y.1 V ∧
          ∀ ⦃W : SmallEtale B S hS Y.1⦄ (g : W ⟶ V), R g →
            IsZero (((SheafOfModules.evaluation.{u} (smallEtaleRingSheaf B S hS X.1 X.2)
              (op ((smallBaseChange B S hS f hf).obj W))).rightDerived p).obj G)) →
      IsZero (((modulePushforward B S hS f).rightDerived p).obj G) := by
  intro _ _ h
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  exact (isZero_rightDerived_modulePushforward_iff_smallBaseChange B S hS f hf p G).mpr
    (isZero_rightDerived_smallBaseChangeModulePushforward_of_presieve B S hS f hf p G h)

/-- The carried 03F9 step, in its module form: for every algebraic space `F`, every affine
étale chart `W` of `F`, every quasi-coherent `𝒪_F`-module `M` and every `p > 0`, the `p`-th
right derived functor of `CategoryTheory.SheafOfModules.evaluation` at `W` vanishes on `M`.

This is the étale-site analogue of Stacks 01XC, that is Stacks 03DW, read as a statement about
module-valued cohomology and quantified over the algebraic space as well — the quantifier is
needed because the criterion above is applied on the chart spaces of the base changes of `f`,
not on `X` and `Y` themselves.  At a fixed `F` it is exactly the conclusion of
`AlgebraicGeometry.Space.SmallEtale.chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H'`,
which is how `AffineChartSheafCohomologyVanishing` discharges it below. -/
def AffineChartModuleSectionsVanishing : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F),
    have := hasInjectiveResolutions_modules B S hS F hF
    ∀ W : SmallEtale B S hS F, IsAffineChart B S hS F W →
      ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (((SheafOfModules.evaluation.{u}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)
          (op W)).rightDerived p).obj M)

/-- **The keystone `h03DW` from the carried 03F9 step.**

For an affine morphism `f : X ⟶ Y` of algebraic spaces over `S`, a quasi-coherent
`𝒪_X`-module `𝓕` and `0 < n`, the chart base changes of `f` have vanishing degree-`n` higher
direct images on the restrictions of `𝓕` — that is,
`AlgebraicGeometry.Space.ChartwiseIsZeroHigherDirectImage` holds — as soon as a quasi-coherent
module has no higher derived module sections over an affine étale chart.

This is the composite of three inputs: the covering presieve of affine charts with affine base
change, `AlgebraicGeometry.Space.exists_presieve_isAffine_smallBaseChange_chartMap`;
the presieve criterion above; and the carried vanishing, applied on the chart space of
`V ×_Y X` to the restriction of `𝓕`, which is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`. -/
theorem chartwiseIsZeroHigherDirectImage_of_affineChartVanishing (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n)
    (h03F9 : AffineChartModuleSectionsVanishing B S hS) :
    ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f haff) F n := by
  intro V
  have hf := relativelyRepresentable_of_isAffineHom B S hS f haff
  refine isZero_rightDerived_modulePushforward_of_presieve B S hS
    (smallBaseChangeChartMap B S hS f hf V)
    (relativelyRepresentable_smallBaseChangeChartMap B S hS f hf haff V) n _ (fun V' => ?_)
  obtain ⟨R, hR, hmem⟩ := exists_presieve_isAffine_smallBaseChange_chartMap B S hS f hf haff V V'
  exact ⟨R, hR, fun W g hg => h03F9 _ _ _ (hmem g hg).2 _
    (isQuasicoherentOnSite_etaleModulePullback B S hS _ _ F hF) n hn⟩

/-- The carried 03F9 step at the abelian-sheaf level: the same vanishing for
`CategoryTheory.Sheaf.H'` of the underlying abelian sheaf `Mᵃ`.

This is the level the Čech criterion `@[stacks 03F9]` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Cech/VanishingOnCofinalCoverings.lean` works at,
and the `Ext` universe is the morphism universe `u + 1` of the sheaf category, which is where
`CategoryTheory.Sheaf.H'` is formed on this site.  `HasExt` is supplied inside the statement by
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale`, so a user of this hypothesis needs no
instance of it. -/
def AffineChartSheafCohomologyVanishing : Prop :=
  ∀ (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F),
    have : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) :=
      hasExt_sheaf_smallEtale B S hS F
    ∀ U : SmallEtale B S hS F, IsAffineChart B S hS F U →
      ∀ M : Modules.{u, u} B S hS F hF, M.IsQuasicoherentOnSite → ∀ p : ℕ, 0 < p →
        IsZero (Sheaf.H'.{u + 1} ((SheafOfModules.toSheaf.{u}
          (ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj M) p U)

/-- The abelian-sheaf form of the carried 03F9 step gives its module form.  This is
`AlgebraicGeometry.Space.SmallEtale.chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H'`
applied at each algebraic space. -/
theorem affineChartModuleSectionsVanishing_of_isZero_H'
    (hab : AffineChartSheafCohomologyVanishing B S hS) :
    AffineChartModuleSectionsVanishing B S hS := by
  intro F hF _ U hU M hM p hp
  exact SmallEtale.chartwise_isZero_rightDerived_moduleEvaluation_of_isZero_H' B S hS F hF
    (hab F hF) U hU M hM p hp

/-- **The keystone `h03DW` from the abelian-sheaf form of the carried 03F9 step.**  The
previous composite with the change of level already performed, so that a Čech-theoretic
vanishing of `CategoryTheory.Sheaf.H'` over affine charts discharges it outright. -/
theorem chartwiseIsZeroHigherDirectImage_of_isZero_H' (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n)
    (hab : AffineChartSheafCohomologyVanishing B S hS) :
    ChartwiseIsZeroHigherDirectImage B S hS f
      (relativelyRepresentable_of_isAffineHom B S hS f haff) F n :=
  chartwiseIsZeroHigherDirectImage_of_affineChartVanishing B S hS f haff F hF n hn
    (affineChartModuleSectionsVanishing_of_isZero_H' B S hS hab)

/-- **Stacks 073H with the 03F9 step as its only carried hypothesis.**  Let `f : X ⟶ Y` be an
affine morphism of algebraic spaces over `S`, let `𝓕` be a quasi-coherent `𝒪_X`-module and let
`0 < n`.  If the cohomology of the underlying abelian sheaf of a quasi-coherent module vanishes
in positive degrees over every affine étale chart of every algebraic space, then
`R^n f_* 𝓕 = 0`.

This is the chartwise reduction
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_isAffineHom` with its
hypothesis `h03DW` supplied by
`AlgebraicGeometry.Space.chartwiseIsZeroHigherDirectImage_of_isZero_H'`.  It carries no tag:
Stacks 073H, with no hypothesis beyond the source's, is
`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_isAffineHom`. -/
theorem isZero_rightDerived_modulePushforward_of_isZero_H' (f : X ⟶ Y)
    (haff : IsAffineHom B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n)
    (hab : AffineChartSheafCohomologyVanishing B S hS) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((modulePushforward B S hS f).rightDerived n).obj F) :=
  isZero_rightDerived_modulePushforward_of_isAffineHom B S hS f haff F n
    (chartwiseIsZeroHigherDirectImage_of_isZero_H' B S hS f haff F hF n hn hab)

end AlgebraicGeometry.Space

end
