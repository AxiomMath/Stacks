module

public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.FpqcCoequalizer
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper

/-!
# Limits of finite étale covers

Let `X` be a scheme. A *finite étale cover* of `X` is a scheme `Y` together with a morphism
`Y ⟶ X` which is both finite and étale; these form the category `FÉt_X`, realized as
`AlgebraicGeometry.FiniteEtaleOver X`, the subcategory of `Over X` cut out by the morphism
property `AlgebraicGeometry.finiteEtale`. This file proves the left-exactness half of Stacks
Tag 0BN9: `FÉt_X` has finite limits, and for every morphism `f : X ⟶ Y` the base-change functor
`FÉt_Y ⥤ FÉt_X` preserves them.

Both statements reduce to the fact that `finiteEtale` is multiplicative, stable under base
change, and satisfies right cancellation: if `g` and `f ≫ g` are finite étale then so is `f`.
The final object of `FÉt_X` is `𝟙 X`, and a fibre product of finite étale covers is again one
because the projection to one factor is a base change of a morphism of covers, which is itself
finite étale by cancellation. Base change is then exact because it commutes with the fully
faithful forgetful functor to `Over X`, where base change is a right adjoint.

The right-exactness half of Tag 0BN9 — finite colimits of `FÉt_X`, and their fpqc-local
description used in Tag 0BNA — is recorded here as the class
`HasFiniteColimitsWithLocalCoequalizers`, whose instance is constructed downstream in
`StacksFrontier/AlgebraicGeometry/FiniteEtaleColimits/LocalCoequalizer.lean`; see the implementation
notes.

## Main definitions

* `Stacks.FundamentalGroup.HasFiniteColimitsWithLocalCoequalizers` — finite colimits of
  `FÉt_X` together with the fpqc-local description of their coequalizers.

## Main results

* `Stacks.FundamentalGroup.hasFiniteLimits_finiteEtaleOver` — `FÉt_X` has finite limits.
* `Stacks.FundamentalGroup.preservesFiniteLimits_finiteEtaleBaseChange` — base change of
  finite étale covers preserves finite limits.
* `Stacks.FundamentalGroup.finiteEtaleBaseChangeForgetIso` — base change commutes with the
  forgetful functor to `Over X`, by the identity of the chosen pullbacks.

## Implementation notes

Finite étale covers are represented by `MorphismProperty.Over finiteEtale ⊤ X` rather than by
a bespoke structure, so that Mathlib's limit API for subcategories of `Over X` defined by a
morphism property applies directly. Exactness is stated as preservation of finite limits, so
that it is available to typeclass search.

The coequalizer of two morphisms `a, b : Z ⟶ Y` of finite étale covers is the relative
spectrum of the equalizer of `a^♯, b^♯ : 𝓑 ⟶ 𝓒`, and the proof that it is again finite étale
proceeds by passing to an étale covering of `X` over which both `Y` and `Z` become finite
disjoint unions of copies of the base (Stacks Tag 04HN,
`Stacks.Etale.exists_etale_pullback_iso_sigma`), where the equalizer is the algebra indexed by the
set-theoretic coequalizer. That construction is
`Stacks.FundamentalGroup.isColimit_finiteEtaleCofork` and the fpqc-local description of its
coequalizers is `Stacks.FundamentalGroup.hasFiniteColimitsWithLocalCoequalizers`; both are
downstream of this file, which is why the class is declared here and instantiated there.

## References

* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The forgetful functor from finite étale covers of `X` to schemes over `X`. -/
abbrev finiteEtaleOverForgetOver (X : Scheme.{u}) : FiniteEtaleOver X ⥤ Over X :=
  MorphismProperty.Over.forget finiteEtale ⊤ X

/-- The forgetful functor from finite étale covers of `X` to schemes. -/
abbrev finiteEtaleOverForget (X : Scheme.{u}) : FiniteEtaleOver X ⥤ Scheme.{u} :=
  finiteEtaleOverForgetOver X ⋙ Over.forget X

end AlgebraicGeometry

namespace Stacks.FundamentalGroup

/-- The finite-colimit structure of Tag 0BN9, including the fpqc-local property of its
coequalizers which is what Tag 0BNA uses. The covering is a covering of the underlying scheme
of the coequalizer, obtained by pulling back a trivializing covering of the base; its index
universe is that of the schemes involved, as for a covering indexed by points of the base. -/
class HasFiniteColimitsWithLocalCoequalizers (X : Scheme.{u}) : Prop
    extends HasFiniteColimits (FiniteEtaleOver X) where
  /-- The underlying cofork of schemes is a coequalizer over each member of an fpqc covering
  of its target and over each pairwise overlap, for the canonical base-changed coforks of
  Tag 0BMN. -/
  exists_fpqcCover_isColimit_baseChangeCofork
    {Y Z : FiniteEtaleOver X} (a b : Y ⟶ Z) (c : Cofork a b) (hc : IsColimit c) :
    ∃ (𝒰 : Scheme.Cover.{u} Scheme.fpqcPrecoverage c.pt.left),
      (∀ i, Nonempty (IsColimit (baseChangeCofork a.left b.left c.π.left
        (congrArg (fun k => k.left) c.condition) (𝒰.f i)))) ∧
      (∀ i j, Nonempty (IsColimit (baseChangeCofork a.left b.left c.π.left
        (congrArg (fun k => k.left) c.condition)
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i))))

/-- **Stacks Project, Tag 0BN9.** The category of finite étale schemes over a scheme has
finite limits. -/
-- One of the four clause sites of 0BN9. Three of them are proved — this one, the base-change
-- clause below, and the finite-colimit clause
-- `Stacks.FundamentalGroup.hasFiniteColimitsWithLocalCoequalizers` of
-- `FiniteEtaleColimits/LocalCoequalizer.lean` — and the fourth, that base change preserves
-- finite colimits, is open for a general morphism; the tag is therefore PARTIAL.
@[stacks 0BN9 "finite limits"]
noncomputable instance hasFiniteLimits_finiteEtaleOver (X : Scheme.{u}) :
    HasFiniteLimits (FiniteEtaleOver X) :=
  MorphismProperty.Over.hasFiniteLimits _ X

/-- The canonical comparison between base change and forgetting finite étaleness. As a natural
isomorphism it identifies both objects and arrows. -/
noncomputable def finiteEtaleBaseChangeForgetIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteEtaleBaseChange f ⋙ MorphismProperty.Over.forget finiteEtale ⊤ X ≅
      MorphismProperty.Over.forget finiteEtale ⊤ Y ⋙ Over.pullback f :=
  MorphismProperty.Over.pullbackCompForgetIso f

/-- The base-change comparison uses the identity of the chosen pullback, so it preserves the
specified cofork maps under forgetting. -/
theorem finiteEtaleBaseChangeForgetIso_hom_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Z : FiniteEtaleOver Y) :
    (finiteEtaleBaseChangeForgetIso f).hom.app Z = 𝟙 _ := rfl

/-- **Stacks Project, Tag 0BN9.** Base change of finite étale schemes preserves finite
limits. -/
@[stacks 0BN9 "base change preserves finite limits"]
noncomputable instance preservesFiniteLimits_finiteEtaleBaseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (finiteEtaleBaseChange f) :=
  inferInstanceAs (PreservesFiniteLimits
    (MorphismProperty.Over.pullback (finiteEtale : MorphismProperty Scheme.{u}) ⊤ f))

end Stacks.FundamentalGroup
