module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRestrictionRightExactAll
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison

/-!
# Part (10) of Stacks 06VE on the big `τ`-site of a scheme, at every `τ`

Part (10) of Descent, Lemma 06VE says that given a short exact sequence
`0 → 𝓕₁ᵃ → 𝓔 → 𝓕₂ᵃ → 0` of `𝒪`-modules on a site of `S`, the middle term `𝓔` is itself an `𝓕ᵃ`
for a quasi-coherent `𝒪_S`-module `𝓕` — in the source's words, "`𝓔` is quasi-coherent, i.e. `𝓔`
is in the essential image of the functor".  **This file proves it on the big site `(Sch/S)_τ`,
at every `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`, with no hypothesis.**

## What was left to do

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionClosure.lean` carries out
the
source's three steps on the big `τ`-site, over two hypotheses, and both are now theorems:

* `AlgebraicGeometry.BigFppfOver.isIso_baseCounit_app_X₂` — step 3, the counit
  `ε^*ε_*𝓔 → 𝓔` is an isomorphism — and
  `AlgebraicGeometry.BigFppfOver.isQuasicoherent_baseRestrictModule_X₂` — step 2, `ε_*𝓔` is
  quasi-coherent on `S` — are proved there;
* essential surjectivity of `𝓕 ↦ 𝓕ᵃ`, Descent, Proposition 03DX (1), is
  `AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule`;
* right exactness of restriction to `S_Zar`, the source's `H¹(U, 𝓕₁) = 0` step of Descent,
  Proposition 03DW, is `AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_all`.

So what is left of the clause is its restatement in the essential-image form the source uses,
and the two statements of this file are that restatement.  The reading of the clause as
"the middle term is quasi-coherent" is a different sentence, naming no functor, and is clause (4)
of Stacks 0GNC: `AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_shortExact_X₂_all`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseRestrictionRightExactAll.lean`),
which carries that tag and not this one.

## The sections description, and why both forms are stated

Stacks Definition 03DU (3) defines `𝓕ᵃ` **by its sections**, `(f : T → S) ↦ Γ(T, f^*𝓕)`, whereas
`AlgebraicGeometry.BigFppfOver.baseAssociatedModule` is the pullback of sheaves of modules along
the morphism of ringed sites of Remark 03FH.  As the faithfulness note of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Functor` records, **every statement of
Tags 03DV, 0GN7, 03DX and 06VE is about the sections description**, so each of them reads through
the identification of the two.  On the big sites that identification is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, Stacks 070S (1), which holds at
every `τ` and for an arbitrary `𝒪_S`-module.  Accordingly the clause is proved here in both
readings: `AlgebraicGeometry.BigFppfOver.essImage_X₂_of_shortExact_big` for the pullback-defined
functor and `AlgebraicGeometry.BigFppfOver.exists_isoSections_X₂_of_shortExact_big` for the
sheaf the source constructs, with the explicit comparison
`AlgebraicGeometry.BigFppfOver.sectionsIso_X₂_of_shortExact_big` between the middle term and the
sections-defined `(ε_*𝓔)ᵃ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.essImage_X₂_of_shortExact_big`: **Stacks 06VE (10) on the big
  site `(Sch/S)_τ` at every `τ`**, for the pullback-defined `𝓕 ↦ 𝓕ᵃ` of Remark 03FH.
* `AlgebraicGeometry.BigFppfOver.sectionsIso_X₂_of_shortExact_big`: the middle term is the
  sheafification of the pullback-sections presheaf of `ε_*𝓔`.
* `AlgebraicGeometry.BigFppfOver.exists_isoSections_X₂_of_shortExact_big`: **Stacks 06VE (10) on
  the big site `(Sch/S)_τ` at every `τ`, for the sections-defined `𝓕ᵃ`** of Definition 03DU (3).

## Implementation notes

The witness of the essential image is `ε_*𝓔 = (baseRestrictModule B S hS τ).obj C.X₂` and the
isomorphism is the counit at `C.X₂`, inverted; nothing else is used, both facts about it coming
from `BaseExtensionClosure`.  The hypotheses on the outer terms are stated as quasi-coherence on
the site rather than as membership of the essential image, which is the source's own hypothesis
("`𝓕₁ᵃ` and `𝓕₂ᵃ`") read through Descent, Proposition 03DX (1); the two are interchangeable at
every `τ` by `baseQuasicoherentIsEssImageAssociatedModule` in one direction and
`AlgebraicGeometry.BigFppfOver.isQuasicoherentOnSite_baseAssociatedModule_of_isQuasicoherent`,
Stacks 03DV (1), in the other.

## References

* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 0GNC](https://stacks.math.columbia.edu/tag/0GNC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06VE (10) on the big site `(Sch/S)_τ`, at every
`τ ∈ {Zariski, étale, smooth, syntomic, fppf}` and with no hypothesis.**  Given a short exact
sequence `0 → 𝓕₁ᵃ → 𝓔 → 𝓕₂ᵃ → 0` of `𝒪`-modules on `(Sch/S)_τ` whose outer terms are
quasi-coherent — which at every `τ` is the same as their being `𝓕ᵃ`'s, by Descent,
Proposition 03DX (1) — the middle term `𝓔` is itself in the essential image of
`𝓕 ↦ 𝓕ᵃ : QCoh(𝒪_S) ⥤ Mod((Sch/S)_τ, 𝒪)`, namely of `𝓔|_{S_Zar}`.

The source's three steps are
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/BaseExtensionClosure.lean`; of the two
hypotheses they carry, essential surjectivity is
`AlgebraicGeometry.BigFppfOver.baseQuasicoherentIsEssImageAssociatedModule` and right
exactness of restriction to `S_Zar` is
`AlgebraicGeometry.BigFppfOver.epi_baseRestrictModule_map_all`.

This is the clause for the *pullback*-defined `𝓕 ↦ 𝓕ᵃ` of Remark 03FH;
`AlgebraicGeometry.BigFppfOver.exists_isoSections_X₂_of_shortExact_big` is it for the
sections-defined `𝓕ᵃ` of Definition 03DU (3), which is the sheaf the source constructs. -/
@[stacks 06VE "part (10), big site (Sch/S)_τ at every τ ∈ {Zariski, étale, smooth, syntomic, \
fppf}, for the PULLBACK-defined functor 𝓕 ↦ 𝓕ᵃ of Remark 03FH.  The same clause for the \
sections-defined 𝓕ᵃ of Definition 03DU (3) is exists_isoSections_X₂_of_shortExact_big; the two \
sheaves are identified by baseAssociatedModuleIsoSections, Stacks 070S (1).  The clause read as \
\"the middle term is quasi-coherent\", which names no functor, is clause (4) of Stacks 0GNC and \
sits on isQuasicoherentOnSite_shortExact_X₂_all"]
public theorem essImage_X₂_of_shortExact_big (τ : SiteKind)
    {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    (baseAssociatedModuleQcoh B S hS τ).essImage C.X₂ := by
  have h₁' := baseQuasicoherentIsEssImageAssociatedModule B S hS τ _ h₁
  have h₃' := baseQuasicoherentIsEssImageAssociatedModule B S hS τ _ h₃
  have hepi := epi_baseRestrictModule_map_all B S hS τ hC h₁
  have := isIso_baseCounit_app_X₂ hC h₁' h₃' hepi
  exact ⟨⟨(baseRestrictModule B S hS τ).obj C.X₂,
      isQuasicoherent_baseRestrictModule_X₂ hC h₁' h₃' hepi⟩,
    ⟨asIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app C.X₂)⟩⟩

/-- **The middle term of such a sequence, identified with the sections-defined `𝓕ᵃ` of its own
restriction.**  The counit `ε^*ε_*𝓔 → 𝓔` is an isomorphism by
`AlgebraicGeometry.BigFppfOver.isIso_baseCounit_app_X₂`, and
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections` — Stacks 070S (1), at every `τ`
and for an arbitrary `𝒪_S`-module — rewrites `ε^*(ε_*𝓔)` as the `τ`-sheafification of the
pullback-sections presheaf `(f : T → S) ↦ Γ(T, f^*(ε_*𝓔))` of Stacks 03DS, which is the sheaf
Definition 03DU (3) calls `(ε_*𝓔)ᵃ`.

The quasi-coherence of `ε_*𝓔` is carried as an instance argument because the *statement* needs
it: `AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules` is only defined on a
quasi-coherent `𝒪_S`-module, so the right-hand side does not elaborate without it.  It is not an
extra assumption — `AlgebraicGeometry.BigFppfOver.isQuasicoherent_baseRestrictModule_X₂`
derives it from `hC`, `h₁` and `h₃`, and that is how
`AlgebraicGeometry.BigFppfOver.exists_isoSections_X₂_of_shortExact_big` discharges it. -/
public noncomputable def sectionsIso_X₂_of_shortExact_big (τ : SiteKind)
    {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite)
    [SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf)
      ((baseRestrictModule B S hS τ).obj C.X₂)] :
    C.X₂ ≅ (PresheafOfModules.sheafification.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).obj
      (sectionsPresheafOfModules B S hS ((baseRestrictModule B S hS τ).obj C.X₂)) :=
  have h₁' := baseQuasicoherentIsEssImageAssociatedModule B S hS τ _ h₁
  have h₃' := baseQuasicoherentIsEssImageAssociatedModule B S hS τ _ h₃
  have hepi := epi_baseRestrictModule_map_all B S hS τ hC h₁
  have := isIso_baseCounit_app_X₂ hC h₁' h₃' hepi
  (asIso ((baseAssociatedModuleAdjunction B S hS τ).counit.app C.X₂)).symm ≪≫
    baseAssociatedModuleIsoSections B S hS τ ((baseRestrictModule B S hS τ).obj C.X₂)

/-- **Stacks 06VE (10) on the big site `(Sch/S)_τ` at every `τ`, for the sheaf the source
constructs.**  Given a short exact sequence `0 → 𝓕₁ᵃ → 𝓔 → 𝓕₂ᵃ → 0` of `𝒪`-modules on
`(Sch/S)_τ` whose outer terms are quasi-coherent, there is a quasi-coherent `𝒪_S`-module `𝓕` with
`𝓔 ≅ 𝓕ᵃ`, where `𝓕ᵃ` is the **sections**-defined associated module of Stacks Definition 03DU (3)
— the `τ`-sheafification of `(f : T → S) ↦ Γ(T, f^*𝓕)`.

`AlgebraicGeometry.BigFppfOver.essImage_X₂_of_shortExact_big` is the same clause for the
pullback-defined `𝓕ᵃ` of Remark 03FH; this is it read through
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSections`, Stacks 070S (1).  The witness is
`𝓕 = 𝓔|_{S_Zar}`, quasi-coherent by
`AlgebraicGeometry.BigFppfOver.isQuasicoherent_baseRestrictModule_X₂`, and the isomorphism is
`AlgebraicGeometry.BigFppfOver.sectionsIso_X₂_of_shortExact_big`. -/
@[stacks 06VE "part (10), big site (Sch/S)_τ at every τ ∈ {Zariski, étale, smooth, syntomic, \
fppf}, for the SECTIONS-defined 𝓕ᵃ of Definition 03DU (3) — the τ-sheafification of \
(f : T → S) ↦ Γ(T, f^*𝓕).  The same clause for the pullback-defined functor of Remark 03FH is \
essImage_X₂_of_shortExact_big; the two sheaves are identified by baseAssociatedModuleIsoSections, \
Stacks 070S (1)"]
public theorem exists_isoSections_X₂_of_shortExact_big (τ : SiteKind)
    {C : ShortComplex (SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B S hS τ))}
    (hC : C.ShortExact) (h₁ : C.X₁.IsQuasicoherentOnSite) (h₃ : C.X₃.IsQuasicoherentOnSite) :
    ∃ F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory,
      Nonempty (C.X₂ ≅ (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).obj
        (sectionsPresheafOfModules B S hS F.obj)) :=
  have h₁' := baseQuasicoherentIsEssImageAssociatedModule B S hS τ _ h₁
  have h₃' := baseQuasicoherentIsEssImageAssociatedModule B S hS τ _ h₃
  have hepi := epi_baseRestrictModule_map_all B S hS τ hC h₁
  have := isQuasicoherent_baseRestrictModule_X₂
    hC h₁' h₃' hepi
  ⟨⟨(baseRestrictModule B S hS τ).obj C.X₂, this⟩,
    ⟨sectionsIso_X₂_of_shortExact_big B S hS τ hC h₁ h₃⟩⟩

end BigFppfOver

end AlgebraicGeometry

end
