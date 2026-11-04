module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementRestrFun

/-!
# Stacks 03DX (1), essential surjectivity at `τ = fppf`, with no hypothesis left

`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/EffectiveGlueAgreementRestrFun.lean`
proves `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_fpqc`: a sheaf of modules
`𝒢` on `(Sch/S)_fppf` lies in the essential image of `𝓕 ↦ 𝓕^a` as soon as there is a family
`X : I → (Sch/S)_fppf` which

* covers the final object,
* whose structure morphisms `X i ⟶ S` are an **fpqc** covering family of the scheme `S`, and
* on whose members the restriction of `𝒢` is the associated module of a quasi-coherent sheaf.

Quasi-coherence of `𝒢` supplies a family satisfying the first and third conditions and *not* the
second: the members of a covering family of the final object of the big fppf category over `S`
are arbitrary schemes over `S`, so their structure morphisms need not even be flat.  This file
supplies the second condition, and so discharges the last hypothesis of the essential
surjectivity half of Stacks 03DX (1) for `τ = fppf`.

The refinement is `AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement`, which is
unconditional: the sieve of objects of a covering family of the final object is a covering sieve,
and Stacks 021R/021S produce inside any covering sieve of `S` a family of morphisms of schemes
that is flat, locally of finite presentation and jointly surjective.  What has to be checked is
that the third condition survives the refinement, and it does for a reason with no descent in it:
each member `Y j` of the refinement admits a morphism to a member `X i` of the original family,
and a global presentation restricts along an arrow of the site
(`Stacks.SheafOfModules.hasGlobalPresentation_overMap`), so the *local step* of Stacks 03DX (1)
— `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_objRestrict`, itself
unconditional — applies at `Y j` directly.  The local associated modules of the refinement are
therefore built from scratch rather than transported from those of `X`.

## Main results

* `AlgebraicGeometry.BigFppfOver.hasGlobalPresentation_over_of_refines`: a global presentation of
  the restriction of `𝒢` to a member of a covering family restricts to any object mapping into
  that member.
* `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_isQuasicoherentOnSite`:
  **a quasi-coherent module on `(Sch/S)_fppf` is an `𝓕^a`**, with no hypothesis.
* `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule'`:
  the same, packaged as
  `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` — **the hypothesis
  that the Stacks 0GNC, 0GNE, 03DX and 06VE statements of this directory were conditional on, as
  a theorem.**

## Implementation notes

Nothing here carries a `stacks` attribute.  The statement proved is the essential surjectivity
half of Stacks 03DX (1) at `τ = fppf`; Stacks 03DX is stated for all five topologies and has a
second clause, and its registration belongs with the full statement rather than with this one
input to it.  Consumers that register a tag on the strength of this theorem say so themselves.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A global presentation of a restriction of `𝒢` restricts further.**  If the restriction of
`𝒢` to the localization of `(Sch/S)_fppf` at `T` has a global presentation and `Z` maps to `T`,
then the restriction of `𝒢` to the localization at `Z` has one too.  This is
`Stacks.SheafOfModules.hasGlobalPresentation_overMap`, read at the big fppf site of `S`. -/
public theorem hasGlobalPresentation_over_of_refines
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {Z T : BigFppfOver B S hS} (f : Z ⟶ T)
    (h : (G.over T).HasGlobalPresentation) : (G.over Z).HasGlobalPresentation :=
  Stacks.SheafOfModules.hasGlobalPresentation_overMap G f h

/-- **Stacks 03DX (1), essential surjectivity, for `τ = fppf`, with no hypothesis.**  Every
quasi-coherent `𝒪`-module on the big fppf site of a scheme `S` is isomorphic to the associated
module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`.

Quasi-coherence (Stacks 03DL (6)) gives, through Stacks 03DN, a family `X` covering the final
object of `(Sch/S)_fppf` on whose members the restriction of `𝒢` has a global presentation.
`AlgebraicGeometry.BigFppfOver.exists_coversTop_fpqc_refinement` refines `X` to a family `Y`
which again covers the final object and whose structure morphisms are an fpqc covering family of
`S`; the global presentations restrict to the members of `Y` because each maps into a member of
`X`, and the unconditional local step turns each into an associated module.  The gluing step
`AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_fpqc` — the effectivity of fpqc
descent for quasi-coherent sheaves (Stacks 023T) together with the sheaf property of `SheafHom`
(Stacks 03EM) — then applies to `Y`. -/
public theorem essImage_associatedModuleQcoh_of_isQuasicoherentOnSite
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u} G) :
    (associatedModuleQcoh B S hS).essImage G := by
  classical
  obtain ⟨I, X, hX, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).1 hG
  obtain ⟨J, Y, hY, hfpqc, hre⟩ := exists_coversTop_fpqc_refinement B S hS X hX
  have hPY : ∀ j, (G.over (Y j)).HasGlobalPresentation := by
    intro j
    obtain ⟨i, ⟨f⟩⟩ := hre j
    exact hasGlobalPresentation_over_of_refines B S hS G f (hP i)
  choose F hF e using fun j =>
    exists_isQuasicoherent_iso_associatedModule_objRestrict B S hS (Y j) (hPY j)
  exact essImage_associatedModuleQcoh_of_fpqc B S hS Y G F hF (fun j => (e j).some) hY hfpqc

end AlgebraicGeometry.BigFppfOver

end
