module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalPresentationObstruction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.QuasicoherentColimitsOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence

/-!
# The globalization step of Stacks 03DX (1): from local presentations to `𝓕 ↦ 𝓕^a`

The essential-surjectivity half of Stacks 03DX (1) says that a quasi-coherent `𝒪`-module `𝒢` on
the big fppf site of a scheme `S` is `𝓕^a` for a quasi-coherent `𝒪_S`-module `𝓕`.  The source's
proof has two steps.  The *local* step is the first paragraph: a module presented on the site as
a cokernel `⊕_{I₂} 𝒪 ⟶ ⊕_{I₁} 𝒪 ⟶ 𝒢 ⟶ 0` of a morphism of free modules is `𝓕^a`, with `𝓕` the
cokernel of the morphism of free `𝒪_S`-modules that full faithfulness (Stacks 0GN7) produces
downstairs; that step is
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree'` and
is unconditional.  The *global* step is the rest: quasi-coherence, Stacks 03DL (6), only gives
such presentations on the members of a covering family of `S`, and the source glues them with
the effectivity of descent for quasi-coherent sheaves (Stacks 023T) together with the sheaf
property of `SheafHom` (Stacks 03EM).

This file does three things.  It restates the local step in terms of Mathlib's
`SheafOfModules.Presentation`, which is the exact datum that `SheafOfModules.QuasicoherentData`
carries on each member of a covering and is therefore the form in which the global step will
hand it over.  It names the global step as a single hypothesis,
`AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal`.  And it derives Stacks
03DX (1)'s essential surjectivity,
`AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule`, from that hypothesis
alone, by rewriting quasi-coherence into the shape the descent argument consumes — a covering
family of the final object of `(Sch/S)_fppf` together with a global presentation of the
restriction of `𝒢` to each member — with Stacks 03DN.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal`: **the globalization step of
  Stacks 03DX (1)** as a hypothesis — a module on `(Sch/S)_fppf` whose restrictions to the
  members of some covering family of the final object have global presentations is `𝓕^a` for a
  quasi-coherent `𝒪_S`-module `𝓕`.  This is the appeal to Stacks 023T and Stacks 03EM.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_presentation`
  and `AlgebraicGeometry.BigFppfOver.essImage_associatedModuleQcoh_of_presentation`: **the local
  step of Stacks 03DX (1) at a `SheafOfModules.Presentation`**, unconditionally.
* `AlgebraicGeometry.BigFppfOver.quasicoherentIsEssImageAssociatedModule`: **Stacks 03DX (1),
  essential surjectivity, over the globalization step** — every quasi-coherent module on
  `(Sch/S)_fppf` is in the essential image of `𝓕 ↦ 𝓕^a`.
* `AlgebraicGeometry.BigFppfOver.essImageAssociatedModuleQcohLocal_iff`: the hypothesis is not a
  strengthening — it is *equivalent* to the conclusion.  So nothing is lost by reformulating
  Stacks 03DX (1) in the shape the descent argument consumes, and nothing is smuggled in either.

## Implementation notes

The index type of the covering family is `Type (u + 1)`, the universe of the objects of
`(Sch/S)_fppf`, because that is what Stacks 03DN
(`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation`) produces
and what `SheafOfModules.QuasicoherentData` indexes its covering family by on this site.

The hypothesis is stated with `SheafOfModules.HasGlobalPresentation` on the members, not with
Mathlib's `SheafOfModules.Presentation`, and this is forced.  A global presentation on the big
fppf site of `S` indexes its coproducts by types in `Type (u + 1)`, whereas
`SheafOfModules.free` on this site is indexed by `Type u`; the two notions are identified by
`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections` only under
`UnivLE.{max u v r, r}`, which here reads `UnivLE.{u + 1, u}` and is false by
`not_univLE_succ`.  Quasi-coherence therefore delivers global presentations and not
`SheafOfModules.Presentation`s, so the hypothesis has to accept the former; the local step above
consumes the latter, and closing the gap between them is part of what the globalization step has
to do — the source does it by passing to the big site of each member of the covering, where the
presentation is again a presentation of a module whose sections are `Type u`-small.  See the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalPresentationObstruction`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03DX (1), essential surjectivity, local step, at a `SheafOfModules.Presentation`.**
A sheaf of modules on the big fppf site of `S` carrying a presentation in Mathlib's sense is the
associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`.

A `SheafOfModules.Presentation` of `G` is exactly a cokernel presentation of `G` by free modules
indexed at `Type u`: its `SheafOfModules.Presentation.isColimit` exhibits `G` as the cokernel of
the composite of the morphism named by the relations with the kernel inclusion.  So this is
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree'`
read at that datum, and like it it is unconditional. -/
public theorem exists_isQuasicoherent_iso_associatedModule_of_presentation
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (P : G.Presentation) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((associatedModule B S hS).obj G' ≅ G) :=
  exists_isQuasicoherent_iso_associatedModule_of_cokernelFree' B S hS
    ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)
    (by simp) P.isColimit

/-- **Stacks 03DX (1), essential surjectivity, local step**, in the form of a membership in the
essential image of the functor `QCoh(𝒪_S) ⥤ Mod((Sch/S)_fppf, 𝒪)` of Stacks 06VE. -/
public theorem essImage_associatedModuleQcoh_of_presentation
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (P : G.Presentation) :
    (associatedModuleQcoh B S hS).essImage G := by
  obtain ⟨G', hG', h⟩ := exists_isQuasicoherent_iso_associatedModule_of_presentation B S hS P
  exact ⟨⟨G', hG'⟩, h⟩

/-- **The globalization step of Stacks 03DX (1) for `τ = fppf`**, as a hypothesis: a sheaf of
modules on `(Sch/S)_fppf` whose restriction to each member of some covering family of the final
object has a global presentation is the associated module `𝓕^a` of a quasi-coherent
`𝒪_S`-module `𝓕`.

This is the second half of the source's proof, the half that is not local: having produced local
presentations from quasi-coherence (Stacks 03DL (6)) and hence, on each member, an isomorphism
with some `(𝓕_i)^a` by the local step, the source turns the canonical gluing isomorphisms of `𝒢`
into gluing isomorphisms of the `𝓕_i` by full faithfulness of `𝓕 ↦ 𝓕^a` (Stacks 0GN7), glues
them to a quasi-coherent `𝓕` on `S` by the effectivity of descent for quasi-coherent sheaves
(Stacks 023T), and assembles the local isomorphisms `𝓕^a|_{(Sch/S_i)} ≅ 𝒢|_{(Sch/S_i)}` into a
global one because `SheafHom(𝓕^a, 𝒢)` is a sheaf (Stacks 03EM). -/
public abbrev EssImageAssociatedModuleQcohLocal : Prop :=
  ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (I : Type (u + 1))
      (X : I → BigFppfOver B S hS), (topology B S hS).CoversTop X →
      (∀ i, (G.over (X i)).HasGlobalPresentation) →
    (associatedModuleQcoh B S hS).essImage G

/-- **Stacks 03DX (1), essential surjectivity, for `τ = fppf`, over the globalization step.**
Every quasi-coherent `𝒪`-module on the big fppf site of `S` is isomorphic to `𝓕^a` for a
quasi-coherent `𝒪_S`-module `𝓕`.

This is the hypothesis of `AlgebraicGeometry.BigFppfOver.isEquivalence_associatedModuleQcohOnSite`,
derived from `AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal`.  The proof is the
translation of quasi-coherence, which is a local condition at *every* object of the site, into
the single covering family of the *final* object that the descent argument needs; that
translation is Stacks 03DN. -/
public theorem quasicoherentIsEssImageAssociatedModule
    (h : EssImageAssociatedModuleQcohLocal B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS := by
  intro G hG
  obtain ⟨I, X, hX, hP⟩ :=
    (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).1 hG
  exact h G I X hX hP

/-- The globalization step is *implied* by the conclusion it is used for: a module with global
presentations on a covering family of the final object is quasi-coherent, again by Stacks 03DN.
So `AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohLocal` is not a strengthening of
Stacks 03DX (1)'s essential surjectivity. -/
public theorem essImageAssociatedModuleQcohLocal_of_quasicoherentIsEssImage
    (h : QuasicoherentIsEssImageAssociatedModule B S hS) :
    EssImageAssociatedModuleQcohLocal B S hS := fun G I X hX hP =>
  h G ((Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_hasGlobalPresentation G).2
    ⟨I, X, hX, hP⟩)

/-- **The globalization step and Stacks 03DX (1)'s essential surjectivity are equivalent.**  The
hypothesis named in this file is therefore exactly the content that the appeal to Stacks 023T
supplies, reformulated so that a covering family of `S` and local presentations are available to
whoever discharges it. -/
public theorem essImageAssociatedModuleQcohLocal_iff :
    EssImageAssociatedModuleQcohLocal B S hS ↔
      QuasicoherentIsEssImageAssociatedModule B S hS :=
  ⟨quasicoherentIsEssImageAssociatedModule B S hS,
    essImageAssociatedModuleQcohLocal_of_quasicoherentIsEssImage B S hS⟩

end BigFppfOver

end AlgebraicGeometry

end
