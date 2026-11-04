module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssSurjReduction
public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcompose
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# The small étale localization as an equivalence of ringed sites

`AlgebraicGeometry.SmallEtale.localizationEquivalence` identifies the small étale site of the
scheme `Y` of an object `U` of the small étale site of `S` with the localization `S_étale/U`.
That statement is about *sites* only: it carries a comparison of topologies
(`AlgebraicGeometry.SmallEtale.localizationEquivalence_topology`) and of the functors to the big
étale site (`AlgebraicGeometry.SmallEtale.localizationEquivalence_restriction`), and no
structure-sheaf or module content whatsoever.

**This file upgrades it to an equivalence of ringed sites and then to an equivalence of the
categories of sheaves of modules.**  The structure sheaves match *on the nose*:
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence` is a `rfl`, because both
structure sheaves send an object to the global functions on its underlying scheme and
post-composition with the structure morphism of `U` does not change that scheme.  With the two
ringed sites so identified, the generic transport machinery of
`StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence` applies: global
presentations and quasi-coherence travel in both directions, and a module on `S_étale` may be
read as a module on `Y_étale`.

That crossover is what the globalization step
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue` was missing.  The step as stated in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleEssSurjReduction.lean:132`
hypothesises *global presentations* of `𝒢|_{S_étale/X_i}`, which stays inside the slice; the
source's proof instead wants, on each member, a quasi-coherent module `𝓕_i` on the *scheme*
`X_i` with `(𝓕_i)^a ≅ 𝒢|_{(X_i)_étale}`.  Passing from the first to the second is exactly the
crossover, and it is discharged here, unconditionally.  The residue that remains is therefore
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleQcohGlue`, which mentions no presentation
of any kind.

The whole file is the small étale counterpart of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/MemberLocalStep.lean`, which does the
same for the big fppf site; the names mirror the ones there.  What is étale-specific is the
equivalence of sites itself: on the big site it is Mathlib's
`CategoryTheory.Over.iteratedSliceEquiv`, whereas here it is
`AlgebraicGeometry.SmallEtale.localizationEquivalence`, whose inverse exists because a scheme
étale over `S` with a morphism to `U` is étale over `U`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.objScheme` and `AlgebraicGeometry.SmallEtale.contains_objScheme`:
  the scheme underlying an object of the small étale site of `S`, and its membership in the site.
* `AlgebraicGeometry.SmallEtale.objRestrictFunctor` and
  `AlgebraicGeometry.SmallEtale.objRestrictEquivalence`: reindexing along the localization
  equivalence, as a functor and as an **equivalence of the categories of sheaves of modules**
  `Mod(S_étale/U, 𝒪) ≌ Mod(Y_étale, 𝒪)`.
* `AlgebraicGeometry.SmallEtale.objRestrict`: **the crossover** — restriction of a module on
  `S_étale` to the small étale site of the scheme of `U`.
* `AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleQcohGlue`: the residue of the
  globalization step of Stacks 03DX (2) at `τ = étale`, with the local step discharged: a module
  on `S_étale` whose crossover restriction to each member of some covering family of the final
  object is an associated module *there* is itself an `𝓕^a`.

## Main results

* `AlgebraicGeometry.SmallEtale.isDenseSubsite_localizationEquivalence_inverse`: the two
  topologies correspond under the localization equivalence.
* `AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`: **the localization
  equivalence is an equivalence of ringed sites, on the nose** — by `rfl`.
* `AlgebraicGeometry.SmallEtale.hasGlobalPresentation_objRestrict` and
  `AlgebraicGeometry.SmallEtale.hasGlobalPresentation_of_objRestrict`: global presentations
  cross over, in both directions.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_objRestrict_iff`: so does quasi-coherence.
* `AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_objRestrict` and
  `AlgebraicGeometry.SmallEtale.essImage_associatedModule_objRestrict`: **the local step of
  Stacks 03DX (2) at `τ = étale`, at an arbitrary object of the small étale site**,
  unconditionally — a global presentation on the slice at `U` produces a quasi-coherent module
  on the *scheme* of `U` whose associated module is the crossover restriction.
* `AlgebraicGeometry.SmallEtale.essImageAssociatedModuleGlue_of_qcohGlue` and
  `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule_of_qcohGlue`: the
  globalization step, and hence essential surjectivity, over the new residue alone.
* `AlgebraicGeometry.SmallEtale.essImageAssociatedModuleQcohGlue_iff`: the new residue is
  *equivalent* to essential surjectivity, so this reduction neither loses content nor smuggles
  any in.

## Implementation notes

Nothing here carries a `stacks` attribute.  Every statement that would be a clause of Stacks
03DX is still conditional on the residue, and a hypothesis is part of a citation; the
unconditional statements below — the ringed comparison, the transport of presentations and
quasi-coherence, the local step — are inputs to that clause rather than the clause itself, and
the clause of Stacks 04M0/04M1 they resemble is about algebraic spaces, not about an object of
the small étale site of a scheme.

`AlgebraicGeometry.SmallEtale.isDenseSubsite_localizationEquivalence_inverse` is obtained from
`AlgebraicGeometry.SmallEtale.localizationEquivalence_topology` and Mathlib's instance
`CategoryTheory.Equivalence.instIsDenseSubsiteFunctorInducedTopology` read at the symmetric
equivalence, not from cover preservation: the two cover-preservation lemmas inside
`StacksFrontier/AlgebraicGeometry/Etale/SmallEtalePostcompose.lean` are `private`, and the public
topology comparison is all that is needed.

`AlgebraicGeometry.SmallEtale.objRestrict` is spelled with
`SheafOfModules.pushforward (𝟙 (Stacks.SheafOfModules.reindexRing …))` rather than through
`AlgebraicGeometry.SmallEtale.objRestrictEquivalence`, even though the two are the same functor
(`AlgebraicGeometry.SmallEtale.objRestrictEquivalence_functor`): that is the exact shape in
which `Stacks.SheafOfModules.hasGlobalPresentation_reindex` and
`Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` state their conclusions, so the
transports need no bridging isomorphism.

The index type of the covering family is `Type (u + 1)`, the universe of the objects of the
small étale site, matching
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue`.

## What this does not give

It does **not** discharge the residue.  What is left is the part of the source's proof that is
not local: turning the canonical isomorphisms of `𝒢` over the fibre products `X_i ×_S X_j` into
a descent datum on the `𝓕_i` by full faithfulness of `𝓕 ↦ 𝓕^a`, gluing that datum by the
effectivity of descent for quasi-coherent modules (Stacks 023T, proved unconditionally as
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`), and assembling the
local isomorphisms by the sheaf property of `SheafHom` (Stacks 03EM).

The missing input for the first of those is a comparison of the associated-module functor with
base change along a morphism of the small étale site — Stacks 03DV at an arbitrary morphism.
The library has it only for an *open* of `S`,
`AlgebraicGeometry.SmallEtale.associatedModuleOverObjIso`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleOpenCoverQuasicoherence.lean`
`:261`), and even there the target is the slice ringed site rather than the small étale site of
the open subscheme.  Without that comparison the transition isomorphisms of the descent datum
cannot be written down, which is the same obstruction the big fppf site meets in
`AlgebraicGeometry.BigFppfOver.AssociatedModuleGlueDescentDatum`
(`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/QcohGlueAssembly.lean`).

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The scheme underlying an object of the small étale site of `S`. -/
abbrev objScheme (U : SmallEtale B S hS) : Scheme.{u} := U.obj.left.obj

/-- The scheme underlying an object of the small étale site of `S` is one of the site, so it has
a small étale site of its own. -/
theorem contains_objScheme (U : SmallEtale B S hS) : B.Contains (objScheme B S hS U) :=
  U.obj.left.property

section Object

variable (U : SmallEtale B S hS)

/-! ### The localization equivalence as an equivalence of ringed sites -/

/-- **The two topologies correspond under the localization equivalence.**  A sieve of the
localization of the small étale site of `S` at `U` is covering exactly when its image in the
small étale site of the scheme of `U` is.

This is `AlgebraicGeometry.SmallEtale.localizationEquivalence_topology` repackaged: the
comparison functor is cover dense, being an equivalence, so the topology it induces from the
slice topology makes it a dense subsite inclusion, and that induced topology *is* the small
étale topology of the scheme of `U`. -/
instance isDenseSubsite_localizationEquivalence_inverse :
    (localizationEquivalence B S hS U).inverse.IsDenseSubsite
      ((topology B S hS).over U)
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U)) := by
  rw [← localizationEquivalence_topology B S hS U]
  exact inferInstanceAs ((localizationEquivalence B S hS U).symm.functor.IsDenseSubsite _
    ((localizationEquivalence B S hS U).symm.inverse.inducedTopology _))

/-- **The localization equivalence of the small étale site is an equivalence of *ringed* sites,
on the nose.**  The structure sheaf of the localization of the small étale site of `S` at `U`,
transported along `AlgebraicGeometry.SmallEtale.localizationEquivalence`, *is* the structure
sheaf of the small étale site of the scheme of `U`.

Both structure sheaves send an object to the global functions on its underlying scheme, and the
comparison functor followed by the slice projection is post-composition with the structure
morphism of `U` — `AlgebraicGeometry.SmallEtale.localizationEquivalence_restriction`, an
equality of functors — which leaves the underlying scheme of an object untouched.  So the match
is an equality and not merely an isomorphism, which is what makes the transports below possible
at all: `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` compares a module over the
transported sheaf of rings with a module over the sheaf of rings of the target site, and the
invariance of quasi-coherence under restriction of scalars along an isomorphism of sheaves of
rings is not available. -/
theorem reindexRing_localizationEquivalence :
    Stacks.SheafOfModules.reindexRing
        (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
        (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U) =
      structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U) :=
  rfl

/-! ### The crossover on sheaves of modules -/

/-- Reindexing a module on the localization of the small étale site of `S` at `U` along
`AlgebraicGeometry.SmallEtale.localizationEquivalence` — a module on the small étale site of the
scheme of `U`, over its own structure sheaf by
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`. -/
noncomputable abbrev objRestrictFunctor :
    SheafOfModules.{u} ((structureSheaf B S hS).over U) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U)) :=
  SheafOfModules.pushforward.{u}
    (𝟙 (Stacks.SheafOfModules.reindexRing
      (topology B (objScheme B S hS U) (contains_objScheme B S hS U))
      (localizationEquivalence B S hS U) ((structureSheaf B S hS).over U)))

/-- **The localization equivalence of the small étale site, on sheaves of modules.**  The
modules on the localization of `S_étale` at `U` are the modules on the small étale site of the
scheme of `U`, the two ringed sites being the same by
`AlgebraicGeometry.SmallEtale.reindexRing_localizationEquivalence`. -/
noncomputable def objRestrictEquivalence :
    SheafOfModules.{u} ((structureSheaf B S hS).over U) ≌
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U)) :=
  Stacks.SheafOfModules.reindexEquivalence (localizationEquivalence B S hS U)
    ((structureSheaf B S hS).over U)

/-- The reindexing functor is the functor of the equivalence it induces. -/
theorem objRestrictEquivalence_functor :
    (objRestrictEquivalence B S hS U).functor = objRestrictFunctor B S hS U :=
  rfl

/-- **The crossover `𝒢 ↦ 𝒢|_{Y_étale}`.**  Restrict a module on `S_étale` to the localization at
`U` and read the result on the small étale site of the scheme `Y` of `U`, which is the same
ringed site.

This is the identification the source's proof of Stacks 03DX (2) uses when it passes from
`𝒢|_{S_étale/X_i}` to `𝒢|_{(X_i)_étale}`; before this file the library had no such functor for
the small étale site, only `AlgebraicGeometry.BigFppfOver.objRestrict` for the big fppf site. -/
noncomputable abbrev objRestrict :
    SheafOfModules.{u} (structureSheaf B S hS) ⥤
      SheafOfModules.{u} (structureSheaf B (objScheme B S hS U) (contains_objScheme B S hS U)) :=
  SheafOfModules.overFunctor.{u} (structureSheaf B S hS) U ⋙ objRestrictFunctor B S hS U

/-- A global presentation of the restriction of `𝒢` to the localization at `U` is a global
presentation of its crossover restriction to the small étale site of the scheme of `U`: the two
ringed sites agree, and a global presentation is carried along an equivalence of ringed sites by
`Stacks.SheafOfModules.hasGlobalPresentation_reindex`. -/
theorem hasGlobalPresentation_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : (G.over U).HasGlobalPresentation) :
    ((objRestrict B S hS U).obj G).HasGlobalPresentation :=
  Stacks.SheafOfModules.hasGlobalPresentation_reindex (localizationEquivalence B S hS U)
    ((structureSheaf B S hS).over U) (G.over U) h

/-- Conversely, a global presentation on the small étale site of the scheme of `U` is one on the
localization at `U`; the reindexing reflects global presentations as well as carrying them. -/
theorem hasGlobalPresentation_of_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    (h : ((objRestrict B S hS U).obj G).HasGlobalPresentation) :
    (G.over U).HasGlobalPresentation :=
  Stacks.SheafOfModules.hasGlobalPresentation_of_reindex (localizationEquivalence B S hS U)
    ((structureSheaf B S hS).over U) (G.over U) h

/-- **Quasi-coherence is invariant under the crossover.**  A module on `S_étale` restricted to
the small étale site of the scheme of `U` is quasi-coherent exactly when its restriction to the
localization of `S_étale` at `U` is.

This is `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff` — Stacks 03DM for clause (6)
of Stacks 03DL — at the equivalence of ringed sites above. -/
theorem isQuasicoherentOnSite_objRestrict_iff (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    ((objRestrict B S hS U).obj G).IsQuasicoherentOnSite ↔ (G.over U).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_reindex_iff (localizationEquivalence B S hS U)
    ((structureSheaf B S hS).over U) (G.over U)

/-! ### The local step at an arbitrary object of the small étale site -/

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, local step, at an arbitrary object
of the small étale site of `S`**, unconditionally.  If the restriction of `𝒢` to the
localization at `U` has a global presentation, then its crossover restriction to the small étale
site of the scheme `Y` of `U` is the associated module `𝓕^a` of a quasi-coherent
`𝒪_Y`-module `𝓕`.

This is the sentence "we claim that this implies that `𝒢|_{(S_i)_τ}` is `𝓕_i^a` for some
quasi-coherent sheaf `𝓕_i` on `S_i`" of the source's proof, at `τ = étale` on the small site.
The global presentation becomes a `SheafOfModules.Presentation` because the small étale site is
essentially small, and the local step at a presentation,
`AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_of_presentation`, is
unconditional. -/
theorem exists_isQuasicoherent_iso_associatedModule_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : (G.over U).HasGlobalPresentation) :
    ∃ 𝓕 : (objScheme B S hS U).Modules, 𝓕.IsQuasicoherent ∧
      Nonempty ((associatedModule B (objScheme B S hS U)
        (contains_objScheme B S hS U)).obj 𝓕 ≅ (objRestrict B S hS U).obj G) :=
  exists_isQuasicoherent_iso_associatedModule_of_presentation B _ _
    (Stacks.SheafOfModules.nonempty_presentation_of_hasGlobalPresentation
      (hasGlobalPresentation_objRestrict B S hS U h)).some

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, local step, at an arbitrary
object**, in the form of a membership in the essential image of `𝓕 ↦ 𝓕^a` on the small étale
site of the scheme of `U`. -/
theorem essImage_associatedModule_objRestrict
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (h : (G.over U).HasGlobalPresentation) :
    (associatedModuleQcoh B (objScheme B S hS U)
      (contains_objScheme B S hS U)).essImage ((objRestrict B S hS U).obj G) := by
  obtain ⟨𝓕, h𝓕, e⟩ := exists_isQuasicoherent_iso_associatedModule_objRestrict B S hS U h
  exact ⟨⟨𝓕, h𝓕⟩, e⟩

/-- A module whose crossover restriction to the small étale site of the scheme of `U` is an
associated module there is quasi-coherent on that site: an associated module of a quasi-coherent
module is quasi-coherent, by Stacks 03DV (2) at `τ = étale`, and quasi-coherence is invariant
under isomorphism. -/
theorem isQuasicoherentOnSite_objRestrict_of_exists_iso
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    (hd : ∃ 𝓕 : (objScheme B S hS U).Modules, 𝓕.IsQuasicoherent ∧
      Nonempty ((associatedModule B (objScheme B S hS U)
        (contains_objScheme B S hS U)).obj 𝓕 ≅ (objRestrict B S hS U).obj G)) :
    ((objRestrict B S hS U).obj G).IsQuasicoherentOnSite := by
  obtain ⟨𝓕, h𝓕, ⟨e⟩⟩ := hd
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso e
    (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B _ _ 𝓕 h𝓕)

end Object

/-! ### The residue, with the local step discharged -/

/-- **The gluing step of Stacks 03DX (2) at `τ = étale`**, as a hypothesis: a module on
`S_étale` whose crossover restriction to the small étale site of the scheme of each member of
some covering family of the final object is the associated module of a quasi-coherent module
there is itself the associated module `𝓕^a` of a quasi-coherent `𝒪_S`-module `𝓕`.

This is `AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue` with the *local* step
discharged: the hypothesis supplies the modules `𝓕_i` on the schemes `X_i`, so what is left is
exactly the part of the source's proof that is not local — full faithfulness of `𝓕 ↦ 𝓕^a`
(Stacks 0GN7, unconditional here) turning the canonical isomorphisms of `𝒢` over the fibre
products `X_i ×_S X_j` into a descent datum on the `𝓕_i`, the effectivity of descent for
quasi-coherent modules (Stacks 023T, also unconditional here) gluing that datum to a
quasi-coherent `𝓕` on `S`, and the sheaf property of `SheafHom(𝓕^a, 𝒢)` (Stacks 03EM) assembling
the local isomorphisms into a global one.  No presentation of any kind occurs in the statement.

The small étale counterpart of
`AlgebraicGeometry.BigFppfOver.EssImageAssociatedModuleQcohGlue`, and better placed than it in
one respect: the members `X_i` are étale over `S`, so their structure morphisms already form an
étale — hence fpqc — covering family of `S`, with no refinement step. -/
abbrev EssImageAssociatedModuleQcohGlue : Prop :=
  ∀ (G : SheafOfModules.{u} (structureSheaf B S hS)) (I : Type (u + 1))
      (X : I → SmallEtale B S hS), (topology B S hS).CoversTop X →
      (∀ i, ∃ 𝓕 : (objScheme B S hS (X i)).Modules, 𝓕.IsQuasicoherent ∧
        Nonempty ((associatedModule B (objScheme B S hS (X i))
          (contains_objScheme B S hS (X i))).obj 𝓕 ≅ (objRestrict B S hS (X i)).obj G)) →
    (associatedModuleQcoh B S hS).essImage G

/-- **The globalization step of Stacks 03DX (2) at `τ = étale` follows from the gluing step
alone.**  The global presentations that
`AlgebraicGeometry.SmallEtale.EssImageAssociatedModuleGlue` carries on the members of the
covering family are turned into quasi-coherent modules on the schemes of those members by
`AlgebraicGeometry.SmallEtale.exists_isQuasicoherent_iso_associatedModule_objRestrict`, which is
unconditional; nothing else about them is used. -/
theorem essImageAssociatedModuleGlue_of_qcohGlue
    (h : EssImageAssociatedModuleQcohGlue B S hS) :
    EssImageAssociatedModuleGlue B S hS := fun G I X hX hP =>
  h G I X hX fun i =>
    exists_isQuasicoherent_iso_associatedModule_objRestrict B S hS (X i) (hP i)

/-- **Stacks 03DX (2) at `τ = étale`, essential surjectivity, over the gluing step.**  Every
quasi-coherent `𝒪`-module on `S_étale` is isomorphic to `𝓕^a` for a quasi-coherent
`𝒪_S`-module `𝓕`.

This is the essential-surjectivity input of
`AlgebraicGeometry.SmallEtale.isEquivalence_associatedModuleQcohOnSite` and of
`AlgebraicGeometry.SmallEtale.isEquivalence_derivedAssociatedModule`, here reduced to the appeal
to Stacks 023T and Stacks 03EM with the local half of the source's proof discharged.  It is
proved outright, by another route, as
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`. -/
theorem quasicoherentIsEssImageAssociatedModule_of_qcohGlue
    (h : EssImageAssociatedModuleQcohGlue B S hS) :
    QuasicoherentIsEssImageAssociatedModule B S hS :=
  quasicoherentIsEssImageAssociatedModule_of_glue B S hS
    (essImageAssociatedModuleGlue_of_qcohGlue B S hS h)

/-- The gluing step is *implied* by the conclusion it is used for, so it is not a strengthening
of Stacks 03DX (2)'s essential surjectivity.  A module whose crossover restriction to each
member of a covering family of the final object is an associated module there is quasi-coherent
on each of those small étale sites, hence — the crossover reflecting quasi-coherence —
quasi-coherent on each member of the family, hence quasi-coherent by Stacks 03DN; and then the
conclusion applies to it. -/
theorem essImageAssociatedModuleQcohGlue_of_quasicoherentIsEssImage
    (h : QuasicoherentIsEssImageAssociatedModule B S hS) :
    EssImageAssociatedModuleQcohGlue B S hS := by
  intro G I X hX hd
  refine h G ?_
  refine (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
    G).2 ⟨I, X, hX, fun i => ?_⟩
  exact (isQuasicoherentOnSite_objRestrict_iff B S hS (X i) G).1
    (isQuasicoherentOnSite_objRestrict_of_exists_iso B S hS (X i) (hd i))

/-- **The gluing step and essential surjectivity at `τ = étale` are equivalent.**  The
hypothesis named here is therefore exactly the content that the appeal to Stacks 023T and
Stacks 03EM supplies, with the local step of the source's proof — the crossover to the small
étale sites of the members — already discharged. -/
theorem essImageAssociatedModuleQcohGlue_iff :
    EssImageAssociatedModuleQcohGlue B S hS ↔
      QuasicoherentIsEssImageAssociatedModule B S hS :=
  ⟨quasicoherentIsEssImageAssociatedModule_of_qcohGlue B S hS,
    essImageAssociatedModuleQcohGlue_of_quasicoherentIsEssImage B S hS⟩

end AlgebraicGeometry.SmallEtale

end
