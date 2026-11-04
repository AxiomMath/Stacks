module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalTypesOfModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.GlobalGenerationComparison
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteLocallyFreeAgreement
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteType
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FiniteColimits.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeFromGlobalGenerators
public import StacksFrontier.AlgebraicGeometry.Topologies.FiniteTypeOnSiteKernel
import StacksCore.Tactic.StacksAttribute

/-!
# Finite type and finite presentation of `𝓕ᵃ` on the small étale site

Descent, Lemma 05VG asserts, for each property of modules of Modules on Sites, Definitions
03DE, 03DL and 03ER, that a quasi-coherent `𝒪_S`-module `𝓕` has the property if and only if
`𝓕ᵃ` has it as an `𝒪`-module on the site.  This file lands the two finiteness clauses of
Definition 03DL at the **small étale** site: clause (5), *of finite type*, and clause (7), *of
finite presentation*, both as equivalences and both for the comparison functor
`AlgebraicGeometry.SmallEtale.associatedModule` of Descent, Proposition 03DX itself.

Neither clause assumes anything of `𝓕` beyond what the property names: the two theorems are
proved for an arbitrary `𝒪_S`-module, so they are the source's clauses over a weaker hypothesis
than the source's, which asks for quasi-coherence.

## The route

The ringed-topos route that lands the same two clauses at the small **Zariski** site —
`AlgebraicGeometry.SmallZariski.isFiniteType_iff_associatedModule` and
`…isFinitePresentation_iff_associatedModule`, which read Stacks 03DM through Remark 03FH's
morphism of ringed topoi — is unavailable here: the comparison's pushforward is not an
equivalence of topoi on the small étale site, so
`AlgebraicGeometry.RingedToposHom.isFiniteType_iff_pullbackModules` and
`…isFinitePresentation_iff_pullbackModules` do not apply.  What is used instead is the source's
own route, Stacks 03DN together with a per-clause descent lemma.

* **Finite type** needs no covering argument here, both implications being already in the tree
  in the categorical rendering `SheafOfModules.IsFiniteTypeOnSite` of clause (5): they are the
  two halves of Stacks 08HD, `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_associatedModule`
  and `AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`.  The clause is
  those two read through the comparison of the two renderings of 03DL (5),
  `Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType` and
  `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`.
* **Finite presentation** runs the covering argument.  The `only if` half transports the
  quasi-coherent data: Stacks 03DV's covering argument is
  `AlgebraicGeometry.SmallEtale.quasicoherentDataAssociatedModule`, whose presentation on a
  member is `AlgebraicGeometry.SmallEtale.presentationAssociatedModuleOver`, and finiteness of
  a presentation survives both of the operations that definition performs.  The `if` half is
  the descent.  Stacks 03DN produces a family covering the final object of `S_étale` on whose
  members `𝓕ᵃ` has a finite presentation; the members are étale over `S`, hence flat, locally
  of finite presentation and jointly surjective, so their structure morphisms are an fpqc
  covering family of `S` on the nose
  (`AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover`) and the
  big site's refinement step drops out.  On a member the crossover of Stacks 06WI and Stacks
  03DV at an object rewrite the restriction of `𝓕ᵃ` as `(f^*𝓕)ᵃ` on the small étale site of the
  scheme of the member, where 05VG for Modules on Sites 03DE (7) —
  `AlgebraicGeometry.SmallEtale.isFinitelyPresentedByGlobalSections_iff_associatedModule`, an
  `iff` — reflects the finite global presentation down to that scheme.  Stacks 05B0,
  `AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`, descends it to `S`.

This is the architecture of
`AlgebraicGeometry.SmallEtale.isFiniteLocallyFreeOnSite_associatedModule_iff`, the clause for
03DL (2) at this site, with the global clause 03DE (2) replaced by the global clause 03DE (7)
and the colimiting cofans replaced by presentations.

## Main results

* `Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_presentation`: a finite
  `SheafOfModules.Presentation` is a finite global presentation in the sense of Stacks
  03DE (7), at an arbitrary module universe.
* `AlgebraicGeometry.SmallEtale.isFiniteType_associatedModule_iff`: **Descent, Lemma 05VG for
  Modules on Sites, Definition 03DL (5), at the small étale site.**
* `AlgebraicGeometry.SmallEtale.isFinite_presentationAssociatedModuleOver` and
  `…isFinitePresentation_quasicoherentDataAssociatedModule`: the finiteness that Stacks 03DV's
  covering argument carries along.
* `AlgebraicGeometry.SmallEtale.isFinitelyPresentedByGlobalSections_associatedModule_objHom`
  and `…isFinitePresentation_pullback_of_presentation_over`: the step at one member of the
  covering family.
* `AlgebraicGeometry.SmallEtale.isFinitePresentation_of_associatedModule`: the descent
  implication of clause 03DL (7).  It carries no `stacks` attribute: 05VG's clause asserts an
  equivalence, and one implication of an equivalence does not realize it.  The equivalence
  itself, with the tag, is
  `AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff` in
  `StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFinitePresentation.lean`.

## Implementation notes

`Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_presentation` is stated at an
arbitrary module universe, which is what the small étale site forces and what rules out the
composite of the two results already in the tree:
`SheafOfModules.HasFiniteGlobalPresentation.of_presentation'` lands in the rendering of
03DE (7) that lifts the sections to the universe `max u v w` of the site, and
`SheafOfModules.isFinitelyPresentedByGlobalSections_iff_hasFiniteGlobalPresentation` undoes
that lift only where the two universes agree.  They do agree on the site of opens of a scheme,
where that composite is used below, and they do not on the small étale site, whose objects live
one universe above its sections.

The finiteness of a presentation transported along a colimit-preserving functor is
`Stacks.Tag01PJFiniteColimits.presentation_map_isFinite`, and a module with a finite global
presentation is of finite presentation by
`Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation`.

## References

* [Stacks Project, Tag 05VG](https://stacks.math.columbia.edu/tag/05VG)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 05B0](https://stacks.math.columbia.edu/tag/05B0)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModules

universe w v₁ u₁

/-- **A finite presentation is a finite global presentation**, in the sense of Stacks 03DE (7),
at an arbitrary module universe.

A `SheafOfModules.Presentation` already exhibits the module as the cokernel of a map between
two free modules, `SheafOfModules.Presentation.isColimit`, and a free module on a type is the
coproduct of copies of the structure sheaf indexed by it,
`SheafOfModules.isColimitFreeCofan`; finiteness of the two index types lets both cofans be
reindexed over a `Fin n` by `CategoryTheory.Limits.Cofan.isColimitEquivOfEquiv`, which is the
shape Stacks 03DE (7) asks for. -/
public theorem isFinitelyPresentedByGlobalSections_of_presentation
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M : _root_.SheafOfModules.{w} R} (P : M.Presentation) [P.IsFinite] :
    M.IsFinitelyPresentedByGlobalSections := by
  classical
  obtain ⟨n, ⟨eg⟩⟩ := Finite.exists_equiv_fin P.generators.I
  obtain ⟨k, ⟨er⟩⟩ := Finite.exists_equiv_fin P.relations.I
  have key : ∀ {I : Type w} {m : ℕ} (e : I ≃ Fin m),
      IsColimit (Cofan.mk (_root_.SheafOfModules.free (R := R) I)
        fun i : Fin m ↦ (_root_.SheafOfModules.freeCofan (R := R) I).inj (e.symm i)) :=
    fun e ↦ (Cofan.isColimitEquivOfEquiv (ε := e.symm)
      (_root_.SheafOfModules.freeCofan (R := R) _))
      (_root_.SheafOfModules.isColimitFreeCofan _)
  exact ⟨n, k, _, _, _, _, ⟨key eg⟩, ⟨key er⟩, _, P.generators.π, _, ⟨P.isColimit⟩⟩

end Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Finite type, Stacks 03DL (5) -/

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (5), at the small étale site.**
An `𝒪_S`-module `𝓕` is of finite type if and only if `𝓕ᵃ` is of finite type as an `𝒪`-module on
`S_étale`.

Both implications are Stacks 08HD in the categorical rendering of 03DL (5),
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_associatedModule` and
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`; the comparison of that
rendering with Mathlib's `SheafOfModules.IsFiniteType` is
`Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType` in one direction and
`Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite` in the other.

The clause string records the scope: this is clause 03DL (5) of 05VG at the **small** site for
`τ = étale`.  The small Zariski site is
`AlgebraicGeometry.SmallZariski.isFiniteType_iff_associatedModule`.  No quasi-coherence is
assumed, so this is the clause over a weaker hypothesis than the source's. -/
@[stacks 05VG "finite type (03DL (5)), small site at τ = étale, at the comparison functor of \
03DX itself"]
public theorem isFiniteType_associatedModule_iff (𝓕 : S.Modules) :
    SheafOfModules.IsFiniteType 𝓕 ↔
      SheafOfModules.IsFiniteType ((associatedModule B S hS).obj 𝓕) :=
  ⟨fun h ↦ Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
      (isFiniteTypeOnSite_associatedModule B S hS 𝓕
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ h)),
    fun h ↦ Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
      (isFiniteTypeOnSite_of_associatedModule B S hS 𝓕
        (Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ h))⟩

/-! ### Finite presentation, Stacks 03DL (7): the pullback direction -/

/-- A finite presentation mapped along a colimit-preserving functor that preserves the unit,
then transported across an isomorphism, is finite. -/
private theorem isFinite_ofIsIso_map {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] {D : Type*} [Category* D]
    {K : GrothendieckTopology D} {R' : Sheaf K RingCat.{u}} [HasSheafify K AddCommGrpCat.{u}]
    [K.WEqualsLocallyBijective AddCommGrpCat.{u}] {M : SheafOfModules.{u} R} (P : M.Presentation)
    [P.IsFinite] (T : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R')
    [PreservesColimitsOfSize.{u, u} T]
    (η : SheafOfModules.unit R' ≅ T.obj (SheafOfModules.unit R)) {N : SheafOfModules.{u} R'}
    (e : T.obj M ≅ N) : ((P.map T η).ofIsIso e.hom).IsFinite := by
  have := Stacks.Tag01PJFiniteColimits.presentation_map_isFinite P T η
  infer_instance

/-- **The transport of Stacks 03DV preserves finiteness of a presentation.**  The presentation
of `(𝓕ᵃ)|_{V_étale}` that `AlgebraicGeometry.SmallEtale.presentationAssociatedModuleOver` builds
from a presentation of `𝓕|_V` is finite as soon as the given one is.

That definition does two things to the presentation: it maps it along the associated-module
functor of the localized site, which keeps the two index types by
`Stacks.Tag01PJFiniteColimits.presentation_map_isFinite`, the functor being a left adjoint and
so preserving colimits; and it transports the result across an isomorphism, which keeps them by
Mathlib's instance for `SheafOfModules.Presentation.ofIsIso`. -/
public theorem isFinite_presentationAssociatedModuleOver (V : S.Opens) {𝓕 : S.Modules}
    (P : (SheafOfModules.over.{u} (R := S.ringCatSheaf) 𝓕 V).Presentation) (hP : P.IsFinite) :
    (presentationAssociatedModuleOver B S hS V P).IsFinite := by
  have := hP
  have : PreservesColimitsOfSize.{u, u}
      (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V)) :=
    (SheafOfModules.pullbackPushforwardAdjunction.{u}
      (sliceStructureMap B S hS V)).leftAdjoint_preservesColimits
  exact isFinite_ofIsIso_map P (SheafOfModules.pullback.{u} (sliceStructureMap B S hS V))
    (asIso (SheafOfModules.pullbackObjUnitToUnit.{u} (sliceStructureMap B S hS V))).symm
    (associatedModuleOverObjIso B S hS V 𝓕)

/-- **The quasi-coherent data of Stacks 03DV is finite as soon as the given data is.**  This is
`AlgebraicGeometry.SmallEtale.isFinite_presentationAssociatedModuleOver` at each member of the
covering family, the data of
`AlgebraicGeometry.SmallEtale.quasicoherentDataAssociatedModule` being built member by member. -/
public theorem isFinitePresentation_quasicoherentDataAssociatedModule {𝓕 : S.Modules}
    (q : SheafOfModules.QuasicoherentData.{u} (R := S.ringCatSheaf) 𝓕)
    (hq : q.IsFinitePresentation) :
    (quasicoherentDataAssociatedModule B S hS q).IsFinitePresentation :=
  ⟨fun i ↦ isFinite_presentationAssociatedModuleOver B S hS (q.X i.down)
    (q.presentation i.down) (hq.isFinite_presentation i.down)⟩

/-! ### Finite presentation, Stacks 03DL (7): the descent direction -/

section Object

variable (U : SmallEtale B S hS)

/-- **A finite presentation of `(𝓕ᵃ)|_{S_étale/U}` is a finite global presentation of
`(f^*𝓕)ᵃ` on the small étale site of the scheme of `U`**, where `f : Y ⟶ S` is the structure
morphism of `U`.

Two steps, each an identification proved in the library.  The crossover of Stacks 06WI,
`AlgebraicGeometry.SmallEtale.objRestrictFunctor`, is the functor of an equivalence of ringed
sites and carries the structure sheaf to the structure sheaf by
`AlgebraicGeometry.SmallEtale.objRestrictFunctorUnitIso`, so it carries the presentation to a
presentation, finite by `Stacks.Tag01PJFiniteColimits.presentation_map_isFinite`; and Stacks
03DV at an arbitrary object of the small étale site,
`AlgebraicGeometry.SmallEtale.associatedModuleObjRestrictObjIso`, moves the result to `(f^*𝓕)ᵃ`.
`Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_presentation` then reads the
presentation as a finite global presentation. -/
public theorem isFinitelyPresentedByGlobalSections_associatedModule_objHom (𝓕 : S.Modules)
    (P : (((associatedModule B S hS).obj 𝓕).over U).Presentation) (hP : P.IsFinite) :
    SheafOfModules.IsFinitelyPresentedByGlobalSections
      ((associatedModule B (objScheme B S hS U) (contains_objScheme B S hS U)).obj
        ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕)) := by
  have := hP
  have : PreservesColimitsOfSize.{u, u} (objRestrictFunctor B S hS U) :=
    (objRestrictEquivalence B S hS U).toAdjunction.leftAdjoint_preservesColimits
  have := isFinite_ofIsIso_map P (objRestrictFunctor B S hS U)
    (objRestrictFunctorUnitIso B S hS U).symm (associatedModuleObjRestrictObjIso B S hS U 𝓕).symm
  exact Stacks.SheafOfModules.isFinitelyPresentedByGlobalSections_of_presentation
    ((P.map (objRestrictFunctor B S hS U)
      (objRestrictFunctorUnitIso B S hS U).symm).ofIsIso
      (associatedModuleObjRestrictObjIso B S hS U 𝓕).symm.hom)

/-- **The pullback of `𝓕` along the structure morphism of `U` is of finite presentation as soon
as the restriction of `𝓕ᵃ` to the localization of `S_étale` at `U` has a finite presentation.**

`AlgebraicGeometry.SmallEtale.isFinitelyPresentedByGlobalSections_associatedModule_objHom`
turns the hypothesis into a finite global presentation of `(f^*𝓕)ᵃ`, and
`AlgebraicGeometry.SmallEtale.isFinitelyPresentedByGlobalSections_iff_associatedModule` — 05VG
for Modules on Sites 03DE (7) at the small étale site of the scheme of `U`, an `iff` — reflects
it down to `f^*𝓕`, which is quasi-coherent by Stacks 01BG.  On the site of opens of a scheme the
two renderings of 03DE (7) agree, so
`SheafOfModules.isFinitelyPresentedByGlobalSections_iff_hasFiniteGlobalPresentation` and
`AlgebraicGeometry.SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation`
turn the global presentation into a `SheafOfModules.Presentation`, and
`Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation` concludes. -/
public theorem isFinitePresentation_pullback_of_presentation_over (𝓕 : S.Modules)
    [h𝓕 : 𝓕.IsQuasicoherent]
    (P : (((associatedModule B S hS).obj 𝓕).over U).Presentation) (hP : P.IsFinite) :
    SheafOfModules.IsFinitePresentation
      ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕) := by
  have hqc : ((Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback _ 𝓕 h𝓕
  have hglob :
      ((Scheme.Modules.pullback (objHom B S hS U)).obj
        𝓕).IsFinitelyPresentedByGlobalSections :=
    (isFinitelyPresentedByGlobalSections_iff_associatedModule B (objScheme B S hS U)
      (contains_objScheme B S hS U)
      ⟨(Scheme.Modules.pullback (objHom B S hS U)).obj 𝓕, hqc⟩).2
      (isFinitelyPresentedByGlobalSections_associatedModule_objHom B S hS U 𝓕 P hP)
  obtain ⟨p, hp⟩ :=
    AlgebraicGeometry.SheafOfModules.exists_isFinite_presentation_of_hasFiniteGlobalPresentation
      _ ((_root_.SheafOfModules.isFinitelyPresentedByGlobalSections_iff_hasFiniteGlobalPresentation
        _).1 hglob)
  have := hp
  exact Stacks.SheafOfModules.SliceFinite.isFinitePresentation_of_presentation p

end Object

/-- **Descent, Lemma 05VG for Modules on Sites, Definition 03DL (7): the descent direction, at
the small étale site.**  If the associated module `𝓕ᵃ` of a quasi-coherent `𝒪_S`-module is of
finite presentation as an `𝒪`-module on `S_étale`, then `𝓕` is of finite presentation.

This is the half that carries the mathematics, and it is the source's own argument.  Stacks
03DN produces a family covering the final object of `S_étale` on whose members `𝓕ᵃ` has a finite
presentation; the members are étale over `S`, hence flat, locally of finite presentation and
jointly surjective, so their structure morphisms are an fpqc covering family of `S` on the nose
— `AlgebraicGeometry.SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover` — and no
refinement step is needed, which is where this differs from the big site's proof.  On each
member `AlgebraicGeometry.SmallEtale.isFinitePresentation_pullback_of_presentation_over` turns
the verdict into finite presentation of the pullback of `𝓕`, and Stacks 05B0,
`AlgebraicGeometry.isFinitePresentation_of_pullback_fpqcCover`, descends it to `S`.

No `stacks` attribute: this is one implication, and the equivalence that assembles the two is
`AlgebraicGeometry.SmallEtale.isFinitePresentation_associatedModule_iff`, which carries the tag
and lives in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFinitePresentation.lean`. -/
public theorem isFinitePresentation_of_associatedModule (𝓕 : S.Modules) [h𝓕 : 𝓕.IsQuasicoherent]
    (h : SheafOfModules.IsFinitePresentation ((associatedModule B S hS).obj 𝓕)) :
    SheafOfModules.IsFinitePresentation 𝓕 := by
  classical
  have := h
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData
    ((associatedModule B S hS).obj 𝓕)
  let 𝒰 : S.Cover.{u + 1} Scheme.fpqcPrecoverage :=
    ⟨coveringHypercover B S hS q.X,
      presieve₀_mem_fpqcPrecoverage_coveringHypercover B S hS q.X q.coversTop⟩
  exact isFinitePresentation_of_pullback_fpqcCover 𝓕 𝒰 fun i ↦
    isFinitePresentation_pullback_of_presentation_over B S hS (q.X i) 𝓕
      (q.presentation i) (hq.isFinite_presentation i)

end AlgebraicGeometry.SmallEtale

end
