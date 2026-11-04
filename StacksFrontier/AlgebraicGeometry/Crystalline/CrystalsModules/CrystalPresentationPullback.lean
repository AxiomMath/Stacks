module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSpace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.AffineRestrictionPresentation
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.ComparisonFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelAmbientDeterminacy
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation

/-!
# A crystal carries a presentation of the restriction along a morphism

Let `F` be a sheaf of `𝒪_{X/S}`-modules on a crystalline site of a global crystalline situation
and let `f : (U, T, δ) ⟶ (U', T', δ')` be a morphism of that site.  The comparison map
`c_f : f^* F_{T'} ⟶ F_T` of [Stacks, Tag 07IQ] is a map of sheaves of `𝒪_T`-modules, and the
crystal condition of [Stacks, Tag 07IS] says that it is an isomorphism.

This file proves the step the second direction of [Stacks, Tag 07IT] takes when it says

> Then by the crystal property of `F` we see that this pulls back to a presentation of
> `F_{T'}` for any morphism `f : (U', T', δ') → (U, T, δ)` of `𝒞`.

namely: a global presentation of the restriction over the *target* of a morphism, by copies of the
structure sheaf of its ambient scheme, is carried along an invertible comparison map to a global
presentation of the restriction over the *source*, with the *same* index types of generators and
of relations.

The source's primes are the other way round from this library's: there the morphism `f` goes from
the primed object to the unprimed one, so the presentation is chosen on `F_T` and pulled back to
`F_{T'}`, whereas here — as in
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal` and everywhere else in
the chapter — `f : (U, T, δ) ⟶ (U', T', δ')` has the unprimed object for its source, so the
presentation is chosen on `F_{T'}` and carried to `F_T`.  The statements below are written with
this library's convention.

The two ingredients are both about the Zariski sites of the ambient schemes, where the pullback
of sheaves of modules exists.  First, the pullback of a module with a presentation has a
presentation: that is `Stacks.SheafOfModules.pullbackPresentation`, which needs the pullback of
the structure sheaf to be the structure sheaf, hence finality of the functor of sites, supplied
here by `Stacks.Topology.final_opensMap` — the preimage functor on the
opens of a continuous map is final because the opens of a space form a poset with a greatest
element.  Second, a presentation transports along an isomorphism of modules, which is Mathlib's
`SheafOfModules.Presentation.ofIsIso`, and the isomorphism is the comparison map itself.

## Index universes

A presentation in the sense of Mathlib's `SheafOfModules.Presentation` indexes its generators and
relations by types in the universe of the coefficient rings, which for the restriction of
`𝒪_{X/S}` to the ambient scheme of an object is `Type u`.  The predicate
`SheafOfModules.HasGlobalPresentation` of [Stacks, Tag 03DE] (6) instead indexes them by
`Type (max u v r m)`, which on the Zariski site of a scheme over `Scheme.{u}` is again `Type u`.
The two are therefore interchangeable here, in both directions: by
`SheafOfModules.Presentation.hasGlobalPresentation` and, back, by
`SheafOfModules.HasGlobalPresentation.nonempty_presentation_of_small_sections`, whose smallness
hypothesis holds on the Zariski site of a scheme by `SheafOfModules.small_sections_of_univLE`.
So the statements below are given for `SheafOfModules.HasGlobalPresentation`, the predicate the
chapter's quasi-coherence is phrased with, and the underlying construction on presentations is
available as well.

## Main definitions

All names in these two lists are in the namespace `Crystalline.GlobalCrystallineSituation`.

* `Thickening.presentationModuleRestrictionSheaf` — **the presentation of `F_T` obtained from one
  of `F_{T'}` along an invertible comparison map**, on the big crystalline site.
* `SmallSite.CohomologyRestriction.presentationModuleRestrictionSheaf` — the same on the small
  crystalline site.

## Main results

* `Thickening.hasGlobalPresentation_moduleRestrictionSheaf_of_isIso_moduleComparisonSheaf`
  and its small-site counterpart — a global presentation of the restriction of `F` to the ambient
  scheme of the target of a morphism is carried to one of the restriction to the ambient scheme of
  its source, as soon as the comparison map of that morphism is an isomorphism.
* `hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal` and
  `SmallSite.hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal`
  — **the same for a crystal in `𝒪_{X/S}`-modules**, on the big and on the small crystalline site:
  a crystal carries a global presentation of `F_{T'}` to a global presentation of `F_T` along
  every morphism `(U, T, δ) ⟶ (U', T', δ')`.
* `hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine` and
  `SmallSite.hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine`
  — [Stacks, Tag 03DX] for the restriction of a locally quasi-coherent module to an affine ambient
  scheme, stated over the restriction of `𝒪_{X/S}` rather than over the structure sheaf of that
  scheme: the change of scalars of `Thickening.ringRestrictionSheafStructureIso` is run back
  through `Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId`.
* `hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine` and
  `SmallSite.hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine`
  — **the opening move of the direction (2) ⇒ (1) of [Stacks, Tag 07IT], in full**: for a locally
  quasi-coherent crystal and an object `(U', T', δ')` whose ambient scheme is affine, the
  restriction `F_T` has a global presentation over *every* object `(U, T, δ)` of the localised site
  `𝒞/(U', T', δ')`, with index types independent of `(U, T, δ)`.

## What is not proved

No `@[stacks]` attribute is placed.  What is proved is one step of the direction
(2) ⇒ (1) of [Stacks, Tag 07IT] — "locally quasi-coherent and a crystal implies quasi-coherent" —
and not that implication, nor any clause of that tag.  The implication (1) ⇒ (2) of
[Stacks, Tag 07IT] carries the attribute where its two halves are proved: (1) ⇒ (2)(a) at
`Crystalline.GlobalCrystallineSituation.isLocallyQuasiCoherent_of_isQuasicoherentOnSite` and its
small-site twin, and (1) ⇒ (2)(b) at
`Crystalline.GlobalCrystallineSituation.isSheafCrystal_of_isQuasicoherentOnSite` and its
small-site twin.

One step still separates what is proved here from the direction (2) ⇒ (1), and it is the larger
one: the *assembly*.  The presentations of `F_T` produced here, one for each object `(U, T, δ)` of
the localised site `𝒞/(U', T', δ')`, have to be assembled into a *single* global presentation of
`F` on that localised site, which is what
`Crystalline.GlobalCrystallineSituation.isQuasicoherentOnSite_of_forall_isAffine` consumes.
Nothing below performs that assembly.

**The index universe is not what stands in the way.**  A global presentation of a module on the
localised crystalline site is indexed by `Type (u + 1)`, the objects of the site lying there,
while the presentations of the `F_T` are indexed by `Type u` on the Zariski sites of the ambient
schemes; but *raising* an index type is free, by
`SheafOfModules.hasGlobalPresentation_uliftForPresentation'`, and lowering it again is
`SheafOfModules.HasGlobalPresentation.of_uliftForPresentation'`.  What the universes do force is
that the assembly be carried out at the module universe `u + 1`: a coproduct of copies of the
structure sheaf at the module universe `u` on the localised crystalline site would need
sheafification of `AddCommGrpCat.{u}`-valued presheaves there, which that site does not have,
whereas `HasSheafify ((topology S).over A) AddCommGrpCat.{u + 1}` does hold (as
`Thickening.preservesColimitsOfSize_pushforward_restrictOpenOverStructureHom`, in the namespace
`Crystalline.GlobalCrystallineSituation`, witnesses).  That is compatible with the crystal
condition living at the module universe `u`, where `SheafOfModules.pullback` exists: the cokernel
condition on the localised crystalline site is to be checked after restricting to the Zariski
sites of the ambient schemes, where
`Stacks.SheafOfModules.GlobalPresentationTransport.pushforwardUliftIso` identifies the
restriction of a universe lift with the universe lift of the restriction and the lift is fully
faithful, by `SheafOfModules.full_uliftForPresentationFunctor` and
`SheafOfModules.faithful_uliftForPresentationFunctor`.

**What is missing is two statements, neither about universes.**  First, a cokernel of sheaves of
modules on the localised crystalline site has to be *recognised* from its restrictions to the
Zariski sites of the ambient schemes.  The categorical half of that is now available as
`CategoryTheory.Limits.isColimitCokernelCoforkOfConservativeFamily` of
`StacksFrontier.CategoryTheory.Limits.CokernelOfConservativeFamily`, and one of its two inputs is
available as well: each such restriction preserves the colimits in question, because
`Stacks.SheafOfModules.pushforward_preservesColimits` needs only continuity and cocontinuity of
the functor of sites.  The other input is not: there is no family of restriction functors indexed
by the objects of a *fixed* localised site — `Thickening.restrictOpenOverFunctor A V` restricts a
module on the slice at `A.restrictOpen V`, not on the slice at an object the various `A` map to —
and no conservativity statement for the ambient restrictions exists on the big crystalline site,
the closest being the small site's *faithfulness*,
`Crystalline.GlobalCrystallineSituation.SmallSite.eq_of_forall_moduleRestrictionSheafMap_eq`.  The
generic tools for the conservativity itself are
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app` and
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward`.

Second, the generators of the per-object presentations produced here have to be the restrictions
of *one* fixed family of sections of `F` over `(U', T', δ')`, rather than an unrelated family for
each `f`.  **That step is available**, as
`Crystalline.GlobalCrystallineSituation.Thickening.pullbackMap_comp_moduleComparisonSheaf` and
its small-site counterpart in
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.ComparisonSections`: the comparison
map carries the pullback of a morphism into `F_{T'}` to the transpose of that morphism followed
by the `f`-map, so the pulled-back presentation is determined by the restrictions along `f` of
the generating sections of `F_{T'}`.

Note that the route through local exactness does *not* need [Stacks, Tag 01XB]: an earlier
reading of the source's "this pulls back to a presentation of `F_T`" took the cokernel property on
the crystalline site to require exactness of global sections on an affine, hence the vanishing of
the higher cohomology of a quasi-coherent module there.  Checking the cokernel property locally —
every object of a crystalline site is covered by the restrictions of itself to the affine opens of
its ambient scheme, by
`Crystalline.GlobalCrystallineSituation.Thickening.isZariskiCovering_restrictOpenCover` — needs
only the presentations of the `F_T` and the fact that a cokernel of sheaves of modules is detected
locally.  That observation is recorded here; the assembly itself is still not performed.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

attribute [local instance] Stacks.SheafOfModules.hasSheafify_opens
  Stacks.SheafOfModules.wEqualsLocallyBijective_opens

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

/-- A map from presentations of `N` to presentations of `M` transfers global presentations. -/
private theorem hasGlobalPresentation_of_presentation_map {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    {R' : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}} {M : SheafOfModules.{u} R}
    {N : SheafOfModules.{u} R'} (h : N.HasGlobalPresentation)
    (f : N.Presentation → M.Presentation) :
    M.HasGlobalPresentation := by
  have : ∀ N : SheafOfModules.{u} R', Small.{u} N.sections :=
    fun N ↦ SheafOfModules.small_sections_of_univLE N
  exact (f h.nonempty_presentation_of_small_sections.some).hasGlobalPresentation

namespace Thickening

variable (M : SheafOfModules.{u} (crystallineStructureSheaf S)) {A B : Thickening S}

/-- **A presentation of `F_{T'}` is carried to a presentation of `F_T` by an invertible
comparison map**, on the big crystalline site.  The pullback along the map of ambient schemes
carries the presentation to a presentation of `f^* F_{T'}`, by
`Stacks.SheafOfModules.pullbackPresentation`, and the comparison map identifies that with `F_T`.
The index types of the generators and of the relations are unchanged. -/
noncomputable def presentationModuleRestrictionSheaf (g : A ⟶ B)
    (hg : IsIso (moduleComparisonSheaf M g))
    (p : (moduleRestrictionSheaf M B).Presentation) :
    (moduleRestrictionSheaf M A).Presentation :=
  haveI : (Opens.map g.targetHom.hom.base).Final := Stacks.Topology.final_opensMap _
  haveI := hg
  (Stacks.SheafOfModules.pullbackPresentation (ringRestrictionSheafFMap g) p).ofIsIso
    (moduleComparisonSheaf M g)

/-- **A global presentation of `F_{T'}` is carried to a global presentation of `F_T` by an
invertible comparison map**, on the big crystalline site.  The global presentation of
[Stacks, Tag 03DE] (6) and Mathlib's `SheafOfModules.Presentation` are interchangeable on the
Zariski site of a scheme, the index universe of the former being the universe of the sections
there; the transport itself is
`Crystalline.GlobalCrystallineSituation.Thickening.presentationModuleRestrictionSheaf`. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isIso_moduleComparisonSheaf (g : A ⟶ B)
    (hg : IsIso (moduleComparisonSheaf M g))
    (h : (moduleRestrictionSheaf M B).HasGlobalPresentation) :
    (moduleRestrictionSheaf M A).HasGlobalPresentation :=
  hasGlobalPresentation_of_presentation_map h (presentationModuleRestrictionSheaf M g hg)

end Thickening

/-- **The restriction of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules to an affine ambient
scheme has a global presentation over the restriction of `𝒪_{X/S}`.**  This is
[Stacks, Tag 03DX] in the shape the direction (2) ⇒ (1) of [Stacks, Tag 07IT] uses it:
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_ambientModuleRestriction` presents
the restriction with its scalars read in the structure sheaf of the ambient scheme, and the two
sheaves of rings are identified by
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`.

The change of scalars is run in both directions: forwards by
`Stacks.SheafOfModules.hasGlobalPresentation_restrictScalars_of_isIso`, and back by the round trip
`Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId`, which identifies the composite of the
two restrictions of scalars along an isomorphism of sheaves of rings and its inverse with the
identity functor. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (B : Thickening S) [IsAffine B.thickening.target.scheme] :
    (Thickening.moduleRestrictionSheaf M B).HasGlobalPresentation :=
  SheafOfModules.HasGlobalPresentation.of_iso
    ((Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId
        (Thickening.ringRestrictionSheafStructureIso B).inv
        (Thickening.ringRestrictionSheafStructureIso B).hom (by simp)).app
      (Thickening.moduleRestrictionSheaf M B))
    (Stacks.SheafOfModules.hasGlobalPresentation_restrictScalars_of_isIso
      (Thickening.ringRestrictionSheafStructureIso B).hom _
      (hasGlobalPresentation_ambientModuleRestriction hM B))

/-- **A crystal in `𝒪_{X/S}`-modules on `CRIS(X/S)` carries a global presentation of `F_{T'}` to
a global presentation of `F_T`, along every morphism `(U, T, δ) ⟶ (U', T', δ')`.**  This is the
step the direction (2) ⇒ (1) of [Stacks, Tag 07IT] takes when it says that the presentation of
`F_T` on an affine ambient scheme "pulls back to a presentation of `F_{T'}` for any morphism
`f`"; the crystal condition enters exactly as the invertibility of the comparison map.  That
implication itself is not proved; see the module documentation. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal
    (M : SheafOfModules.{u} (crystallineStructureSheaf S)) (hM : IsSheafCrystal M)
    {A B : Thickening S} (g : A ⟶ B)
    (h : (Thickening.moduleRestrictionSheaf M B).HasGlobalPresentation) :
    (Thickening.moduleRestrictionSheaf M A).HasGlobalPresentation :=
  Thickening.hasGlobalPresentation_moduleRestrictionSheaf_of_isIso_moduleComparisonSheaf M g
    (hM A B g) h

/-- **For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules on `CRIS(X/S)` and an object
`(U', T', δ')` with affine ambient scheme, the restriction `F_T` has a global presentation over
every object `(U, T, δ)` of the localised site `CRIS(X/S)/(U', T', δ')`.**

This is the whole of the opening move of the direction (2) ⇒ (1) of [Stacks, Tag 07IT]: a
presentation `⊕_J 𝒪_{T'} → ⊕_I 𝒪_{T'} → F_{T'} → 0` is chosen because `F_{T'}` is a
quasi-coherent module on the affine `T'`, and then "by the crystal property of `F` we see that
this pulls back to a presentation" of the restriction over every object mapping to
`(U', T', δ')`.  The index types of generators and relations are the same for every such `f`,
being those of the presentation over `(U', T', δ')`.  (The source's primes are the other way
round; see the module documentation.)

What the source then does, and what is *not* done anywhere in this library, is to assemble these
presentations into a single global presentation of `F` on `CRIS(X/S)/(U', T', δ')`, which is the
conclusion the tag's direction (2) ⇒ (1) asks for; see the module documentation. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine
    {M : SheafOfModules.{u} (crystallineStructureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) {A B : Thickening S} [IsAffine B.thickening.target.scheme]
    (g : A ⟶ B) : (Thickening.moduleRestrictionSheaf M A).HasGlobalPresentation :=
  hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal M hcrys g
    (hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine hlqc B)

namespace SmallSite

namespace CohomologyRestriction

variable (M : SheafOfModules.{u} (structureSheaf S)) {A B : CrystallineThickening S}

/-- **A presentation of `F_{T'}` is carried to a presentation of `F_T` by an invertible
comparison map**, on the small crystalline site.  A morphism of `Cris(X/S)` is a morphism of
`CRIS(X/S)` between the underlying objects, and the comparison map is formed over the very same
`f`-map of restricted structure sheaves, so the argument is the big site's; it is repeated here
because a sheaf of modules on `Cris(X/S)` is in general not the restriction of one on
`CRIS(X/S)`. -/
noncomputable def presentationModuleRestrictionSheaf (g : A ⟶ B)
    (hg : IsIso (moduleComparisonSheaf M g))
    (p : (moduleRestrictionSheaf M B).Presentation) :
    (moduleRestrictionSheaf M A).Presentation :=
  haveI : (Opens.map g.hom.targetHom.hom.base).Final := Stacks.Topology.final_opensMap _
  haveI := hg
  (Stacks.SheafOfModules.pullbackPresentation
    (Thickening.ringRestrictionSheafFMap g.hom) p).ofIsIso (moduleComparisonSheaf M g)

/-- **A global presentation of `F_{T'}` is carried to a global presentation of `F_T` by an
invertible comparison map**, on the small crystalline site. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isIso_moduleComparisonSheaf (g : A ⟶ B)
    (hg : IsIso (moduleComparisonSheaf M g))
    (h : (moduleRestrictionSheaf M B).HasGlobalPresentation) :
    (moduleRestrictionSheaf M A).HasGlobalPresentation :=
  hasGlobalPresentation_of_presentation_map h (presentationModuleRestrictionSheaf M g hg)

end CohomologyRestriction

/-- **A crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` carries a global presentation of `F_{T'}` to
a global presentation of `F_T`, along every morphism of `Cris(X/S)`.**  [Stacks, Tag 07IT] is
stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike, and this is the small-site form of the
step that the theorem of the same name in the namespace `Crystalline.GlobalCrystallineSituation`
takes on the big site. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal
    (M : SheafOfModules.{u} (structureSheaf S)) (hM : IsSheafCrystal M)
    {A B : CrystallineThickening S} (g : A ⟶ B)
    (h : (CohomologyRestriction.moduleRestrictionSheaf M B).HasGlobalPresentation) :
    (CohomologyRestriction.moduleRestrictionSheaf M A).HasGlobalPresentation :=
  CohomologyRestriction.hasGlobalPresentation_moduleRestrictionSheaf_of_isIso_moduleComparisonSheaf
    M g (hM A B g) h

/-- **The restriction of a locally quasi-coherent sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` to an
affine ambient scheme has a global presentation over the restriction of `𝒪_{X/S}`**, the small-site
form of
`Crystalline.GlobalCrystallineSituation.hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine`.
The restriction with its scalars read in the structure sheaf of the ambient scheme is
`Crystalline.GlobalCrystallineSituation.SmallSite.ambientModuleRestriction`, which is
quasi-coherent in the sense of Mathlib by
`Crystalline.GlobalCrystallineSituation.SmallSite.isQuasicoherent_ambientModuleRestriction`;
[Stacks, Tag 03DX] presents it, and the change of scalars is run back along
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafStructureIso`. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine
    {M : SheafOfModules.{u} (structureSheaf S)} (hM : IsLocallyQuasiCoherent M)
    (B : CrystallineThickening S) [IsAffine B.obj.thickening.target.scheme] :
    (CohomologyRestriction.moduleRestrictionSheaf M B).HasGlobalPresentation :=
  SheafOfModules.HasGlobalPresentation.of_iso
    ((Stacks.Sheaves.RingedPoint.sheafRestrictScalarsCompIsoId
        (Thickening.ringRestrictionSheafStructureIso B.obj).inv
        (Thickening.ringRestrictionSheafStructureIso B.obj).hom (by simp)).app
      (CohomologyRestriction.moduleRestrictionSheaf M B))
    (Stacks.SheafOfModules.hasGlobalPresentation_restrictScalars_of_isIso
      (Thickening.ringRestrictionSheafStructureIso B.obj).hom _
      (Stacks.AlgebraicGeometry.AffinePresentation.hasGlobalPresentation_of_isQuasicoherentOnSite
        _ _ (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso _ _
          (isQuasicoherentOnSite_moduleRestrictionSheaf hM B))))

/-- **For a locally quasi-coherent crystal in `𝒪_{X/S}`-modules on `Cris(X/S)` and an object with
affine ambient scheme, the restriction `F_T` has a global presentation over every object of the
localised site.**  This is the small-site form of the theorem of the same name in the namespace
`Crystalline.GlobalCrystallineSituation`;
[Stacks, Tag 07IT] is stated for `𝒞 = CRIS(X/S)` and for `𝒞 = Cris(X/S)` alike. -/
theorem hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal_isAffine
    {M : SheafOfModules.{u} (structureSheaf S)} (hlqc : IsLocallyQuasiCoherent M)
    (hcrys : IsSheafCrystal M) {A B : CrystallineThickening S}
    [IsAffine B.obj.thickening.target.scheme] (g : A ⟶ B) :
    (CohomologyRestriction.moduleRestrictionSheaf M A).HasGlobalPresentation :=
  hasGlobalPresentation_moduleRestrictionSheaf_of_isSheafCrystal M hcrys g
    (hasGlobalPresentation_moduleRestrictionSheaf_of_isAffine hlqc B)

end SmallSite

end Crystalline.GlobalCrystallineSituation

end
