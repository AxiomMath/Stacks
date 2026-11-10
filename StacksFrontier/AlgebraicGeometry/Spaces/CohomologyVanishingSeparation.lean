module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafIsos
public import StacksFrontier.AlgebraicGeometry.AmpleH1Vanishing.SectionsEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraDegreeZero
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDefiningIdeal
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianOfGlobalPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
-- for `AlgebraicGeometry.Space.sieve_mem_of_forall_isAffine_hom`, used in a proof below; not
-- `public`, since no statement of this module mentions it
import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective

/-!
# Separating disjoint closed sets by a global function

Let `X` be an algebraic space all of whose quasi-coherent modules have vanishing first
cohomology, and write `A = Γ(X, 𝒪_X)`. Given two disjoint closed subsets `Z₀, Z₁ ⊆ |X|` one
wants `a ∈ A` with `Z₀ ⊆ V(a)` and `Z₁ ⊆ V(a - 1)`: a function vanishing along `Z₀` and
equal to `1` along `Z₁`. The vanishing locus `V(a)` is the complement of
`AlgebraicGeometry.Space.sectionSupport`, the set of points at which `a` does not vanish.

**That statement is proved here**, as
`AlgebraicGeometry.Space.CohomologyVanishingSituation`'s
`exists_subset_compl_sectionSupport_of_disjoint`. The route runs through the reduced closed
subspaces `W₀, W₁` of Stacks 03IQ on the two sets.
Global sections are right exact against a quasi-coherent kernel, which is where the cohomology
hypothesis is consumed; brought down to the module universe of the structure sheaf this says that
`𝓘_{W₀} ⟶ 𝒪_X ⟶ i_*𝒪_{W₁}` is surjective on global sections, once that morphism is an
epimorphism with quasi-coherent kernel. Both of those come from the defining ideal sheaves of the
two subspaces, through the two statements of
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspaceDefiningIdeal.lean`: disjointness
makes
the two defining ideals comaximal on every affine chart, which gives the epimorphism, and the two
defining ideal sheaves meet in the defining ideal sheaf of the reduced closed subspace of
`Z₀ ∪ Z₁`, which gives quasi-coherence of the kernel. Lifting the image of `1` then yields the
function, and the point-set conclusion `Z₀ ⊆ V(a)` is read off the étale charts.

The affine case is proved separately and independently, by the comaximality argument on an affine
scheme: two disjoint closed subsets of an affine scheme have comaximal vanishing ideals, so `1`
splits as a sum of a function vanishing on the first and a function vanishing on the second.

## Main results

* `AlgebraicGeometry.Space.CohomologyVanishingSituation.epi_globalSections_map_of_shortExact`
  and `…surjective_sectionsMap_of_shortExact`: in the situation of Stacks 07UY, global
  sections take a short exact sequence of `𝒪_X`-modules with quasi-coherent first term to a
  surjection, so every global section of the third term is the image of one of the second.
* `SheafOfModules.kerIotaCompIso`: the kernel of a morphism out of a submodule `N ⊆ M` induced by
  a morphism `h : M ⟶ P` is the meet of `N` with the kernel of `h`.
* `SheafOfModules.IsQuasicoherentOnSite.ulift`, `SheafOfModules.kerUliftForPresentationIso`,
  `SheafOfModules.epi_uliftForPresentationMap` and
  `SheafOfModules.surjective_sectionsMap_of_ulift`: raising the universe of the sections of a
  sheaf of modules preserves quasi-coherence, kernels and epimorphisms, and surjectivity on
  global sections descends along the lift.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_of_epi`: in the
  situation of Stacks 07UY, global sections carry an epimorphism of `𝒪_X`-modules whose kernel
  is quasi-coherent to a surjection. This is the previous statement transported to the module
  universe of the structure sheaf itself, which is where the ideal sheaves of Stacks 03MB live.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_structureProjection`
  states that **in the situation of Stacks 07UY every global regular function on a closed
  subspace `Z ⊆ X` is the restriction of a global regular function on `X`.** This is the step
  of Stacks 07V1 that consumes the cohomology hypothesis.
* `AlgebraicGeometry.exists_sub_one_mem_vanishingIdeal_of_disjoint`: on an affine scheme, two
  disjoint closed subsets are separated by a global function — `a` vanishes on the first and
  `a - 1` on the second. This is the comaximality step of Stacks 07V1.
* `AlgebraicGeometry.exists_isIdempotentElem_basicOpen_eq`: a clopen subset of a scheme is the
  nonvanishing locus of an idempotent global function. This is what splits the structure sheaf
  of a space whose points are the disjoint union of two closed sets.
* `AlgebraicGeometry.Space.subset_compl_sectionSupport_iff_forall_chart`: a set of points of
  an algebraic space lies in the vanishing locus of a global function exactly when, on every
  étale chart, the function vanishes at every point of the chart lying over it.
* `AlgebraicGeometry.Space.epi_ι_comp_structureProjection` and
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_ker_ι_comp_structureProjection`: for two closed
  subspaces `W₀, W₁ ⊆ X` whose defining ideals are comaximal on the affine étale charts lying over
  a fixed surjective chart, the morphism `𝓘_{W₀} ⟶ 𝒪_X ⟶ i_*𝒪_{W₁}` is an epimorphism; and its
  kernel is quasi-coherent as soon as the two defining ideal sheaves meet in the defining ideal
  sheaf of a closed subspace.
* `AlgebraicGeometry.Space.subset_compl_sectionSupport_of_forall_mem_definingIdealAt`: a global
  regular function which is a section of the defining ideal sheaf of a closed subspace over every
  étale chart vanishes at every point of that subspace.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation`'s
  `exists_mem_definingIdealAt_and_sub_one_mem`: in the situation of Stacks 07UY, two closed
  subspaces whose defining ideals are comaximal on the affine charts and meet in the defining
  ideal sheaf of a third are separated by a global regular function, at the level of ideal
  memberships.
* `AlgebraicGeometry.Space.CohomologyVanishingSituation`'s
  `exists_subset_compl_sectionSupport_of_disjoint`: **Stacks 07V1 for an algebraic space.** In
  the situation of Stacks 07UY two disjoint closed subsets `Z₀, Z₁ ⊆ |X|` are separated by a
  global regular function `a ∈ A = Γ(X, 𝒪_X)`: `Z₀ ⊆ V(a)` and `Z₁ ⊆ V(a - 1)`.

## Implementation notes

The cohomology of `𝒪_X`-modules is `Stacks.Cohomology.SiteModules.globalModuleCohomology` on
the small étale ringed site, and `globalModuleCohomology O n` is by definition the `n`-th right
derived functor of `Stacks.Cohomology.SiteModules.globalSectionsFunctor O`. So the vanishing
hypothesis of `AlgebraicGeometry.Space.CohomologyVanishingSituation` is literally the
hypothesis of `Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one`, and the
only thing to supply is that global sections preserve finite limits, which is
`Stacks.Cohomology.SiteModules.preservesFiniteLimits_globalSectionsFunctor`. The module
universe is the one the vanishing hypothesis quantifies over, so no universe lifting is
needed: the statement below is about `AlgebraicGeometry.Space.Modules` at
`max (u + 1) m`, exactly where `firstCohomologyVanishing` lives.

That universe is *not* the one the geometry lives in. The structure sheaf `𝒪_X` is a sheaf of
rings in `RingCat.{u}`, so `𝒪_X` as a module over itself and every sheaf of ideals of it —
`AlgebraicGeometry.Space.definingIdealSheaf`, and hence the short exact sequence
`0 → 𝓘_Z → 𝒪_X → i_*𝒪_Z → 0` of
`AlgebraicGeometry.Space.definingIdealShortComplex_shortExact` — have their sections in
`Type u`, and `max (u + 1) m` is never `u`. The bridge is
`SheafOfModules.uliftForPresentation`, the objectwise `ULift` of the sections: it carries the
sequence to the universe `u + 1`, where it stays short exact because kernels and local
surjectivity are objectwise, and it preserves quasi-coherence because
`SheafOfModules.HasGlobalPresentation` is itself a statement about the lift of the module to
the presentation universe, which for a site of `Scheme.{u}`-charts is already `u + 1`. So a
global presentation of `M` *is* one of `uliftForPresentation M` once the double lift is undone
by `Stacks.SheafOfModules.uliftForPresentationIsoSelf`.

The two statements in the situation of Stacks 07UY which use that bridge are stated for
`AlgebraicGeometry.Space.CohomologyVanishingSituation.{u, u}` rather than for a general module
universe `m`. The reason is the same universe arithmetic: the bridge lands at `u + 1`, and
`max (u + 1) m` is `u + 1` only for the instantiation `m := u`. That instantiation is the
weakest form of the vanishing hypothesis — it asks for `H¹ = 0` on quasi-coherent modules whose
sections lie in `Type (u + 1)`, the smallest universe in which the first cohomology of the small
étale site can be formed at all — so it is not a restriction on the geometry, only on how
general the statement is in a universe parameter that Stacks 07UY does not have. Lifting these
two statements to a general `m` needs the lift from `u` to `max (u + 1) m` to preserve
quasi-coherence, which is a genuinely stronger statement than the one proved here: the
coproducts of a global presentation have to move with it.

On an affine scheme the comaximality is read on the ideal sheaves
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` of the two closed sets rather than on
their reduced closed subschemes: the support of a join of ideal sheaves is the intersection of
the supports, so disjointness makes the join have empty support and hence be the unit ideal
sheaf, and the unit is recovered at the affine open `⊤` as a sum of a section of each. Taking
the subschemes and intersecting kernels of their closed immersions would prove the same thing
through `AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine`, but needs the
subschemes to be built first.

The chart criterion is phrased with the non-vanishing locus
`AlgebraicGeometry.Space.sectionSupport` because that is the notion the library already relates
to the basic opens of the charts, through
`AlgebraicGeometry.Space.mem_sectionSupport_iff`: membership is detected on *any* single chart,
which is what makes the criterion an equivalence rather than only a sufficient condition.

**The route actually taken to Stacks 07V1 uses no compatible family of idempotents.** The
original plan was to produce the global function on the reduced closed subspace `W` of `Z₀ ∪ Z₁`
which is `0` along `Z₀` and `1` along `Z₁` — each of `Z₀, Z₁` being open in `|W|`, so that on each
étale chart of `W` the two preimages are complementary clopen subsets and
`AlgebraicGeometry.exists_isIdempotentElem_basicOpen_eq` supplies a separating function there —
and then to extend it along `surjective_sectionsMap_structureProjection`. That needs the
compatibility of the family of idempotents across the chart morphisms, which is not proved
anywhere. It is not needed: applying
`AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_of_epi` not to
`𝒪_X ⟶ i_*𝒪_{W₁}` but to `𝓘_{W₀} ⟶ 𝒪_X ⟶ i_*𝒪_{W₁}` lets the function be lifted directly out of
the ideal, and the only thing the lift has to be applied to is the image of the global function
`1`, which exists without any chartwise construction.

`AlgebraicGeometry.exists_isIdempotentElem_basicOpen_eq` is therefore not used by the proof of
Stacks 07V1 here; it is kept because it is the scheme-level statement that a clopen subset is the
non-vanishing locus of an idempotent, which is what Stacks 07V1 specialises to when `Z₀` and `Z₁`
cover `|X|`.

## References

* [Stacks Project, Tag 07V1](https://stacks.math.columbia.edu/tag/07V1)
* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 047X](https://stacks.math.columbia.edu/tag/047X)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 09RP](https://stacks.math.columbia.edu/tag/09RP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SiteModules

attribute [local instance] HasDerivedCategory.standard

universe u m

/-! ### Raising the universe of the sections of a sheaf of modules

The results of this section are about an arbitrary site whose objects form a `Type (u + 1)` with
morphisms in `Type u`, carrying a sheaf of rings in `RingCat.{u}` — the shape of the small étale
ringed site of an algebraic space over `Scheme.{u}`. They say that the objectwise `ULift` of the
sections from `Type u` to `Type (u + 1)` preserves quasi-coherence, kernels and epimorphisms,
and that surjectivity on global sections descends along it. -/

namespace SheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}

/-- **A global presentation survives raising the universe of the sections.** A global
presentation of `M` is already a presentation of the lift of `M` to the presentation universe,
which for a site of this shape is `u + 1`; the only thing to do is to undo the resulting double
lift, which `Stacks.SheafOfModules.uliftForPresentationIsoSelf` does. -/
theorem HasGlobalPresentation.ulift {M : SheafOfModules.{u} R}
    (h : HasGlobalPresentation.{u + 1, u, u, u} M) :
    HasGlobalPresentation.{u + 1, u, u, u + 1}
      (uliftForPresentation.{u + 1, u, u, u, u + 1} M) := by
  obtain ⟨I, K, P, Q, ιP, κQ, hP, hQ, a, b, hab, hc⟩ := h
  refine ⟨I, K, P, Q, ιP, κQ, hP, hQ, a,
    b ≫ (Stacks.SheafOfModules.uliftForPresentationIsoSelf.{u + 1, u, u, 0}
      (uliftForPresentation.{u + 1, u, u, u, u + 1} M)).hom, ?_, ⟨?_⟩⟩
  · rw [← Category.assoc, hab, zero_comp]
  · exact hc.some.ofIsoColimit (Cofork.ext
      (Stacks.SheafOfModules.uliftForPresentationIsoSelf.{u + 1, u, u, 0}
        (uliftForPresentation.{u + 1, u, u, u, u + 1} M)) rfl)

/-- **Quasi-coherence survives raising the universe of the sections.** The coverings witnessing
quasi-coherence are the same ones, because the lift is objectwise and therefore commutes with
restriction to a slice of the site. -/
theorem IsQuasicoherentOnSite.ulift {M : SheafOfModules.{u} R}
    (h : M.IsQuasicoherentOnSite) :
    (uliftForPresentation.{u + 1, u, u, u, u + 1} M).IsQuasicoherentOnSite where
  locally_hasGlobalPresentation V := by
    obtain ⟨I, Vs, f, hcov, hpres⟩ := h.locally_hasGlobalPresentation V
    exact ⟨I, Vs, f, hcov, fun i => (hpres i).ulift⟩

/-- **The kernel of the universe lift of a morphism is the universe lift of its kernel.** Both
are computed objectwise, and a lifted section is annihilated exactly when the section it lifts
is. -/
noncomputable def kerUliftForPresentationIso {M N : SheafOfModules.{u} R} (g : M ⟶ N) :
    (Submodule.ker (uliftForPresentationMap.{u + 1, u, u, u, u + 1} g)).toSheafOfModules ≅
      uliftForPresentation.{u + 1, u, u, u, u + 1} (Submodule.ker g).toSheafOfModules :=
  (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun _ => LinearEquiv.toModuleIso
        { toFun := fun x => ULift.up ⟨x.1.down, ULift.down_inj.2 x.2⟩
          invFun := fun y => ⟨ULift.up y.down.1, congrArg ULift.up y.down.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
      (fun {_ _} _ => by ext x; rfl))

/-- **The universe lift of an epimorphism is an epimorphism.** An epimorphism of sheaves of
modules is a locally surjective morphism of the underlying presheaves of abelian groups, and
lifting the sections does not change the image sieves. -/
theorem epi_uliftForPresentationMap [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    {M N : SheafOfModules.{u} R} (g : M ⟶ N) (hg : Epi g) :
    Epi (uliftForPresentationMap.{u + 1, u, u, u, u + 1} g) := by
  have := hg
  have h0 : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map g.val) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi g
  have hfac : (PresheafOfModules.toPresheaf R.obj).map
      (uliftForPresentationMap.{u + 1, u, u, u, u + 1} g).val =
      Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map g.val)
        AddCommGrpCat.uliftFunctor.{u + 1} := rfl
  have h1 : Presheaf.IsLocallySurjective J
      (Functor.whiskerRight ((PresheafOfModules.toPresheaf R.obj).map g.val)
        AddCommGrpCat.uliftFunctor.{u + 1}) := inferInstance
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ (hfac ▸ h1)

/-- Raising the universe of a compatible family of sections of a sheaf of modules. -/
noncomputable def uliftForPresentationSections {M : SheafOfModules.{u} R} (s : M.sections) :
    (uliftForPresentation.{u + 1, u, u, u, u + 1} M).sections :=
  PresheafOfModules.sectionsMk (fun X => ULift.up (s.val X))
    (fun _ _ _ => congrArg ULift.up (s.property _))

/-- The universe lift of sections of a sheaf of modules is injective. -/
theorem uliftForPresentationSections_injective {M : SheafOfModules.{u} R} :
    Function.Injective (uliftForPresentationSections (M := M)) := fun _ _ h =>
  PresheafOfModules.sections_ext _ _
    fun X => congrArg ULift.down (congrFun (congrArg Subtype.val h) X)

/-- The universe lift of sections of a sheaf of modules is surjective. -/
theorem uliftForPresentationSections_surjective {M : SheafOfModules.{u} R} :
    Function.Surjective (uliftForPresentationSections (M := M)) := fun t =>
  ⟨PresheafOfModules.sectionsMk (fun X => (t.val X).down)
      (fun _ _ f => congrArg ULift.down (t.property f)),
    PresheafOfModules.sections_ext _ _ fun _ => rfl⟩

/-- The map on sections induced by the universe lift of a morphism `g` sends the lift of a
section `s` to the lift of its image under `g`. -/
theorem sectionsMap_uliftForPresentationSections {M N : SheafOfModules.{u} R} (g : M ⟶ N)
    (s : M.sections) :
    sectionsMap (uliftForPresentationMap.{u + 1, u, u, u, u + 1} g)
        (uliftForPresentationSections s) =
      uliftForPresentationSections (sectionsMap g s) :=
  PresheafOfModules.sections_ext _ _ fun _ => rfl

/-- **Surjectivity on global sections descends from the universe lift.** -/
theorem surjective_sectionsMap_of_ulift {M N : SheafOfModules.{u} R} (g : M ⟶ N)
    (h : Function.Surjective
      (sectionsMap (uliftForPresentationMap.{u + 1, u, u, u, u + 1} g))) :
    Function.Surjective (sectionsMap g) := by
  intro t
  obtain ⟨s', hs'⟩ := h (uliftForPresentationSections t)
  obtain ⟨s, rfl⟩ := uliftForPresentationSections_surjective s'
  exact ⟨s, uliftForPresentationSections_injective
    ((sectionsMap_uliftForPresentationSections g s).symm.trans hs')⟩

/-- **The kernel of a morphism out of a submodule is the meet of that submodule with the kernel
of the morphism it is induced by.** For a submodule `N ⊆ M` and `h : M ⟶ P`, a section of `N` is
annihilated by `h` exactly when the section of `M` it is is, so the two submodules have the same
sections and the comparison is the identity on underlying sections. -/
noncomputable def kerIotaCompIso {M P : SheafOfModules.{u} R} (N : M.Submodule) (h : M ⟶ P) :
    (Submodule.ker (N.ι ≫ h)).toSheafOfModules ≅
      (N ⊓ Submodule.ker h).toSheafOfModules :=
  (fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun X => LinearEquiv.toModuleIso
        { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
      (fun {_ _} _ => by ext x; rfl))

end SheafOfModules

namespace AlgebraicGeometry

/-! ### Comaximality on an affine scheme -/

/-- **Two disjoint closed subsets of an affine scheme are separated by a global function.**
The vanishing ideals of the two sets are comaximal, because the support of their join is the
intersection of the two sets, so `1` is a sum `a + b` with `a` vanishing on the first set and
`b` on the second; then `a - 1 = -b` vanishes on the second. -/
@[stacks 07V1 "the conclusion for an affine scheme, with the two closed subsets taken in the \
scheme rather than in the points of an algebraic space"]
theorem exists_sub_one_mem_vanishingIdeal_of_disjoint (X : Scheme.{u}) [IsAffine X]
    {T₀ T₁ : Set X} (hT₀ : IsClosed T₀) (hT₁ : IsClosed T₁) (hdisj : Disjoint T₀ T₁) :
    ∃ a : Γ(X, ⊤), T₀ ⊆ X.zeroLocus {a} ∧ T₁ ⊆ X.zeroLocus {a - 1} := by
  classical
  set I₀ := Scheme.IdealSheafData.vanishingIdeal (⟨T₀, hT₀⟩ : Closeds X) with hI₀
  set I₁ := Scheme.IdealSheafData.vanishingIdeal (⟨T₁, hT₁⟩ : Closeds X) with hI₁
  have hs₀ : ((I₀.support : Closeds X) : Set X) = T₀ := by rw [hI₀]; rfl
  have hs₁ : ((I₁.support : Closeds X) : Set X) = T₁ := by rw [hI₁]; rfl
  have hsup : I₀ ⊔ I₁ = ⊤ := by
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
    refine SetLike.coe_injective ?_
    rw [Closeds.coe_inf, hs₀, hs₁]
    exact hdisj.inter_eq
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have htop : I₀.ideal U ⊔ I₁.ideal U = ⊤ := by
    have h := congrArg (fun I : X.IdealSheafData => I.ideal U) hsup
    rw [Scheme.IdealSheafData.ideal_sup] at h
    simpa using h
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Submodule.mem_sup.1 (htop ▸ Submodule.mem_top : (1 : Γ(X, U.1)) ∈ _)
  have key : ∀ (I : X.IdealSheafData) (T : Set X), ((I.support : Closeds X) : Set X) = T →
      ∀ f ∈ I.ideal U, T ⊆ X.zeroLocus {f} := by
    intro I T hT f hf x hx
    have hxs : x ∈ I.support := by rwa [← SetLike.mem_coe, hT]
    have hz := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) (Set.mem_univ x)).1 hxs
    simp only [Scheme.mem_zeroLocus_iff, Set.mem_singleton_iff, forall_eq]
    exact (Scheme.mem_zeroLocus_iff X _ x).1 hz f hf
  refine ⟨a, key I₀ T₀ hs₀ a ha, key I₁ T₁ hs₁ (a - 1) ?_⟩
  rw [show a - 1 = -b by rw [← hab]; ring]
  exact neg_mem hb

/-! ### Clopen subsets and idempotent global functions -/

/-- **An open subset of a scheme which is also closed is the nonvanishing locus of an
idempotent global function.** The subset and its complement are disjoint opens covering the
scheme, so the sections `1` and `0` on them are compatible and glue; the glued function is
idempotent and has the subset as its basic open because both can be checked on each of the two
pieces. -/
theorem exists_isIdempotentElem_basicOpen_eq (X : Scheme.{u}) (U : X.Opens)
    (hU : IsClosed (U : Set X)) :
    ∃ e : Γ(X, ⊤), IsIdempotentElem e ∧ X.basicOpen e = U := by
  classical
  let V : X.Opens := ⟨(U : Set X)ᶜ, hU.isOpen_compl⟩
  let W : Bool → X.Opens := fun b => cond b U V
  have hsup : iSup W = ⊤ := by
    refine le_antisymm le_top fun x _ => ?_
    by_cases h : x ∈ (U : Set X)
    exacts [Opens.mem_iSup.2 ⟨true, h⟩, Opens.mem_iSup.2 ⟨false, h⟩]
  let iUV : ∀ b, W b ⟶ (⊤ : X.Opens) := fun _ => homOfLE le_top
  let sf : ∀ b, ToType (X.sheaf.1.obj (op (W b))) :=
    fun b => Bool.rec (0 : Γ(X, V)) (1 : Γ(X, U)) b
  have hst : sf true = (1 : Γ(X, U)) := rfl
  have hsf : sf false = (0 : Γ(X, V)) := rfl
  have hbot : ∀ i j : Bool, i ≠ j → W i ⊓ W j = ⊥ := by
    intro i j hij
    rcases i with _ | _ <;> rcases j with _ | _ <;> first
      | exact absurd rfl hij
      | (apply SetLike.coe_injective
         simp only [Opens.coe_inf, Opens.coe_bot, W, V, Bool.cond_true, Bool.cond_false]
         simp [Set.inter_comm])
  have hsub : ∀ i j : Bool, i ≠ j →
      ∀ s t : ToType (X.sheaf.1.obj (op (W i ⊓ W j))), s = t := by
    intro i j hij s t
    have hss : Subsingleton (ToType (X.sheaf.1.obj (op (W i ⊓ W j)))) := by
      rw [hbot i j hij]; exact inferInstanceAs (Subsingleton Γ(X, ⊥))
    exact hss.elim s t
  have hcpt : TopCat.Presheaf.IsCompatible X.sheaf.1 W sf := by
    intro i j
    rcases i with _ | _ <;> rcases j with _ | _
    · rfl
    · exact hsub false true (by simp) _ _
    · exact hsub true false (by simp) _ _
    · rfl
  obtain ⟨e, he, -⟩ :=
    X.sheaf.existsUnique_gluing' W ⊤ iUV (le_of_eq hsup.symm) sf hcpt
  refine ⟨e, ?_, ?_⟩
  · refine X.sheaf.eq_of_locally_eq' W ⊤ iUV (le_of_eq hsup.symm) (e * e) e fun b => ?_
    rcases b with _ | _
    · rw [map_mul, he false, hsf]; exact mul_zero _
    · rw [map_mul, he true, hst]; exact mul_one _
  · have hres : ∀ b, X.basicOpen (X.sheaf.1.map (iUV b).op e) = W b ⊓ X.basicOpen e :=
      fun b => Scheme.basicOpen_res (X := X) e (iUV b).op
    have h₁ : U = W true ⊓ X.basicOpen e := by
      rw [← hres true, he true, hst, X.basicOpen_one (U := U)]
    have h₂ : (⊥ : X.Opens) = W false ⊓ X.basicOpen e := by
      rw [← hres false, he false, hsf, X.basicOpen_zero V]
    refine le_antisymm (fun x hx => ?_) (fun x hx => (h₁.symm ▸ hx : x ∈ W true ⊓ _).2)
    by_contra h
    exact absurd (show x ∈ (W false ⊓ X.basicOpen e : X.Opens) from ⟨h, hx⟩)
        (h₂ ▸ (fun hh => hh : x ∈ (⊥ : X.Opens) → False))

namespace Space

/-! ### The vanishing locus of a global function, read on the charts -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **A set of points lies in the vanishing locus of a global function exactly when the
function vanishes at every chart point above it.** The vanishing locus is the complement of
`AlgebraicGeometry.Space.sectionSupport`, and membership in the support is detected on any
single chart, which is what makes this an equivalence. -/
theorem subset_compl_sectionSupport_iff_forall_chart (a : globalFunctions B S hS F)
    (Z : Set (points B S hS F)) :
    Z ⊆ (sectionSupport B S hS F a)ᶜ ↔
      ∀ (U : SmallEtale B S hS F) (p : points B S hS (yoneda.obj U.obj.left)),
        pointsMap B S hS (yoneda.obj U.obj.left) U.obj.hom p ∈ Z →
        pointsToScheme B S hS U.obj.left p ∉
          ((BigFppfOver.toScheme B S hS).obj U.obj.left).basicOpen (a.val (op U)) := by
  refine ⟨fun h U p hp hb => h hp ((mem_sectionSupport_iff B S hS F a U p).2 hb), ?_⟩
  intro h x hx hmem
  obtain ⟨U, p, hb, he⟩ := hmem
  exact h U p (he ▸ hx) hb

/-! ### Comaximal defining ideals and the structure projection -/

section Comaximal

variable (X : AlgebraicSpaces B S hS)

/-- **Comaximality on the affine charts makes `𝓘_{W₀} ⟶ 𝒪_X ⟶ i_*𝒪_{W₁}` an epimorphism.**

An epimorphism of `𝒪_X`-modules is a locally surjective morphism, so it is enough to produce, for
a section `s` of `i_*𝒪_{W₁}` over a chart, a covering family of arrows along which `s` restricts
into the image. The structure projection is itself locally surjective, by the corresponding clause
of Stacks 03MB, so after restricting to a chart `Z` the section is `π₁(a)` for some regular
function `a` on `Z`; and on an affine chart `A` over `Uc` comaximality splits `a` as `b₀ + b₁`
with `b₀` a section of `𝓘_{W₀}` and `b₁` a section of `𝓘_{W₁}`. Since `𝓘_{W₁}` is the kernel of
`π₁` — `AlgebraicGeometry.Space.ker_structureProjection` — the section `b₀` already has the right
image. No surjectivity of `Γ(A) ⟶ Γ(W₁ ×_X A)` is needed. -/
theorem epi_ι_comp_structureProjection
    (W₀ W₁ : ClosedSubspaces B S hS X.1) (Uc : SmallEtale B S hS X.1)
    (hsurj : IsSurjective B S hS Uc.1.hom)
    (hcom : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ Uc) →
      definingIdealAt B S hS X W₀ (op A) ⊔ definingIdealAt B S hS X W₁ (op A) = ⊤) :
    Epi ((definingIdealSheaf B S hS X W₀).ι ≫ structureProjection B S hS X W₁) := by
  have hker := ker_structureProjection B S hS X W₁
  have hπ : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      ((PresheafOfModules.toPresheaf (structureRingSheaf B S hS X).obj).map
        (structureProjection B S hS X W₁).val) := by
    have h : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
        (structureSharp B S hS (subspaceInclusion B S hS X W₁)).hom :=
      isLocallySurjective_structureSharp B S hS (subspaceInclusion B S hS X W₁) W₁.2.2
    rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
    exact ⟨fun {_} s ↦ h.imageSieve_mem s⟩
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {V} s => ?_⟩
  refine (SmallEtale.topology B S hS X.1).transitive
    (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf
      (structureRingSheaf B S hS X).obj).map
      (structureProjection B S hS X W₁).val) s) _ ?_
  intro Z f hf
  rw [Presheaf.pullback_imageSieve]
  obtain ⟨a, ha⟩ := hf
  refine sieve_mem_of_forall_isAffine_hom B S hS X Uc hsurj Z _ fun A hA mA k => ?_
  obtain ⟨b₀, hb₀, b₁, hb₁, hsum⟩ := Submodule.mem_sup.1
    (Submodule.eq_top_iff'.1 (hcom A hA mA)
      ((SheafOfModules.unit (structureRingSheaf B S hS X)).val.map k.op a))
  refine ⟨⟨b₀, hb₀⟩, ?_⟩
  have hmem : b₁ ∈ (SheafOfModules.Submodule.ker
      (structureProjection B S hS X W₁)).obj (op A) := by
    rwa [hker]
  have hzero : PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val (op A) b₁ = 0 :=
    (PresheafOfModules.Submodule.mem_ker (structureProjection B S hS X W₁).val (op A) b₁).1 hmem
  have ha' : PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val (op Z) a =
      (pushforwardStructureSheaf B S hS X W₁).val.map f.op s := ha
  have hsplit : PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val (op A)
      (b₀ + b₁) = PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val (op A) b₀ :=
    ((ConcreteCategory.hom (PresheafOfModules.Hom.app
      (structureProjection B S hS X W₁).val (op A))).map_add b₀ b₁).trans
        (by rw [hzero]; exact add_zero _)
  -- Term mode rather than `rw […, ha']`: the two sides of the residual goal differ only in
  -- whether the scalar ring of the ambient `LinearMap` reads `structureRingSheaf B S hS X` or
  -- its unfolding `Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite …).O`, which
  -- the reducible-transparency `rfl` that `rw` finishes with cannot bridge.
  have hgoal : PresheafOfModules.Hom.app (structureProjection B S hS X W₁).val (op A)
      ((SheafOfModules.unit (structureRingSheaf B S hS X)).val.map k.op a) =
      (pushforwardStructureSheaf B S hS X W₁).val.map k.op
        ((pushforwardStructureSheaf B S hS X W₁).val.map f.op s) :=
    (PresheafOfModules.naturality_apply (structureProjection B S hS X W₁).val k.op a).trans
      (congrArg (fun t => (pushforwardStructureSheaf B S hS X W₁).val.map k.op t) ha')
  exact (hsplit.symm.trans (congrArg (PresheafOfModules.Hom.app
    (structureProjection B S hS X W₁).val (op A)) hsum)).trans hgoal

/-- **The kernel of `𝓘_{W₀} ⟶ i_*𝒪_{W₁}` is quasi-coherent as soon as the meet of the two
defining ideal sheaves is one.** The kernel is the meet of `𝓘_{W₀}` with the kernel of the
structure projection, by `SheafOfModules.kerIotaCompIso`, and that kernel is `𝓘_{W₁}`; so the
hypothesis identifies it with the defining ideal sheaf of a closed subspace, which is
quasi-coherent by `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`. -/
theorem isQuasicoherentOnSite_ker_ι_comp_structureProjection
    (W₀ W₁ W : ClosedSubspaces B S hS X.1)
    (hinf : definingIdealSheaf B S hS X W₀ ⊓ definingIdealSheaf B S hS X W₁ =
      definingIdealSheaf B S hS X W) :
    (SheafOfModules.Submodule.ker ((definingIdealSheaf B S hS X W₀).ι ≫
      structureProjection B S hS X W₁)).toSheafOfModules.IsQuasicoherentOnSite := by
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    (SheafOfModules.kerIotaCompIso (definingIdealSheaf B S hS X W₀)
      (structureProjection B S hS X W₁)).symm ?_
  rw [ker_structureProjection, hinf]
  exact isQuasicoherentOnSite_definingIdealSheaf B S hS X W

/-- The global section `1` of the structure sheaf, as a section of `𝒪_X` viewed as a module over
itself. -/
noncomputable def oneSections :
    (SheafOfModules.unit (structureRingSheaf B S hS X)).sections :=
  PresheafOfModules.sectionsMk
    (fun V => (1 : (structureRingSheaf B S hS X).obj.obj V))
    (fun _ _ f => map_one ((structureRingSheaf B S hS X).obj.map f).hom)


/-- **A global regular function lying in the defining ideal sheaf of a closed subspace vanishes
at every point of that subspace.**

The criterion `AlgebraicGeometry.Space.subset_compl_sectionSupport_iff_forall_chart` reduces this
to one chart `U` at a time. There the points of `X` lying in the subspace are, by Stacks 03H4
through `AlgebraicGeometry.Space.preimage_range_pointsMap_eq_range_pointsMap_snd`, the image of
the base change `W ×_X U ⟶ U`; and the defining ideal at `U` is the kernel of pullback of regular
functions along that morphism, so the preimage of the non-vanishing locus of the function is the
non-vanishing locus of `0`, which is empty. -/
theorem subset_compl_sectionSupport_of_forall_mem_definingIdealAt
    (W : ClosedSubspaces B S hS X.1) (a : globalFunctions B S hS X.1)
    (hmem : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ, a.val V ∈ definingIdealAt B S hS X W V) :
    Set.range (pointsMap B S hS W.1.toFunctor W.1.ι) ⊆
      (sectionSupport B S hS X.1 a)ᶜ := by
  rw [subset_compl_sectionSupport_iff_forall_chart]
  intro U p hpz hb
  obtain ⟨r, hr⟩ : ∃ r : Γ((BigFppfOver.toScheme B S hS).obj U.1.left, ⊤),
      r = a.val (op U) := ⟨a.val (op U), rfl⟩
  rw [← hr] at hb
  have hz : ((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd U.1.hom)).appTop r = 0 := by
    have h := hmem (op U)
    rw [definingIdealAt_eq_ker, Scheme.Γ_map_op] at h
    rwa [hr]
  have hprange : p ∈ (pointsEquivScheme B S hS U.1.left).symm ''
      Set.range ((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd U.1.hom)).base := by
    rwa [← range_pointsMap_yoneda_map,
      ← preimage_range_pointsMap_eq_range_pointsMap_snd B S hS W.2.2.rep U.1.hom]
  obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := hprange
  rw [pointsToScheme_pointsEquivScheme_symm] at hb
  have hb' : z ∈ ((BigFppfOver.toScheme B S hS).map (W.2.2.rep.snd U.1.hom)) ⁻¹ᵁ
      (((BigFppfOver.toScheme B S hS).obj U.1.left).basicOpen r) := hb
  rw [Scheme.preimage_basicOpen_top, hz,
    Scheme.basicOpen_zero _ (⊤ : ((BigFppfOver.toScheme B S hS).obj
      (W.2.2.rep.pullback U.1.hom)).Opens)] at hb'
  exact hb'

end Comaximal

/-! ### Lifting global sections in the situation of Stacks 07UY -/

namespace CohomologyVanishingSituation

variable (T : CohomologyVanishingSituation.{u, m})

/-- **Global sections are right exact against a quasi-coherent kernel.** On an algebraic space
whose quasi-coherent modules have vanishing first cohomology, a short exact sequence of
`𝒪_X`-modules whose first term is quasi-coherent stays exact on the right after taking global
sections. -/
theorem epi_globalSections_map_of_shortExact
    {Q : ShortComplex (Modules.{u, max (u + 1) m} T.site T.base T.containsBase
      T.space.1 T.space.2)}
    (hQ : Q.ShortExact) (h₁ : Q.X₁.IsQuasicoherentOnSite) :
    Epi ((globalSectionsFunctor.{u + 1, u, u, max (u + 1) m}
      (structureRingSheaf T.site T.base T.containsBase T.space)).map Q.g) := by
  have hs : HasSheafify (SmallEtale.topology T.site T.base T.containsBase T.space.1)
      AddCommGrpCat.{max (u + 1) m} := site_hasSheafify_addCommGrp
  have hpf := preservesFiniteLimits_globalSectionsFunctor.{u + 1, u, u, m}
    (structureRingSheaf T.site T.base T.containsBase T.space)
  exact Stacks.Cohomology.SectionsEpi.epi_map_g_of_isZero_rightDerived_one _ hQ
    (T.firstCohomologyVanishing ⟨Q.X₁, h₁⟩)

/-- **A global section of the quotient lifts.** The elementwise form of
`AlgebraicGeometry.Space.CohomologyVanishingSituation.epi_globalSections_map_of_shortExact`:
every compatible family of sections of the third term of the sequence is the image of one of
the second. -/
theorem surjective_sectionsMap_of_shortExact
    {Q : ShortComplex (Modules.{u, max (u + 1) m} T.site T.base T.containsBase
      T.space.1 T.space.2)}
    (hQ : Q.ShortExact) (h₁ : Q.X₁.IsQuasicoherentOnSite) :
    Function.Surjective (SheafOfModules.sectionsMap Q.g) :=
  (ModuleCat.epi_iff_surjective _).1 (T.epi_globalSections_map_of_shortExact hQ h₁)

/-! ### Lifting global sections at the module universe of the structure sheaf -/

section SmallUniverse

variable (T' : CohomologyVanishingSituation.{u, u})

/-- **Global sections are right exact against a quasi-coherent kernel, at the module universe of
the structure sheaf.** On an algebraic space whose quasi-coherent modules have vanishing first
cohomology, an epimorphism of `𝒪_X`-modules whose sheaf-theoretic kernel is quasi-coherent stays
surjective on global sections.

This is
`AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_of_shortExact`
transported from the module universe `max (u + 1) m` at which the vanishing hypothesis is
imposed down to the universe `u` of the sections of the structure sheaf, which is where the ideal
sheaves of Stacks 03MB live. The transport is along `SheafOfModules.uliftForPresentation`, and it
is what forces the situation here to be one at `m := u`; see the implementation notes. -/
@[sga "6 II 2.1.2" "Clause b)"]
theorem surjective_sectionsMap_of_epi
    {M N : Modules.{u, u} T'.site T'.base T'.containsBase T'.space.1 T'.space.2} (g : M ⟶ N)
    (hg : Epi g)
    (hker : (SheafOfModules.Submodule.ker g).toSheafOfModules.IsQuasicoherentOnSite) :
    Function.Surjective (SheafOfModules.sectionsMap g) := by
  refine SheafOfModules.surjective_sectionsMap_of_ulift g ?_
  have hs : HasSheafify
      (smallEtaleRingedSite T'.site T'.base T'.containsBase T'.space.1 T'.space.2).J
      AddCommGrpCat.{u + 1} := site_hasSheafify_addCommGrp.{u + 1, u, 0}
  let _ : Abelian (Modules.{u, u + 1} T'.site T'.base T'.containsBase T'.space.1 T'.space.2) :=
    _root_.SheafOfModules.instAbelian _
  have hQ : (ShortComplex.mk
      (C := Modules.{u, u + 1} T'.site T'.base T'.containsBase T'.space.1 T'.space.2)
      (SheafOfModules.Submodule.ker
        (SheafOfModules.uliftForPresentationMap.{u + 1, u, u, u, u + 1} g)).ι
      (SheafOfModules.uliftForPresentationMap.{u + 1, u, u, u, u + 1} g)
      (SheafOfModules.Submodule.ker_ι_comp _)).ShortExact :=
    { exact := ShortComplex.exact_of_f_is_kernel _
        (SheafOfModules.Submodule.isLimitKernelFork _)
      mono_f := mono_of_isLimit_fork (SheafOfModules.Submodule.isLimitKernelFork _)
      epi_g := SheafOfModules.epi_uliftForPresentationMap g hg }
  exact T'.surjective_sectionsMap_of_shortExact hQ
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      (SheafOfModules.kerUliftForPresentationIso g).symm hker.ulift)

/-- **In Situation 07UY every global regular function on a closed subspace is the restriction of
a global regular function on the space.** For a closed subspace `i : Z ⟶ X` with defining ideal
sheaf `𝓘_Z`, the canonical map `𝒪_X ⟶ i_*𝒪_Z` is surjective on global sections.

This is the step of Stacks 07V1 which consumes the vanishing hypothesis. Its two inputs are
Stacks 03MB — `𝓘_Z` is the kernel of `𝒪_X ⟶ i_*𝒪_Z`, by
`AlgebraicGeometry.Space.ker_structureProjection`, and it is quasi-coherent, by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf` — and the surjectivity of
that map, `AlgebraicGeometry.Space.epi_structureProjection`. -/
theorem surjective_sectionsMap_structureProjection
    (Z : ClosedSubspaces T'.site T'.base T'.containsBase T'.space.1) :
    Function.Surjective (SheafOfModules.sectionsMap
      (structureProjection T'.site T'.base T'.containsBase T'.space Z)) := by
  refine T'.surjective_sectionsMap_of_epi
    (structureProjection T'.site T'.base T'.containsBase T'.space Z)
    (epi_structureProjection T'.site T'.base T'.containsBase T'.space Z) ?_
  exact (ker_structureProjection T'.site T'.base T'.containsBase T'.space Z) ▸
    isQuasicoherentOnSite_definingIdealSheaf T'.site T'.base T'.containsBase T'.space Z

attribute [local instance] pointTopology

/-- **In Situation 07UY, two closed subspaces whose defining ideals are comaximal on the affine
charts and meet in the defining ideal sheaf of a third are separated by a global regular
function.** There is `a ∈ Γ(X, 𝒪_X)` which is a section of `𝓘_{W₀}` over every étale chart and
whose difference from `1` is a section of `𝓘_{W₁}` over every étale chart.

This is where the cohomology hypothesis of Stacks 07UY is spent. The morphism
`𝓘_{W₀} ⟶ 𝒪_X ⟶ i_*𝒪_{W₁}` is an epimorphism with quasi-coherent kernel, by
`AlgebraicGeometry.Space.epi_ι_comp_structureProjection` and
`AlgebraicGeometry.Space.isQuasicoherentOnSite_ker_ι_comp_structureProjection`, so it is
surjective on global sections by
`AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_of_epi`; lifting the
image of the global function `1` produces `a`. -/
theorem exists_mem_definingIdealAt_and_sub_one_mem
    (W₀ W₁ W : ClosedSubspaces T'.site T'.base T'.containsBase T'.space.1)
    (Uc : SmallEtale T'.site T'.base T'.containsBase T'.space.1)
    (hsurj : IsSurjective T'.site T'.base T'.containsBase Uc.1.hom)
    (hcom : ∀ A : SmallEtale T'.site T'.base T'.containsBase T'.space.1,
      IsAffine ((BigFppfOver.toScheme T'.site T'.base T'.containsBase).obj
        ((SmallEtale.toOver T'.site T'.base T'.containsBase T'.space.1).obj A)) →
      (A ⟶ Uc) →
      definingIdealAt T'.site T'.base T'.containsBase T'.space W₀ (op A) ⊔
        definingIdealAt T'.site T'.base T'.containsBase T'.space W₁ (op A) = ⊤)
    (hinf : definingIdealSheaf T'.site T'.base T'.containsBase T'.space W₀ ⊓
        definingIdealSheaf T'.site T'.base T'.containsBase T'.space W₁ =
      definingIdealSheaf T'.site T'.base T'.containsBase T'.space W) :
    ∃ a : _root_.AlgebraicGeometry.Space.globalFunctions
        T'.site T'.base T'.containsBase T'.space.1,
      (∀ V : (SmallEtale T'.site T'.base T'.containsBase T'.space.1)ᵒᵖ,
        a.val V ∈ definingIdealAt T'.site T'.base T'.containsBase T'.space W₀ V) ∧
      ∀ V : (SmallEtale T'.site T'.base T'.containsBase T'.space.1)ᵒᵖ,
        a.val V - 1 ∈ definingIdealAt T'.site T'.base T'.containsBase T'.space W₁ V := by
  obtain ⟨s, hs⟩ := T'.surjective_sectionsMap_of_epi
    ((definingIdealSheaf T'.site T'.base T'.containsBase T'.space W₀).ι ≫
      structureProjection T'.site T'.base T'.containsBase T'.space W₁)
    (epi_ι_comp_structureProjection T'.site T'.base T'.containsBase T'.space W₀ W₁ Uc hsurj hcom)
    (isQuasicoherentOnSite_ker_ι_comp_structureProjection T'.site T'.base T'.containsBase
      T'.space W₀ W₁ W hinf)
    (SheafOfModules.sectionsMap
      (structureProjection T'.site T'.base T'.containsBase T'.space W₁)
      (oneSections T'.site T'.base T'.containsBase T'.space))
  refine ⟨SheafOfModules.sectionsMap
    (definingIdealSheaf T'.site T'.base T'.containsBase T'.space W₀).ι s,
    fun V => (s.val V).2, fun V => ?_⟩
  change _ - 1 ∈ (definingIdealSheaf T'.site T'.base T'.containsBase T'.space W₁).obj V
  rw [← ker_structureProjection T'.site T'.base T'.containsBase T'.space W₁]
  refine (PresheafOfModules.Submodule.mem_ker
    (structureProjection T'.site T'.base T'.containsBase T'.space W₁).val V _).2 ?_
  have hV : PresheafOfModules.Hom.app
        (structureProjection T'.site T'.base T'.containsBase T'.space W₁).val V
        ((SheafOfModules.sectionsMap
          (definingIdealSheaf T'.site T'.base T'.containsBase T'.space W₀).ι s).val V) =
      PresheafOfModules.Hom.app
        (structureProjection T'.site T'.base T'.containsBase T'.space W₁).val V
        (1 : (structurePresheaf T'.site T'.base T'.containsBase T'.space.1 ⋙
          forget CommRingCat).obj V) :=
    congrFun (congrArg Subtype.val hs) V
  exact ((ConcreteCategory.hom (PresheafOfModules.Hom.app
    (structureProjection T'.site T'.base T'.containsBase T'.space W₁).val V)).map_sub _ _).trans
      (by rw [hV]; exact sub_self _)

attribute [local instance] pointTopology

/-- **Stacks 07V1 for an algebraic space.** In the situation of Stacks 07UY, two disjoint closed
subsets `Z₀, Z₁` of the points of `X` are separated by a global regular function: there is
`a ∈ A = Γ(X, 𝒪_X)` with `Z₀ ⊆ V(a)` and `Z₁ ⊆ V(a - 1)`. The vanishing locus `V(-)` is the
complement of `AlgebraicGeometry.Space.sectionSupport`, the set of points at which a global
function does not vanish.

The function is produced by
`AlgebraicGeometry.Space.CohomologyVanishingSituation.exists_mem_definingIdealAt_and_sub_one_mem`
applied to the reduced closed subspaces of Stacks 03IQ on `Z₀`, on `Z₁` and on `Z₀ ∪ Z₁`. Its two
hypotheses are exactly the two statements about the defining ideal sheaves of reduced closed
subspaces proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspaceDefiningIdeal.lean`: the defining
ideals of the subspaces on two *disjoint* closed sets are comaximal on every affine chart, and the
defining ideal sheaves of the subspaces on `Z₀` and on `Z₁` meet in that of the subspace on
`Z₀ ∪ Z₁`. The passage from the resulting ideal memberships to the point-set conclusion is
`AlgebraicGeometry.Space.subset_compl_sectionSupport_of_forall_mem_definingIdealAt`.

The situation is one at the module universe of the structure sheaf — see the implementation
notes — because that is the form in which the lifting statement
`AlgebraicGeometry.Space.CohomologyVanishingSituation.surjective_sectionsMap_of_epi` is
available. -/
@[stacks 07V1 "the conclusion for an algebraic space, with the cohomology-vanishing hypothesis \
of Situation 07UY imposed at the module universe of the structure sheaf rather than at a general \
module universe"]
theorem exists_subset_compl_sectionSupport_of_disjoint
    {Z₀ Z₁ : Set (points T'.site T'.base T'.containsBase T'.space.1)}
    (hZ₀ : IsClosed Z₀) (hZ₁ : IsClosed Z₁) (hdisj : Disjoint Z₀ Z₁) :
    ∃ a : _root_.AlgebraicGeometry.Space.globalFunctions
        T'.site T'.base T'.containsBase T'.space.1,
      Z₀ ⊆ (_root_.AlgebraicGeometry.Space.sectionSupport
          T'.site T'.base T'.containsBase T'.space.1 a)ᶜ ∧
        Z₁ ⊆ (_root_.AlgebraicGeometry.Space.sectionSupport
          T'.site T'.base T'.containsBase T'.space.1 (a - 1))ᶜ := by
  let R : ∀ Z : Set (points T'.site T'.base T'.containsBase T'.space.1), IsClosed Z →
      ClosedSubspaces T'.site T'.base T'.containsBase T'.space.1 := fun Z hZ =>
    ⟨reducedClosedSubspace T'.site T'.base T'.containsBase T'.space.1 T'.space.2 Z hZ,
      isClosedSubspace_reducedClosedSubspace T'.site T'.base T'.containsBase T'.space.1
        T'.space.2 Z hZ⟩
  obtain ⟨a, ha₀, ha₁⟩ := exists_mem_definingIdealAt_and_sub_one_mem T'
    (R Z₀ hZ₀) (R Z₁ hZ₁) (R (Z₀ ∪ Z₁) (hZ₀.union hZ₁))
    ⟨CostructuredArrow.mk (Classical.choose
        (Classical.choose_spec T'.space.2.exists_atlas)),
      (Classical.choose_spec (Classical.choose_spec T'.space.2.exists_atlas)).2⟩
    ((presheafSurjective_iff_isSurjective_yoneda T'.site T'.base T'.containsBase
      T'.space.1 T'.space.2 _ _).1
        (Classical.choose_spec (Classical.choose_spec T'.space.2.exists_atlas)).1)
    (fun A hA m => sup_definingIdealAt_reducedClosedSubspace_of_disjoint T'.site T'.base
      T'.containsBase T'.space Z₀ Z₁ hZ₀ hZ₁ hdisj A hA m)
    (definingIdealSheaf_reducedClosedSubspace_inf T'.site T'.base T'.containsBase T'.space
      Z₀ Z₁ hZ₀ hZ₁)
  exact ⟨a,
    (range_pointsMap_ι_reducedClosedSubspace T'.site T'.base T'.containsBase
      T'.space.1 T'.space.2 Z₀ hZ₀).symm.subset.trans
      (subset_compl_sectionSupport_of_forall_mem_definingIdealAt T'.site T'.base
        T'.containsBase T'.space _ a ha₀),
    (range_pointsMap_ι_reducedClosedSubspace T'.site T'.base T'.containsBase
      T'.space.1 T'.space.2 Z₁ hZ₁).symm.subset.trans
      (subset_compl_sectionSupport_of_forall_mem_definingIdealAt T'.site T'.base
        T'.containsBase T'.space _ (a - 1) ha₁)⟩

end SmallUniverse

end CohomologyVanishingSituation

end Space

end AlgebraicGeometry

end
