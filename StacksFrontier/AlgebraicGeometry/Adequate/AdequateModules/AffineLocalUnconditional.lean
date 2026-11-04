module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.FlatBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.StandardAffineProductAdequacy

/-!
# Adequacy on every affine of the site, with no hypothesis

[Stacks, Tag 06VI] says that for an adequate sheaf of modules `F` on the big `τ`-site over `S`
the affine-section functor `F_{F, A}` is adequate at *every* affine scheme `Spec A` of the site
over `S`, not only at the members of the covering witnessing adequacy of `F`. The source's proof
has three steps, named in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineLocal.lean` as
`Stacks.Adequate.StandardAffineRefinement`, `Stacks.Adequate.AffineSectionRestriction` and
`Stacks.Adequate.StandardAffineDescent`, and all three are now theorems:
`Stacks.Adequate.standardAffineRefinement` and `Stacks.Adequate.affineSectionRestriction` there,
and `Stacks.Adequate.standardAffineDescent` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineProductAdequacy.lean`.
So Tag 06VI holds outright, and that is what this module states.

## Main results

* `Stacks.Adequate.isAdequate_affineSectionFunctor` — **[Stacks, Tag 06VI]**, with no hypothesis
  beyond adequacy of `F` itself.
* `Stacks.Adequate.affineLocalAdequacy` — the same conclusion for every adequate sheaf of
  modules at once: `Stacks.Adequate.AffineLocalAdequacy` holds for every chosen big site.
* `Stacks.Adequate.bijective_affineSectionBaseChangeMap` — **[Stacks, Tag 06VL]**, first step:
  the affine-section functor of an adequate sheaf of modules commutes with flat base change
  along any morphism of `A`-algebras of the site. It is Tag 06VI followed by [Stacks, Tag 06UW].
* `Stacks.Adequate.bijective_affineSectionBaseChangeMap_base` — its specialization to the
  structure morphism of a flat `A`-algebra `C` of the site: `F(Spec C) = C ⊗_A F(Spec A)`.

## Implementation notes

**Why these four statements are here and not in the modules they belong to.** The proof of
`Stacks.Adequate.standardAffineDescent` runs through the Čech-exactness of a standard affine
covering and the reduction of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/StandardAffineDescentReduction.lean`,
and those rest in turn on `AffineLocal.lean` — which supplies the affine-section machinery they
are stated with — and on
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/FlatBaseChangeSections.lean` and
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineSectionExactness.lean`. A
statement that *uses*
`Stacks.Adequate.standardAffineDescent` therefore cannot live in any of those three modules
without a cycle of imports, so the four statements whose only remaining hypothesis was
`Stacks.Adequate.StandardAffineDescent` are collected here, above the module that discharges it.
Nothing else changes about them: the hypotheses of `Stacks.Adequate.IsAdequate`, of flatness and
of membership of the site are untouched, and only the discharged one is gone.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

/-! ### Adequacy of the affine-section functors at every affine -/

/-- [Stacks, Tag 06VI]: for an adequate sheaf of modules `F` on the big `τ`-site over `S`, the
affine-section functor `F_{F, A}` is adequate for *every* affine scheme `Spec A` of the site
over `S`, not only for the members of the covering witnessing adequacy of `F`.

All three steps of the source's proof are supplied by the library:
`Stacks.Adequate.standardAffineRefinement` and `Stacks.Adequate.affineSectionRestriction`, which
discharge `StandardAffineRefinement` and `AffineSectionRestriction`, and
`Stacks.Adequate.standardAffineDescent`, which discharges `StandardAffineDescent`. See the module
documentation. -/
@[stacks 06VI]
public theorem isAdequate_affineSectionFunctor
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A)) :
    AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) := by
  obtain ⟨I, A₀, f₀, hcov, hsurj, hmem⟩ := hF
  obtain ⟨n, A', g, hstd, hsize, hfac⟩ :=
    standardAffineRefinement B I A₀ f₀ hcov hsurj (fun i => (hmem i).1) A f hA
  refine standardAffineDescent.{u, m} B F A f hA n A' g hstd hsize fun j => ?_
  obtain ⟨i, φ, hφ⟩ := hfac j
  exact hφ ▸ affineBaseChangeAdequacy B F (A₀ i) (A' j) φ (f₀ i) (hmem i).2

/-- [Stacks, Tag 06VI] applied to every adequate sheaf of modules at once:
`Stacks.Adequate.AffineLocalAdequacy` holds for every chosen big site. -/
public theorem affineLocalAdequacy {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) :
    AffineLocalAdequacy.{u, m} B :=
  fun F hF A f hA =>
    isAdequate_affineSectionFunctor.{u, m} B F hF A f hA

/-! ### Flat base change for the affine sections of an adequate module -/

/-- The affine-section functor of an adequate sheaf of modules commutes with flat base change
along any morphism of `A`-algebras of the site: this is [Stacks, Tag 06VI] followed by
[Stacks, Tag 06UW]. -/
public theorem bijective_affineSectionBaseChangeMap {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A))
    {C D : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)} (g : C ⟶ D)
    (hg : RingHom.Flat ((AdequateFunctor.siteAlgebraInclusion A
      (schemeSizeBelow B.cutoff)).map g).hom.toRingHom) :
    Function.Bijective (AdequateFunctor.moduleValuedFunctorBaseChangeMap
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) g) :=
  AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective _ _
    (isAdequate_affineSectionFunctor.{u, m} B F hF A f hA) g hg

/-- For an adequate sheaf of modules `F` and an `A`-algebra `C` of the site which is flat over
`A`, the canonical map `C ⊗_A F(Spec A) → F(Spec C)` is bijective. -/
public theorem bijective_affineSectionBaseChangeMap_base {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (hF : IsAdequate B F)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A))
    (C : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))
    (hC : Module.Flat A C.obj) :
    Function.Bijective (AdequateFunctor.moduleValuedFunctorBaseChangeMap
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))
      (affineSectionFunctor B F A f) (baseAlgebraInSiteHom B A hA C)) :=
  bijective_affineSectionBaseChangeMap.{u, m} B F hF A f hA
    (baseAlgebraInSiteHom B A hA C)
    (show RingHom.Flat (algebraMap A C.obj) from RingHom.flat_algebraMap_iff.mpr hC)

end Stacks.Adequate

end
