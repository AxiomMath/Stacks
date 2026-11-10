module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteFlatCover
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteModuleExtensionCartesian
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSitePullbacks
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AlgebraSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Pullback
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.Sheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves

/-!
# A topology on the algebras of an affine of the site, with the module extensions as sheaves

`Stacks.Adequate.AffineAdequateSheafTopology` asks, for every affine scheme `Spec A` of a chosen
big `τ`-site over `S`, for a topology on the `A`-algebras of the site which makes the
affine-spectrum functor continuous and cocontinuous and for which every module extension
`C ↦ C ⊗_A M` is a sheaf. It was the one input of [Stacks, Tag 06VP] that the library did not
supply. This file supplies it.

## Main results

* `Stacks.Adequate.affineAdequateSheafTopology` — **`Stacks.Adequate.AffineAdequateSheafTopology`
  for every chosen big site, with no hypothesis, at every value universe.**
* `Stacks.Adequate.isSheaf_moduleExtensionFunctorOn` — the module extensions `C ↦ C ⊗[A] M` of
  the `A`-algebras of the site are sheaves for the induced topology, for an `A`-module `M` of
  arbitrary value universe.
* `Stacks.Adequate.isSheaf_affineSectionFunctor` — the affine sections of a sheaf of modules are
  a sheaf for the induced topology.

## The construction

The topology is not new: it is `Stacks.Adequate.affineSubsiteTopology` *of the localization of
the ambient big site at `Spec A`*, and the point of the file is that every one of the three
conditions is already available there.

A chosen big site over `S` is the localization of an ambient big `τ`-site `𝒮` at `S`
(`Stacks.Adequate.BigSite.exists_eq_ofAmbient`), so for an affine `Spec A` of the site the
localization of the same `𝒮` at `Spec A` is again a chosen big site, `B' = BigSite.ofAmbient 𝒮
(Spec A) hA`, whose base is affine. Over an affine base the `A`-algebras of the site are a dense
subsite (`Stacks.Adequate.affineSpecOver_isDenseSubsite`), and the two sites are related by
`Over.map` of the structure morphism, which is continuous and cocontinuous because the
localized topology of a big site is the localization of its topology
(`AlgebraicGeometry.overTopology_eq_siteTopology_over`). The affine-spectrum functor of the
original site at `(A, f)` is, *on the nose*, the affine-spectrum functor of `B'` for the
identity structure morphism followed by that `Over.map`
(`Stacks.Adequate.affineSpecOver_eq_localizationMap_comp`), so it inherits both conditions.

That the structure morphism `f` is arbitrary is what makes this route necessary. The
affine-spectrum functor is full only when the base is `Spec A` and `f` is the identity — a
morphism of the site between spectra of `A`-algebras need not respect the `A`-structure unless
the base is `Spec A` — so the dense-subsite argument cannot be run at a general `f` directly.
Continuity and cocontinuity, unlike fullness, are stable under composition, and the composite
above routes the general `f` through the one case where fullness holds.

The third condition is the module extensions, and it is proved by descent on the algebras
themselves rather than by transport from the big site. The module extension `C ↦ C ⊗_A M` is a
*cartesian* presheaf of modules — its restriction along `C ⟶ D` is the cancellation isomorphism
`D ⊗_C (C ⊗_A M) ≅ D ⊗_A M` of a tower of base changes
(`Stacks.Adequate.isIso_restrictionBaseChange_moduleExtension`) — and every covering sieve of
the induced topology is refined by a finite family of algebra maps which is a flat covering of
spectra (`Stacks.Adequate.exists_finite_flat_refinement_algebraSite`, from the cofinality of the
finite affine coverings, `Stacks.Adequate.BigSite.affineCovCofinal`). A cartesian presheaf of
modules is a sheaf for such a topology,
`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'`: over a finite flat
covering the rings of sections form a faithfully flat family
(`Stacks.Adequate.faithfullyFlat_pi_algebraSiteRings_map`) and the double overlaps are
tensor-product squares (`Stacks.Adequate.isPushout_algebraSiteRings_of_isPullback`), so
faithfully flat descent applies. No descent is re-proved here either: it is
`Stacks.PresheafOfModules.isSheafFor_of_cartesian`, which is unconditional.

## Universes

The result is proved at `AffineAdequateSheafTopology.{u, m}` for an arbitrary `m`, so the
consumers of the hypothesis — [Stacks, Tag 06VP] in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Sheafification.lean` and the clauses of
[Stacks, Tag 06VQ] in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/Abelian.lean` and
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/TopologyIndependence.lean`, all stated
over sheaves of modules of value universe `max u m` — can discharge it by
`Stacks.Adequate.affineAdequateSheafTopology B` without narrowing to `m = u`.

Reaching an arbitrary `m` is the reason the third condition is proved by descent on the algebras
rather than by transport from the big site. The transport route identifies a module extension
with the affine sections of an associated `𝒪`-module, and that identification runs through
`AlgebraicGeometry.tilde`, which takes a `ModuleCat.{u} A`: Mathlib's
`AlgebraicGeometry.Scheme.Modules` is `CategoryTheory.SheafOfModules.{u}` over the structure sheaf
of a `Scheme.{u}`, and `CategoryTheory.SheafOfModules.IsQuasicoherent` is defined only when the
value universe of the module agrees with the universe of the sheaf of rings. So the whole
associated-module pipeline is pinned to `m = u`, and no generalisation of a single lemma unpins it.

The cartesian route crosses none of that. Its two universe-sensitive steps are both free: the
cancellation isomorphism of a tower of base changes is polymorphic in the module, and the
assembly of the per-covering sheaf axiom into the sheaf condition uses
`Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget`, which amalgamates element by element and
so relates no universe of the sections to any universe of the site. Mathlib's
`CategoryTheory.Presheaf.isSheaf_iff_isSheaf_comp` would do the same assembly but asks the value
category for limits of the size of the site, which would force the sections to dominate the
universe of the algebras and lose exactly the generality wanted here; that is why
`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'` exists alongside
`Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements`.

## References

* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u m

namespace Stacks.Adequate

/-! ### The module extensions over an affine base -/

section AffineBase

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The affine sections of a sheaf of modules on a chosen big site over `Spec A` are a sheaf for
the topology induced on the `A`-algebras of the site: they are the restriction of the sheaf
along the affine-spectrum functor, which is continuous. -/
public theorem isSheaf_affineSectionFunctor (F : SheafOfModules.{max u m} B.structureSheaf) :
    Presheaf.IsSheaf (affineSubsiteTopology B)
      (affineSectionFunctor.{u, max u m} B F A (𝟙 (Spec A))).presheaf := by
  change Presheaf.IsSheaf (affineSubsiteTopology B)
    ((affineSpecOver B A (𝟙 (Spec A))).op ⋙ F.val.presheaf)
  exact (affineSpecOver B A (𝟙 (Spec A))).op_comp_isSheaf_of_isSheaf
    (affineSubsiteTopology B) B.topology F.val.presheaf F.isSheaf

/-- **The module extensions are sheaves over an affine base, at every value universe.**
`C ↦ C ⊗[A] M` is a cartesian presheaf of modules on the `A`-algebras of the site, every
covering sieve of the induced topology is refined by a finite family which is a flat covering of
spectra, and a cartesian presheaf of modules is a sheaf for such a topology.

The value universe of `M` is unconstrained because every step is: the cancellation isomorphism
that makes a module extension cartesian is universe-polymorphic in the module, and the sheaf
condition is assembled from the per-covering axiom by
`Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget`, which relates no universe of the
sections to any universe of the site.  See the module documentation. -/
public theorem isSheaf_moduleExtensionFunctorOn (M : ModuleCat.{max u m} A) :
    Presheaf.IsSheaf (affineSubsiteTopology B)
      ((AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion (A : Type u)
          (schemeSizeBelow B.cutoff))).obj M).presheaf :=
  Stacks.PresheafOfModules.isSheaf_of_cartesian_of_flat_refinements'.{u, u + 1, u,
      max u m, u, u}
    (algebraSiteScheme B) (algebraSiteRings B)
    (fun E hfin hE => faithfullyFlat_pi_algebraSiteRings_map B E hfin hE)
    (fun h => isPushout_algebraSiteRings_of_isPullback B h) _
    (fun {_ _} f => isIso_restrictionBaseChange_moduleExtension.{u, m} B M f) _
    (fun S hS => exists_finite_flat_refinement_algebraSite B S hS)

end AffineBase

/-! ### Passing to an arbitrary structure morphism -/

section Ambient

variable {τ : CoveringTopology} {S : Scheme.{u}}
  (𝒮 : AlgebraicGeometry.BigSite.{u} τ)
  (hS : S.size < AlgebraicGeometry.cutoff τ 𝒮)
  (A : CommRingCat.{u}) (f : Spec A ⟶ S)
  (hA : (Spec A).size < AlgebraicGeometry.cutoff τ 𝒮)

/-- The structure morphism of an affine of the site, read as a morphism of the ambient site. -/
public noncomputable abbrev baseHomOf :
    AlgebraicGeometry.base 𝒮 (Spec A) hA ⟶ AlgebraicGeometry.base 𝒮 S hS :=
  ObjectProperty.homMk f

/-- The comparison from the localization of the ambient big site at `Spec A` to its
localization at `S`: composition with the structure morphism. -/
public noncomputable abbrev localizationMap :
    (BigSite.ofAmbient 𝒮 (Spec A) hA).category ⥤ (BigSite.ofAmbient 𝒮 S hS).category :=
  Over.map (baseHomOf 𝒮 hS A f hA)

/-- The topology of the localization of the ambient big site at `X` is the localization of its
topology. -/
private theorem topology_ofAmbient_eq {X : Scheme.{u}}
    (hX : X.size < AlgebraicGeometry.cutoff τ 𝒮) :
    (BigSite.ofAmbient 𝒮 X hX).topology =
      (AlgebraicGeometry.siteTopology τ 𝒮).over (AlgebraicGeometry.base 𝒮 X hX) :=
  AlgebraicGeometry.overTopology_eq_siteTopology_over _ _ _ _

/-- The comparison is continuous: `Over.map` is continuous between localizations. -/
public theorem isContinuous_localizationMap :
    (localizationMap 𝒮 hS A f hA).IsContinuous
      (BigSite.ofAmbient 𝒮 (Spec A) hA).topology (BigSite.ofAmbient 𝒮 S hS).topology := by
  rw [topology_ofAmbient_eq, topology_ofAmbient_eq]
  exact inferInstanceAs ((Over.map (baseHomOf 𝒮 hS A f hA)).IsContinuous _ _)

/-- The comparison is cocontinuous, by the same identification of the localized topology. -/
public theorem isCocontinuous_localizationMap :
    (localizationMap 𝒮 hS A f hA).IsCocontinuous
      (BigSite.ofAmbient 𝒮 (Spec A) hA).topology (BigSite.ofAmbient 𝒮 S hS).topology := by
  rw [topology_ofAmbient_eq, topology_ofAmbient_eq]
  exact inferInstanceAs ((Over.map (baseHomOf 𝒮 hS A f hA)).IsCocontinuous _ _)

/-- **The affine-spectrum functor at an arbitrary structure morphism factors through the
localization at the affine.** Both sides send an `A`-algebra of the site to its spectrum, over
`S` through `f`; the two structure morphisms are the same composite, so this holds by
definitional unfolding. -/
public theorem affineSpecOver_eq_localizationMap_comp :
    affineSpecOver (BigSite.ofAmbient 𝒮 S hS) A f =
      affineSpecOver (BigSite.ofAmbient 𝒮 (Spec A) hA) A (𝟙 (Spec A)) ⋙
        localizationMap 𝒮 hS A f hA := rfl

/-- The affine-spectrum functor at an arbitrary structure morphism is continuous for the
topology induced on the `A`-algebras by the localization at `Spec A`. -/
public theorem isContinuous_affineSpecOver :
    (affineSpecOver (BigSite.ofAmbient 𝒮 S hS) A f).IsContinuous
      (affineSubsiteTopology (BigSite.ofAmbient 𝒮 (Spec A) hA))
      (BigSite.ofAmbient 𝒮 S hS).topology := by
  have := isContinuous_localizationMap 𝒮 hS A f hA
  exact Functor.isContinuous_comp
    (affineSpecOver (BigSite.ofAmbient 𝒮 (Spec A) hA) A (𝟙 (Spec A)))
    (localizationMap 𝒮 hS A f hA)
    (affineSubsiteTopology (BigSite.ofAmbient 𝒮 (Spec A) hA))
    (BigSite.ofAmbient 𝒮 (Spec A) hA).topology (BigSite.ofAmbient 𝒮 S hS).topology

/-- The affine-spectrum functor at an arbitrary structure morphism is cocontinuous for the same
topology. -/
public theorem isCocontinuous_affineSpecOver :
    (affineSpecOver (BigSite.ofAmbient 𝒮 S hS) A f).IsCocontinuous
      (affineSubsiteTopology (BigSite.ofAmbient 𝒮 (Spec A) hA))
      (BigSite.ofAmbient 𝒮 S hS).topology := by
  have := isCocontinuous_localizationMap 𝒮 hS A f hA
  exact CategoryTheory.isCocontinuous_comp
    (G := affineSpecOver (BigSite.ofAmbient 𝒮 (Spec A) hA) A (𝟙 (Spec A)))
    (G' := localizationMap 𝒮 hS A f hA)
    (J := affineSubsiteTopology (BigSite.ofAmbient 𝒮 (Spec A) hA))
    (K := (BigSite.ofAmbient 𝒮 (Spec A) hA).topology)
    (L := (BigSite.ofAmbient 𝒮 S hS).topology)

end Ambient

/-! ### The hypothesis of Tag 06VP, discharged -/

/-- **`Stacks.Adequate.AffineAdequateSheafTopology`, proved, with no hypothesis.** For every
affine scheme `Spec A` of a chosen big `τ`-site over `S` there is a topology on the `A`-algebras
of the site making the affine-spectrum functor continuous and cocontinuous and for which every
module extension `C ↦ C ⊗[A] M` is a sheaf: the topology induced on them by the localization of
the ambient big site at `Spec A`, where they are a dense subsite and where the module extensions
are the affine sections of the associated modules. -/
public theorem affineAdequateSheafTopology {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : AffineAdequateSheafTopology.{u, m} B := by
  obtain ⟨𝒮, hS, rfl⟩ := B.exists_eq_ofAmbient
  intro A f hA
  exact ⟨affineSubsiteTopology (BigSite.ofAmbient 𝒮 (Spec A) hA),
    isCocontinuous_affineSpecOver 𝒮 hS A f hA,
    isContinuous_affineSpecOver 𝒮 hS A f hA,
    isSheaf_moduleExtensionFunctorOn (BigSite.ofAmbient 𝒮 (Spec A) hA)⟩

end Stacks.Adequate

end
