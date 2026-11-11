module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedLocalizationAffineSections
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# Tag 06ZR on a chosen big `τ`-site, for each of the five topologies

The chapter on adequate modules fixes `τ ∈ {Zar, étale, smooth, syntomic, fppf}` and a big
`τ`-site (Conventions, [Stacks, Tag 06Z3]), and [Stacks, Tag 06ZR] is stated for that `τ`: over
an affine scheme `U = Spec A`, the bounded below derived category `D⁺(Adeq(𝒪))` of the adequate
`𝒪`-modules on `(Sch/U)_τ` is the localization of `K⁺(QCoh(𝒪_U))` at the universal
quasi-isomorphisms.

The source's proof uses one input about `u : QCoh(𝒪_U) ⥤ Adeq(𝒪)`: a morphism `φ` of bounded
below complexes of quasi-coherent `𝒪_U`-modules is a universal quasi-isomorphism exactly when
`uφ` is a quasi-isomorphism. At `τ = fppf` that input is
`Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections` together with
the rewriting of `DerivedLocalizationAffineSections.lean`. This module carries it to the other
four topologies, by the observation the source makes in Descent, Lemma 0GNE: the functor
`𝓕 ↦ 𝓕^a` is given by the same formula for every `τ`.

Precisely, acyclicity of a bounded below complex of adequate `𝒪`-modules is read off its complex
of affine-section functors on the `A`-algebras of the site, for every `τ`
(`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq_eq`, from the
exactness of [Stacks, Tag 06ZJ]); those algebras depend only on the cutoff of the site; and the
affine sections of `𝓕^a` do not depend on the topology, naturally in `𝓕`
(`Stacks.Adequate.BigSite.associatedModuleQcohAffineSectionsIsoFppf`, from
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso`). So the input over the
big `τ`-site is the input over the big fppf site with the same cutoff.

## Main results

* `Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq_eq` —
  acyclicity in `Adeq(𝒪)` of a complex in the image of `u` read on affine sections, on a chosen
  big `τ`-site.
* `Stacks.Adequate.BigSite.associatedModuleQcohAffineSectionsIsoFppf` — the affine sections of
  `𝓕^a` on a big `τ`-site are those on the big fppf site with the same cutoff, naturally in `𝓕`.
* `Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_associatedModuleAdeq` — a bounded
  below complex of quasi-coherent `𝒪_U`-modules is universally acyclic exactly when its image
  under `u` is acyclic, on a chosen big `τ`-site.
* `Stacks.Adequate.BigSite.isLocalization_associatedModuleAdeq_universalQuasiIso` —
  **[Stacks, Tag 06ZR]**.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 06Z3](https://stacks.math.columbia.edu/tag/06Z3)
* [Stacks Project, Tag 0GNE](https://stacks.math.columbia.edu/tag/0GNE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {A : CommRingCat.{u}}

/-- The inverse image of an object property closed under isomorphisms along the
`mapHomotopyCategoryPlus` of a composite of additive functors depends on the composite only up
to isomorphism, even when the middle categories differ. -/
public theorem inverseImage_mapHomotopyCategoryPlus_comp_eq_of_iso
    {C M₁ M₂ D : Type*} [Category* C] [Category* M₁] [Category* M₂] [Category* D]
    [Preadditive C] [Preadditive M₁] [Preadditive M₂] [Preadditive D]
    (P : ObjectProperty (HomotopyCategory.Plus D)) [P.IsClosedUnderIsomorphisms]
    {X₁ : C ⥤ M₁} {Y₁ : M₁ ⥤ D} {X₂ : C ⥤ M₂} {Y₂ : M₂ ⥤ D}
    [X₁.Additive] [hY₁ : Y₁.Additive] [X₂.Additive] [Y₂.Additive] (e : X₁ ⋙ Y₁ ≅ X₂ ⋙ Y₂) :
    P.inverseImage (X₁ ⋙ Y₁).mapHomotopyCategoryPlus =
      P.inverseImage (X₂ ⋙ Y₂).mapHomotopyCategoryPlus :=
  inverseImage_eq_of_natIso P
    ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (X₁ ⋙ Y₁))).symm ≪≫
      Functor.mapHomotopyCategoryPlusCompIso e)

attribute [local instance] abelian_adequate

/-- **Acyclicity in `Adeq(𝒪)` of a complex in the image of `u`, read on affine sections**, on a
chosen big `τ`-site over `U = Spec A`: the complex `u𝓖^•` is acyclic exactly when its complex of
affine-section functors on the `A`-algebras of the site is. The affine-section functor is exact
and reflects isomorphisms on `Adeq(𝒪)`, by `Stacks.Adequate.preservesHomology_affineSections` and
`Stacks.Adequate.reflectsIsomorphisms_affineSections`. -/
public theorem BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq_eq
    (B : BigSite τ (Spec A)) :
    (HomotopyCategory.Plus.subcategoryAcyclic
          (adequate.{u, u} B).FullSubcategory).inverseImage
        B.associatedModuleAdeq.mapHomotopyCategoryPlus =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (AdequateFunctor.ModuleValuedFunctorOn.{u}
            (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))).inverseImage
        (B.associatedModuleQcoh ⋙
          affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).mapHomotopyCategoryPlus := by
  let := preservesHomology_affineSections B
  let := reflectsIsomorphisms_affineSections B
  rw [plus_subcategoryAcyclic_eq_inverseImage
    ((adequate.{u, u} B).ι ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)))]
  exact inverseImage_eq_of_natIso _ (Functor.mapHomotopyCategoryPlusCompIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((adequate.{u, u} B).liftCompιIso B.associatedModuleQcoh
          B.isAdequate_associatedModuleQcoh_obj)
        (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)))))

/-- **The affine sections of `𝓕^a` do not depend on the topology, naturally in `𝓕`.** On the
chosen big `τ`-site whose topology is the `τ`-topology on the big fppf category of `P` over
`Spec A`, the affine sections of the associated module of a quasi-coherent `𝒪_{Spec A}`-module
are those computed on the big fppf site of `P`. This is
`AlgebraicGeometry.BigFppfOver.restrictTopologyAssociatedModuleQcohIso` — the associated module
on `(Sch/U)_τ` is the one on `(Sch/U)_fppf` read for the coarser topology — followed by the
affine-section functor, which reads only the underlying presheaf of modules. -/
public noncomputable def BigSite.associatedModuleQcohAffineSectionsIsoFppf
    (P : BigFppfSite.{u}) (hP : P.Contains (Spec A)) (base_mem : schemeSizeBelow P.cutoff (Spec A))
    (isSheaf) (chosen) :
    (⟨P.cutoff, base_mem, BigFppfOver.baseOverTopology P (Spec A) hP τ.toSiteKind, isSheaf,
        chosen⟩ : BigSite τ (Spec A)).associatedModuleQcoh ⋙
        affineSectionsFunctor.{u, u}
          (⟨P.cutoff, base_mem, BigFppfOver.baseOverTopology P (Spec A) hP τ.toSiteKind, isSheaf,
            chosen⟩ : BigSite τ (Spec A)) A (𝟙 (Spec A)) ≅
      (BigSite.ofBigFppfSite P (Spec A) hP).associatedModuleQcoh ⋙
        affineSectionsFunctor.{u, u} (BigSite.ofBigFppfSite P (Spec A) hP) A (𝟙 (Spec A)) :=
  Functor.isoWhiskerRight
      (BigFppfOver.restrictTopologyAssociatedModuleQcohIso P (Spec A) hP τ.toSiteKind)
      (affineSectionsFunctor.{u, u}
        (⟨P.cutoff, base_mem, BigFppfOver.baseOverTopology P (Spec A) hP τ.toSiteKind, isSheaf,
          chosen⟩ : BigSite τ (Spec A)) A (𝟙 (Spec A))) ≪≫
    Functor.associator _ _ _

/-- **The input of [Stacks, Tag 06ZR] at `τ = fppf`.** A bounded below complex of quasi-coherent
`𝒪_U`-modules is universally acyclic exactly when its image under `u` in `Adeq(𝒪)` is acyclic.
This is `Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections` with
the right-hand side read back through
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections` and
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq`. -/
public theorem BigSite.universallyAcyclic_eq_inverseImage_associatedModuleAdeq_ofBigFppfSite
    (P : BigFppfSite.{u}) (hP : P.Contains (Spec A)) :
    universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (adequate.{u, u} (BigSite.ofBigFppfSite P (Spec A) hP)).FullSubcategory).inverseImage
        (BigSite.ofBigFppfSite P (Spec A) hP).associatedModuleAdeq.mapHomotopyCategoryPlus :=
  ((BigSite.universallyAcyclic_eq_inverseImage_qcohAllAlgebraSections P hP).trans
    (BigSite.plus_subcategoryAcyclic_inverseImage_qcohAllAlgebraSections P hP).symm).trans
    (BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq P hP).symm

/-- **The input of [Stacks, Tag 06ZR], on a chosen big `τ`-site for each of the five
topologies.** A bounded below complex of quasi-coherent `𝒪_U`-modules is universally acyclic
exactly when its image under `u : QCoh(𝒪_U) ⥤ Adeq(𝒪)` is acyclic.

The topology of a chosen big `τ`-site is the `τ`-topology on the big fppf category with the same
cutoff, by `Stacks.Adequate.BigSite.exists_baseOverTopology`. Both sides of the statement are
then read on affine sections over the same `A`-algebras, by
`Stacks.Adequate.BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq_eq`, where
they agree by `Stacks.Adequate.BigSite.associatedModuleQcohAffineSectionsIsoFppf`; and at
`τ = fppf` the statement is
`Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_associatedModuleAdeq_ofBigFppfSite`. -/
public theorem BigSite.universallyAcyclic_eq_inverseImage_associatedModuleAdeq
    (B : BigSite τ (Spec A)) :
    universallyAcyclic (Spec A) =
      (HomotopyCategory.Plus.subcategoryAcyclic
          (adequate.{u, u} B).FullSubcategory).inverseImage
        B.associatedModuleAdeq.mapHomotopyCategoryPlus := by
  obtain ⟨κ, base_mem, J, isSheaf, chosen⟩ := B
  obtain ⟨P, hP, e, hJ⟩ := BigSite.exists_baseOverTopology ⟨κ, base_mem, J, isSheaf, chosen⟩
  cases e
  obtain rfl := eq_of_heq hJ
  have e := BigSite.associatedModuleQcohAffineSectionsIsoFppf P hP base_mem isSheaf chosen
  have h := inverseImage_mapHomotopyCategoryPlus_comp_eq_of_iso
    (HomotopyCategory.Plus.subcategoryAcyclic
      (AdequateFunctor.ModuleValuedFunctorOn.{u}
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow P.cutoff)))) e.symm
    (hY₁ := affineSectionsFunctor_additive (BigSite.ofBigFppfSite P (Spec A) hP) A (𝟙 (Spec A)))
  rw [BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq_eq]
  exact ((BigSite.universallyAcyclic_eq_inverseImage_associatedModuleAdeq_ofBigFppfSite P hP).trans
    (BigSite.plus_subcategoryAcyclic_inverseImage_associatedModuleAdeq_eq
      (BigSite.ofBigFppfSite P (Spec A) hP))).trans h

/-- **[Stacks, Tag 06ZR].** Over an affine scheme `U = Spec A`, on a chosen big `τ`-site over
`U` for any of the five topologies `τ ∈ {Zar, étale, smooth, syntomic, fppf}`, the bounded below
derived category `D⁺(Adeq(𝒪))` is the localization of `K⁺(QCoh(𝒪_U))` at the universal
quasi-isomorphisms: the functor `K⁺(QCoh(𝒪_U)) ⥤ D⁺(Adeq(𝒪))` induced by `u` is a localization
functor for them.

This is
`Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv`
— the source's argument, from the embedding of every adequate module into a module in the image
of `u` ([Stacks, Tag 06VK]) and [Stacks, Tag 05T6] — with its input supplied by
`Stacks.Adequate.universalQuasiIso_eq_inverseImage_of_universallyAcyclic_eq` on
`Stacks.Adequate.BigSite.universallyAcyclic_eq_inverseImage_associatedModuleAdeq`. -/
@[stacks 06ZR "`D⁺(Adeq(𝒪))`, taken as the source does as the localization of `K⁺(Adeq(𝒪))` at
the quasi-isomorphisms, is the localization of `K⁺(QCoh(𝒪_U))` at the universal
quasi-isomorphisms along `u`, for `U = Spec A` and `(Sch/U)_τ` a chosen big `τ`-site over `U`
for each of the five topologies `τ`"]
public theorem BigSite.isLocalization_associatedModuleAdeq_universalQuasiIso
    (B : BigSite τ (Spec A)) :
    (B.associatedModuleAdeq.mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} B).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  B.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv
    (universalQuasiIso_eq_inverseImage_of_universallyAcyclic_eq _
      (B.universallyAcyclic_eq_inverseImage_associatedModuleAdeq))

end Stacks.Adequate

end
