module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedAffineSections
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedSheafFunctor

/-!
# The quasi-inverse of the affine comparison, and the equivalence of Tag 06ZJ

Let `S = Spec A` be affine and let `B` be a chosen big `τ`-site over `S`.  The comparison
`𝓕 ↦ F_{𝓕, A}` from adequate `𝒪`-modules on `(Sch/S)_τ` to adequate module-valued functors on
`Alg_A` is `Stacks.Adequate.affineSectionsFunctor`, lifted to the two subcategories cut out by
adequacy; [Stacks, Tag 06ZJ] asserts that it is an **equivalence**.  This module supplies the
half that was missing, the quasi-inverse, and concludes the equivalence.

The source's quasi-inverse chooses, for an adequate functor `F`, an exact sequence
`0 → F → M̲ → N̲` and forms `𝓕 = Ker(M^a → N^a)`.  Here that construction is carried out as a
*functor* on `A`-modules rather than a choice: `Stacks.Adequate.associatedTilde`, of
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedSheafFunctor.lean`, sends an
`A`-module `M` to `M^a`, the associated `𝒪`-module of the quasi-coherent `𝒪_S`-module `M^~`,
and the exact sequence is chosen only inside the proof of an existence statement, so no
independence-of-the-choice argument is needed.

## Main definitions

* `Stacks.Adequate.affineBaseSectionsFunctor` — the sections over the base affine as a functor;
  on objects it is `Stacks.Adequate.affineBaseSections` and on morphisms
  `Stacks.Adequate.affineBaseSectionsMap`.
* `Stacks.Adequate.affineSectionsCompareNatTrans` — the comparison `C ⊗_A 𝓕(Spec A) ⟶ F_{𝓕, A}`
  of `Stacks.Adequate.affineSectionsCompare` assembled into a natural transformation in the
  sheaf `𝓕`.

## Main results

* `Stacks.Adequate.associatedTildeBaseSectionsIso` — **the sections of `M^a` over the base
  affine are `M` again**, naturally in `M`.  This is the computation the quasi-inverse rests on;
  see the implementation notes for why it is cheap.
* `Stacks.Adequate.affineSectionsAssociatedTildeIso` — **the affine-section functor of `M^a` is
  the module extension `B ↦ B ⊗_A M`**, naturally in `M`.  Together with the previous result
  this says that the comparison functor sends `M^a` to the free adequate functor on `M`.
* `Stacks.Adequate.isAdequate_kernel_associatedTilde` — the kernel of `M^a → N^a` is an adequate
  `𝒪`-module.  This is [Stacks, Tag 06VK]'s implication from a kernel presentation,
  `Stacks.Adequate.isAdequate_of_isAssociatedKernel`, at the presentation this module builds.
* `Stacks.Adequate.exists_isAdequate_affineSectionsFunctor_iso` — **the quasi-inverse.** Every
  adequate module-valued functor on the `A`-algebras of the site is the affine-section functor
  of an adequate `𝒪`-module on the site.
* `Stacks.Adequate.essSurj_of_affineSectionsFunctor` and
  `Stacks.Adequate.fullyFaithful_of_affineSectionsFunctor` — a functor between the two adequate
  subcategories which the subcategory inclusions identify with the affine-section functor is
  essentially surjective, and fully faithful.
* `Stacks.Adequate.isEquivalence_of_affineSectionsFunctor` — **the equivalence of
  [Stacks, Tag 06ZJ]**: such a functor is an equivalence of categories.

## Implementation notes

The three results are stated for an arbitrary functor `Φ` between the two adequate
subcategories together with an isomorphism `Φ ⋙ ι ≅ ι ⋙ affineSectionsFunctor`, rather than for
`Stacks.Adequate.adequateComparison` itself.  That is the content: a functor over the
affine-section functor is determined up to isomorphism, so the statement applies verbatim to
`Stacks.Adequate.adequateComparison` — its own
`Stacks.Adequate.adequateComparison_ι` is such an isomorphism, by `Iso.refl` — and keeps
holding if the shape of that definition changes.

`Stacks.Adequate.associatedTildeBaseSectionsIso` is the step that looks expensive and is not.
The sections of `(M^~)ᵃ` over the base affine are, *by definition*, the global sections of the
pullback of `M^~` along the structure morphism of the base object of the site, with the scalars
of `A` acting through `AlgebraicGeometry.Scheme.ΓSpecIso`; and that is exactly the value of
Mathlib's `AlgebraicGeometry.moduleSpecΓFunctor` on that pullback, on the nose
(`Stacks.Adequate.affineBaseSections_associatedTilde`).  So the computation reduces to two
Mathlib statements: the structure morphism of the base object is the identity, so the pullback
is the identity functor, and `AlgebraicGeometry.tilde.toTildeΓNatIso` identifies
`M ↦ Γ(Spec A, M^~)` with the identity.

The structure morphism of the base object is `Spec` of the algebra map of `A` as an `A`-algebra,
composed with the identity of the base; it is the identity because that algebra map is
`RingHom.id`.  The equality is proved in term mode rather than by `simp`: the source of that
morphism is `Spec (CommRingCat.of ↥(CommAlgCat.of A A))`, which is the base `Spec A` only after
unfolding semireducible definitions, so the statement is type-correct at `default` transparency
but not at `implicit`, and a tactic which rechecks the goal there fails on it.

`Stacks.Adequate.affineSectionsCompareNatTrans` is assembled with the sheaf `𝓕` a **variable**,
and `Stacks.Adequate.affineSectionsAssociatedTildeIso` then obtains the transformation it needs
by whiskering with `Stacks.Adequate.associatedTilde`.  Writing the same natural transformation
out directly at the associated modules — components `affineSectionsCompare … ((associatedTilde
B).obj M)`, naturality the same `Stacks.Adequate.affineSectionsCompare_naturality` — elaborates
and then dies in the **kernel** with a deterministic timeout, because its naturality square has
to be identified at a specific sheaf, where the identification descends into the module
extension's tensor products.  At a variable sheaf the same square is checked in under a second.
This is the same wall that `Stacks.Adequate.exists_bijective_affineSectionsCompare` exists to
avoid, met here at the level of natural transformations rather than of elements.

## References

* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace Stacks.Adequate

/-! ### The base affine as an object of the site -/

section QuasiInverse

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- The base affine as an object of the site: the spectrum of `A` regarded as an `A`-algebra of
the site, over the base `Spec A`. -/
public noncomputable abbrev baseAffineOver : B.category :=
  (affineSpecOver B A (𝟙 (Spec A))).obj (op (baseSiteAlgebra B A B.base_mem))

/-- **The structure morphism of the base affine object is the identity.** It is `Spec` of the
algebra map of `A` as an `A`-algebra, composed with the identity of the base, and that algebra
map is `RingHom.id`. See the module documentation for why this is proved in term mode. -/
public theorem baseAffineOver_hom :
    (B.toOver.obj (baseAffineOver B)).hom = 𝟙 (Spec A) :=
  (Category.comp_id _).trans
    ((congrArg Spec.map
      (show CommRingCat.ofHom (algebraMap ↥A ↥(CommAlgCat.of A A)) = 𝟙 A from rfl)).trans
      (Spec.map_id A))

/-- The sections over the base affine as a functor on the `𝒪`-modules of the site: the
affine-section functor evaluated at the base algebra. On objects this is
`Stacks.Adequate.affineBaseSections`. -/
public noncomputable def affineBaseSectionsFunctor :
    SheafOfModules.{u} B.structureSheaf ⥤ ModuleCat.{u} A where
  obj F := affineBaseSections B A (𝟙 (Spec A)) B.base_mem F
  map u := affineBaseSectionsMap B A (𝟙 (Spec A)) B.base_mem u
  map_id F :=
    congrArg (fun φ => PresheafOfModules.Hom.app φ (op (op (baseSiteAlgebra B A B.base_mem))))
      ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).map_id F)
  map_comp u v :=
    congrArg (fun φ => PresheafOfModules.Hom.app φ (op (op (baseSiteAlgebra B A B.base_mem))))
      ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).map_comp u v)

/-- The sections-over-the-base functor agrees on objects with
`Stacks.Adequate.affineBaseSections`. -/
public theorem affineBaseSectionsFunctor_obj (F : SheafOfModules.{u} B.structureSheaf) :
    (affineBaseSectionsFunctor B).obj F =
      affineBaseSections B A (𝟙 (Spec A)) B.base_mem F := rfl

/-- The sections-over-the-base functor agrees on morphisms with
`Stacks.Adequate.affineBaseSectionsMap`. -/
public theorem affineBaseSectionsFunctor_map {F F' : SheafOfModules.{u} B.structureSheaf}
    (u : F ⟶ F') :
    (affineBaseSectionsFunctor B).map u =
      affineBaseSectionsMap B A (𝟙 (Spec A)) B.base_mem u := rfl

/-- **The sections of `M^a` over the base affine are the global sections of `M^~`.** Both sides
are the global sections of the pullback of `M^~` along the structure morphism of the base
object, with `A` acting through `AlgebraicGeometry.Scheme.ΓSpecIso`; this holds by definitional
unfolding, and it is what makes
`Stacks.Adequate.associatedTildeBaseSectionsIso` cheap. -/
public theorem affineBaseSections_associatedTilde :
    associatedTilde B ⋙ affineBaseSectionsFunctor B =
      tilde.functor A ⋙ Scheme.Modules.pullback (B.toOver.obj (baseAffineOver B)).hom ⋙
        moduleSpecΓFunctor := rfl

/-- Pulling back along the structure morphism of the base affine object is the identity, because
that morphism is the identity. -/
public noncomputable def pullbackBaseAffineIso :
    Scheme.Modules.pullback (B.toOver.obj (baseAffineOver B)).hom ≅ 𝟭 (Spec A).Modules :=
  Scheme.Modules.pullbackCongr (baseAffineOver_hom B) ≪≫ Scheme.Modules.pullbackId (Spec A)

/-- **The sections of `M^a` over the base affine are `M` again**, naturally in `M`. By
`Stacks.Adequate.affineBaseSections_associatedTilde` the composite is
`M ↦ Γ(Spec A, (M^~)|_{Spec A})`; the pullback is the identity functor by
`Stacks.Adequate.pullbackBaseAffineIso`, and `M ↦ Γ(Spec A, M^~)` is the identity by the unit
`AlgebraicGeometry.tilde.toTildeΓNatIso` of the tilde-Gamma adjunction, which is an
isomorphism. -/
public noncomputable def associatedTildeBaseSectionsIso :
    associatedTilde B ⋙ affineBaseSectionsFunctor B ≅ 𝟭 (ModuleCat.{u} A) :=
  eqToIso (affineBaseSections_associatedTilde B) ≪≫
    Functor.isoWhiskerLeft (tilde.functor A)
      (Functor.isoWhiskerRight (pullbackBaseAffineIso B) moduleSpecΓFunctor ≪≫
        Functor.leftUnitor _) ≪≫
    tilde.toTildeΓNatIso.symm

/-- **The comparison `C ⊗_A 𝓕(Spec A) ⟶ F_{𝓕, A}` as a natural transformation**, natural in
the sheaf of modules `𝓕`. This is `Stacks.Adequate.affineSectionsCompare` together with
`Stacks.Adequate.affineSectionsCompare_naturality`, assembled once with `𝓕` a variable; see the
implementation notes for why it is assembled here rather than at the associated modules. -/
public noncomputable def affineSectionsCompareNatTrans :
    affineBaseSectionsFunctor B ⋙
        AdequateFunctor.moduleExtensionFunctorOn
          (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) ⟶
      affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)) where
  app F := affineSectionsCompare B A (𝟙 (Spec A)) B.base_mem F
  naturality _ _ u :=
    (affineSectionsCompare_naturality B A (𝟙 (Spec A)) B.base_mem u).symm

/-- The comparison is an isomorphism at the associated module of `M^~`, by
`Stacks.Adequate.isIso_affineSectionsCompare`. -/
public instance isIso_affineSectionsCompareNatTrans_app (M : ModuleCat.{u} A) :
    IsIso ((Functor.whiskerLeft (associatedTilde B)
      (affineSectionsCompareNatTrans B)).app M) :=
  isIso_affineSectionsCompare B A (𝟙 (Spec A)) B.base_mem (tilde M)
    (isSheaf_associatedPresheaf B (tilde M))

/-- The comparison at the associated modules of the `M^~` is an isomorphism of functors: it is
one at every `A`-module. -/
public instance isIso_whiskerLeft_affineSectionsCompareNatTrans :
    IsIso (Functor.whiskerLeft (associatedTilde B) (affineSectionsCompareNatTrans B)) :=
  NatIso.isIso_of_isIso_app _

/-- **The affine-section functor of `M^a` is the module extension `C ↦ C ⊗_A M`**, naturally in
the `A`-module `M`. The affine sections of `M^a` are the module extension of its sections over
the base affine (`Stacks.Adequate.affineSectionsCompareNatTrans`), and those sections are `M`
again (`Stacks.Adequate.associatedTildeBaseSectionsIso`). -/
public noncomputable def affineSectionsAssociatedTildeIso :
    AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) ≅
      associatedTilde B ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)) :=
  (Functor.isoWhiskerRight (associatedTildeBaseSectionsIso B) _ ≪≫
      Functor.leftUnitor _).symm ≪≫
    Functor.associator _ _ _ ≪≫
    asIso (Functor.whiskerLeft (associatedTilde B) (affineSectionsCompareNatTrans B))

/-! ### The quasi-inverse -/

/-- **The kernel of `M^a → N^a` is an adequate `𝒪`-module.** This is [Stacks, Tag 06VK]'s
implication from a kernel presentation, `Stacks.Adequate.isAdequate_of_isAssociatedKernel`, at
the presentation by the quasi-coherent modules `M^~` and `N^~`. -/
public theorem isAdequate_kernel_associatedTilde {M N : ModuleCat.{u} A} (ψ : M ⟶ N) :
    IsAdequate B (kernel ((associatedTilde B).map ψ)) :=
  isAdequate_of_isAssociatedKernel B _
    ⟨{ source := tilde M
       target := tilde N
       source_isSheaf := isSheaf_associatedPresheaf B (tilde M)
       target_isSheaf := isSheaf_associatedPresheaf B (tilde N)
       hom := (associatedTilde B).map ψ
       iso := Iso.refl _ }⟩

/-- **The quasi-inverse of [Stacks, Tag 06ZJ].** Every adequate module-valued functor `F` on the
`A`-algebras of the site is the affine-section functor of an adequate `𝒪`-module on the site.

Adequacy of `F` supplies an exact sequence `0 → F → M̲ → N̲`; the `𝒪`-module is
`𝓕 = Ker(M^a → N^a)`, which is adequate by
`Stacks.Adequate.isAdequate_kernel_associatedTilde`. Its affine-section functor is the kernel of
the affine-section functors, because affine sections commute with finite limits, and those are
the module extensions of `M` and `N` by
`Stacks.Adequate.affineSectionsAssociatedTildeIso`; so it is `Ker(M̲ → N̲) = F`.

The exact sequence is chosen inside this proof, so no independence of the choice is needed: the
construction `M ↦ M^a` of `Stacks.Adequate.associatedTilde` is already a functor. -/
public theorem exists_isAdequate_affineSectionsFunctor_iso
    (F : AdequateFunctor.ModuleValuedFunctorOn.{u}
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)))
    (hF : AdequateFunctor.IsAdequate
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) F) :
    ∃ G : SheafOfModules.{u} B.structureSheaf, IsAdequate B G ∧
      Nonempty ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).obj G ≅ F) := by
  obtain ⟨M, N, ψ, ⟨e⟩⟩ := hF
  refine ⟨kernel ((associatedTilde B).map ψ), isAdequate_kernel_associatedTilde B ψ, ⟨?_⟩⟩
  refine PreservesKernel.iso (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A)))
    ((associatedTilde B).map ψ) ≪≫ ?_
  have hArrow : Arrow.mk ((affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).map
        ((associatedTilde B).map ψ)) ≅
      Arrow.mk ((AdequateFunctor.moduleExtensionFunctorOn
        (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).map ψ) :=
    Arrow.isoMk ((affineSectionsAssociatedTildeIso B).app M).symm
      ((affineSectionsAssociatedTildeIso B).app N).symm
      ((affineSectionsAssociatedTildeIso B).inv.naturality ψ).symm
  refine KernelFork.mapIsoOfIsLimit (limit.isLimit (parallelPair _ 0))
    (limit.isLimit (parallelPair _ 0)) hArrow ≪≫ ?_
  exact e.symm ≪≫ AdequateFunctor.presheafOfModulesUliftIso _ F

/-! ### The equivalence of Tag 06ZJ -/

section Equivalence

variable {Φ : (adequate.{u, u} B).FullSubcategory ⥤
    (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).FullSubcategory}

/-- A functor from adequate `𝒪`-modules to adequate module-valued functors which the subcategory
inclusions identify with the affine-section functor is **fully faithful**: the affine-section
functor of a chosen big site over an affine base is fully faithful
(`Stacks.Adequate.fullyFaithfulAffineSectionsFunctor`), so the composite with the inclusion of
the adequate module-valued functors is, and that inclusion is faithful. -/
public noncomputable def fullyFaithful_of_affineSectionsFunctor
    (hΦ : Φ ⋙ (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι ≅
      (adequate.{u, u} B).ι ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))) :
    Φ.FullyFaithful := by
  have : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Full :=
    (fullyFaithfulAffineSectionsFunctor B).full
  have : (affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))).Faithful :=
    (fullyFaithfulAffineSectionsFunctor B).faithful
  have : Φ.Faithful := Functor.Faithful.of_comp_iso hΦ
  have : Φ.Full := Functor.Full.of_comp_faithful_iso hΦ
  exact Functor.FullyFaithful.ofFullyFaithful Φ

/-- A functor from adequate `𝒪`-modules to adequate module-valued functors which the subcategory
inclusions identify with the affine-section functor is **essentially surjective**. This is the
quasi-inverse, `Stacks.Adequate.exists_isAdequate_affineSectionsFunctor_iso`, read through the
inclusions: the adequate `𝒪`-module it produces is the required preimage. -/
public theorem essSurj_of_affineSectionsFunctor
    (hΦ : Φ ⋙ (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι ≅
      (adequate.{u, u} B).ι ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))) :
    Φ.EssSurj where
  mem_essImage Y := by
    obtain ⟨G, hG, ⟨e⟩⟩ := exists_isAdequate_affineSectionsFunctor_iso B Y.obj Y.property
    exact ⟨⟨G, hG⟩, ⟨(adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).fullyFaithfulι.preimageIso
      (hΦ.app ⟨G, hG⟩ ≪≫ e)⟩⟩

/-- **[Stacks, Tag 06ZJ], the equivalence.** For `S = Spec A` affine, a functor from the category
`Adeq(𝒪)` of adequate `𝒪`-modules on `(Sch/S)_τ` to the category of adequate module-valued
functors on the `A`-algebras of the site which the two subcategory inclusions identify with the
affine-section functor `𝓕 ↦ F_{𝓕, A}` is an **equivalence of categories**.

The comparison functor `Stacks.Adequate.adequateComparison` is such a functor, by its own
`Stacks.Adequate.adequateComparison_ι`.

Full faithfulness is `Stacks.Adequate.fullyFaithful_of_affineSectionsFunctor` and essential
surjectivity is `Stacks.Adequate.essSurj_of_affineSectionsFunctor`, which is the quasi-inverse
the source constructs from an exact sequence `0 → F → M̲ → N̲`. -/
public theorem isEquivalence_of_affineSectionsFunctor
    (hΦ : Φ ⋙ (adequateOn.{u, u} A (schemeSizeBelow B.cutoff)).ι ≅
      (adequate.{u, u} B).ι ⋙ affineSectionsFunctor.{u, u} B A (𝟙 (Spec A))) :
    Φ.IsEquivalence where
  faithful := (fullyFaithful_of_affineSectionsFunctor B hΦ).faithful
  full := (fullyFaithful_of_affineSectionsFunctor B hΦ).full
  essSurj := essSurj_of_affineSectionsFunctor B hΦ

end Equivalence

end QuasiInverse

end Stacks.Adequate

end
