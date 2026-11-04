module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedKernelConverse
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedLocalization
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence

/-!
# The derived localization over an affine base

Over an affine base `U = Spec A`, the comparison functor `u : QCoh(𝒪_U) ⥤ Adeq(𝒪)` of
[Stacks, Tag 06VN] identifies the pullback of a quasi-coherent module with its associated module,
and every adequate module admits a monomorphism into the image of `u` ([Stacks, Tag 06VK]). From
this, the bounded below derived category `D⁺(Adeq(𝒪))` is the localization of `K⁺(QCoh(𝒪_U))` at
the universal quasi-isomorphisms ([Stacks, Tag 06ZR]).

## Main definitions

* `Stacks.Adequate.BigSite.associatedModuleFunctorObjIso`: on the chosen big fppf site attached
  to a chosen big fppf site of schemes, the isomorphism between the pullback of a quasi-coherent
  module and its associated module of [Stacks, Tag 03DU].

## Main results

* `Stacks.Adequate.BigSite.exists_mono_associatedModuleAdeq`: every adequate `𝒪`-module admits a
  monomorphism into the associated module of a quasi-coherent `𝒪_U`-module.
* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq`:
  `D⁺(Adeq(𝒪))` is the localization of `K⁺(QCoh(𝒪_U))` at the universal quasi-isomorphisms,
  given the abelian structures, the additivity of `u`, the existence of monomorphisms into the
  image of `u`, and the description of the universal quasi-isomorphisms as an inverse image.
* `Stacks.Adequate.BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv`:
  the same localization, without the hypothesis on monomorphisms into the image of `u`.

## References

* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

section AssociatedModule

variable {A : CommRingCat.{u}} (B : BigFppfSite.{u}) (hS : B.Contains (Spec A))

/-- On the chosen big fppf site attached to a chosen big fppf site of schemes, the isomorphism
between `u G`, the pullback of a quasi-coherent `𝒪_U`-module `G` along the morphism of ringed
sites, and the associated module of `G` of [Stacks, Tag 03DU] (3). -/
public noncomputable def BigSite.associatedModuleFunctorObjIso (G : (Spec A).Modules)
    [G.IsQuasicoherent] :
    (BigSite.ofBigFppfSite B (Spec A) hS).associatedModuleFunctor.obj G ≅
      (BigSite.ofBigFppfSite B (Spec A) hS).associatedModule G
        (isSheaf_associatedPresheaf _ G) :=
  AlgebraicGeometry.BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B (Spec A) hS .fppf G

end AssociatedModule

section AnyTopology

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- Every adequate `𝒪`-module on a chosen big `τ`-site over `U = Spec A` admits a monomorphism
into `u G` for some quasi-coherent `𝒪_U`-module `G`: the implication (1) ⇒ (2) of
[Stacks, Tag 06VK]. -/
public theorem BigSite.exists_mono_associatedModuleAdeq
    (F : (adequate.{u, u} B).FullSubcategory) :
    ∃ (G : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory)
      (i : F ⟶ B.associatedModuleAdeq.obj G), Mono i := by
  obtain ⟨p, i, hi⟩ := exists_mono_into_associatedModule_of_isAdequate A B B.base_mem
    F.obj F.property
  let := p.source_isQuasicoherent
  obtain ⟨e⟩ := B.nonempty_associatedModuleFunctor_obj_iso p.source
  let g : F.obj ⟶ B.associatedModuleFunctor.obj p.source := i ≫ e.inv
  exact ⟨⟨p.source, p.source_isQuasicoherent⟩, ObjectProperty.homMk g,
    (adequate.{u, u} B).ι.mono_of_mono_map (mono_comp i e.inv)⟩

end AnyTopology

/-! ### The bounded below derived category of adequate modules -/

section AffineGeneral

-- Inside this section the preadditive structure of a full subcategory is the one underlying the
-- assumed abelian structure, not the one induced from the ambient category.
attribute [-instance] CategoryTheory.Preadditive.fullSubcategory

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- Over an affine scheme `U = Spec A`, on a chosen big `τ`-site over `U`, the bounded below
derived category `D⁺(Adeq(𝒪))` is the localization of `K⁺(QCoh(𝒪_U))` at the universal
quasi-isomorphisms, provided `Adeq(𝒪)` and `QCoh(𝒪_U)` are abelian, `u` is additive, every
adequate module admits a monomorphism into the image of `u` (`hmono`), and the universal
quasi-isomorphisms are the morphisms that `u` sends to quasi-isomorphisms (`huniv`). -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq
    [Abelian (adequate.{u, u} B).FullSubcategory]
    [Abelian (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory]
    [(SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι.Additive]
    [B.associatedModuleAdeq.Additive]
    (hmono : ∀ F : (adequate.{u, u} B).FullSubcategory,
      ∃ (G : (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory)
        (i : F ⟶ B.associatedModuleAdeq.obj G), Mono i)
    (huniv : universalQuasiIso (Spec A) =
      (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} B).FullSubcategory).inverseImage
        B.associatedModuleAdeq.mapHomotopyCategoryPlus) :
    (B.associatedModuleAdeq.mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} B).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) := by
  have := B.full_associatedModuleAdeq
  have := B.faithful_associatedModuleAdeq
  exact Functor.isLocalization_mapHomotopyCategoryPlus_comp'
    B.associatedModuleAdeq hmono _ (universalQuasiIso (Spec A)) huniv

end AffineGeneral

/-! ### The derived localization over an affine base, with the monomorphisms supplied -/

section Affine

-- Inside this section the preadditive structure of a full subcategory is the one underlying the
-- assumed abelian structure, not the one induced from the ambient category.
attribute [-instance] CategoryTheory.Preadditive.fullSubcategory

variable {τ : CoveringTopology} {A : CommRingCat.{u}} (B : BigSite τ (Spec A))

/-- Over an affine scheme `U = Spec A`, on a chosen big `τ`-site over `U`, the bounded below
derived category `D⁺(Adeq(𝒪))` is the localization of `K⁺(QCoh(𝒪_U))` at the universal
quasi-isomorphisms, provided `Adeq(𝒪)` and `QCoh(𝒪_U)` are abelian, `u` is additive, and the
universal quasi-isomorphisms are the morphisms that `u` sends to quasi-isomorphisms (`huniv`).
This is [Stacks, Tag 06ZR] under these hypotheses. -/
public theorem BigSite.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq_of_huniv
    [Abelian (adequate.{u, u} B).FullSubcategory]
    [Abelian (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).FullSubcategory]
    [(SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).ι.Additive]
    [B.associatedModuleAdeq.Additive]
    (huniv : universalQuasiIso (Spec A) =
      (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} B).FullSubcategory).inverseImage
        B.associatedModuleAdeq.mapHomotopyCategoryPlus) :
    (B.associatedModuleAdeq.mapHomotopyCategoryPlus ⋙
        MorphismProperty.Q (HomotopyCategory.Plus.quasiIso
          (adequate.{u, u} B).FullSubcategory)).IsLocalization
      (universalQuasiIso (Spec A)) :=
  B.isLocalization_mapHomotopyCategoryPlus_associatedModuleAdeq
    B.exists_mono_associatedModuleAdeq huniv

end Affine

end Stacks.Adequate

end
