module

public import StacksFrontier.Algebra.Homology.DerivedCategory.JointlyFaithfulExact
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing

/-!
# Restriction to the members of a decomposition into disjoint open subsets

Let `X` be a ringed space which is the union of pairwise disjoint open subsets `U r`. The
restrictions of sheaves of `𝒪_X`-modules to the `U r` form a jointly faithful family with gluing:
a morphism `M ⟶ N` is determined by its restrictions, and any family of morphisms
`M|_{U r} ⟶ N|_{U r}` is the family of restrictions of one morphism (no compatibility is needed,
the members being disjoint). Consequently a morphism of the derived category `D(𝒪_X)` vanishes as
soon as all its restrictions to the `D(𝒪_{U r})` do: in the words of the proof of
[Stacks, Tag 0FUW], the derived category decomposes as a product.

## Main definitions

* `Stacks.Cohomology.DisjointOpenCover.localApp`: the action of a morphism of restrictions to an
  open `U` on the sections over an open `V ⊆ U` of `X`.
* `Stacks.Cohomology.DisjointOpenCover.toLocalModuleHom`: the local morphism on `U` of a morphism
  of restrictions to `U`.

## Main results

* `Stacks.Cohomology.DisjointOpenCover.eq_zero_of_forall_restriction_map_eq_zero`: joint
  faithfulness.
* `Stacks.Cohomology.DisjointOpenCover.exists_restriction_map_eq`: gluing.
* `Stacks.Cohomology.DisjointOpenCover.eq_zero_of_forall_mapDerivedCategory_map_eq_zero`: the
  vanishing in the derived category.
* `eq_zero_of_forall_modulePullback_mapDerivedCategory_map_eq_zero`: the same for a family of open
  immersions of ringed spaces with pairwise disjoint images covering `X`.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DisjointOpenCover

section Restriction

variable {X : RingedSpace.{u, u}} (U : Opens (X : TopCat))

/-- The functor on opens of the inclusion of the open subspace `U` into `X`. -/
abbrev imageFunctor : Opens (X.restrict U.isOpenEmbedding : TopCat) ⥤ Opens (X : TopCat) :=
  (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open.functor

/-- The sections of the restriction of `M` to `U` over `W` are the sections of `M` over the image
of `W`. -/
theorem restriction_obj_val_obj (M : SheafOfModules.{u} (structureSheafRing X))
    (W : Opens (X.restrict U.isOpenEmbedding : TopCat)) :
    (((openInclusionSiteRestriction X U).obj M).val.obj (op W) : Type u) =
      M.val.obj (op ((imageFunctor U).obj W)) :=
  rfl

variable {U} {M N : SheafOfModules.{u} (structureSheafRing X)}
  (ψ : (openInclusionSiteRestriction X U).obj M ⟶ (openInclusionSiteRestriction X U).obj N)

/-- **The action of a morphism of restrictions on the sections over an image open**, written at
the open of `X`. -/
def appImage (W : Opens (X.restrict U.isOpenEmbedding : TopCat)) :
    M.val.obj (op ((imageFunctor U).obj W)) → N.val.obj (op ((imageFunctor U).obj W)) :=
  fun s => ψ.val.app (op W) s

/-- `appImage ψ W` is additive. -/
theorem appImage_add (W : Opens (X.restrict U.isOpenEmbedding : TopCat))
    (s t : M.val.obj (op ((imageFunctor U).obj W))) :
    appImage ψ W (s + t) = appImage ψ W s + appImage ψ W t :=
  (ψ.val.app (op W)).hom.map_add s t

/-- `appImage ψ W` is linear over the sections of the structure sheaf over the image of `W`. -/
theorem appImage_smul (W : Opens (X.restrict U.isOpenEmbedding : TopCat))
    (r : (structureSheafRing X).obj.obj (op ((imageFunctor U).obj W)))
    (s : M.val.obj (op ((imageFunctor U).obj W))) :
    appImage ψ W (r • s) = r • appImage ψ W s :=
  (ψ.val.app (op W)).hom.map_smul r s

/-- `appImage ψ` commutes with the restriction maps along an inclusion `W₂ ≤ W₁`. -/
theorem appImage_map {W₁ W₂ : Opens (X.restrict U.isOpenEmbedding : TopCat)} (h : W₂ ≤ W₁)
    (s : M.val.obj (op ((imageFunctor U).obj W₁))) :
    appImage ψ W₂ (M.val.map ((imageFunctor U).map (homOfLE h)).op s) =
      N.val.map ((imageFunctor U).map (homOfLE h)).op (appImage ψ W₁ s) :=
  PresheafOfModules.naturality_apply ψ.val (homOfLE h).op s

/-- For the restriction of a morphism `φ : M ⟶ N`, `appImage` is the action of `φ` on sections
over the image of `W`. -/
theorem appImage_restriction_map (φ : M ⟶ N) (W : Opens (X.restrict U.isOpenEmbedding : TopCat))
    (s : M.val.obj (op ((imageFunctor U).obj W))) :
    appImage ((openInclusionSiteRestriction X U).map φ) W s =
      φ.val.app (op ((imageFunctor U).obj W)) s :=
  rfl

/-- The action of a morphism of restrictions on the sections over an open `V` of `X` presented as
the image `V = U ∩ W` of an open `W` of `U`. -/
def localApp {W : Opens (X.restrict U.isOpenEmbedding : TopCat)} {V : Opens (X : TopCat)}
    (hWV : (imageFunctor U).obj W = V) : M.val.obj (op V) → N.val.obj (op V) :=
  hWV ▸ appImage ψ W

/-- `localApp ψ hWV` is additive. -/
theorem localApp_add {W : Opens (X.restrict U.isOpenEmbedding : TopCat)} {V : Opens (X : TopCat)}
    (hWV : (imageFunctor U).obj W = V) (s t : M.val.obj (op V)) :
    localApp ψ hWV (s + t) = localApp ψ hWV s + localApp ψ hWV t := by
  subst hWV
  exact appImage_add ψ W s t

/-- `localApp ψ hWV` is linear over the sections of the structure sheaf over `V`. -/
theorem localApp_smul {W : Opens (X.restrict U.isOpenEmbedding : TopCat)} {V : Opens (X : TopCat)}
    (hWV : (imageFunctor U).obj W = V) (r : (structureSheafRing X).obj.obj (op V))
    (s : M.val.obj (op V)) :
    localApp ψ hWV (r • s) = r • localApp ψ hWV s := by
  subst hWV
  exact appImage_smul ψ W r s

/-- `localApp ψ` commutes with the restriction maps along an inclusion `V₂ ≤ V₁`. -/
theorem localApp_map {W₁ W₂ : Opens (X.restrict U.isOpenEmbedding : TopCat)}
    {V₁ V₂ : Opens (X : TopCat)} (h₁ : (imageFunctor U).obj W₁ = V₁)
    (h₂ : (imageFunctor U).obj W₂ = V₂) (hV : V₂ ≤ V₁) (s : M.val.obj (op V₁)) :
    localApp ψ h₂ (M.val.map (homOfLE hV).op s) = N.val.map (homOfLE hV).op (localApp ψ h₁ s) := by
  subst h₁ h₂
  have hW : W₂ ≤ W₁ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hV ⟨x, hx, rfl⟩
    rwa [(SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open.injective hyx]
      at hy
  exact appImage_map ψ hW s

/-- For the restriction of a morphism `φ : M ⟶ N`, `localApp` is the action of `φ` on sections
over `V`. -/
theorem localApp_restriction_map (φ : M ⟶ N) {W : Opens (X.restrict U.isOpenEmbedding : TopCat)}
    {V : Opens (X : TopCat)} (hWV : (imageFunctor U).obj W = V) (s : M.val.obj (op V)) :
    localApp ((openInclusionSiteRestriction X U).map φ) hWV s = φ.val.app (op V) s := by
  subst hWV
  rfl

/-- The zero morphism of restrictions acts as zero on sections. -/
theorem localApp_zero {W : Opens (X.restrict U.isOpenEmbedding : TopCat)} {V : Opens (X : TopCat)}
    (hWV : (imageFunctor U).obj W = V) (s : M.val.obj (op V)) :
    localApp (0 : (openInclusionSiteRestriction X U).obj M ⟶
      (openInclusionSiteRestriction X U).obj N) hWV s = 0 := by
  subst hWV
  rfl

/-- An open of `X` inside `U` is the image of its preimage in `U`. -/
theorem imageFunctor_obj_preimage {V : Opens (X : TopCat)} (hV : V ≤ U) :
    (imageFunctor U).obj
        ((Opens.map (X.ofRestrict U.isOpenEmbedding).hom.base).obj V) = V := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, hV hx⟩, hx, rfl⟩

/-- **The local morphism on `U` of a morphism of restrictions to `U`.** -/
def toLocalModuleHom : TopCat.Sheaf.LocalModuleHom M.val N.val U where
  app _ hV := ModuleCat.ofHom
    { toFun := localApp ψ (imageFunctor_obj_preimage hV)
      map_add' := localApp_add ψ _
      map_smul' := localApp_smul ψ _ }
  naturality {_ _} hV hWV s :=
    localApp_map ψ (imageFunctor_obj_preimage hV) (imageFunctor_obj_preimage (hWV.trans hV)) hWV s

/-- On an open `V ≤ U`, `toLocalModuleHom ψ` acts by `localApp ψ`. -/
theorem toLocalModuleHom_app {V : Opens (X : TopCat)} (hV : V ≤ U) (s : M.val.obj (op V)) :
    (toLocalModuleHom ψ).app V hV s = localApp ψ (imageFunctor_obj_preimage hV) s :=
  rfl

end Restriction

section Cover

variable {X : RingedSpace.{u, u}} {ι : Type u} (U : ι → Opens (X : TopCat))
  (hdisj : Pairwise (fun r s => Disjoint (U r) (U s))) (hcov : ⨆ r, U r = ⊤)

include hcov in
/-- **Joint faithfulness of the restrictions to a cover.** A morphism of sheaves of modules all of
whose restrictions to the members of an open cover vanish is zero. -/
theorem eq_zero_of_forall_restriction_map_eq_zero {M N : SheafOfModules.{u} (structureSheafRing X)}
    (g : M ⟶ N) (hg : ∀ r, (openInclusionSiteRestriction X (U r)).map g = 0) : g = 0 := by
  have key : g.val = (0 : M ⟶ N).val :=
    TopCat.Sheaf.eq_hom_of_restrict hcov N.isSheaf (fun _ V _ => 0)
      (fun r V hV => ModuleCat.hom_ext (LinearMap.ext fun s => by
        have h := localApp_restriction_map (U := U r) g (imageFunctor_obj_preimage hV) s
        rw [hg r, localApp_zero] at h
        exact h.symm))
      (fun _ _ _ => rfl)
  exact SheafOfModules.hom_ext key

/-- Two sections of a sheaf of modules over the empty open agree. -/
theorem section_eq_of_eq_bot (N : SheafOfModules.{u} (structureSheafRing X))
    {V : Opens (X : TopCat)} (hV : V = ⊥) (a b : N.val.obj (op V)) : a = b :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf (ι := PEmpty.{u + 1}) N.isSheaf
    (fun k => k.elim) (fun k => k.elim) (by rw [hV]; exact bot_le) (fun k => k.elim)

/-- `localApp ψ h` does not depend on the open `W` of `U` presenting `V` as an image. -/
theorem localApp_congr {U : Opens (X : TopCat)} {M N : SheafOfModules.{u} (structureSheafRing X)}
    (ψ : (openInclusionSiteRestriction X U).obj M ⟶ (openInclusionSiteRestriction X U).obj N)
    {W₁ W₂ : Opens (X.restrict U.isOpenEmbedding : TopCat)} {V : Opens (X : TopCat)}
    (h₁ : (imageFunctor U).obj W₁ = V) (h₂ : (imageFunctor U).obj W₂ = V) :
    localApp ψ h₁ = localApp ψ h₂ := by
  obtain rfl : W₁ = W₂ := by
    rw [← Opens.map_functor_eq' _
        (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open W₁,
      ← Opens.map_functor_eq' _
        (SheafedSpace.IsOpenImmersion.ofRestrict X U.isOpenEmbedding).base_open W₂]
    exact congrArg _ (h₁.trans h₂.symm)
  rfl

include hdisj hcov in
/-- **Gluing along a decomposition into disjoint opens.** Any family of morphisms of the
restrictions of `M` and `N` to the members `U r` is the family of restrictions of one morphism
`M ⟶ N`. -/
theorem exists_restriction_map_eq (M N : SheafOfModules.{u} (structureSheafRing X))
    (h : ∀ r, (openInclusionSiteRestriction X (U r)).obj M ⟶
      (openInclusionSiteRestriction X (U r)).obj N) :
    ∃ g : M ⟶ N, ∀ r, (openInclusionSiteRestriction X (U r)).map g = h r := by
  classical
  obtain ⟨ψ, hψ, -⟩ := TopCat.Sheaf.existsUnique_hom_of_localModuleHom U hcov M.val N.val
    N.isSheaf (fun r => toLocalModuleHom (h r)) (fun r s V hVr hVs => by
      by_cases hrs : r = s
      · subst hrs
        rfl
      · refine ModuleCat.hom_ext (LinearMap.ext fun a => section_eq_of_eq_bot N ?_ _ _)
        exact le_bot_iff.mp ((le_inf hVr hVs).trans (disjoint_iff_inf_le.mp (hdisj hrs))))
  refine ⟨⟨ψ⟩, fun r => SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W =>
    ModuleCat.hom_ext (LinearMap.ext fun a => ?_))⟩
  have hW : (imageFunctor (U r)).obj W.unop ≤ U r := by
    rintro x ⟨y, -, rfl⟩
    exact y.2
  exact (congrArg (fun φ => φ.hom a) (hψ r _ hW)).trans
    (congrFun (localApp_congr (h r) (imageFunctor_obj_preimage hW) rfl) a)

variable [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
  [∀ r, HasDerivedCategory (SheafOfModules.{u}
    (structureSheafRing (X.restrict (U r).isOpenEmbedding)))]

/-- Restriction of sheaves of modules to an open is additive. -/
instance (V : Opens (X : TopCat)) : (openInclusionSiteRestriction X V).Additive := by
  change (HigherDirectImage.moduleRestriction X V).Additive
  infer_instance

/-- Restriction of sheaves of modules to an open preserves finite limits. -/
instance (V : Opens (X : TopCat)) : PreservesFiniteLimits (openInclusionSiteRestriction X V) := by
  change PreservesFiniteLimits (ExtensionByZeroModules.jStar V (structureSheafRing X))
  have : PreservesLimits (ExtensionByZeroModules.jStar V (structureSheafRing X)) :=
    (ExtensionByZeroModules.jShriekAdjunction V (structureSheafRing X)).rightAdjoint_preservesLimits
  infer_instance

/-- Restriction of sheaves of modules to an open preserves finite colimits. -/
instance (V : Opens (X : TopCat)) :
    PreservesFiniteColimits (openInclusionSiteRestriction X V) := by
  change PreservesFiniteColimits (ExtensionByZeroModules.jStar V (structureSheafRing X))
  have : PreservesColimits (ExtensionByZeroModules.jStar V (structureSheafRing X)) :=
    (ExtensionByZeroModules.jStarAdjunction V (structureSheafRing X)).leftAdjoint_preservesColimits
  infer_instance

include hdisj hcov in
/-- **The derived category of a space decomposed into disjoint opens embeds into the product of
the derived categories of the pieces**: a morphism of `D(𝒪_X)` all of whose restrictions to the
`D(𝒪_{U r})` vanish is zero. -/
theorem eq_zero_of_forall_mapDerivedCategory_map_eq_zero
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L)
    (hφ : ∀ r, (openInclusionSiteRestriction X (U r)).mapDerivedCategory.map φ = 0) : φ = 0 :=
  DerivedCategory.eq_zero_of_forall_mapDerivedCategory_map_eq_zero
    (fun r => openInclusionSiteRestriction X (U r))
    (fun r I hI => by
      have := hI
      show CochainComplex.IsKInjective
        (((ExtensionByZeroModules.jStar (U r) (structureSheafRing X)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)
      infer_instance)
    (fun Y => by
      obtain ⟨I, q, hI, hq⟩ := sheaf_exists_kInjective_resolution X Y
      exact ⟨I, hI, q, hq⟩)
    (fun M N h => exists_restriction_map_eq U hdisj hcov M N h)
    (fun g hg => eq_zero_of_forall_restriction_map_eq_zero U hcov g hg) φ hφ

end Cover

section Transfer

variable {A : Type*} [Category* A] [Preadditive A] {ι : Type*} {B C : ι → Type*}
  [∀ r, Category* (B r)] [∀ r, Category* (C r)] [∀ r, Preadditive (B r)]
  [∀ r, Preadditive (C r)] (F : ∀ r, A ⥤ C r) (G : ∀ r, A ⥤ B r) (E : ∀ r, B r ⥤ C r)
  [∀ r, (E r).Faithful] [∀ r, (E r).Full] (e : ∀ r, F r ≅ G r ⋙ E r)

omit [Preadditive A] [∀ r, Preadditive (B r)] [∀ r, Preadditive (C r)] [∀ r, (E r).Faithful] in
include e in
/-- Gluing for a family of functors transfers along isomorphisms with a family followed by fully
faithful functors. -/
theorem hglue_of_iso
    (hglue : ∀ (M N : A) (h : ∀ r, (G r).obj M ⟶ (G r).obj N), ∃ g : M ⟶ N,
      ∀ r, (G r).map g = h r) (M N : A) (h : ∀ r, (F r).obj M ⟶ (F r).obj N) :
    ∃ g : M ⟶ N, ∀ r, (F r).map g = h r := by
  obtain ⟨g, hg⟩ := hglue M N fun r => (E r).preimage ((e r).inv.app M ≫ h r ≫ (e r).hom.app N)
  refine ⟨g, fun r => ?_⟩
  have h1 := (e r).hom.naturality g
  rw [Functor.comp_map, hg r, Functor.map_preimage] at h1
  rw [← cancel_mono ((e r).hom.app N), h1, ← Category.assoc, Iso.hom_inv_id_app,
    Category.id_comp]

omit [∀ r, (E r).Full] in
include e in
/-- Joint faithfulness transfers along isomorphisms with a family followed by faithful
functors. -/
theorem hinj_of_iso [∀ r, (G r).PreservesZeroMorphisms] [∀ r, (E r).PreservesZeroMorphisms]
    (hinj : ∀ {M N : A} (g : M ⟶ N), (∀ r, (G r).map g = 0) → g = 0) {M N : A} (g : M ⟶ N)
    (hg : ∀ r, (F r).map g = 0) : g = 0 :=
  hinj g fun r => (E r).map_injective (by
    have h1 := (e r).hom.naturality g
    rw [hg r, zero_comp, Functor.comp_map] at h1
    rw [Functor.map_zero, ← cancel_epi ((e r).hom.app M), comp_zero, h1.symm])

end Transfer

section OpenImmersions

variable {X : RingedSpace.{u, u}} {ι : Type u} {Y : ι → RingedSpace.{u, u}} (k : ∀ r, Y r ⟶ X)
  [∀ r, SheafedSpace.IsOpenImmersion (k r)]

/-- The open of `X` which is the image of an open immersion. -/
abbrev rangeOpen (r : ι) : Opens (X : TopCat) :=
  (inferInstance : SheafedSpace.IsOpenImmersion (k r)).base_open.functor.obj ⊤

/-- An open immersion is the identification of its source with the open subspace on its image,
followed by the inclusion of that open subspace. -/
def rangeIso (r : ι) : Y r ≅ X.restrict (rangeOpen k r).isOpenEmbedding :=
  (SheafedSpace.IsOpenImmersion.isoRestrict (k r)).trans (openImmersionRangeIso (k r))

/-- `rangeIso k r` followed by the inclusion of the open subspace on the image is `k r`. -/
theorem rangeIso_hom_comp (r : ι) :
    (rangeIso k r).hom ≫ X.ofRestrict (rangeOpen k r).isOpenEmbedding = k r := by
  show ((SheafedSpace.IsOpenImmersion.isoRestrict (k r)).hom ≫
      (openImmersionRangeIso (k r)).hom) ≫
    X.ofRestrict (rangeOpen k r).isOpenEmbedding = k r
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (openImmersionRangeIso_comp (k r))).trans
    (SheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict (k r)))

/-- Pullback along an open immersion is restriction to its image followed by the equivalence of
the open subspace with the source. -/
def modulePullbackIsoRestriction (r : ι) :
    modulePullback (k r) ≅
      openInclusionSiteRestriction X (rangeOpen k r) ⋙ modulePullback (rangeIso k r).hom :=
  (eqToIso (congrArg modulePullback (rangeIso_hom_comp k r))).symm ≪≫
    pullbackComp (rangeIso k r).hom (X.ofRestrict (rangeOpen k r).isOpenEmbedding) ≪≫
    Functor.isoWhiskerRight (openInclusionModulePullbackIso X (rangeOpen k r)).symm _

/-- Pullback of sheaves of modules along the isomorphism `rangeIso k r` is an equivalence. -/
instance (r : ι) : (modulePullback (rangeIso k r).hom).IsEquivalence :=
  modulePullbackIso_isEquivalence (rangeIso k r)

/-- A point lies in `rangeOpen k r` if and only if it lies in the image of `k r`. -/
theorem mem_rangeOpen_iff (r : ι) (x : (X : TopCat)) :
    x ∈ rangeOpen k r ↔ x ∈ Set.range (k r).hom.base := by
  show x ∈ (IsOpenMap.functor _).obj ⊤ ↔ _
  rw [← SetLike.mem_coe, IsOpenMap.coe_functor_obj]
  simp

variable (hdisj : Pairwise fun r s =>
    Disjoint (Set.range (k r).hom.base) (Set.range (k s).hom.base))
  (hcov : ∀ x : (X : TopCat), ∃ r, x ∈ Set.range (k r).hom.base)
  [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
  [∀ r, HasDerivedCategory (SheafOfModules.{u} (structureSheafRing (Y r)))]

omit [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
  [∀ r, HasDerivedCategory (SheafOfModules.{u} (structureSheafRing (Y r)))] in
include hdisj in
/-- If the images of the `k r` are pairwise disjoint, so are the opens `rangeOpen k r`. -/
theorem disjoint_rangeOpen : Pairwise fun r s => Disjoint (rangeOpen k r) (rangeOpen k s) :=
  fun r s hrs => disjoint_iff.mpr (eq_bot_iff.mpr fun x hx =>
    (Set.disjoint_left.mp (hdisj hrs) ((mem_rangeOpen_iff k r x).mp hx.1)
      ((mem_rangeOpen_iff k s x).mp hx.2)).elim)

omit [HasDerivedCategory (SheafOfModules.{u} (structureSheafRing X))]
  [∀ r, HasDerivedCategory (SheafOfModules.{u} (structureSheafRing (Y r)))] in
include hcov in
/-- If the images of the `k r` cover `X`, so do the opens `rangeOpen k r`. -/
theorem iSup_rangeOpen : ⨆ r, rangeOpen k r = ⊤ :=
  eq_top_iff.mpr fun x _ => by
    obtain ⟨r, hr⟩ := hcov x
    exact Opens.mem_iSup.mpr ⟨r, (mem_rangeOpen_iff k r x).mpr hr⟩

/-- Pullback of sheaves of modules along an open immersion preserves finite limits. -/
instance (r : ι) : PreservesFiniteLimits (modulePullback (k r)) :=
  haveI := openImmersionModulePullback_preservesHomology (k r)
  (modulePullback (k r)).preservesFiniteLimits_of_preservesHomology

/-- Pullback of sheaves of modules along an open immersion preserves finite colimits. -/
instance (r : ι) : PreservesFiniteColimits (modulePullback (k r)) :=
  haveI := openImmersionModulePullback_preservesHomology (k r)
  (modulePullback (k r)).preservesFiniteColimits_of_preservesHomology

include hdisj hcov in
/-- **The derived category decomposes along a decomposition into disjoint open pieces**: for a
family of open immersions of ringed spaces with pairwise disjoint images covering `X`, a morphism
of `D(𝒪_X)` all of whose pullbacks to the pieces vanish is zero. -/
theorem eq_zero_of_forall_modulePullback_mapDerivedCategory_map_eq_zero
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (φ : K ⟶ L)
    (hφ : ∀ r, (modulePullback (k r)).mapDerivedCategory.map φ = 0) : φ = 0 :=
  DerivedCategory.eq_zero_of_forall_mapDerivedCategory_map_eq_zero
    (fun r => modulePullback (k r))
    (fun r I hI => by
      have := hI
      exact openImmersionModulePullback_preservesKInjective (k r) I)
    (fun Z => by
      obtain ⟨I, q, hI, hq⟩ := sheaf_exists_kInjective_resolution X Z
      exact ⟨I, hI, q, hq⟩)
    (hglue_of_iso _ _ _ (modulePullbackIsoRestriction k)
      (exists_restriction_map_eq _ (disjoint_rangeOpen k hdisj) (iSup_rangeOpen k hcov)))
    (fun g hg => hinj_of_iso _ _ _ (modulePullbackIsoRestriction k)
      (fun g hg => eq_zero_of_forall_restriction_map_eq_zero _ (iSup_rangeOpen k hcov) g hg) g hg)
    φ hφ

end OpenImmersions


end Stacks.Cohomology.DisjointOpenCover

end
