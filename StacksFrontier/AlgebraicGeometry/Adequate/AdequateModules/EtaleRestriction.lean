module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AdequateFpqcDescent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionExactness
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.FlatAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ProductAlgebra
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.ZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Etale.SupportSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleGlobalFunctions

/-!
# The étale restriction of an adequate module is an associated module

Let `S` be a scheme and let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site `(Sch/S)_τ`
over `S`, for `τ` any of the five topologies. The restriction `𝓕|_{S_étale}` of `𝓕` to the small
étale site of `S` is the quasi-coherent `𝒪`-module associated to the restriction `𝓕|_{S_Zar}`.
This is **[Stacks, Tag 06VM] (2)**.

The small étale site `S_étale` is that of a chosen big étale site `E` containing `S` whose
schemes are schemes of the big site: its cutoff is at most that of `(Sch/S)_τ`, as when both
are cut out of one category `Sch_α`.

## Main definitions

* `Stacks.Adequate.BigSite.smallEtaleInclusion` — the inclusion `S_étale ⥤ (Sch/S)_τ`.
* `Stacks.Adequate.BigSite.etaleRestrict` — `𝓕|_{S_étale}` for an adequate `𝒪`-module `𝓕`, as a
  sheaf of modules on `S_étale`: the restriction of sections along the inclusion.
* `Stacks.Adequate.BigSite.etaleRestrictionComparison` — the canonical comparison
  `(𝓕|_{S_Zar})^a ⟶ 𝓕|_{S_étale}`, the counit of the associated-module adjunction of
  `S_étale`.

## Main results

* `Stacks.Adequate.BigSite.isSheaf_etaleRestrict` — `𝓕|_{S_étale}` is a sheaf: an adequate
  module satisfies the sheaf condition for fpqc coverings, by [Stacks, Tag 06VL], and an étale
  covering of `S_étale` is carried to an fpqc covering of the big site.
* `Stacks.Adequate.BigSite.zariskiRestrictModule_eq` — restricting `𝓕|_{S_étale}` further to the
  small Zariski site gives `𝓕|_{S_Zar}`.
* `Stacks.Adequate.BigSite.isIso_etaleRestrictionComparison` — **[Stacks, Tag 06VM] (2)**, for the
  small étale site of any big étale site whose schemes are schemes of `(Sch/S)_τ`.
* `Stacks.Adequate.BigSite.etaleSite` — the big étale site on the category of schemes of
  `(Sch/S)_τ`, for every `τ`, and `Stacks.Adequate.BigSite.isIso_etaleSiteRestrictionComparison`,
  **[Stacks, Tag 06VM] (2)** for its small étale site.

## Implementation notes

The proof is the source's. An étale morphism `U → V` of affine objects of `S_étale` is flat,
so `𝓕(U) = 𝓕(V) ⊗_{𝒪(V)} 𝒪(U)` by
`Stacks.Adequate.BigSite.bijective_restrictionBaseChange_of_flat`: `𝓕|_{S_étale}` is cartesian
between affine objects. Its restriction to `S_Zar` is `𝓕|_{S_Zar}`, quasi-coherent by
[Stacks, Tag 06VM] (1). A module on `S_étale` with these two properties is the associated module
of its Zariski restriction, the counit of the adjunction being an isomorphism, by
`AlgebraicGeometry.SmallEtale.isIso_counit_of_isCartesianOnAffines`.

The inclusion of `S_étale` into `(Sch/S)_τ` is not continuous for `τ = Zariski` — an étale
covering is not a Zariski covering — so the sheaf condition of `𝓕|_{S_étale}` is not read off a
continuity statement; it is read off the fpqc sheaf condition of the adequate module, which
covers all five topologies at once.

## References

* [Stacks Project, Tag 06VM](https://stacks.math.columbia.edu/tag/06VM)
* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) (E : BigEtaleSite.{u})
  (hSE : E.Contains S) (hle : E.cutoff ≤ B.cutoff)

include hle

/-! ### The inclusion of the small étale site -/

/-- The schemes of the big étale site `E` are schemes of the big site `B`. -/
theorem BigSite.schemeSizeBelow_le_of_cutoff_le :
    schemeSizeBelow E.cutoff ≤ schemeSizeBelow B.cutoff := fun _ h ↦ lt_of_lt_of_le h hle

/-- **The inclusion `S_étale ⥤ (Sch/S)_τ`** of the small étale site of `S` into a chosen big site
over `S` whose schemes contain those of the big étale site. -/
public noncomputable def BigSite.smallEtaleInclusion : SmallEtale E S hSE ⥤ B.category :=
  SmallEtale.inclusion E S hSE ⋙
    Over.post (ObjectProperty.ιOfLE (B.schemeSizeBelow_le_of_cutoff_le E hle))

/-- The inclusion is compatible-preserving for the fpqc topology of the big site: a cospan of
the small étale site is completed by its fibre product, which is the fibre product of the
underlying schemes. -/
private theorem compatiblePreserving_smallEtaleInclusion :
    CompatiblePreserving.{u} (fpqcPrecoverageOn B).toGrothendieck
      (B.smallEtaleInclusion E hSE hle) := by
  refine Stacks.Sites.compatiblePreserving_of_lift _ _ ?_
  intro Y₁ Y₂ Z g₁ g₂ X f₁ f₂ e
  have h : IsPullback ((SmallEtale.toScheme E S hSE).map (pullback.fst g₁ g₂))
      ((SmallEtale.toScheme E S hSE).map (pullback.snd g₁ g₂))
      ((SmallEtale.toScheme E S hSE).map g₁) ((SmallEtale.toScheme E S hSE).map g₂) :=
    (IsPullback.of_hasPullback g₁ g₂).map (SmallEtale.toScheme E S hSE)
  have e' : f₁.left.hom ≫ (SmallEtale.toScheme E S hSE).map g₁ =
      f₂.left.hom ≫ (SmallEtale.toScheme E S hSE).map g₂ :=
    congrArg (fun k : X.left ⟶ _ ↦ k.hom) (congrArg (fun k ↦ k.left) e)
  refine ⟨pullback g₁ g₂, pullback.fst g₁ g₂, pullback.snd g₁ g₂,
    Over.homMk (ObjectProperty.homMk (h.lift f₁.left.hom f₂.left.hom e')) ?_,
    pullback.condition, ?_, ?_⟩
  · have hw : (SmallEtale.toScheme E S hSE).map (pullback.fst g₁ g₂) ≫
        E.inclusion.map Y₁.obj.hom = E.inclusion.map (pullback g₁ g₂).obj.hom :=
      congrArg (fun k ↦ E.inclusion.map k) (Over.w (pullback.fst g₁ g₂).hom)
    apply ObjectProperty.hom_ext
    change h.lift f₁.left.hom f₂.left.hom e' ≫ E.inclusion.map (pullback g₁ g₂).obj.hom =
      X.hom.hom
    rw [← hw]
    exact (h.lift_fst_assoc _ _ e' _).trans (congrArg (fun k : X.left ⟶ _ ↦ k.hom) (Over.w f₁))
  · exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (h.lift_fst _ _ _))
  · exact Over.OverMorphism.ext (ObjectProperty.hom_ext _ (h.lift_snd _ _ _))

/-- A covering family of the small étale site of `S` is carried by the inclusion to an fpqc
covering family of the big site. -/
private theorem functorPushforward_mem_fpqc {X : SmallEtale E S hSE} {R : Presieve X}
    (hR : R ∈ SmallEtale.precoverage E S hSE X) :
    (Sieve.generate R).functorPushforward (B.smallEtaleInclusion E hSE hle) ∈
      (fpqcPrecoverageOn B).toGrothendieck ((B.smallEtaleInclusion E hSE hle).obj X) := by
  obtain ⟨𝒰, rfl, h𝒰⟩ := hR
  rw [← Sieve.generate_map_eq_functorPushforward, ← PreZeroHypercover.presieve₀_map]
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  exact Scheme.etalePrecoverage_le_fpqcPrecoverage _ h𝒰.1

/-! ### The restriction of an adequate module to the small étale site -/

/-- **`𝓕|_{S_étale}` is a sheaf** for the étale topology, for an adequate `𝒪`-module `𝓕`: an
adequate module satisfies the sheaf condition for fpqc covering families of the site
([Stacks, Tag 06VL]), and the inclusion carries étale coverings to fpqc coverings. -/
public theorem BigSite.isSheaf_etaleRestrict (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) :
    Presheaf.IsSheaf (SmallEtale.topology E S hSE)
      ((B.smallEtaleInclusion E hSE hle).op ⋙ F.val.presheaf) := by
  let ℱ : Sheaf (fpqcPrecoverageOn B).toGrothendieck (Type u) :=
    ⟨F.val.presheaf ⋙ forget AddCommGrpCat.{u}, isSheaf_fpqc_forget_of_isAdequate.{u, 0} B F hF⟩
  refine Stacks.Sites.isSheaf_addCommGrpCat_of_isSheaf_forget _ _ ?_
  have := smallEtale_precoverage_stableUnderBaseChange E S hSE
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro X R hR
  rw [Presieve.isSheafFor_iff_generate]
  exact Stacks.Sites.isSheafFor_op_comp (compatiblePreserving_smallEtaleInclusion B E hSE hle) ℱ
    _ (functorPushforward_mem_fpqc B E hSE hle hR)

/-- **The restriction `𝓕|_{S_étale}`** of an adequate `𝒪`-module on a chosen big site over `S` to
the small étale site of `S`: its sections over an object of `S_étale` are the sections of `𝓕`
over that object, viewed in the big site. -/
public noncomputable def BigSite.etaleRestrict (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) : SheafOfModules.{u} (SmallEtale.structureSheaf E S hSE) where
  val := (PresheafOfModules.pushforward₀ (B.smallEtaleInclusion E hSE hle)
    B.structureSheaf.obj).obj F.val
  isSheaf := B.isSheaf_etaleRestrict E hSE hle F hF

/-- Restricting `𝓕|_{S_étale}` further to the small Zariski site of `S` gives `𝓕|_{S_Zar}`. -/
public theorem BigSite.zariskiRestrictModule_eq (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) :
    (SmallEtale.restrictModule E S hSE).obj (B.etaleRestrict E hSE hle F hF) =
      B.zariskiRestrictModule.obj F :=
  rfl

/-! ### Assertion (2) -/

/-- **The canonical comparison `(𝓕|_{S_Zar})^a ⟶ 𝓕|_{S_étale}`** of [Stacks, Tag 06VM] (2): the
counit of the associated-module adjunction of `S_étale` at `𝓕|_{S_étale}`, whose restriction to
the small Zariski site is `𝓕|_{S_Zar}`. -/
public noncomputable def BigSite.etaleRestrictionComparison
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    (SmallEtale.associatedModule E S hSE).obj (B.zariskiRestrictModule.obj F) ⟶
      B.etaleRestrict E hSE hle F hF :=
  (SmallEtale.associatedModuleAdjunction E S hSE).counit.app (B.etaleRestrict E hSE hle F hF)

/-- **[Stacks, Tag 06VM] (2).** Let `𝓕` be an adequate `𝒪`-module on a chosen big `τ`-site
`(Sch/S)_τ` over a scheme `S`. The restriction `𝓕|_{S_étale}` of `𝓕` to the small étale site of
`S` is the quasi-coherent module associated to `𝓕|_{S_Zar}`: the canonical comparison
`(𝓕|_{S_Zar})^a ⟶ 𝓕|_{S_étale}` is an isomorphism. -/
@[stacks 06VM "(2), for the small étale site of any big étale site whose schemes are schemes of
(Sch/S)_τ: the restriction F|_{S_étale} of an adequate 𝒪-module F is the quasi-coherent module
associated to F|_{S_Zar}, the canonical map (F|_{S_Zar})^a → F|_{S_étale} being an isomorphism"]
public theorem BigSite.isIso_etaleRestrictionComparison
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    IsIso (B.etaleRestrictionComparison E hSE hle F hF) := by
  refine SmallEtale.isIso_counit_of_isCartesianOnAffines E S hSE _ (fun {T T'} g hT hT' ↦ ?_)
    (B.isQuasicoherent_zariskiRestrictModule F hF)
  have : IsAffine ((B.smallEtaleInclusion E hSE hle).obj T).left.obj := hT
  have : IsAffine ((B.smallEtaleInclusion E hSE hle).obj T').left.obj := hT'
  have : Etale ((SmallEtale.toScheme E S hSE).map g) := SmallEtale.etale_toScheme_map g
  exact B.bijective_restrictionBaseChange_of_flat F hF ((B.smallEtaleInclusion E hSE hle).map g)
    (inferInstanceAs (Flat ((SmallEtale.toScheme E S hSE).map g)))

/-- **[Stacks, Tag 06VM] (2)** as an isomorphism: `𝓕|_{S_étale} ≅ (𝓕|_{S_Zar})^a`. -/
public noncomputable def BigSite.etaleRestrictionIso
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    (SmallEtale.associatedModule E S hSE).obj (B.zariskiRestrictModule.obj F) ≅
      B.etaleRestrict E hSE hle F hF :=
  have := B.isIso_etaleRestrictionComparison E hSE hle F hF
  asIso (B.etaleRestrictionComparison E hSE hle F hF)

end Stacks.Adequate

/-! ### The small étale site of the base inside a chosen big site -/

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-- **The big étale site on the schemes of a chosen big site.** For a chosen big `τ`-site
`(Sch/S)_τ`, for any of the five topologies, the big étale site with the same cutoff — the
category `Sch_α` of the source — whose initial schemes are `S` alone. Its covering bound is
supplied by [Stacks, Tag 000X], `AlgebraicGeometry.BigEtaleSite.ofCutoff`; the cutoff conditions
of [Stacks, Tag 000J] it needs are those of the chosen big site,
`Stacks.Adequate.BigSite.cutoff_isStrongPrelimit` and
`Stacks.Adequate.BigSite.aleph0_lt_cutoff_cof`. -/
public noncomputable def BigSite.etaleSite : BigEtaleSite.{u} :=
  haveI := small_single.{u} S
  BigEtaleSite.ofCutoff B.cutoff B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    B.aleph0_lt_cutoff_cof {S} (by rintro X rfl; exact B.base_mem) ∅ (by simp) (by simp)

/-- The big étale site of a chosen big site has the same cutoff. -/
public theorem BigSite.etaleSite_cutoff : B.etaleSite.cutoff = B.cutoff :=
  rfl

/-- The base scheme belongs to the big étale site of a chosen big site. -/
public theorem BigSite.contains_etaleSite : B.etaleSite.Contains S :=
  B.base_mem

/-- **[Stacks, Tag 06VM] (2) for the small étale site `S_étale` of `(Sch/S)_τ` itself.** Let `𝓕`
be an adequate `𝒪`-module on a chosen big `τ`-site `(Sch/S)_τ`, for any of the five
topologies, and let `S_étale` be the small étale site of `S` in the same category of schemes,
`Stacks.Adequate.BigSite.etaleSite`. The restriction `𝓕|_{S_étale}` is the quasi-coherent module
associated to `𝓕|_{S_Zar}`: the canonical comparison `(𝓕|_{S_Zar})^a ⟶ 𝓕|_{S_étale}` is an
isomorphism. -/
@[stacks 06VM "(2): for an adequate 𝒪-module F on (Sch/S)_τ the restriction F|_{S_étale} to the
small étale site of S is the quasi-coherent module associated to F|_{S_Zar}, the canonical map
(F|_{S_Zar})^a → F|_{S_étale} being an isomorphism"]
public theorem BigSite.isIso_etaleSiteRestrictionComparison
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    IsIso (B.etaleRestrictionComparison B.etaleSite B.contains_etaleSite B.etaleSite_cutoff.le
      F hF) :=
  B.isIso_etaleRestrictionComparison B.etaleSite B.contains_etaleSite B.etaleSite_cutoff.le F hF

end Stacks.Adequate

end
