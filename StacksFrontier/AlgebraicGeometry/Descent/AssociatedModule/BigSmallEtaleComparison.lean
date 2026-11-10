module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedSheafNaturality
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsCorepresentable
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentTopologiesTwo.TopologyIndependence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor

/-!
# The big and the small étale associated module

Let `T` be a scheme and `𝓕` a quasi-coherent `𝒪_T`-module.  Descent, Definition 03DU, attaches to
`𝓕` an associated module `𝓕^a` on every site of `T` of Section 03DT, by the one formula
`(f : W → T) ↦ Γ(W, f^*𝓕)`.  Two of these sites are the big `τ`-site `(Sch/T)_τ` and the small
étale site `T_étale`, and the small étale site is a full subcategory of the big site for every
`τ` finer than the étale topology.  The formula then says that **the restriction of the big
`𝓕^a` to `T_étale` is the small `𝓕^a`**.

In this library the two associated modules are the pullbacks of `𝓕` along the two morphisms of
ringed sites to the small Zariski site of `T`
(`AlgebraicGeometry.BigFppfOver.baseAssociatedModule` and
`AlgebraicGeometry.SmallEtale.associatedModule`), and the restriction is the pushforward
`AlgebraicGeometry.SmallEtale.bigRestrict` along the inclusion of the small étale site.  The
comparison is therefore not a reflexivity: it is the mate
`AlgebraicGeometry.SmallEtale.bigRestrictAssociatedModuleNatTrans` of the identification of the
two right adjoints (restricting to the small Zariski site directly, or through the small étale
site), natural in every `𝒪_T`-module, and it is an isomorphism at a quasi-coherent module because
both associated modules are the sheaf of pullback sections (Stacks 070S).

## Main definitions

* `AlgebraicGeometry.SmallEtale.bigRestrict`: restriction from the big `τ`-site of `T` to the
  small étale site of `T`.
* `AlgebraicGeometry.SmallEtale.bigRestrictAssociatedModuleNatTrans`: the canonical comparison
  `𝓕^a_small ⟶ (𝓕^a_big)|_{T_étale}`.
* `AlgebraicGeometry.SmallEtale.bigRestrictAssociatedModuleIso`: **(1) the restriction of the
  big associated module of a quasi-coherent module to the small étale site is the small associated
  module.**
* `AlgebraicGeometry.SmallEtale.bigRestrictAlong`: for `a : X ⟶ Y`, restriction from the big site
  of `Y` to the small étale site of `X` along `W' ↦ (W' ⟶ X ⟶ Y)`, and
  `AlgebraicGeometry.SmallEtale.bigRestrictAlongAssociatedModuleIso`: **(1') it carries `𝓕^a` to
  `(a^*𝓕)^a`**, again the inverse of a canonical mate
  (`AlgebraicGeometry.SmallEtale.bigRestrictAlongAssociatedModuleNatTrans`).
* `AlgebraicGeometry.SmallEtale.bigRestrictComparison`: the comparison of Stacks 06WC on the big
  site of `Y`, `G|_{Y_ét} ⟶ ε_{a,*}(G|_{X_ét, along a})`, restriction along the base-change
  projections `W ×_Y X ⟶ W`.

## Main results

* `AlgebraicGeometry.SmallEtale.bigRestrictAssociatedModuleIso_hom_naturality`: the
  identification is natural in the quasi-coherent module.
* `AlgebraicGeometry.SmallEtale.bigRestrictAssociatedModuleNatTrans_app_comp`: on a
  quasi-coherent module the canonical comparison is the identification through the sheaves of
  pullback sections.
* `AlgebraicGeometry.SmallEtale.bigRestrictAlongAssociatedModuleIso_hom_naturality`: (2') the
  identification along `a` is natural in the quasi-coherent module.
* `AlgebraicGeometry.SmallEtale.bigRestrictComparison_app_associatedModule`: **(3) compatibility
  with base change**: under (1) and (1'), the comparison of Stacks 06WC at `𝓕^a` is the transpose
  of the base-change identification `(a^*𝓕)^a ≅ ε_a^*(𝓕^a)` of Stacks 03LC (1)
  (`AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso`).  No flatness is needed.
* `AlgebraicGeometry.SmallEtale.isIso_homEquiv_symm_bigRestrictComparison_app`: hence the
  comparison `ε_a^*(𝓕^a|_{Y_ét}) ⟶ 𝓕^a|_{X_ét, along a}` is an isomorphism.
* `BigFppfOver.val_unit_comp_baseRestrictModule_map_baseAssociatedModuleIsoSectionsSheaf`:
  the unit of the big associated-module adjunction pulls sections back, at every topology.

## Implementation notes

The identifications (1) and (1') are defined as inverses of mates, so that their naturality is
the naturality of a natural transformation and (3) is a computation with mates: the transposes of
both sides of (3) are restriction maps along arrows into an open of `Y`, and
`AlgebraicGeometry.SmallEtale.conjugateEquiv_associatedModuleBaseChangeIso_inv` pins the
base-change identification.  Invertibility is the only place where sections are computed: both
sides are read as sheaves of pullback sections (Stacks 070S), and on a section `s` over an open
`V` of `Y` the two transposes are the pullback of `s` to `a⁻¹(V)` in its two spellings, compared
by the composition isomorphism of pullbacks (`AlgebraicGeometry.SmallEtale.zariskiSections_eq`).
Comparing a big-site and a small-site map of pullback-sections presheaves by `rfl` is far over
the kernel's budget, which is why the proofs go through the adjunction units instead.

## References

* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

/-- Pasting three commuting squares side by side. -/
private theorem comp_comp_comp_eq {C : Type*} [Category C] {A B P Q R S T U : C} {f : A ⟶ B}
    {g : B ⟶ P} {g' : A ⟶ Q} {s : Q ⟶ P} {m : P ⟶ R} {m' : Q ⟶ S} {u : S ⟶ R} {c : R ⟶ T}
    {c' : S ⟶ U} {t : U ⟶ T} (h₁ : f ≫ g = g' ≫ s) (h₂ : s ≫ m = m' ≫ u)
    (h₃ : u ≫ c = c' ≫ t) : f ≫ g ≫ m ≫ c = (g' ≫ m' ≫ c') ≫ t := by
  simp only [Category.assoc]
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- A functor carries a commuting square to a commuting square. -/
private theorem map_comp_eq_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z W : C} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ W} {d : W ⟶ Z} (h : a ≫ b = c ≫ d) :
    F.map a ≫ F.map b = F.map c ≫ F.map d := by
  rw [← F.map_comp, h, F.map_comp]

namespace AlgebraicGeometry.SmallEtale

/-! ### The small étale associated module as the sheaf of pullback sections -/

section SmallSheaf

variable (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T)

/-- The map of sheaves of pullback sections on the small étale site induced by a morphism of
quasi-coherent modules. -/
def sectionsSheafOfModulesMap {𝓕 𝓖 : T.Modules} [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent]
    (α : 𝓕 ⟶ 𝓖) : sectionsSheafOfModules' E T hT 𝓕 ⟶ sectionsSheafOfModules' E T hT 𝓖 :=
  ⟨sectionsPresheafOfModulesMap E T hT α⟩

/-- **Stacks 070S (2) with the sheafification stripped is natural in the module.** -/
theorem associatedModuleIsoSectionsSheafOfModules'_hom_naturality {𝓕 𝓖 : T.Modules}
    [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) :
    (associatedModule E T hT).map α ≫ (associatedModuleIsoSectionsSheafOfModules' E T hT 𝓖).hom =
      (associatedModuleIsoSectionsSheafOfModules' E T hT 𝓕).hom ≫
        sectionsSheafOfModulesMap E T hT α := by
  exact comp_comp_comp_eq ((associatedModuleSheafificationIso E T hT).hom.naturality α)
    (map_comp_eq_map_comp (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf E T hT).obj))
      (sectionsComparison_naturality_module E T hT α))
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf E T hT).obj)).counit.naturality (sectionsSheafOfModulesMap E T hT α))

end SmallSheaf
end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.BigFppfOver

/-! ### The big associated module as the sheaf of pullback sections, naturally -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The map of sheaves of pullback sections on `(Sch/S)_τ` induced by a morphism of
quasi-coherent modules. -/
def sectionsSheafOfModulesMap (τ : SiteKind) {𝓕 𝓖 : S.Modules} [𝓕.IsQuasicoherent]
    [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) :
    sectionsSheafOfModules B S hS τ 𝓕 ⟶ sectionsSheafOfModules B S hS τ 𝓖 :=
  ⟨Stacks.Adequate.pullbackSectionsPresheafMap B S hS α⟩

/-- **Stacks 070S (1) at every topology is natural in the module.** -/
theorem baseAssociatedModuleIsoSections_hom_naturality (τ : SiteKind) {𝓕 𝓖 : S.Modules}
    [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) :
    (baseAssociatedModule B S hS τ).map α ≫ (baseAssociatedModuleIsoSections B S hS τ 𝓖).hom =
      (baseAssociatedModuleIsoSections B S hS τ 𝓕).hom ≫
        (PresheafOfModules.sheafification.{u}
          (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (Stacks.Adequate.pullbackSectionsPresheafMap B S hS α) := by
  unfold baseAssociatedModuleIsoSections
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (baseAssociatedModuleSheafificationIso B S hS τ).hom.naturality α]
  simp only [Category.assoc]
  exact congrArg ((baseAssociatedModuleSheafificationIso B S hS τ).hom.app 𝓕 ≫ ·)
    (map_comp_eq_map_comp (PresheafOfModules.sheafification.{u}
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj))
      (Stacks.Adequate.sectionsComparison_naturality_module B S hS α))

/-- **Stacks 070S (1) with the sheafification stripped is natural in the module.** -/
theorem baseAssociatedModuleIsoSectionsSheaf_hom_naturality (τ : SiteKind) {𝓕 𝓖 : S.Modules}
    [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) :
    (baseAssociatedModule B S hS τ).map α ≫
        (baseAssociatedModuleIsoSectionsSheaf B S hS τ 𝓖).hom =
      (baseAssociatedModuleIsoSectionsSheaf B S hS τ 𝓕).hom ≫
        sectionsSheafOfModulesMap B S hS τ α := by
  have h1 := baseAssociatedModuleIsoSections_hom_naturality B S hS τ α
  have h2 := ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).counit).naturality
        (sectionsSheafOfModulesMap B S hS τ α)
  exact (Category.assoc _ _ _).symm.trans ((eq_whisker h1 _).trans ((Category.assoc _ _ _).trans
    ((whisker_eq _ h2).trans (Category.assoc _ _ _).symm)))

/-- The sheafification of a sheaf of pullback sections is that sheaf: the unit of the
sheafification adjunction at it is invertible. -/
def baseSheafificationSectionsIso (τ : SiteKind) (F : S.Modules) [F.IsQuasicoherent] :
    (PresheafOfModules.sheafification.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).obj
        (sectionsPresheafOfModules B S hS F) ≅ sectionsSheafOfModules B S hS τ F :=
  (SheafOfModules.fullyFaithfulForget (FibredSite.baseRingStructureSheaf B S hS τ)).preimageIso
    (@asIso _ _ _ _ _ (isIso_baseSheafificationAdjunction_unit_app B S hS τ
      (sectionsPresheafOfModules B S hS F)
      (isSheaf_sectionsPresheafOfModules_baseOverTopology B S hS τ F))).symm

/-- **The unit of the big associated-module adjunction pulls sections back**, read through the
identification of `𝓕^a` with the sheaf of pullback sections. -/
theorem val_unit_comp_baseRestrictModule_map_baseAssociatedModuleIsoSectionsSheaf (τ : SiteKind)
    (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.Hom.val ((baseAssociatedModuleAdjunction B S hS τ).unit.app F ≫
      (baseRestrictModule B S hS τ).map (baseAssociatedModuleIsoSectionsSheaf B S hS τ F).hom) =
      sectionsUnit B S hS F := by
  have hA := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.pullbackPushforwardAdjunction.{u} (baseStructureMap B S hS τ))
    (SheafOfModules.PullbackConstruction.adjunction.{u} (baseStructureMap B S hS τ)) F
  have hkey := Adjunction.unit_comp_map_unit_comp
      (PresheafOfModules.pullbackPushforwardAdjunction.{u} (baseStructureMap B S hS τ).hom)
      (PresheafOfModules.sheafificationAdjunction (𝟙
        (FibredSite.baseRingStructureSheaf B S hS τ).obj))
      ((SheafOfModules.forget S.ringCatSheaf).obj F)
      (sectionsComparison B S hS F)
      (unit_comp_map_sectionsComparison B S hS F)
  have hu := isIso_baseSheafificationAdjunction_unit_app B S hS τ
    (sectionsPresheafOfModules B S hS F)
      (isSheaf_sectionsPresheafOfModules_baseOverTopology B S hS τ F)
  have hcounit : (PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).counit.app
        (sectionsSheafOfModules B S hS τ F) =
      (baseSheafificationSectionsIso B S hS τ F).hom := by
    refine (SheafOfModules.fullyFaithfulForget
      (FibredSite.baseRingStructureSheaf B S hS τ)).map_injective ?_
    refine Eq.trans (IsIso.inv_eq_of_hom_inv_id
      ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).right_triangle_components
          (Y := sectionsSheafOfModules B S hS τ F))).symm ?_
    exact ((SheafOfModules.fullyFaithfulForget
      (FibredSite.baseRingStructureSheaf B S hS τ)).map_preimage _).symm
  have hiso : (baseAssociatedModuleIsoSectionsSheaf B S hS τ F).hom =
      (((baseAssociatedModuleSheafificationIso B S hS τ).app F).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙
          (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (sectionsComparison B S hS F)) ≫
        (baseSheafificationSectionsIso B S hS τ F).hom :=
    congrArg (fun k => (((baseAssociatedModuleSheafificationIso B S hS τ).app F).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙
          (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (sectionsComparison B S hS F)) ≫ k) hcounit
  have hA' : (baseAssociatedModuleAdjunction B S hS τ).unit.app F ≫
      (baseRestrictModule B S hS τ).map
        ((baseAssociatedModuleSheafificationIso B S hS τ).app F).hom =
      (SheafOfModules.PullbackConstruction.adjunction.{u}
        (baseStructureMap B S hS τ)).unit.app F := hA
  rw [hiso, Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc, hA']
  refine Eq.trans (show _ = (((SheafOfModules.forget S.ringCatSheaf).map
        ((SheafOfModules.PullbackConstruction.adjunction.{u}
          (baseStructureMap B S hS τ)).unit.app F) ≫
      (PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map
        ((SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ) ⋙
          PresheafOfModules.restrictScalars (𝟙
            (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          ((PresheafOfModules.sheafification.{u} (𝟙
            (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
            (sectionsComparison B S hS F)))) ≫
      (PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map
        ((SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ) ⋙
          PresheafOfModules.restrictScalars (𝟙
            (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (baseSheafificationSectionsIso B S hS τ F).hom)) from rfl) ?_
  refine Eq.trans (congrArg (fun k => k ≫
    (PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map
      ((SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ) ⋙
        PresheafOfModules.restrictScalars (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (baseSheafificationSectionsIso B S hS τ F).hom)) hkey) ?_
  have hCc : (SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ) ⋙
        PresheafOfModules.restrictScalars (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (baseSheafificationSectionsIso B S hS τ F).hom =
      inv ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app
          (sectionsPresheafOfModules B S hS F)) :=
    (SheafOfModules.fullyFaithfulForget (FibredSite.baseRingStructureSheaf B S hS τ)).map_preimage _
  have hfin : (PresheafOfModules.sheafificationAdjunction
        (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app
          (sectionsPresheafOfModules B S hS F) ≫
      (SheafOfModules.forget (FibredSite.baseRingStructureSheaf B S hS τ) ⋙
        PresheafOfModules.restrictScalars (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).map
          (baseSheafificationSectionsIso B S hS τ F).hom = 𝟙 _ :=
    Eq.trans (congrArg (fun k => (PresheafOfModules.sheafificationAdjunction
      (𝟙 (FibredSite.baseRingStructureSheaf B S hS τ).obj)).unit.app
        (sectionsPresheafOfModules B S hS F) ≫ k) hCc)
      (IsIso.hom_inv_id _)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => sectionsUnit B S hS F ≫ k) ((Functor.map_comp _ _ _).symm.trans
    ((congrArg (fun k => (PresheafOfModules.pushforward.{u} (baseStructureMap B S hS τ).hom).map k)
      hfin).trans (CategoryTheory.Functor.map_id _ _)))).trans ?_
  exact Category.comp_id _



end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry.SmallEtale

/-! ### Restriction from the big site to the small étale site -/

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

include h

/-- A scheme of the big étale site lies in a big fppf site with the same cutoff. -/
theorem bigContains {T : Scheme.{u}} (hT : E.Contains T) : B.Contains T := by
  simpa [h] using hT

/-- The inclusion of the small étale site of `T` into the big site of `T` is continuous for every
topology `τ` finer than the étale one. -/
theorem isContinuous_smallEtaleInclusion_baseOverTopology (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    (Stack.smallEtaleInclusion B E h T hT).IsContinuous (SmallEtale.topology E T hT)
      (BigFppfOver.baseOverTopology B T (bigContains B E h hT) τ) :=
  have _h0 := (Stack.isContinuous_and_isCocontinuous_smallEtaleInclusion B E h T hT).1
  ⟨fun F => Functor.IsContinuous.op_comp_isSheaf_of_types (J := SmallEtale.topology E T hT)
    (K := (etaleTopology B).over (B.obj (bigContains B E h hT)))
    ⟨F.obj, F.property.of_le (Stacks.Sites.over_mono hτ _)⟩⟩

/-- The comparison of structure sheaves along the inclusion of the small étale site into the big
site: the identity, the two structure sheaves having the same sections. -/
def bigRestrictStructureMap (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    letI := isContinuous_smallEtaleInclusion_baseOverTopology B E h T hT τ hτ
    SmallEtale.structureSheaf E T hT ⟶
      ((Stack.smallEtaleInclusion B E h T hT).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology E T hT)
        (BigFppfOver.baseOverTopology B T (bigContains B E h hT) τ)).obj
          (FibredSite.baseRingStructureSheaf B T (bigContains B E h hT) τ) :=
  𝟙 _

/-- The restriction of a module on the big `τ`-site of `T` to the small étale site of `T`:
restriction of sections along the inclusion, the two structure sheaves having the same
sections. -/
def bigRestrict (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    SheafOfModules.{u} (FibredSite.baseRingStructureSheaf B T (bigContains B E h hT) τ) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf E T hT) :=
  letI := isContinuous_smallEtaleInclusion_baseOverTopology B E h T hT τ hτ
  SheafOfModules.pushforward.{u} (bigRestrictStructureMap B E h T hT τ hτ)

/-- The underlying presheaf of a restriction is the restriction of the underlying presheaf. -/
theorem bigRestrict_obj_val_presheaf (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (G : SheafOfModules.{u}
      (FibredSite.baseRingStructureSheaf B T (bigContains B E h hT) τ)) :
    ((bigRestrict B E h T hT τ hτ).obj G).val.presheaf =
      (Stack.smallEtaleInclusion B E h T hT).op ⋙ G.val.presheaf :=
  rfl

/-- The small Zariski site of `T`, included into the small étale site and then into the big
site, is the small Zariski site included into the big site. -/
theorem opensToSmallEtale_comp_smallEtaleInclusion (T : Scheme.{u}) (hT : E.Contains T) :
    opensToSmallEtale E T hT ⋙ Stack.smallEtaleInclusion B E h T hT =
      BigFppfOver.opensToBig B T (bigContains B E h hT) :=
  rfl


/-- The structure-sheaf comparison of the big site over its small Zariski site factors through
the small étale site. -/
theorem structureMap_comp_bigRestrictStructureMap (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    letI := isContinuous_smallEtaleInclusion_baseOverTopology B E h T hT τ hτ
    structureMap E T hT ≫ ((opensToSmallEtale E T hT).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology ↥T) (SmallEtale.topology E T hT)).map
          (bigRestrictStructureMap B E h T hT τ hτ) =
      BigFppfOver.baseStructureMap B T (bigContains B E h hT) τ :=
  rfl

/-- Restricting to the small Zariski site through the small étale site is restricting to the
small Zariski site directly. -/
def bigRestrictCompRestrictModuleIso (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    BigFppfOver.baseRestrictModule B T (bigContains B E h hT) τ ≅
      bigRestrict B E h T hT τ hτ ⋙ restrictModule E T hT :=
  letI := isContinuous_smallEtaleInclusion_baseOverTopology B E h T hT τ hτ
  (SheafOfModules.pushforwardComp.{u} (structureMap E T hT)
    (bigRestrictStructureMap B E h T hT τ hτ)).symm

/-- **The restriction of the big sheaf of pullback sections is the small one**: both are the
presheaf `(W → T) ↦ Γ(W, W^*𝓕)` read on the small étale site. -/
def bigRestrictSectionsSheafIso (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : T.Modules) [𝓕.IsQuasicoherent] :
    (bigRestrict B E h T hT τ hτ).obj
        (BigFppfOver.sectionsSheafOfModules B T (bigContains B E h hT) τ 𝓕) ≅
      sectionsSheafOfModules' E T hT 𝓕 :=
  Iso.refl _

/-- **The canonical comparison `𝓕^a_small ⟶ (𝓕^a_big)|_{T_ét}`**, the mate of the
identification `bigRestrictCompRestrictModuleIso` of the two right adjoints: restricting from
the big site to the small Zariski site directly, or through the small étale site. -/
def bigRestrictAssociatedModuleNatTrans (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    associatedModule E T hT ⟶
      BigFppfOver.baseAssociatedModule B T (bigContains B E h hT) τ ⋙
        bigRestrict B E h T hT τ hτ :=
  (mateEquiv (BigFppfOver.baseAssociatedModuleAdjunction B T (bigContains B E h hT) τ)
    (associatedModuleAdjunction E T hT)).symm
      (TwoSquare.mk (BigFppfOver.baseRestrictModule B T (bigContains B E h hT) τ)
        (bigRestrict B E h T hT τ hτ) (𝟭 T.Modules) (restrictModule E T hT)
        (bigRestrictCompRestrictModuleIso B E h T hT τ hτ).hom)

/-- The transpose of the canonical comparison is the unit of the big associated-module
adjunction, read through `bigRestrictCompRestrictModuleIso`. -/
theorem unit_comp_bigRestrictAssociatedModuleNatTrans (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) (𝓕 : T.Modules) :
    (associatedModuleAdjunction E T hT).unit.app 𝓕 ≫
        (restrictModule E T hT).map ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕) =
      (BigFppfOver.baseAssociatedModuleAdjunction B T (bigContains B E h hT) τ).unit.app 𝓕 ≫
        (bigRestrictCompRestrictModuleIso B E h T hT τ hτ).hom.app _ :=
  (unit_mateEquiv_symm _ _ _ 𝓕).symm

/-- **On a quasi-coherent module the canonical comparison is the identification through
pullback sections**: followed by the identification of `𝓕^a_big` with the sheaf of pullback
sections, it is the identification of `𝓕^a_small` with the same sheaf.  Both are pinned by their
transposes, which pull a section of `𝓕` back to the open subscheme it lives on. -/
theorem bigRestrictAssociatedModuleNatTrans_app_comp (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : T.Modules) [𝓕.IsQuasicoherent] :
    (bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕 ≫
        (bigRestrict B E h T hT τ hτ).map
          (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B T (bigContains B E h hT) τ 𝓕).hom ≫
        (bigRestrictSectionsSheafIso B E h T hT τ hτ 𝓕).hom =
      (associatedModuleIsoSectionsSheafOfModules' E T hT 𝓕).hom := by
  apply ((associatedModuleAdjunction E T hT).homEquiv _ _).injective
  have hθ : (associatedModuleAdjunction E T hT).homEquiv _ _
      ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕) =
      (BigFppfOver.baseAssociatedModuleAdjunction B T (bigContains B E h hT) τ).unit.app 𝓕 ≫
        (bigRestrictCompRestrictModuleIso B E h T hT τ hτ).hom.app _ :=
    (Adjunction.homEquiv_unit (associatedModuleAdjunction E T hT) 𝓕 _
      ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕)).trans
      (unit_comp_bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ 𝓕)
  refine ((associatedModuleAdjunction E T hT).homEquiv_naturality_right _ _).trans ?_
  refine (congrArg (fun k => k ≫ (restrictModule E T hT).map
    ((bigRestrict B E h T hT τ hτ).map
      (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B T (bigContains B E h hT) τ 𝓕).hom ≫
      (bigRestrictSectionsSheafIso B E h T hT τ hτ 𝓕).hom)) hθ).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit (associatedModuleAdjunction E T hT) 𝓕 _
    (associatedModuleIsoSectionsSheafOfModules' E T hT 𝓕).hom).symm
  have h1 := BigFppfOver.val_unit_comp_baseRestrictModule_map_baseAssociatedModuleIsoSectionsSheaf
    B T (bigContains B E h hT) τ 𝓕
  have h2 := SmallEtale.val_unit_comp_restrictModule_map_associatedModuleIsoSections E T hT 𝓕
  refine SheafOfModules.hom_ext (PresheafOfModules.Hom.ext (funext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_)))
  have h1' := congrArg (fun φ => (φ.app U).hom x) h1
  have h2' := congrArg (fun φ => (φ.app U).hom x) h2
  exact h1'.trans h2'.symm

/-- **The canonical comparison is an isomorphism at a quasi-coherent module.** -/
instance isIso_bigRestrictAssociatedModuleNatTrans_app (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : T.Modules) [𝓕.IsQuasicoherent] :
    IsIso ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕) := by
  have h1 := bigRestrictAssociatedModuleNatTrans_app_comp B E h T hT τ hτ 𝓕
  have : IsIso ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕 ≫
      (bigRestrict B E h T hT τ hτ).map
        (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B T (bigContains B E h hT) τ 𝓕).hom ≫
      (bigRestrictSectionsSheafIso B E h T hT τ hτ 𝓕).hom) := by
    rw [h1]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((bigRestrict B E h T hT τ hτ).map
        (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B T (bigContains B E h hT) τ 𝓕).hom ≫
      (bigRestrictSectionsSheafIso B E h T hT τ hτ 𝓕).hom)

/-- **(1) The big and the small étale associated modules.**  For a quasi-coherent
`𝒪_T`-module `𝓕`, the restriction to the small étale site of `T` of the associated module of
`𝓕` on the big `τ`-site of `T` is the associated module of `𝓕` on the small étale site.  The
isomorphism is the inverse of the canonical comparison
`AlgebraicGeometry.SmallEtale.bigRestrictAssociatedModuleNatTrans`. -/
def bigRestrictAssociatedModuleIso (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : T.Modules) [𝓕.IsQuasicoherent] :
    (bigRestrict B E h T hT τ hτ).obj
        ((BigFppfOver.baseAssociatedModule B T (bigContains B E h hT) τ).obj 𝓕) ≅
      (SmallEtale.associatedModule E T hT).obj 𝓕 :=
  (asIso ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).app 𝓕)).symm

/-- **(2) The identification of the big and the small étale associated modules is natural in
the quasi-coherent module.** -/
theorem bigRestrictAssociatedModuleIso_hom_naturality (T : Scheme.{u}) (hT : E.Contains T)
    (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) {𝓕 𝓖 : T.Modules}
    [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) :
    (bigRestrict B E h T hT τ hτ).map
          ((BigFppfOver.baseAssociatedModule B T (bigContains B E h hT) τ).map α) ≫
        (bigRestrictAssociatedModuleIso B E h T hT τ hτ 𝓖).hom =
      (bigRestrictAssociatedModuleIso B E h T hT τ hτ 𝓕).hom ≫
        (SmallEtale.associatedModule E T hT).map α := by
  rw [bigRestrictAssociatedModuleIso, bigRestrictAssociatedModuleIso, Iso.symm_hom, Iso.symm_hom,
    asIso_inv, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact ((bigRestrictAssociatedModuleNatTrans B E h T hT τ hτ).naturality α).symm

variable {X Y : E.Scheme} (a : X ⟶ Y)

/-- `a` as a morphism of the big fppf site. -/
def bigHom : B.obj (bigContains B E h X.property) ⟶ B.obj (bigContains B E h Y.property) :=
  (ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff) (P' := schemeSizeBelow B.cutoff)
    (by intro Z hZ; simpa [h] using hZ)).map a

/-- The small étale site of `X` inside the big fppf site of `Y`, along `a`:
`W' ↦ (W' ⟶ X ⟶ Y)`. -/
def bigRestrictAlongFunctor :
    SmallEtale E X.obj X.property ⥤ BigFppfOver B Y.obj (bigContains B E h Y.property) :=
  Stack.smallEtaleInclusion B E h X.obj X.property ⋙ Over.map (bigHom B E h a)

/-- The small étale site of `X`, included into the big site of `Y` along `a`, is continuous. -/
theorem isContinuous_bigRestrictAlongFunctor (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    (bigRestrictAlongFunctor B E h a).IsContinuous (SmallEtale.topology E X.obj X.property)
      (BigFppfOver.baseOverTopology B Y.obj (bigContains B E h Y.property) τ) :=
  let := isContinuous_smallEtaleInclusion_baseOverTopology B E h X.obj X.property τ hτ
  Functor.isContinuous_comp _ _ _
    (BigFppfOver.baseOverTopology B X.obj (bigContains B E h X.property) τ) _

/-- The comparison of structure sheaves along the inclusion of the small étale site of `X` into
the big site of `Y` along `a`: the identity, both structure sheaves having the same sections. -/
def bigRestrictAlongStructureMap (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    letI := isContinuous_bigRestrictAlongFunctor B E h a τ hτ
    SmallEtale.structureSheaf E X.obj X.property ⟶
      ((bigRestrictAlongFunctor B E h a).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology E X.obj X.property)
        (BigFppfOver.baseOverTopology B Y.obj (bigContains B E h Y.property) τ)).obj
          (FibredSite.baseRingStructureSheaf B Y.obj (bigContains B E h Y.property) τ) :=
  𝟙 _

/-- Restriction of a module on the big `τ`-site of `Y` to the small étale site of `X` along
`a`: the sections over `W' ∈ X_ét` are the sections over `W' ⟶ X ⟶ Y`. -/
def bigRestrictAlong (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    SheafOfModules.{u}
        (FibredSite.baseRingStructureSheaf B Y.obj (bigContains B E h Y.property) τ) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf E X.obj X.property) :=
  letI := isContinuous_bigRestrictAlongFunctor B E h a τ hτ
  SheafOfModules.pushforward.{u} (bigRestrictAlongStructureMap B E h a τ hτ)

/-- The base-change projection `W ×_Y X ⟶ W`, as an arrow of the big site of `Y`, natural in
`W ∈ Y_ét`. -/
def baseChangeProjection :
    smallEtaleBaseChange E a ⋙ bigRestrictAlongFunctor B E h a ⟶
      Stack.smallEtaleInclusion B E h Y.obj Y.property where
  app W := Over.homMk ((ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
      (P' := schemeSizeBelow B.cutoff) (by intro Z hZ; simpa [h] using hZ)).map
        (Limits.pullback.fst W.obj.hom a))
      (((ObjectProperty.ιOfLE _).map_comp _ _).symm.trans
        ((congrArg (ObjectProperty.ιOfLE _).map Limits.pullback.condition).trans
          ((ObjectProperty.ιOfLE _).map_comp _ _)))
  naturality W₁ W₂ f := by
    apply Over.OverMorphism.ext
    refine ((ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff) (P' := schemeSizeBelow B.cutoff)
        (by intro Z hZ; simpa [h] using hZ)).map_comp _ _).symm.trans
      (Eq.trans ?_ ((ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
        (P' := schemeSizeBelow B.cutoff)
        (by intro Z hZ; simpa [h] using hZ)).map_comp _ _))
    refine congrArg (ObjectProperty.ιOfLE (P := schemeSizeBelow E.cutoff)
      (P' := schemeSizeBelow B.cutoff)
        (by intro Z hZ; simpa [h] using hZ)).map ?_
    exact Limits.pullback.lift_fst _ _ _

/-- The two maps of structure sheaves below the base-change projection agree: both pull a
global function on `W` back along `W ×_Y X ⟶ W`. -/
theorem bigRestrictStructureMap_comp_baseChangeProjection (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    letI := isContinuous_smallEtaleInclusion_baseOverTopology B E h Y.obj Y.property τ hτ
    letI := isContinuous_bigRestrictAlongFunctor B E h a τ hτ
    letI : (smallEtaleBaseChange E a ⋙ bigRestrictAlongFunctor B E h a).IsContinuous
        (SmallEtale.topology E Y.obj Y.property)
        (BigFppfOver.baseOverTopology B Y.obj (bigContains B E h Y.property) τ) :=
      Functor.isContinuous_comp _ _ _ (SmallEtale.topology E X.obj X.property) _
    bigRestrictStructureMap B E h Y.obj Y.property τ hτ ≫
        (Functor.sheafPushforwardContinuousNatTrans (baseChangeProjection B E h a) RingCat.{u}
          (SmallEtale.topology E Y.obj Y.property)
          (BigFppfOver.baseOverTopology B Y.obj (bigContains B E h Y.property) τ)).app
          (FibredSite.baseRingStructureSheaf B Y.obj (bigContains B E h Y.property) τ) =
      smallEtaleStructureMapRing E a ≫
        ((smallEtaleBaseChange E a).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology E Y.obj Y.property) (SmallEtale.topology E X.obj X.property)).map
          (bigRestrictAlongStructureMap B E h a τ hτ) :=
  rfl

/-- **The comparison of Stacks 06WC for a module on the big site of `Y`.**  Over `W ∈ Y_ét` it is
the restriction map of the module along the base-change projection `W ×_Y X ⟶ W`, from the
restriction to `Y_ét` to the pushforward along `ε_a` of the restriction to `X_ét` along `a`. -/
def bigRestrictComparison (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    bigRestrict B E h Y.obj Y.property τ hτ ⟶
      bigRestrictAlong B E h a τ hτ ⋙
        SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E a) :=
  letI := isContinuous_smallEtaleInclusion_baseOverTopology B E h Y.obj Y.property τ hτ
  letI := isContinuous_bigRestrictAlongFunctor B E h a τ hτ
  letI : (smallEtaleBaseChange E a ⋙ bigRestrictAlongFunctor B E h a).IsContinuous
      (SmallEtale.topology E Y.obj Y.property)
      (BigFppfOver.baseOverTopology B Y.obj (bigContains B E h Y.property) τ) :=
    Functor.isContinuous_comp _ _ _ (SmallEtale.topology E X.obj X.property) _
  SheafOfModules.pushforwardNatTrans.{u} (bigRestrictStructureMap B E h Y.obj Y.property τ hτ)
      (baseChangeProjection B E h a) ≫
    (SheafOfModules.pushforwardCongr.{u}
      (bigRestrictStructureMap_comp_baseChangeProjection B E h a τ hτ)).hom ≫
    (SheafOfModules.pushforwardComp.{u} (smallEtaleStructureMapRing E a)
      (bigRestrictAlongStructureMap B E h a τ hτ)).inv

/-- **The comparison of Stacks 06WC on the small Zariski site of `Y`.**  Restricting a module on
the big site of `Y` to the small Zariski site of `Y`, and restricting it along `a` to the small
Zariski site of `X` and pushing forward along `a`, are compared by the restriction maps along the
arrows `a⁻¹(V) ≅ V ×_Y X ⟶ V`.  It is `AlgebraicGeometry.SmallEtale.bigRestrictComparison` read
on the small Zariski sites. -/
def bigRestrictAlongZariskiComparison (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    BigFppfOver.baseRestrictModule B Y.obj (bigContains B E h Y.property) τ ⟶
      bigRestrictAlong B E h a τ hτ ⋙
        (restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a)) :=
  (bigRestrictCompRestrictModuleIso B E h Y.obj Y.property τ hτ).hom ≫
    Functor.whiskerRight (bigRestrictComparison B E h a τ hτ) (restrictModule E Y.obj Y.property) ≫
    Functor.whiskerLeft (bigRestrictAlong B E h a τ hτ) (restrictModuleBaseChangeIso E a).hom

/-- **The canonical comparison `(a^*𝓕)^a_small ⟶ (𝓕^a_big)|_{X_ét, along a}`**, the mate of
`AlgebraicGeometry.SmallEtale.bigRestrictAlongZariskiComparison` with respect to the big
associated-module adjunction of `Y` and the composite of the pullback along `a` with the small
associated-module adjunction of `X`. -/
def bigRestrictAlongAssociatedModuleNatTrans (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) :
    Scheme.Modules.pullback (schemeHom E a) ⋙ associatedModule E X.obj X.property ⟶
      BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ ⋙
        bigRestrictAlong B E h a τ hτ :=
  (mateEquiv (BigFppfOver.baseAssociatedModuleAdjunction B Y.obj (bigContains B E h Y.property) τ)
    ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
      (associatedModuleAdjunction E X.obj X.property))).symm
      (TwoSquare.mk (BigFppfOver.baseRestrictModule B Y.obj (bigContains B E h Y.property) τ)
        (bigRestrictAlong B E h a τ hτ) (𝟭 Y.obj.Modules)
        (restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a))
        (bigRestrictAlongZariskiComparison B E h a τ hτ))

/-- The transpose of the canonical comparison along `a` is the unit of the big associated-module
adjunction of `Y` followed by the comparison on the small Zariski sites. -/
theorem unit_comp_bigRestrictAlongAssociatedModuleNatTrans (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) (𝓕 : Y.obj.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
        (associatedModuleAdjunction E X.obj X.property)).unit.app 𝓕 ≫
        (restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a)).map
          ((bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕) =
      (BigFppfOver.baseAssociatedModuleAdjunction B Y.obj (bigContains B E h Y.property) τ).unit.app
          𝓕 ≫
        (bigRestrictAlongZariskiComparison B E h a τ hτ).app _ :=
  (unit_mateEquiv_symm _ _ _ 𝓕).symm

/-- The arrow `a⁻¹(V) ≅ V ×_Y X ⟶ V` of the big site of `Y` along which the comparison on the
small Zariski sites restricts. -/
def zariskiArrow (V : Y.obj.Opens) :
    (bigRestrictAlongFunctor B E h a).obj
        ((opensToSmallEtale E X.obj X.property).obj (schemeHom E a ⁻¹ᵁ V)) ⟶
      (Stack.smallEtaleInclusion B E h Y.obj Y.property).obj
        ((opensToSmallEtale E Y.obj Y.property).obj V) :=
  (bigRestrictAlongFunctor B E h a).map ((baseChangeOpensIso E a).hom.app V) ≫
    (baseChangeProjection B E h a).app ((opensToSmallEtale E Y.obj Y.property).obj V)

/-- **The comparison on the small Zariski sites is restriction along `a⁻¹(V) ⟶ V`.** -/
theorem bigRestrictAlongZariskiComparison_app_app (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (G : SheafOfModules.{u}
      (FibredSite.baseRingStructureSheaf B Y.obj (bigContains B E h Y.property) τ))
    (V : Y.obj.Opens) (x : G.val.obj (op ((Stack.smallEtaleInclusion B E h Y.obj Y.property).obj
        ((opensToSmallEtale E Y.obj Y.property).obj V)))) :
    Scheme.Modules.Hom.app ((bigRestrictAlongZariskiComparison B E h a τ hτ).app G) V x =
      G.val.presheaf.map (zariskiArrow B E h a V).op x :=
  (congrArg (fun φ => φ x) (G.val.presheaf.map_comp
    ((baseChangeProjection B E h a).app ((opensToSmallEtale E Y.obj Y.property).obj V)).op
    ((bigRestrictAlongFunctor B E h a).map ((baseChangeOpensIso E a).hom.app V)).op)).symm

omit h in
/-- An isomorphism of modules on a scheme is a bijection on sections. -/
theorem modules_iso_hom_app_inv_app_apply {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (U : Z.Opens) (x : Γ(N, U)) : e.hom.app U (e.inv.app U x) = x := by
  change (e.inv.app U ≫ e.hom.app U) x = x
  rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]
  rfl

section Sections

variable (τ : SiteKind) (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
  (𝓕 : Y.obj.Modules) [𝓕.IsQuasicoherent]

/-- The pullback along `a` of a quasi-coherent module is quasi-coherent (Stacks 01BG). -/
instance isQuasicoherent_pullback_schemeHom (𝓖 : Y.obj.Modules) [h𝓖 : 𝓖.IsQuasicoherent] :
    ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓖).IsQuasicoherent :=
  @SheafOfModules.modulePullback_isQuasicoherent _ _ (schemeHom E a).toLRSHom.toShHom 𝓖 h𝓖

omit [𝓕.IsQuasicoherent] in
/-- The structure morphism of `W' ⟶ X ⟶ Y`, read on the big site of `Y`, is the composite. -/
theorem bigRestrictAlongFunctor_obj_hom (W : SmallEtale E X.obj X.property) :
    ((Over.post (X := B.obj (bigContains B E h Y.property)) B.inclusion).obj
        ((bigRestrictAlongFunctor B E h a).obj W)).hom =
      ((toOver E X.obj X.property).obj W).hom ≫ schemeHom E a :=
  rfl

omit [𝓕.IsQuasicoherent] in
/-- The object `W' ⟶ X ⟶ Y` of the big site of `Y`, read over `Y`, is the base change of `W'`. -/
theorem bigRestrictAlongFunctor_obj_eq (W : SmallEtale E X.obj X.property) :
    (Over.post (X := B.obj (bigContains B E h Y.property)) B.inclusion).obj
        ((bigRestrictAlongFunctor B E h a).obj W) =
      (Over.map (schemeHom E a)).obj ((toOver E X.obj X.property).obj W) :=
  rfl

/-- The comparison of sections of `AlgebraicGeometry.SmallEtale.bigRestrictAlongSectionsHom`, on
the underlying abelian presheaves. -/
def bigRestrictAlongSectionsPresheafHom :
    (bigRestrictAlongFunctor B E h a ⋙
        Over.post (X := B.obj (bigContains B E h Y.property)) B.inclusion).op ⋙
        quasiCoherentPresheafFunctor Y.obj 𝓕 ⟶
      (toOver E X.obj X.property).op ⋙
        quasiCoherentPresheafFunctor X.obj ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕) where
  app W := ((Scheme.Modules.pullbackComp ((toOver E X.obj X.property).obj W.unop).hom
      (schemeHom E a)).inv.app 𝓕).app ⊤
  naturality _ _ f :=
    Stacks.Sites.pullbackSectionsMap_baseChange 𝓕 (Over.mk (schemeHom E a))
      ((toOver E X.obj X.property).map f.unop)

/-- The comparison of sections along `a` is invertible on presheaves. -/
instance isIso_bigRestrictAlongSectionsPresheafHom :
    IsIso (bigRestrictAlongSectionsPresheafHom B E h a 𝓕) := by
  have : ∀ W, IsIso ((bigRestrictAlongSectionsPresheafHom B E h a 𝓕).app W) := fun W =>
    (Stacks.Sites.sectionsTopIso ((Scheme.Modules.pullbackComp
      ((toOver E X.obj X.property).obj W.unop).hom (schemeHom E a)).app 𝓕).symm).isIso_hom
  exact NatIso.isIso_of_isIso_app _

/-- **The sections of `𝓕^a_big` along `a` are the sections of `(a^*𝓕)^a_small`**: over
`W' ∈ X_ét` both are global sections of a pullback of `𝓕` to `W'`, along `W' ⟶ X ⟶ Y` and along
`W' ⟶ X` after `a`, compared by the composition isomorphism of pullbacks. -/
def bigRestrictAlongSectionsIso :
    (bigRestrictAlong B E h a τ hτ).obj
        (BigFppfOver.sectionsSheafOfModules B Y.obj (bigContains B E h Y.property) τ 𝓕) ≅
      sectionsSheafOfModules' E X.obj X.property ((Scheme.Modules.pullback
        (schemeHom E a)).obj 𝓕) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun W => LinearEquiv.toModuleIso
        (R := (SmallEtale.structureSheaf E X.obj X.property).obj.obj W)
        (m₁ := ModuleCat.isModule _) (m₂ := ModuleCat.isModule _)
        (X₁ := ((bigRestrictAlong B E h a τ hτ).obj
          (BigFppfOver.sectionsSheafOfModules B Y.obj
            (bigContains B E h Y.property) τ 𝓕)).val.obj W)
        (X₂ := (sectionsSheafOfModules' E X.obj X.property
          ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕)).val.obj W)
        { toFun := fun x => ((Scheme.Modules.pullbackComp
          ((toOver E X.obj X.property).obj W.unop).hom
              (schemeHom E a)).inv.app 𝓕).app ⊤ x
          invFun := fun x => ((Scheme.Modules.pullbackComp
            ((toOver E X.obj X.property).obj W.unop).hom
              (schemeHom E a)).hom.app 𝓕).app ⊤ x
          map_add' := fun x y => map_add _ x y
          map_smul' := fun r x => Scheme.Modules.Hom.app_smul _ r x
          left_inv := fun x => modules_iso_hom_app_inv_app_apply
            ((Scheme.Modules.pullbackComp ((toOver E X.obj X.property).obj W.unop).hom
              (schemeHom E a)).app 𝓕) ⊤ x
          right_inv := fun x => modules_iso_hom_app_inv_app_apply
            ((Scheme.Modules.pullbackComp ((toOver E X.obj X.property).obj W.unop).hom
              (schemeHom E a)).app 𝓕).symm ⊤ x })
      (fun _ _ f => ModuleCat.hom_ext (LinearMap.ext fun x =>
        congrArg (fun φ => φ.hom x)
          ((bigRestrictAlongSectionsPresheafHom B E h a 𝓕).naturality f))))

omit h [𝓕.IsQuasicoherent] in
/-- **The sections identity behind (1').**  Pulling a section `s` of `𝓕` over `V` back to the open
subscheme `V`, then along `a⁻¹(V) ⟶ V`, and reading it through the composition isomorphism of
pullbacks, is pulling `s` back along `a` and then to the open subscheme `a⁻¹(V)`. -/
theorem zariskiSections_eq (V : Y.obj.Opens) (s : 𝓕.val.obj (op V)) :
    ((Scheme.Modules.pullbackComp (schemeHom E a ⁻¹ᵁ V).ι (schemeHom E a)).inv.app 𝓕).app ⊤
        (pullbackSectionHom ((schemeHom E a ⁻¹ᵁ V).ι ≫ schemeHom E a) 𝓕 V ⊤
          (by simp) s) =
      pullbackSectionHom (schemeHom E a ⁻¹ᵁ V).ι
        ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕) (schemeHom E a ⁻¹ᵁ V) ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl)
        (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).app V s) := by
  have hc := Scheme.Modules.pullbackSection_comp (schemeHom E a ⁻¹ᵁ V).ι (schemeHom E a) 𝓕 V
    (schemeHom E a ⁻¹ᵁ V) ⊤ le_rfl (Scheme.Opens.top_le_ι_preimage le_rfl) (by simp) s
  have hu : Scheme.Modules.pullbackSection (schemeHom E a) 𝓕 V (schemeHom E a ⁻¹ᵁ V) le_rfl s =
      ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).app V s := by
    unfold Scheme.Modules.pullbackSection
    have e : (homOfLE (le_refl (schemeHom E a ⁻¹ᵁ V))).op = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (fun f => ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕).val.map f
      (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).val.app
        (op V) s)) e).trans (congrArg (fun f => f
      (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).val.app
        (op V) s)) (((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕).val.map_id _))
  rw [← hu, pullbackSectionHom_apply, pullbackSectionHom_apply, ← hc]
  exact modules_iso_hom_app_inv_app_apply
    ((Scheme.Modules.pullbackComp (schemeHom E a ⁻¹ᵁ V).ι (schemeHom E a)).app 𝓕).symm ⊤ _

omit [𝓕.IsQuasicoherent] in
/-- The structure morphism of an open of `Y`, read on the big site of `Y`, is its inclusion. -/
theorem smallEtaleInclusion_opens_hom (V : Y.obj.Opens) :
    ((Over.post (X := B.obj (bigContains B E h Y.property)) B.inclusion).obj
      ((Stack.smallEtaleInclusion B E h Y.obj Y.property).obj
        ((opensToSmallEtale E Y.obj Y.property).obj V))).hom = V.ι := rfl

omit [𝓕.IsQuasicoherent] in
/-- The structure morphism of `a⁻¹(V)`, read on the big site of `Y` along `a`. -/
theorem bigRestrictAlong_opens_hom (V : Y.obj.Opens) :
    ((Over.post (X := B.obj (bigContains B E h Y.property)) B.inclusion).obj
      ((bigRestrictAlongFunctor B E h a).obj
        ((opensToSmallEtale E X.obj X.property).obj (schemeHom E a ⁻¹ᵁ V)))).hom =
      (schemeHom E a ⁻¹ᵁ V).ι ≫ schemeHom E a := rfl

/-- The comparison of sections along `a`, on an element over `a⁻¹(V)`. -/
theorem bigRestrictAlongSectionsIso_hom_apply (V : Y.obj.Opens)
    (x : Γ((Scheme.Modules.pullback ((schemeHom E a ⁻¹ᵁ V).ι ≫ schemeHom E a)).obj 𝓕, ⊤)) :
    (ModuleCat.Hom.hom ((bigRestrictAlongSectionsIso B E h a τ hτ 𝓕).hom.val.app
      (op ((opensToSmallEtale E X.obj X.property).obj (schemeHom E a ⁻¹ᵁ V))))) x =
      ((Scheme.Modules.pullbackComp (schemeHom E a ⁻¹ᵁ V).ι (schemeHom E a)).inv.app 𝓕).app ⊤ x :=
  rfl

omit h [𝓕.IsQuasicoherent] in
/-- Restriction to the small Zariski site of `X` followed by pushforward along `a`, on sections. -/
theorem restrictModule_pushforward_map_apply (V : Y.obj.Opens) {M N : SheafOfModules.{u}
  (structureSheaf E X.obj X.property)}
    (φ : M ⟶ N) (y : M.val.obj (op ((opensToSmallEtale E X.obj X.property).obj
      (schemeHom E a ⁻¹ᵁ V)))) :
    (ModuleCat.Hom.hom (((restrictModule E X.obj X.property ⋙
      Scheme.Modules.pushforward (schemeHom E a)).map φ).val.app (op V))) y =
      (ModuleCat.Hom.hom (φ.val.app (op ((opensToSmallEtale E X.obj X.property).obj
        (schemeHom E a ⁻¹ᵁ V))))) y :=
  rfl

omit h [𝓕.IsQuasicoherent] in
/-- The unit of `𝓕 ↦ a_*(a^*𝓕)^a`, on sections, is the unit of `a^* ⊣ a_*` followed by the unit
of the small associated-module adjunction of `X`. -/
theorem compUnit_restrict_apply (V : Y.obj.Opens) (s : 𝓕.val.obj (op V))
    {N : SheafOfModules.{u} (structureSheaf E X.obj X.property)}
    (f : (associatedModule E X.obj X.property).obj
      ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕) ⟶ N) :
    (ModuleCat.Hom.hom ((((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
        (associatedModuleAdjunction E X.obj X.property)).unit.app 𝓕 ≫
      (restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a)).map f
        ).val.app (op V))) s =
      (ModuleCat.Hom.hom (((associatedModuleAdjunction E X.obj X.property).unit.app
        ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕) ≫
          (restrictModule E X.obj X.property).map f).val.app (op (schemeHom E a ⁻¹ᵁ V))))
        (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).app V s) :=
  rfl

omit [𝓕.IsQuasicoherent] in
/-- The restriction map of the sheaf of pullback sections along `a⁻¹(V) ⟶ V`, on a section
pulled back to `V`. -/
theorem pullbackSectionsMap_zariskiArrow (V : Y.obj.Opens) (s : 𝓕.val.obj (op V)) :
    pullbackSectionsMap 𝓕 ((Over.post (X := B.obj (bigContains B E h Y.property))
        B.inclusion).map (zariskiArrow B E h a V))
        (pullbackSectionHom V.ι 𝓕 V ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) s) =
      pullbackSectionHom ((schemeHom E a ⁻¹ᵁ V).ι ≫ schemeHom E a) 𝓕 V ⊤ (by simp) s :=
  pullbackSectionsMap_pullbackSectionHom 𝓕 _ V _ _ s

/-- The comparison of sections along `a`, on a section of `𝓕` restricted along `a⁻¹(V) ⟶ V`. -/
theorem sectionsIso_apply_zariski (V : Y.obj.Opens) (s : 𝓕.val.obj (op V)) :
    (ModuleCat.Hom.hom ((bigRestrictAlongSectionsIso B E h a τ hτ 𝓕).hom.val.app
      (op ((opensToSmallEtale E X.obj X.property).obj (schemeHom E a ⁻¹ᵁ V)))))
      ((BigFppfOver.sectionsSheafOfModules B Y.obj (bigContains B E h Y.property) τ
        𝓕).val.presheaf.map (zariskiArrow B E h a V).op
        (pullbackSectionHom V.ι 𝓕 V ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) s)) =
      pullbackSectionHom (schemeHom E a ⁻¹ᵁ V).ι
        ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕) (schemeHom E a ⁻¹ᵁ V) ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl)
        (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).app V s) := by
  refine (bigRestrictAlongSectionsIso_hom_apply B E h a τ hτ 𝓕 V _).trans ?_
  refine (congrArg (fun y => ((Scheme.Modules.pullbackComp (schemeHom E a ⁻¹ᵁ V).ι
    (schemeHom E a)).inv.app 𝓕).app ⊤ y) (pullbackSectionsMap_zariskiArrow B E h a 𝓕 V s)).trans ?_
  exact zariskiSections_eq E a 𝓕 V s

omit h in
/-- The transpose of the identification of `(a^*𝓕)^a_small` with its sheaf of pullback sections,
on a section of `𝓕`. -/
theorem compUnit_sectionsIso_apply (V : Y.obj.Opens) (s : 𝓕.val.obj (op V)) :
    (ModuleCat.Hom.hom ((((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
        (associatedModuleAdjunction E X.obj X.property)).unit.app 𝓕 ≫
      (restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a)).map
        (associatedModuleIsoSectionsSheafOfModules' E X.obj X.property
          ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕)).hom).val.app (op V))) s =
      pullbackSectionHom (schemeHom E a ⁻¹ᵁ V).ι
        ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕) (schemeHom E a ⁻¹ᵁ V) ⊤
          (Scheme.Opens.top_le_ι_preimage le_rfl)
        (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).app V s) :=
  (compUnit_restrict_apply E a 𝓕 V s _).trans (congrArg (fun φ => (φ.app (op
    (schemeHom E a ⁻¹ᵁ V))).hom
    (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).unit.app 𝓕).app V s))
    (SmallEtale.val_unit_comp_restrictModule_map_associatedModuleIsoSections E X.obj
      X.property ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕)))

/-- **On a quasi-coherent module the canonical comparison along `a` is the identification through
pullback sections.** -/
theorem bigRestrictAlongAssociatedModuleNatTrans_app_comp :
    (bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕 ≫
        (bigRestrictAlong B E h a τ hτ).map
          (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B Y.obj (bigContains B E h Y.property)
            τ 𝓕).hom ≫
        (bigRestrictAlongSectionsIso B E h a τ hτ 𝓕).hom =
      (associatedModuleIsoSectionsSheafOfModules' E X.obj X.property
        ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕)).hom := by
  let adj := (Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
    (associatedModuleAdjunction E X.obj X.property)
  let R₂ := restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a)
  let κ := bigRestrictAlongZariskiComparison B E h a τ hτ
  let i := (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B Y.obj (bigContains B E h Y.property)
    τ 𝓕).hom
  let m := (bigRestrictAlongSectionsIso B E h a τ hτ 𝓕).hom
  apply (adj.homEquiv _ _).injective
  refine (adj.homEquiv_naturality_right _ _).trans ?_
  have hΨ : adj.homEquiv _ _ ((bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕) =
      (BigFppfOver.baseAssociatedModuleAdjunction B Y.obj (bigContains B E h Y.property)
        τ).unit.app 𝓕 ≫ κ.app _ :=
    (Adjunction.homEquiv_unit adj 𝓕 _ _).trans
      (unit_comp_bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ 𝓕)
  refine (congrArg (fun k => k ≫ R₂.map ((bigRestrictAlong B E h a τ hτ).map i ≫ m)) hΨ).trans ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_unit adj 𝓕 _
    (associatedModuleIsoSectionsSheafOfModules' E X.obj X.property
      ((Scheme.Modules.pullback (schemeHom E a)).obj 𝓕)).hom).symm
  have hκ : κ.app _ ≫ R₂.map ((bigRestrictAlong B E h a τ hτ).map i) =
      (BigFppfOver.baseRestrictModule B Y.obj _ τ).map i ≫ κ.app _ := (κ.naturality i).symm
  have hL : ((BigFppfOver.baseAssociatedModuleAdjunction B Y.obj (bigContains B E h Y.property)
        τ).unit.app 𝓕 ≫ κ.app _) ≫ R₂.map ((bigRestrictAlong B E h a τ hτ).map i ≫ m) =
      ((BigFppfOver.baseAssociatedModuleAdjunction B Y.obj (bigContains B E h Y.property)
        τ).unit.app 𝓕 ≫ (BigFppfOver.baseRestrictModule B Y.obj _ τ).map i) ≫
        κ.app _ ≫ R₂.map m := by
    rw [Functor.map_comp, Category.assoc, Category.assoc, ← Category.assoc (κ.app _), hκ]
    simp only [Category.assoc]
  refine hL.trans ?_
  have h1 := BigFppfOver.val_unit_comp_baseRestrictModule_map_baseAssociatedModuleIsoSectionsSheaf
    B Y.obj (bigContains B E h Y.property) τ 𝓕
  refine SheafOfModules.hom_ext (PresheafOfModules.Hom.ext (funext fun V => ?_))
  obtain ⟨V⟩ := V
  change Y.obj.Opens at V
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  have e1 := congrArg (fun φ => (φ.app (op V)).hom s) h1
  have e3 := bigRestrictAlongZariskiComparison_app_app B E h a τ hτ
    (BigFppfOver.sectionsSheafOfModules B Y.obj (bigContains B E h Y.property) τ 𝓕) V
    (pullbackSectionHom V.ι 𝓕 V ⊤ (Scheme.Opens.top_le_ι_preimage le_rfl) s)
  refine (congrArg (fun y => (ModuleCat.Hom.hom ((R₂.map m).val.app (op V)))
    ((ModuleCat.Hom.hom ((κ.app _).val.app (op V))) y)) e1).trans ?_
  refine (congrArg (fun y => (ModuleCat.Hom.hom ((R₂.map m).val.app (op V))) y) e3).trans ?_
  refine (restrictModule_pushforward_map_apply E a V m _).trans ?_
  exact (sectionsIso_apply_zariski B E h a τ hτ 𝓕 V s).trans
    (compUnit_sectionsIso_apply E a 𝓕 V s).symm

/-- **The canonical comparison along `a` is an isomorphism at a quasi-coherent module.** -/
instance isIso_bigRestrictAlongAssociatedModuleNatTrans_app :
    IsIso ((bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕) := by
  have h1 := bigRestrictAlongAssociatedModuleNatTrans_app_comp B E h a τ hτ 𝓕
  have : IsIso ((bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕 ≫
      (bigRestrictAlong B E h a τ hτ).map
        (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B Y.obj (bigContains B E h Y.property)
          τ 𝓕).hom ≫
      (bigRestrictAlongSectionsIso B E h a τ hτ 𝓕).hom) := by
    rw [h1]; infer_instance
  exact IsIso.of_isIso_comp_right _
    ((bigRestrictAlong B E h a τ hτ).map
        (BigFppfOver.baseAssociatedModuleIsoSectionsSheaf B Y.obj (bigContains B E h Y.property)
          τ 𝓕).hom ≫
      (bigRestrictAlongSectionsIso B E h a τ hτ 𝓕).hom)

/-- **(1') The big associated module restricted along a morphism.**  For `a : X ⟶ Y` and a
quasi-coherent `𝒪_Y`-module `𝓕`, the restriction of `𝓕^a` on the big `τ`-site of `Y` to the
small étale site of `X` along `a` is the small étale associated module of `a^*𝓕`.  The
isomorphism is the inverse of the canonical comparison
`AlgebraicGeometry.SmallEtale.bigRestrictAlongAssociatedModuleNatTrans`. -/
def bigRestrictAlongAssociatedModuleIso :
    (bigRestrictAlong B E h a τ hτ).obj
        ((BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ).obj 𝓕) ≅
      (SmallEtale.associatedModule E X.obj X.property).obj
        ((Scheme.Modules.pullback (SmallEtale.schemeHom E a)).obj 𝓕) :=
  (asIso ((bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕)).symm

end Sections

/-- **(2') The identification along `a` is natural in the quasi-coherent module.** -/
theorem bigRestrictAlongAssociatedModuleIso_hom_naturality (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) {𝓕 𝓖 : Y.obj.Modules}
    [𝓕.IsQuasicoherent] [𝓖.IsQuasicoherent] (α : 𝓕 ⟶ 𝓖) :
    (bigRestrictAlong B E h a τ hτ).map
          ((BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ).map α) ≫
        (bigRestrictAlongAssociatedModuleIso B E h a τ hτ 𝓖).hom =
      (bigRestrictAlongAssociatedModuleIso B E h a τ hτ 𝓕).hom ≫
        (SmallEtale.associatedModule E X.obj X.property).map
          ((Scheme.Modules.pullback (SmallEtale.schemeHom E a)).map α) := by
  rw [bigRestrictAlongAssociatedModuleIso, bigRestrictAlongAssociatedModuleIso, Iso.symm_hom,
    Iso.symm_hom, asIso_inv, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq]
  exact ((bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).naturality α).symm


omit h in
/-- **The transposed base-change identification, read on the small Zariski site of `Y`.**  The
unit of `𝓕 ↦ ε_{a,*}ε_a^*(𝓕^a)` followed by the base-change identification of Stacks 03LC (1) is,
after restriction to the small Zariski site of `Y`, the unit of `𝓕 ↦ a_*(a^*𝓕)^a` followed by the
comparison of the two composite restrictions. -/
theorem unit_comp_restrictModule_map_associatedModuleObjBaseChangeIso_inv (𝓕 : Y.obj.Modules) :
    (associatedModuleAdjunction E Y.obj Y.property).unit.app 𝓕 ≫
        (restrictModule E Y.obj Y.property).map
          ((SheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureMapRing E a)).unit.app _ ≫
          (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing E a)).map
            (associatedModuleObjBaseChangeIso E a 𝓕).inv) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
          (associatedModuleAdjunction E X.obj X.property)).unit.app 𝓕 ≫
        (restrictModuleBaseChangeIso E a).inv.app _ := by
  have hc := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
      (associatedModuleAdjunction E X.obj X.property))
    ((associatedModuleAdjunction E Y.obj Y.property).comp
      (SheafOfModules.pullbackPushforwardAdjunction.{u} (smallEtaleStructureMapRing E a)))
    (associatedModuleBaseChangeIso E a).inv 𝓕
  rw [conjugateEquiv_associatedModuleBaseChangeIso_inv] at hc
  rw [hc, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc]
  rfl

/-- **(3), transposed.**  The canonical comparison at `Y` followed by the comparison of Stacks 06WC
on the big site is the unit of `ε_a` followed by the base-change identification and the canonical
comparison along `a`. -/
theorem bigRestrictAssociatedModuleNatTrans_app_comp_bigRestrictComparison (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ) (𝓕 : Y.obj.Modules) :
    (bigRestrictAssociatedModuleNatTrans B E h Y.obj Y.property τ hτ).app 𝓕 ≫
        (bigRestrictComparison B E h a τ hτ).app
          ((BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ).obj 𝓕) =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureMapRing E a)).unit.app _ ≫
        (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing E a)).map
          ((associatedModuleObjBaseChangeIso E a 𝓕).inv ≫
            (bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕) := by
  let A := (BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ).obj 𝓕
  let Ψ := (bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ).app 𝓕
  let κ := bigRestrictAlongZariskiComparison B E h a τ hτ
  have hκ : (bigRestrictCompRestrictModuleIso B E h Y.obj Y.property τ hτ).hom.app A ≫
      (restrictModule E Y.obj Y.property).map ((bigRestrictComparison B E h a τ hτ).app A) =
      κ.app A ≫ (restrictModuleBaseChangeIso E a).inv.app _ := by
    change _ = ((bigRestrictCompRestrictModuleIso B E h Y.obj Y.property τ hτ).hom.app A ≫
      (restrictModule E Y.obj Y.property).map ((bigRestrictComparison B E h a τ hτ).app A) ≫
      (restrictModuleBaseChangeIso E a).hom.app _) ≫ (restrictModuleBaseChangeIso E a).inv.app _
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact congrArg (fun k => _ ≫ k) (Category.comp_id _).symm
  apply ((associatedModuleAdjunction E Y.obj Y.property).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  calc (associatedModuleAdjunction E Y.obj Y.property).unit.app 𝓕 ≫
        (restrictModule E Y.obj Y.property).map
          ((bigRestrictAssociatedModuleNatTrans B E h Y.obj Y.property τ hτ).app 𝓕 ≫
            (bigRestrictComparison B E h a τ hτ).app A)
      = ((associatedModuleAdjunction E Y.obj Y.property).unit.app 𝓕 ≫
          (restrictModule E Y.obj Y.property).map
            ((bigRestrictAssociatedModuleNatTrans B E h Y.obj Y.property τ hτ).app 𝓕)) ≫
          (restrictModule E Y.obj Y.property).map ((bigRestrictComparison B E h a τ hτ).app A) := by
        rw [Functor.map_comp, Category.assoc]
    _ = (BigFppfOver.baseAssociatedModuleAdjunction B Y.obj (bigContains B E h Y.property)
          τ).unit.app 𝓕 ≫ κ.app A ≫ (restrictModuleBaseChangeIso E a).inv.app _ := by
        rw [unit_comp_bigRestrictAssociatedModuleNatTrans, Category.assoc, hκ]
    _ = (((Scheme.Modules.pullbackPushforwardAdjunction (schemeHom E a)).comp
          (associatedModuleAdjunction E X.obj X.property)).unit.app 𝓕 ≫
          (restrictModule E X.obj X.property ⋙ Scheme.Modules.pushforward (schemeHom E a)).map Ψ) ≫
          (restrictModuleBaseChangeIso E a).inv.app _ := by
        rw [unit_comp_bigRestrictAlongAssociatedModuleNatTrans B E h a τ hτ 𝓕, Category.assoc]
        rfl
    _ = (associatedModuleAdjunction E Y.obj Y.property).unit.app 𝓕 ≫
          (restrictModule E Y.obj Y.property).map
            ((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureMapRing E a)).unit.app _ ≫
            (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing E a)).map
              (associatedModuleObjBaseChangeIso E a 𝓕).inv) ≫
          (restrictModule E Y.obj Y.property).map
            ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing E a)).map Ψ) := by
        rw [Category.assoc, (restrictModuleBaseChangeIso E a).inv.naturality Ψ, ← Category.assoc,
          ← unit_comp_restrictModule_map_associatedModuleObjBaseChangeIso_inv E a 𝓕,
          Category.assoc]
        rfl
    _ = _ := by
        rw [← Functor.map_comp, Category.assoc, ← Functor.map_comp]

/-- **(3) Compatibility with base change along a morphism.**  For `a : X ⟶ Y` and a
quasi-coherent `𝒪_Y`-module `𝓕`, the comparison of Stacks 06WC for `𝓕^a` on the big site of `Y`
(restriction along the base-change projections `W ×_Y X ⟶ W`) is, under the identifications (1) at
`Y` and (1') along `a`, the transpose of the base-change identification
`(a^*𝓕)^a ≅ ε_a^*(𝓕^a)` of Stacks 03LC (1). -/
theorem bigRestrictComparison_app_associatedModule (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : Y.obj.Modules) [𝓕.IsQuasicoherent] :
    (bigRestrictComparison B E h a τ hτ).app
          ((BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ).obj 𝓕) ≫
        (SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E a)).map
          (bigRestrictAlongAssociatedModuleIso B E h a τ hτ 𝓕).hom =
      (bigRestrictAssociatedModuleIso B E h Y.obj Y.property τ hτ 𝓕).hom ≫
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (SmallEtale.smallEtaleStructureMapRing E a)).unit.app _ ≫
        (SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E a)).map
          (SmallEtale.associatedModuleObjBaseChangeIso E a 𝓕).inv := by
  rw [bigRestrictAssociatedModuleIso, bigRestrictAlongAssociatedModuleIso, Iso.symm_hom,
    Iso.symm_hom, asIso_inv, asIso_inv, IsIso.eq_inv_comp, Functor.map_inv,
    ← Category.assoc, IsIso.comp_inv_eq,
    bigRestrictAssociatedModuleNatTrans_app_comp_bigRestrictComparison B E h a τ hτ 𝓕,
    Functor.map_comp, Category.assoc]

/-- **The flat base change property holds for an associated module, on the big site of a
scheme.**  The comparison `ε_a^*(𝓕^a|_{Y_ét}) ⟶ 𝓕^a|_{X_ét, along a}` of Stacks 06WC, the
transpose of `AlgebraicGeometry.SmallEtale.bigRestrictComparison`, is an isomorphism for every
quasi-coherent `𝓕` and every morphism `a`: by (3) it is the composite of (1), the base-change
identification of Stacks 03LC (1) and (1'). -/
theorem isIso_homEquiv_symm_bigRestrictComparison_app (τ : SiteKind)
    (hτ : B.baseTopology .etale ≤ B.baseTopology τ)
    (𝓕 : Y.obj.Modules) [𝓕.IsQuasicoherent] :
    IsIso (((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E a)).homEquiv _ _).symm
        ((bigRestrictComparison B E h a τ hτ).app
          ((BigFppfOver.baseAssociatedModule B Y.obj
            (bigContains B E h Y.property) τ).obj 𝓕))) := by
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{u}
    (SmallEtale.smallEtaleStructureMapRing E a)
  let ρ := (bigRestrictComparison B E h a τ hτ).app
    ((BigFppfOver.baseAssociatedModule B Y.obj (bigContains B E h Y.property) τ).obj 𝓕)
  let ε := SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E a)
  let Φ := bigRestrictAlongAssociatedModuleIso B E h a τ hτ 𝓕
  have e : ρ = (bigRestrictAssociatedModuleIso B E h Y.obj Y.property τ hτ 𝓕).hom ≫
      adj.unit.app _ ≫ ε.map ((SmallEtale.associatedModuleObjBaseChangeIso E a 𝓕).inv ≫ Φ.inv) :=
    calc ρ = (ρ ≫ ε.map Φ.hom) ≫ ε.map Φ.inv := by
          rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
          exact (Category.comp_id ρ).symm
      _ = _ := by
          rw [bigRestrictComparison_app_associatedModule B E h a τ hτ 𝓕, Functor.map_comp]
          simp only [Category.assoc]
          rfl
  have e2 : adj.homEquiv _ _ ((SmallEtale.associatedModuleObjBaseChangeIso E a 𝓕).inv ≫ Φ.inv) =
      adj.unit.app _ ≫ ε.map ((SmallEtale.associatedModuleObjBaseChangeIso E a 𝓕).inv ≫ Φ.inv) :=
    Adjunction.homEquiv_unit _ _ _ _
  change IsIso ((adj.homEquiv _ _).symm ρ)
  rw [e, ← e2, Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  infer_instance

end AlgebraicGeometry.SmallEtale
