module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologyPullbackComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TruncGESingleHomology
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.QuasicoherentSupportedComplexes
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomologyCompare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ExactFunctorSingleHomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity
public import StacksFrontier.Algebra.Homology.DerivedCategory.HomEqualDegree
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryTopDegreeMate
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PushforwardComparisonAgreesWithOrdinary

/-!
# The Gysin edge morphism is compatible with pullback

Let `g : X' ⟶ X` be a morphism of ringed spaces, `Z ⊆ X`, `Z' ⊆ X'` closed, and `ℱ`, `ℱ'` modules
whose local cohomology sheaves vanish below degree `c`.  The Gysin edge morphism
`supportedGysinEdge : i_*ℋ^c_Z(ℱ)[-c] ⟶ ℱ` of [Stacks, Tag 0G8A] is compatible with the derived
`g`-maps of [Stacks, Tag 01F8], once the arrow `i_*ℋ^c_Z(ℱ) ⟶ g_*i'_*ℋ^c_{Z'}(ℱ')` is the one the
map `θ : Lg^*(i_*Rℋ_Z ℱ) ⟶ i'_*Rℋ_{Z'} ℱ'` of [Stacks, Tag 0G78] induces in degree `c`, and `θ`
satisfies the triangle of that remark.  This is the content Cohomology, Remark [Stacks, Tag 0G78]
and Lemma [Stacks, Tag 0G79] contribute to [Stacks, Tag 0G8D]: that lemma's proof is "combine
0G89 and 0G79".

## Main results

* `homologyFunctor_map_singleHomologyToOfIsGE`, `eq_singleFunctor_map_comp_singleHomologyToOfIsGE`:
  the edge map `H^c(K)[-c] ⟶ K` induces the canonical identification on `H^c`, and every map out
  of a single object in degree `c` into `D^{≥c}` factors through it.
* `derivedPullback_map_singleHomologyToOfIsGE_comp`: the edge map commutes with derived pullback
  and any `θ`, through the top-degree comparison `H^c(Lg^*A) ≅ g^*H^c(A)` of `D^{≤c}` objects.
* `derivedPushforwardMap_canonical_eq`: the derived `g`-map of [Stacks, Tag 01F8] built from the
  canonical comparison is the transpose, along `Lg^* ⊣ Rg_*`, of the derived-to-ordinary
  comparison followed by the adjoint `g^*`-map.
* `supportedGysinEdgeFrontHomology_eq`: the identification `i_*ℋ^c_Z ≅ H^c(i_*Rℋ_Z)` that the front
  of the edge induces is the exactness comparison of the direct image from a closed subset.
* `supportedGysinEdge_derivedPushforwardMap`: **the edge compatibility.**

## References

* [Stacks Project, Tag 0G8D](https://stacks.math.columbia.edu/tag/0G8D)
* [Stacks Project, Tag 0G79](https://stacks.math.columbia.edu/tag/0G79)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G8A](https://stacks.math.columbia.edu/tag/0G8A)
* [Stacks Project, Tag 01F8](https://stacks.math.columbia.edu/tag/01F8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.CohomologicalGysin

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

open _root_.DerivedCategory

section Generic

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- `H^c` of the edge map `H^c(K)[-c] ⟶ K` is the canonical identification. -/
theorem homologyFunctor_map_singleHomologyToOfIsGE (K : DerivedCategory C) (c : ℤ)
    (hK : TStructure.t.IsGE K c) :
    (homologyFunctor C c).map (singleHomologyToOfIsGE K c hK) =
      (singleFunctorCompHomologyFunctorIso C c).hom.app ((homologyFunctor C c).obj K) := by
  have : IsIso ((TStructure.t.truncGEπ c).app K) :=
    (TStructure.t.isGE_iff_isIso_truncGEπ_app c K).1 hK
  have h1 := Stacks.TruncGESingleHomology.homologyMap_truncGELTIso_hom_app c K
  have h2 := Stacks.TruncGESingleHomology.truncGELTCompHomologyFunctorIso_hom_app c K
  have h3 := Stacks.TruncGESingleHomology.truncGECompHomologyFunctorIso_hom_app c c le_rfl
    ((TStructure.t.truncLT (c + 1)).obj K)
  have hnat := (TStructure.t.truncGEπ c).naturality ((TStructure.t.truncLTι (c + 1)).app K)
  simp only [Functor.id_map, Functor.id_obj] at hnat
  have key : (truncGELTCompHomologyFunctorIso c).hom.app K ≫
      (homologyFunctor C c).map ((TStructure.t.truncGEπ c).app K) =
      (homologyFunctor C c).map
        ((TStructure.t.truncGE c).map ((TStructure.t.truncLTι (c + 1)).app K)) := by
    rw [h2, Category.assoc, ← Functor.map_comp, hnat, Functor.map_comp, ← h3,
      Iso.inv_hom_id_app_assoc]
  have hinv : (homologyFunctor C c).map
      ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K) =
      (singleFunctorCompHomologyFunctorIso C c).hom.app ((homologyFunctor C c).obj K) ≫
        (truncGELTCompHomologyFunctorIso c).inv.app K := by
    have hb : (singleFunctorCompHomologyFunctorIso C c).hom.app ((homologyFunctor C c).obj K) =
        (homologyFunctor C c).map ((truncGELTIsoHomologyFunctorCompSingleFunctor c).inv.app K) ≫
          (truncGELTCompHomologyFunctorIso c).hom.app K := by
      rw [← h1, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rw [hb, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [← cancel_mono ((homologyFunctor C c).map ((TStructure.t.truncGEπ c).app K))]
  simp only [singleHomologyToOfIsGE, Functor.map_comp, Category.assoc, Functor.map_inv,
    IsIso.inv_hom_id, Category.comp_id]
  rw [hinv, Category.assoc, ← key, Iso.inv_hom_id_app_assoc]

/-- The edge map followed by the canonical projection `K ⟶ H^c(K)[-c]` is the identity, for `K`
concentrated in degree `c`. -/
theorem singleHomologyToOfIsGE_comp_truncGEIsoSingleHomology (K : DerivedCategory C) (c : ℤ)
    (hGE : TStructure.t.IsGE K c) (hLE : TStructure.t.IsLE K c) :
    singleHomologyToOfIsGE K c hGE ≫ (TStructure.t.truncGEπ c).app K ≫
        (Stacks.AlgebraicGeometry.TopDegreeBaseChange.truncGEIsoSingleHomology K c hLE).hom =
      𝟙 _ := by
  have hι : IsIso ((TStructure.t.truncLTι (c + 1)).app K) :=
    (TStructure.t.isLE_iff_isIso_truncLTι_app c (c + 1) rfl K).1 hLE
  have hκ := Stacks.TruncGESingleHomology.homologyMap_truncGEπ_truncGELTIso K c hι
  have : ((singleFunctor C c).obj ((homologyFunctor C c).obj K)).IsLE c := inferInstance
  have : ((singleFunctor C c).obj ((homologyFunctor C c).obj K)).IsGE c := inferInstance
  refine eq_of_isLE_of_isGE_of_homologyFunctor_map_eq c _ _ ?_
  rw [Functor.map_comp, homologyFunctor_map_singleHomologyToOfIsGE, CategoryTheory.Functor.map_id]
  rw [← cancel_mono ((singleFunctorCompHomologyFunctorIso C c).hom.app
    ((homologyFunctor C c).obj K)), Category.assoc]
  show _ ≫ (homologyFunctor C c).map ((TStructure.t.truncGEπ c).app K ≫
    (TStructure.t.truncGE c).map (asIso ((TStructure.t.truncLTι (c + 1)).app K)).inv ≫
      (truncGELTIsoHomologyFunctorCompSingleFunctor c).hom.app K) ≫ _ = _
  rw [hκ]
  simp

/-- **Every map from a single object in degree `c` to an object with no cohomology below `c`
factors through the edge map**, by the map it induces on `H^c`. -/
theorem eq_singleFunctor_map_comp_singleHomologyToOfIsGE (A : DerivedCategory C) (c : ℤ)
    (hA : TStructure.t.IsGE A c) {N : C} (σ : (singleFunctor C c).obj N ⟶ A) :
    σ = (singleFunctor C c).map ((singleFunctorCompHomologyFunctorIso C c).inv.app N ≫
        (homologyFunctor C c).map σ) ≫ singleHomologyToOfIsGE A c hA := by
  have : A.IsGE c := hA
  refine eq_of_isLE_of_isGE_of_homologyFunctor_map_eq c _ _ ?_
  have hnat := (singleFunctorCompHomologyFunctorIso C c).hom.naturality
    ((singleFunctorCompHomologyFunctorIso C c).inv.app N ≫ (homologyFunctor C c).map σ)
  simp only [Functor.comp_map, Functor.id_map, Functor.id_obj] at hnat
  rw [Functor.map_comp, homologyFunctor_map_singleHomologyToOfIsGE, hnat]
  exact (Iso.hom_inv_id_app_assoc (singleFunctorCompHomologyFunctorIso C c) N _).symm

end Generic

section Pullback

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat
attribute [local instance] Stacks.DeRham.CohomologicalGysin.moduleSheavesHasDerivedCategory

open Stacks.AlgebraicGeometry.TopDegreeBaseChange

variable {X X' : RingedSpace.{u, u}} (g : X' ⟶ X)

/-- **The edge map is compatible with derived pullback.** For `A` concentrated in degree `c`,
`A'` with no cohomology below `c` and `θ : Lg^*A ⟶ A'`, pulling back the edge map of `A` and
following it by `θ` is the comparison `Lg^*(H^c(A)[-c]) ⟶ (g^*H^c(A))[-c]`, followed by the map
`g^*H^c(A) ≅ H^c(Lg^*A) ⟶ H^c(A')` that `θ` induces, followed by the edge map of `A'`. -/
theorem derivedPullback_map_singleHomologyToOfIsGE_comp
    (c : ℤ) (A : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hAge : TStructure.t.IsGE A c) (hAle : TStructure.t.IsLE A c)
    (A' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X')))
    (hA' : TStructure.t.IsGE A' c) (θ : (derivedPullback g).obj A ⟶ A') :
    (derivedPullback g).map (singleHomologyToOfIsGE A c hAge) ≫ θ =
      derivedToOrdinaryPullbackSingle g ((homologyFunctor _ c).obj A) c ≫
        (singleFunctor _ c).map ((derivedPullbackTopDegreeIsoPullback g A c hAle).inv ≫
          (homologyFunctor _ c).map θ) ≫
        singleHomologyToOfIsGE A' c hA' := by
  have : ((derivedPullback g).obj ((singleFunctor _ c).obj
      ((homologyFunctor _ c).obj A))).IsLE c :=
    have h0 : TStructure.t.IsLE ((singleFunctor (SheafOfModules.{u} (structureSheafRing X)) c).obj
        ((homologyFunctor _ c).obj A)) c := inferInstance
    isLE_derivedPullback_obj g _ c h0
  have : A'.IsGE c := hA'
  refine eq_of_isLE_of_isGE_of_homologyFunctor_map_eq c _ _ ?_
  have hκ := singleHomologyToOfIsGE_comp_truncGEIsoSingleHomology A c hAge hAle
  have htop := derivedPullbackTopDegreeIsoPullback_hom g A c hAle
  have hnat := (singleFunctorCompHomologyFunctorIso (SheafOfModules.{u} (structureSheafRing X'))
    c).hom.naturality ((derivedPullbackTopDegreeIsoPullback g A c hAle).inv ≫
      (homologyFunctor _ c).map θ)
  simp only [Functor.comp_map] at hnat
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp,
    homologyFunctor_map_singleHomologyToOfIsGE, hnat]
  have hD : (homologyFunctor _ c).map (derivedToOrdinaryPullbackSingle g
        ((homologyFunctor _ c).obj A) c) ≫
      (singleFunctorCompHomologyFunctorIso _ c).hom.app
        ((modulePullback g).obj ((homologyFunctor _ c).obj A)) =
      homologyDerivedPullbackSingleMap g ((homologyFunctor _ c).obj A) c := by
    rw [homologyDerivedPullbackSingleMap, homologySingleIso_hom]
  rw [reassoc_of% hD]
  have hE : (homologyFunctor _ c).map ((derivedPullback g).map (singleHomologyToOfIsGE A c hAge)) =
      homologyDerivedPullbackSingleMap g ((homologyFunctor _ c).obj A) c ≫
        (derivedPullbackTopDegreeIsoPullback g A c hAle).inv := by
    rw [← cancel_mono (derivedPullbackTopDegreeIsoPullback g A c hAle).hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, htop, ← Functor.map_comp_assoc, ← Functor.map_comp, hκ,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hE, Category.assoc]
  rfl

/-- **The transpose of the canonical single map at the unit.** Under `Lg^* ⊣ Rg_*`, the comparison
`Lg^*(M[-a]) ⟶ (g^*M)[-a]` corresponds to the unit `M ⟶ g_*g^*M` placed in degree `a` followed by
the canonical map `(g_*g^*M)[-a] ⟶ Rg_*((g^*M)[-a])`. -/
theorem homEquiv_derivedToOrdinaryPullbackSingle (a : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (derivedAdjunction g).homEquiv _ _ (derivedToOrdinaryPullbackSingle g M a) =
      (singleFunctor _ a).map ((modulePullbackPushforwardAdjunction g).unit.app M) ≫
        (singleToDerivedPushforward g a).app ((modulePullback g).obj M) := by
  have hu := mapHomotopyCategoryAdjunction_unit_app_singleFunctor
    (modulePullbackPushforwardAdjunction g) a M
  have hc := Stacks.Cohomology.DerivedBaseChange.derivedPullbackComparison_homEquiv g
    ((HomotopyCategory.singleFunctor _ a).obj M)
  have hn1 := (derivedPushforwardUnit g).naturality
    ((Functor.mapHomotopyCategorySingleFunctor (modulePullback g) a).hom.app M)
  have hn2 := (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing X)) a).hom.naturality
    ((modulePullbackPushforwardAdjunction g).unit.app M)
  simp only [Functor.comp_map] at hn1 hn2
  rw [derivedToOrdinaryPullbackSingle, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  simp only [Functor.comp_obj]
  rw [hc]
  simp only [singleToDerivedPushforward, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_obj, Category.assoc]
  rw [reassoc_of% hn2]
  congr 1
  have hu' : (homotopyPullbackPushforwardAdjunction g).unit.app
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) a).obj M) ≫
      ((modulePushforward g).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategorySingleFunctor (modulePullback g) a).hom.app M) =
      (HomotopyCategory.singleFunctor _ a).map
          ((modulePullbackPushforwardAdjunction g).unit.app M) ≫
        ((modulePushforward g).mapHomotopyCategorySingleFunctor a).inv.app
          ((modulePullback g).obj M) := by
    rw [← hu]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [Functor.map_comp, ← reassoc_of% hn1, ← Functor.map_comp_assoc]
  show DerivedCategory.Qh.map (_ ≫ _) ≫ _ = _
  rw [hu', Functor.map_comp, Category.assoc]

/-- **The derived `g`-map of [Stacks, Tag 01F8] is the transpose of the comparison followed by
the adjoint `g`-map.** -/
theorem derivedPushforwardMap_canonical_eq (a : ℤ) {M : RModules X} {M' : RModules X'}
    (ψ : M ⟶ (modulePushforward g).obj M') :
    derivedPushforwardMap (CohomologyPullbackComparison.canonical g) a ψ =
      (derivedAdjunction g).homEquiv _ _ (derivedToOrdinaryPullbackSingle g M a ≫
        (singleFunctor _ a).map
          (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm ψ)) := by
  rw [Adjunction.homEquiv_naturality_right, homEquiv_derivedToOrdinaryPullbackSingle]
  have hψ : ψ = (modulePullbackPushforwardAdjunction g).unit.app M ≫
      (modulePushforward g).map (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm ψ) :=
    (((modulePullbackPushforwardAdjunction g).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ ψ)).symm
  have hn := (singleToDerivedPushforward g a).naturality
    (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm ψ)
  simp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp, ← hψ]
  rfl

/-- `i_*Rℋ_Z(K)` has no cohomology below `c` as soon as the local cohomology sheaves of `K`
vanish below `c`: the direct image from a closed subset is exact, so it commutes with the
cohomology sheaves. -/
theorem isGE_derivedSupportedPushforward (Z : Set X.carrier) (hZ : IsClosed Z) (c : ℤ)
    (K : DerivedCategory (RModules X))
    (hvan : ∀ i : ℤ, i < c → IsZero
      (Stacks.Cohomology.SupportedComplexes.localCohomologySheafOfComplex X Z hZ i K)) :
    TStructure.t.IsGE
      ((Stacks.Perfect.SupportedQuasicoherent.derivedSupportedPushforward X Z hZ).obj K) c := by
  let := Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteLimits X Z
  let := Stacks.Cohomology.SupportedComplexes.pushforward_preservesFiniteColimits X Z hZ
  refine (DerivedCategory.isGE_iff _ c).2 fun i hi => ?_
  refine IsZero.of_iso (Functor.map_isZero (modulePushforward
    (Stacks.Cohomology.SupportedComplexes.closedSubsetInclusion X Z)) (hvan i hi)) ?_
  exact (Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso
    (modulePushforward (Stacks.Cohomology.SupportedComplexes.closedSubsetInclusion X Z)) i).app
      ((Stacks.Cohomology.SupportedComplexes.derivedSupportedSectionsOnClosed X Z hZ).obj K)

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- The front half `i_*ℋ^c_Z(K)[-c] ⟶ i_*Rℋ_Z(K)` of the Gysin edge morphism. -/
def supportedGysinEdgeFront (Z : Set X.carrier) (hZ : IsClosed Z) (c : ℤ)
    (K : DerivedCategory (RModules X))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K)) :
    (singleFunctor (RModules X) c).obj
        ((modulePushforward (closedSubsetInclusion X Z)).obj
          (localCohomologySheafOfComplex X Z hZ c K)) ⟶
      (derivedSupportedPushforward X Z hZ).obj K :=
  letI := pushforward_preservesFiniteLimits X Z
  letI := pushforward_preservesFiniteColimits X Z hZ
  ((modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategorySingleFunctor c).inv.app
      (localCohomologySheafOfComplex X Z hZ c K) ≫
    (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
      (localCohomologySingleToDerived Z hZ c K hvan)

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- The Gysin edge morphism is its front followed by the adjunction map of [Stacks, Tag 0A3B]. -/
theorem supportedGysinEdge_eq (Z : Set X.carrier) (hZ : IsClosed Z) (c : ℤ)
    (K : DerivedCategory (RModules X))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K)) :
    supportedGysinEdge Z hZ c K hvan = supportedGysinEdgeFront Z hZ c K hvan ≫
      (derivedPushforwardAdjunction X Z hZ).counit.app K := by
  simp only [supportedGysinEdge, supportedGysinEdgeFront]
  exact (Category.assoc _ _ _).symm

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- The identification `i_*ℋ^c_Z(K) ⟶ H^c(i_*Rℋ_Z(K))` induced by the front of the edge. -/
def supportedGysinEdgeFrontHomology (Z : Set X.carrier) (hZ : IsClosed Z) (c : ℤ)
    (K : DerivedCategory (RModules X))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex X Z hZ i K)) :
    (modulePushforward (closedSubsetInclusion X Z)).obj
        (localCohomologySheafOfComplex X Z hZ c K) ⟶
      (homologyFunctor (RModules X) c).obj ((derivedSupportedPushforward X Z hZ).obj K) :=
  (singleFunctorCompHomologyFunctorIso (RModules X) c).inv.app _ ≫
    (homologyFunctor (RModules X) c).map (supportedGysinEdgeFront Z hZ c K hvan)

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- **The identification induced by the front of the edge is the exactness comparison**
`i_*ℋ^c_Z(K) ≅ H^c(i_*Rℋ_Z(K))` of the direct image from a closed subset. -/
theorem supportedGysinEdgeFrontHomology_eq {Y : RingedSpace.{u, u}} (Z : Set Y.carrier)
    (hZ : IsClosed Z) (c : ℤ) (K : DerivedCategory (RModules Y))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex Y Z hZ i K)) :
    letI := pushforward_preservesFiniteLimits Y Z
    letI := pushforward_preservesFiniteColimits Y Z hZ
    supportedGysinEdgeFrontHomology Z hZ c K hvan =
      (@exactFunctorDerivedHomologyIso _ _ _ _ _ _ (moduleSheavesHasDerivedCategory _)
        (moduleSheavesHasDerivedCategory _) (modulePushforward (closedSubsetInclusion Y Z)) _ _ _
        c).inv.app ((derivedSupportedSectionsOnClosed Y Z hZ).obj K) := by
  let := pushforward_preservesFiniteLimits Y Z
  let := pushforward_preservesFiniteColimits Y Z hZ
  set Fp := modulePushforward (closedSubsetInclusion Y Z)
  set L := localCohomologySheafOfComplex Y Z hZ c K
  let E := @exactFunctorDerivedHomologyIso _ _ _ _ _ _ (moduleSheavesHasDerivedCategory _)
    (moduleSheavesHasDerivedCategory _) Fp _ _ _ c
  have hs : (homologyFunctor _ c).map (localCohomologySingleToDerived Z hZ c K hvan) =
      (singleFunctorCompHomologyFunctorIso _ c).hom.app L :=
    homologyFunctor_map_singleHomologyToOfIsGE _ _ _
  have hnat := E.hom.naturality
    (localCohomologySingleToDerived Z hZ c K hvan)
  simp only [Functor.comp_map] at hnat
  have h5 := @Stacks.ExactFunctorSingleHomology.homologyMap_mapDerivedCategorySingleFunctor
    _ _ _ _ _ _ Fp _ _ _ (moduleSheavesHasDerivedCategory _) (moduleSheavesHasDerivedCategory _) c L
  rw [← @Stacks.Cohomology.SupportedComplexes.exactFunctorDerivedHomologyIso_eq _ _ _
    (moduleSheavesHasDerivedCategory _) _ _ _ (moduleSheavesHasDerivedCategory _) Fp _ _ _ c] at h5
  have h1 : (homologyFunctor (RModules Y) c).map (Fp.mapDerivedCategory.map
        (localCohomologySingleToDerived Z hZ c K hvan)) ≫
      E.hom.app
        ((derivedSupportedSectionsOnClosed Y Z hZ).obj K) =
      (homologyFunctor (RModules Y) c).map ((Fp.mapDerivedCategorySingleFunctor c).hom.app L) ≫
        (singleFunctorCompHomologyFunctorIso (RModules Y) c).hom.app (Fp.obj L) := by
    rw [hnat, hs]
    exact h5.symm
  have key : supportedGysinEdgeFrontHomology Z hZ c K hvan ≫
      E.hom.app
        ((derivedSupportedSectionsOnClosed Y Z hZ).obj K) = 𝟙 _ := by
    show ((singleFunctorCompHomologyFunctorIso (RModules Y) c).inv.app (Fp.obj L) ≫
      (homologyFunctor (RModules Y) c).map
        ((Fp.mapDerivedCategorySingleFunctor c).inv.app L ≫
          Fp.mapDerivedCategory.map (localCohomologySingleToDerived Z hZ c K hvan))) ≫ _ = _
    rw [Functor.map_comp, Category.assoc, Category.assoc, h1, ← Category.assoc
      ((homologyFunctor (RModules Y) c).map ((Fp.mapDerivedCategorySingleFunctor c).inv.app L)),
      ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id_app]
    rfl
  exact (Iso.comp_hom_eq_id (E.app ((derivedSupportedSectionsOnClosed Y Z hZ).obj K))).1 key

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- The front of the Gysin edge is the edge map of `i_*Rℋ_Z(K)` precomposed with the
identification `supportedGysinEdgeFrontHomology`. -/
theorem supportedGysinEdgeFront_eq {Y : RingedSpace.{u, u}} (Z : Set Y.carrier) (hZ : IsClosed Z)
    (c : ℤ) (K : DerivedCategory (RModules Y))
    (hvan : ∀ i : ℤ, i < c → IsZero (localCohomologySheafOfComplex Y Z hZ i K)) :
    supportedGysinEdgeFront Z hZ c K hvan =
      (singleFunctor _ c).map (supportedGysinEdgeFrontHomology Z hZ c K hvan) ≫
        singleHomologyToOfIsGE _ c (isGE_derivedSupportedPushforward Z hZ c K hvan) :=
  eq_singleFunctor_map_comp_singleHomologyToOfIsGE _ _ _ _

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- The front of the Gysin edge morphism, pulled back and followed by `θ`, is the comparison of
single objects followed by the adjoint of `tgtHom` and the front on `X'`. -/
theorem supportedGysinEdgeFront_pullback (Z : Set X.carrier) (hZ : IsClosed Z)
    (Z' : Set X'.carrier) (hZ' : IsClosed Z') (c : ℕ) (F : RModules X) (F' : RModules X')
    (hvan : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ i
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (hvan' : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X' Z' hZ' i
      ((singleFunctor _ (0 : ℤ)).obj F')))
    (hLE : TStructure.t.IsLE ((derivedSupportedPushforward X Z hZ).obj
      ((singleFunctor _ (0 : ℤ)).obj F)) (c : ℤ))
    (θ : (derivedPullback g).obj ((derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor _ (0 : ℤ)).obj F)) ⟶
      (derivedSupportedPushforward X' Z' hZ').obj ((singleFunctor _ (0 : ℤ)).obj F'))
    (tgtHom : (modulePushforward (closedSubsetInclusion X Z)).obj
        (localCohomologySheafOfComplex X Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F)) ⟶
      (modulePushforward g).obj ((modulePushforward (closedSubsetInclusion X' Z')).obj
        (localCohomologySheafOfComplex X' Z' hZ' (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F'))))
    (htgt : (modulePullback g).map (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan) ≫
        (derivedPullbackTopDegreeIsoPullback g _ (c : ℤ) hLE).inv ≫
          (homologyFunctor _ (c : ℤ)).map θ =
      ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom ≫
        supportedGysinEdgeFrontHomology Z' hZ' (c : ℤ) _ hvan') :
    (derivedPullback g).map (supportedGysinEdgeFront Z hZ (c : ℤ) _ hvan) ≫ θ =
    derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫
      (singleFunctor _ (c : ℤ)).map
        (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom) ≫
      supportedGysinEdgeFront Z' hZ' (c : ℤ) _ hvan' := by
  have hGE := isGE_derivedSupportedPushforward Z hZ (c : ℤ) _ hvan
  have hGE' := isGE_derivedSupportedPushforward Z' hZ' (c : ℤ) _ hvan'
  calc (derivedPullback g).map (supportedGysinEdgeFront Z hZ (c : ℤ) _ hvan) ≫ θ
      = (derivedPullback g).map ((singleFunctor _ (c : ℤ)).map
            (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan)) ≫
          ((derivedPullback g).map (singleHomologyToOfIsGE _ _ hGE) ≫ θ) := by
        rw [supportedGysinEdgeFront_eq Z hZ (c : ℤ) _ hvan, Functor.map_comp, Category.assoc]
    _ = (derivedPullback g).map ((singleFunctor _ (c : ℤ)).map
            (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan)) ≫
          derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫
            (singleFunctor _ (c : ℤ)).map ((derivedPullbackTopDegreeIsoPullback g _ (c : ℤ)
              hLE).inv ≫ (homologyFunctor _ (c : ℤ)).map θ) ≫
            singleHomologyToOfIsGE _ _ hGE' := by
        rw [derivedPullback_map_singleHomologyToOfIsGE_comp g (c : ℤ) _ hGE hLE _ hGE' θ]
    _ = derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫
          (singleFunctor _ (c : ℤ)).map
            ((modulePullback g).map (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan) ≫
              (derivedPullbackTopDegreeIsoPullback g _ (c : ℤ) hLE).inv ≫
                (homologyFunctor _ (c : ℤ)).map θ) ≫
            singleHomologyToOfIsGE _ _ hGE' := by
        rw [reassoc_of% (derivedToOrdinaryPullbackSingle_naturality g
          (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan) (c : ℤ)), ← Functor.map_comp_assoc]
    _ = derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫
          (singleFunctor _ (c : ℤ)).map
            (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom ≫
              supportedGysinEdgeFrontHomology Z' hZ' (c : ℤ) _ hvan') ≫
            singleHomologyToOfIsGE _ _ hGE' := by rw [htgt]
    _ = derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫
          (singleFunctor _ (c : ℤ)).map
            (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom) ≫
          supportedGysinEdgeFront Z' hZ' (c : ℤ) _ hvan' := by
        refine congrArg (fun t => derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫ t) ?_
        refine ((congrArg (fun t => t ≫ singleHomologyToOfIsGE _ _ hGE')
            ((singleFunctor _ (c : ℤ)).map_comp _ _)).trans (Category.assoc _ _ _)).trans ?_
        exact congrArg (fun t => (singleFunctor _ (c : ℤ)).map
          (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom) ≫ t)
          (supportedGysinEdgeFront_eq Z' hZ' (c : ℤ) _ hvan').symm

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- **The Gysin edge morphism is compatible with pullback.**  Let `g : X' ⟶ X`, let `Z ⊆ X`,
`Z' ⊆ X'` be closed, let `F`, `F'` be modules with local cohomology vanishing below `c`, with
`i_*Rℋ_Z(F)` concentrated in degrees `≤ c`.  Let `amb : F ⟶ g_*F'` and let
`θ : Lg^*(i_*Rℋ_Z F) ⟶ i'_*Rℋ_{Z'} F'` satisfy the triangle with the two adjunction maps.  If
`tgtHom : i_*ℋ^c_Z(F) ⟶ g_*i'_*ℋ^c_{Z'}(F')` is the map `θ` induces on `H^c`, then the two Gysin
edge morphisms fit into the derived square with the derived `g`-maps of [Stacks, Tag 01F8]. -/
theorem supportedGysinEdge_derivedPushforwardMap (Z : Set X.carrier) (hZ : IsClosed Z)
    (Z' : Set X'.carrier) (hZ' : IsClosed Z') (c : ℕ) (F : RModules X) (F' : RModules X')
    (hvan : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ i
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (hvan' : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X' Z' hZ' i
      ((singleFunctor _ (0 : ℤ)).obj F')))
    (hLE : TStructure.t.IsLE ((derivedSupportedPushforward X Z hZ).obj
      ((singleFunctor _ (0 : ℤ)).obj F)) (c : ℤ))
    (amb : F ⟶ (modulePushforward g).obj F')
    (θ : (derivedPullback g).obj ((derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor _ (0 : ℤ)).obj F)) ⟶
      (derivedSupportedPushforward X' Z' hZ').obj ((singleFunctor _ (0 : ℤ)).obj F'))
    (hθ : θ ≫ (derivedPushforwardAdjunction X' Z' hZ').counit.app
        ((singleFunctor _ (0 : ℤ)).obj F') =
      (derivedPullback g).map ((derivedPushforwardAdjunction X Z hZ).counit.app
          ((singleFunctor _ (0 : ℤ)).obj F)) ≫
        derivedToOrdinaryPullbackSingle g F 0 ≫
          (singleFunctor _ 0).map (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm amb))
    (tgtHom : (modulePushforward (closedSubsetInclusion X Z)).obj
        (localCohomologySheafOfComplex X Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F)) ⟶
      (modulePushforward g).obj ((modulePushforward (closedSubsetInclusion X' Z')).obj
        (localCohomologySheafOfComplex X' Z' hZ' (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F'))))
    (htgt : (modulePullback g).map (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan) ≫
        (derivedPullbackTopDegreeIsoPullback g _ (c : ℤ) hLE).inv ≫
          (homologyFunctor _ (c : ℤ)).map θ =
      ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom ≫
        supportedGysinEdgeFrontHomology Z' hZ' (c : ℤ) _ hvan') :
    supportedGysinEdge Z hZ (c : ℤ) _ hvan ≫
        derivedPushforwardMap (CohomologyPullbackComparison.canonical g) (0 : ℤ) amb =
      derivedPushforwardMap (CohomologyPullbackComparison.canonical g) (c : ℤ) tgtHom ≫
        (derivedPushforward g).map (supportedGysinEdge Z' hZ' (c : ℤ) _ hvan') := by
  have hGE := isGE_derivedSupportedPushforward Z hZ (c : ℤ) _ hvan
  have hGE' := isGE_derivedSupportedPushforward Z' hZ' (c : ℤ) _ hvan'
  have hfront := supportedGysinEdgeFront_pullback g Z hZ Z' hZ' c F F' hvan hvan' hLE θ tgtHom htgt
  have key : (derivedPullback g).map (supportedGysinEdge Z hZ (c : ℤ) _ hvan) ≫
        derivedToOrdinaryPullbackSingle g F 0 ≫
          (singleFunctor _ 0).map
            (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm amb) =
      (derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫
        (singleFunctor _ (c : ℤ)).map
          (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom)) ≫
        supportedGysinEdge Z' hZ' (c : ℤ) _ hvan' := by
    have hE : (derivedPullback g).map (supportedGysinEdge Z hZ (c : ℤ) _ hvan) =
        (derivedPullback g).map (supportedGysinEdgeFront Z hZ (c : ℤ) _ hvan) ≫
          (derivedPullback g).map ((derivedPushforwardAdjunction X Z hZ).counit.app
            ((singleFunctor _ (0 : ℤ)).obj F)) := by
      rw [supportedGysinEdge_eq]
      exact Functor.map_comp _ _ _
    rw [hE, Category.assoc]
    refine (congrArg (fun t => (derivedPullback g).map
      (supportedGysinEdgeFront Z hZ (c : ℤ) _ hvan) ≫ t) hθ.symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun t => t ≫ (derivedPushforwardAdjunction X' Z' hZ').counit.app
      ((singleFunctor _ (0 : ℤ)).obj F')) hfront).trans ?_
    rw [supportedGysinEdge_eq Z' hZ' (c : ℤ) _ hvan']
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t => derivedToOrdinaryPullbackSingle g _ (c : ℤ) ≫ t)
        (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm)
  refine (congrArg (fun t => supportedGysinEdge Z hZ (c : ℤ) _ hvan ≫ t)
    (derivedPushforwardMap_canonical_eq g (0 : ℤ) amb)).trans ?_
  refine (Adjunction.homEquiv_naturality_left _ _ _).symm.trans ?_
  refine (congrArg _ key).trans ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  exact congrArg
    (fun t => t ≫ (derivedPushforward g).map (supportedGysinEdge Z' hZ' (c : ℤ) _ hvan'))
    (derivedPushforwardMap_canonical_eq g (c : ℤ) tgtHom).symm

open Stacks.Cohomology.SupportedComplexes Stacks.Perfect.SupportedQuasicoherent in
/-- `supportedGysinEdge_derivedPushforwardMap` with `θ` landing at a second spelling `Z''` of the
closed subset of `X'`. -/
theorem supportedGysinEdge_derivedPushforwardMap_of_eq (Z : Set X.carrier) (hZ : IsClosed Z)
    (Z' : Set X'.carrier) (hZ' : IsClosed Z') (Z'' : Set X'.carrier) (hZ'' : IsClosed Z'')
    (hZZ : Z' = Z'') (c : ℕ) (F : RModules X) (F' : RModules X')
    (hvan : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X Z hZ i
      ((singleFunctor _ (0 : ℤ)).obj F)))
    (hvan' : ∀ i : ℤ, i < (c : ℤ) → IsZero (localCohomologySheafOfComplex X' Z' hZ' i
      ((singleFunctor _ (0 : ℤ)).obj F')))
    (hLE : TStructure.t.IsLE ((derivedSupportedPushforward X Z hZ).obj
      ((singleFunctor _ (0 : ℤ)).obj F)) (c : ℤ))
    (amb : F ⟶ (modulePushforward g).obj F')
    (θ : (derivedPullback g).obj ((derivedSupportedPushforward X Z hZ).obj
        ((singleFunctor _ (0 : ℤ)).obj F)) ⟶
      (derivedSupportedPushforward X' Z'' hZ'').obj ((singleFunctor _ (0 : ℤ)).obj F'))
    (hθ : θ ≫ (derivedPushforwardAdjunction X' Z'' hZ'').counit.app
        ((singleFunctor _ (0 : ℤ)).obj F') =
      (derivedPullback g).map ((derivedPushforwardAdjunction X Z hZ).counit.app
          ((singleFunctor _ (0 : ℤ)).obj F)) ≫
        derivedToOrdinaryPullbackSingle g F 0 ≫
          (singleFunctor _ 0).map (((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm amb))
    (tgtHom : (modulePushforward (closedSubsetInclusion X Z)).obj
        (localCohomologySheafOfComplex X Z hZ (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F)) ⟶
      (modulePushforward g).obj ((modulePushforward (closedSubsetInclusion X' Z')).obj
        (localCohomologySheafOfComplex X' Z' hZ' (c : ℤ) ((singleFunctor _ (0 : ℤ)).obj F'))))
    (hH : (homologyFunctor (RModules X') (c : ℤ)).obj
        ((derivedSupportedPushforward X' Z'' hZ'').obj ((singleFunctor _ (0 : ℤ)).obj F')) =
      (homologyFunctor (RModules X') (c : ℤ)).obj
        ((derivedSupportedPushforward X' Z' hZ').obj ((singleFunctor _ (0 : ℤ)).obj F')))
    (htgt : (modulePullback g).map (supportedGysinEdgeFrontHomology Z hZ (c : ℤ) _ hvan) ≫
        (derivedPullbackTopDegreeIsoPullback g _ (c : ℤ) hLE).inv ≫
          (homologyFunctor _ (c : ℤ)).map θ ≫ eqToHom hH =
      ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm tgtHom ≫
        supportedGysinEdgeFrontHomology Z' hZ' (c : ℤ) _ hvan') :
    supportedGysinEdge Z hZ (c : ℤ) _ hvan ≫
        derivedPushforwardMap (CohomologyPullbackComparison.canonical g) (0 : ℤ) amb =
      derivedPushforwardMap (CohomologyPullbackComparison.canonical g) (c : ℤ) tgtHom ≫
        (derivedPushforward g).map (supportedGysinEdge Z' hZ' (c : ℤ) _ hvan') := by
  subst hZZ
  simp only [eqToHom_refl, Category.comp_id] at htgt
  exact supportedGysinEdge_derivedPushforwardMap g Z hZ Z' hZ' c F F' hvan hvan' hLE amb θ hθ
    tgtHom htgt

/-- The comparison `Lg^*(M[0]) ⟶ (g^*M)[0]` of the thickening files is the degree-`0` case of
`derivedToOrdinaryPullbackSingle`. -/
theorem derivedPullbackSingleObj_eq_derivedToOrdinaryPullbackSingle (M : RModules X) :
    AlgebraicGeometry.RingedSpaceThickening.derivedPullbackSingleObj g M =
      derivedToOrdinaryPullbackSingle g M 0 := by
  have h0 := Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app (C := RModules X') 0
    ((modulePullback g).obj M)
  have hinv : (singleFunctorIsoCompQh (RModules X') 0).inv.app ((modulePullback g).obj M) =
      (DerivedCategory.quotientCompQhIso (RModules X')).hom.app
        ((CochainComplex.singleFunctor (RModules X') 0).obj ((modulePullback g).obj M)) :=
    Iso.inv_ext (f := (singleFunctorIsoCompQh (RModules X') 0).app ((modulePullback g).obj M))
      ((congrArg (· ≫ (DerivedCategory.quotientCompQhIso (RModules X')).hom.app
        ((CochainComplex.singleFunctor (RModules X') 0).obj ((modulePullback g).obj M))) h0).trans
        (Iso.inv_hom_id_app _ _))
  have hnat := (DerivedCategory.quotientCompQhIso (RModules X')).hom.naturality
    ((HomologicalComplex.singleMapHomologicalComplex (modulePullback g)
      (ComplexShape.up ℤ) 0).hom.app M)
  simp only [Functor.comp_map] at hnat
  rw [derivedToOrdinaryPullbackSingle,
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.mapHomotopyCategorySingleFunctor_hom_app_eq]
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ _ ≫ _ ≫ t) hinv.symm)
  refine Eq.trans ?_ (congrArg (fun t => _ ≫ _ ≫ t) hnat.symm)
  rfl

end Pullback

end Stacks.DeRham.GysinCohomologyBaseChange

end
