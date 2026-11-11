module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedStrictlyPerfectDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.ChartSliceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBranchCodimension
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineGlobalFunctions
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FppfDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatOpcycles
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PseudoCoherentAndFiniteTorDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PseudoCoherenceGeneral
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness on the small étale site of a scheme comes from the Zariski site

Let `X = h_U` be the algebraic space represented by an object `U` of the big fppf site over a
scheme `S`, with underlying scheme `T`, and let `ε^* : D(𝒪_T) ⥤ D(𝒪_{h_U})` be the comparison of
Stacks 08H7. Stacks 08HG says that an object `E` of `D(𝒪_T)` is perfect if and only if `ε^*E` is
perfect. The forward implication is
`AlgebraicGeometry.Space.isPerfect_representedDerivedAssociatedModule`; this file proves the
converse for `E` with quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.Space.exists_chart_strictlyPerfect_model`: a perfect object of `D(𝒪_X)` on
  an algebraic space has, near any point of any étale chart, a strictly perfect model on a
  smaller chart.
* `AlgebraicGeometry.Space.hasTorAmplitude_image_of_etale`: a Tor-amplitude interval on an open
  of the source of an étale morphism of schemes descends to its image.
* `AlgebraicGeometry.Space.isPerfect_of_isPerfect_representedDerivedAssociatedModule`: the
  converse half of Stacks 08HG, on `D_QCoh`.

## References

* [Stacks Project, Tag 08HG](https://stacks.math.columbia.edu/tag/08HG)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 09UD](https://stacks.math.columbia.edu/tag/09UD)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

/-! ### Tor amplitude descends along an étale morphism of schemes -/

section TorDescent

open RingedSpace Stacks.Cohomology.TorAmplitude StrictlyPerfect

attribute [local instance] Stacks.Cohomology.TorAmplitude.hasDerivedCategoryModules

/-- Tor amplitude is invariant under isomorphism in the derived category. -/
theorem hasTorAmplitude_of_iso' {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]
    {E E' : DerivedCategory (OXMod.{u} X)} (e : E ≅ E') {a b : ℤ}
    (h : HasTorAmplitude X E a b) : HasTorAmplitude X E' a b := fun F i hi =>
  (h F i hi).of_iso ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).mapIso
    (((derTensor X).tensor.mapIso e.symm).app
      ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)))

attribute [local instance 2000] HasDerivedCategory.standard

/-- The image of an open of the source of an étale morphism of schemes, an open of the
target. -/
def etaleImageOpens {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] [LocallyOfFinitePresentation f]
    (V : Y.Opens) : X.Opens :=
  ⟨f.base '' (V : Set Y), f.isOpenMap _ V.isOpen⟩

/-- A Tor-amplitude interval on an open of the source of an étale morphism of schemes descends
to its image: if `f : Y ⟶ X` is étale and `(Lf^*E)|_V` has Tor amplitude in `[a, b]` for an
open `V` of `Y`, then `E|_{f(V)}` has Tor amplitude in `[a, b]`. -/
theorem hasTorAmplitude_image_of_etale {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f]
    [LocallyOfFinitePresentation f]
    (E : DerivedCategory (OXMod.{u} X.toRingedSpace)) (V : Y.Opens) (a b : ℤ)
    (h : HasTorAmplitude (Y.toRingedSpace.restrict V.isOpenEmbedding)
      ((derivedRestrictModules Y.toRingedSpace V).obj
        ((derivedPullback f.toLRSHom.toShHom).obj E)) a b) :
    HasTorAmplitude (X.toRingedSpace.restrict (etaleImageOpens f V).isOpenEmbedding)
      ((derivedRestrictModules X.toRingedSpace (etaleImageOpens f V)).obj E) a b := by
  set W := etaleImageOpens f V
  have hVU : V ≤ f ⁻¹ᵁ W := fun z hz => ⟨z, hz, rfl⟩
  have hsurj : Function.Surjective (f.resLE W V hVU).base := by
    intro z
    obtain ⟨w, hw, hwz⟩ := z.property
    exact ⟨⟨w, hw⟩, Subtype.ext ((f.coe_resLE_apply hVU ⟨w, hw⟩).trans hwz)⟩
  refine (Stacks.Cohomology.TorAmplitude.FlatDescent.hasTorAmplitude_derivedPullback_iff
    (f.resLE W V hVU).toLRSHom hsurj
    (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _) _ a b).2 ?_
  exact hasTorAmplitude_of_iso' (derivedPullbackRestrictIso f.toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom f) W V
      (f.resLE W V hVU).toLRSHom.toShHom
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)
      (Stacks.Cohomology.PseudoCoherence.FlatDescent.resLE_square f W V hVU) E).symm h

end TorDescent

/-! ### Strictly perfect models on étale charts -/

section ChartModel

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  RingedSite.ovFunctorLimits RingedSite.ovFunctorColimits smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective RingedSite.sliceHasSheafify
  RingedSite.sliceWEqualsLocallyBijective

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The comparison of Stacks 04M0 at a chart carries the structure sheaf of the slice to the
structure sheaf of the chart. -/
def chartModuleSliceReindexUnitRingStructureIso (V : SmallEtale B S hS X.1) :
    (chartModuleSliceReindex B S hS X V).obj
        (SheafOfModules.unit ((structureRingSheaf B S hS X).over V)) ≅
      SheafOfModules.unit (ringStructureSheaf B S hS (chartSpace B S hS X V).1) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intro A A' a; ext; rfl))

/-- The `𝒪_X`-modules on a slice of the small étale site form an abelian category. -/
local instance (priority := high) modules_over_abelian''
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    Abelian (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over U)) :=
  SheafOfModules.instAbelian _

/-- A strictly perfect model on the slice at a chart is a strictly perfect model on the chart:
if `P ≅ E|_V` in the derived category of the slice of the small étale site of `X` at a chart `V`,
for a strictly perfect complex `P`, then the comparison of Stacks 04M0 carries `P` to a strictly
perfect complex on the small étale site of `h_V` isomorphic to the étale restriction `E|_V`. -/
theorem exists_chart_strictlyPerfect_model_of_slice
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (V : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over V)) ℤ)
    (hP : IsStrictlyPerfect
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over V) P)
    (α : DerivedCategory.Q.obj P ≅
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          V).mapDerivedCategory.obj E) :
    ∃ K : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS X V).1
        (chartSpace B S hS X V).2) ℤ,
      IsStrictlyPerfect (ringStructureSheaf B S hS (chartSpace B S hS X V).1) K ∧
        Nonempty (DerivedCategory.Q.obj K ≅
          (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
            (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) := by
  let F : SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over V) ⥤
      Modules.{u, u} B S hS (chartSpace B S hS X V).1 (chartSpace B S hS X V).2 :=
    chartModuleSliceReindex B S hS X V
  have : F.Additive := ⟨fun {_ _} _ _ => rfl⟩
  have : F.IsEquivalence := isEquivalence_chartModuleSliceReindex B S hS X V
  let oV := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) V
  have := etaleModulePullback_additive.{u, u} B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  have := preservesFiniteLimits_etaleModulePullback B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  have := preservesFiniteColimits_etaleModulePullback B S hS (chartToSpace B S hS X V)
    (isEtale_chartToSpace B S hS X V)
  let ι : oV ⋙ F ≅ etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
      (isEtale_chartToSpace B S hS X V) :=
    chartSliceReindexOverIso B S hS X V
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    SheafOfModules.isStrictlyPerfect_map F
      (chartModuleSliceReindexUnitRingStructureIso B S hS X V) hP, ⟨?_⟩⟩
  exact (F.mapDerivedCategoryFactors.app P).symm ≪≫ F.mapDerivedCategory.mapIso α ≪≫
    ((Functor.mapDerivedCategoryComp oV F).app E).symm ≪≫
      (asIso (NatTrans.mapDerivedCategory ι.hom)).app E

/-- A perfect object has strictly perfect models on charts through every point: let `E` be a
perfect object of `D(𝒪_X)`, let `U` be an étale chart of `X` and let `x` be a point of `U`.
Then there are a chart `V ⟶ U` through whose image `x` passes and a strictly perfect complex on
the small étale site of `h_V` isomorphic to `E|_V`. -/
theorem exists_chart_strictlyPerfect_model
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E) (U : SmallEtale B S hS X.1)
    (x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U))) :
    ∃ (V : SmallEtale B S hS X.1) (f : V ⟶ U)
      (y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj V))
          (yoneda.map ((SmallEtale.toOver B S hS X.1).map f)) y = x ∧
        ∃ K : CochainComplex (Modules.{u, u} B S hS (chartSpace B S hS X V).1
            (chartSpace B S hS X V).2) ℤ,
          IsStrictlyPerfect (ringStructureSheaf B S hS (chartSpace B S hS X V).1) K ∧
            Nonempty (DerivedCategory.Q.obj K ≅
              (etaleModulePullback.{u, u} B S hS (chartToSpace B S hS X V)
                (isEtale_chartToSpace B S hS X V)).mapDerivedCategory.obj E) := by
  obtain ⟨Ec, hEc, ⟨eE⟩⟩ := hE
  obtain ⟨Sv, hSv, hmod⟩ := hEc U
  obtain ⟨V, f, hf, y, hy⟩ := SmallEtale.exists_mem_arrows_pointsMap_eq B S hS X.1 hSv x
  obtain ⟨Z, h, s, hs, rfl⟩ := hf
  obtain ⟨P, hP, q, hq⟩ := hmod s hs
  have := hq
  let oZ := SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) Z
  obtain ⟨P₁, hP₁, ⟨α₁⟩⟩ := RingedSite.exists_strictlyPerfect_model_of_hom _ E h P hP
    (asIso (DerivedCategory.Q.map q) ≪≫ (oZ.mapDerivedCategoryFactors.app Ec).symm ≪≫
      oZ.mapDerivedCategory.mapIso eE)
  exact ⟨V, h ≫ s, y, hy, exists_chart_strictlyPerfect_model_of_slice B S hS X E V P₁ hP₁ α₁⟩

end ChartModel

/-! ### The converse half of Stacks 08HG -/

section Represented

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] SmallEtale.preservesFiniteLimits_associatedModule

attribute [local instance 10000] SmallEtale.hasSheafify_smallEtale
  SmallEtale.wEqualsLocallyBijective_smallEtale smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance 10000] smallEtaleModulesAbelianAtSchemeUniverse
  smallEtaleModulesHasDerivedCategory

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

/-- Étale restriction along two equal morphisms agrees, on derived categories. -/
theorem nonempty_etaleModulePullback_mapDerivedCategory_congr {X Y : AlgebraicSpaces B S hS}
    {f f' : X ⟶ Y} (hf : IsEtale B S hS f.hom) (hf' : IsEtale B S hS f'.hom) (h : f = f')
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) :
    Nonempty ((etaleModulePullback.{u, u} B S hS f hf).mapDerivedCategory.obj E ≅
      (etaleModulePullback.{u, u} B S hS f' hf').mapDerivedCategory.obj E) := by
  subst h; exact ⟨Iso.refl _⟩

/-- If `ε^*E` is perfect on the small étale site of `h_U`
and `E` has quasi-coherent cohomology, then every point `x` of the scheme `T` underlying `U` is
in the image of an étale morphism `g : V ⟶ T` of the big fppf site with `Lg^*E` perfect. -/
theorem exists_etale_isPerfect_derivedPullback
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      ((representedDerivedAssociatedModule B S hS U).obj E₀))
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (V : BigFppfOver B S hS) (g : V ⟶ U) (_ : Etale ((BigFppfOver.toScheme B S hS).map g))
      (y : (BigFppfOver.toScheme B S hS).obj V), (BigFppfOver.toScheme B S hS).map g y = x ∧
        Stacks.Cohomology.PerfectComplexes.IsPerfect
          (X := ((BigFppfOver.toScheme B S hS).obj V).toRingedSpace)
          ((derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj E₀) := by
  let X : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  obtain ⟨V, f, y, hy, K, hK, ⟨eK⟩⟩ := exists_chart_strictlyPerfect_model B S hS X _ h
    (selfChart B S hS U) ((pointsEquivScheme B S hS U).symm x)
  let V' := (SmallEtale.toOver B S hS X.1).obj V
  let g : V' ⟶ U := (SmallEtale.toOver B S hS X.1).map f
  have hVg : V.1.hom = yoneda.map g :=
    (CostructuredArrow.w ((SmallEtale.inclusion B S hS X.1).map f)).symm.trans (Category.comp_id _)
  have hch : chartToSpace B S hS X V = representedSpaceMap B S hS g :=
    ObjectProperty.hom_ext _ hVg
  have hφ : IsEtale B S hS (representedSpaceMap B S hS g).hom :=
    hch ▸ isEtale_chartToSpace B S hS X V
  have hg : Etale ((BigFppfOver.toScheme B S hS).map g) :=
    (presheaf_yoneda_map_etale_iff B S hS g).1 (hVg ▸ V.2)
  have : Flat ((BigFppfOver.toScheme B S hS).map g) := inferInstance
  obtain ⟨eC⟩ := nonempty_etaleModulePullback_mapDerivedCategory_congr B S hS
    (isEtale_chartToSpace B S hS X V) hφ hch ((representedDerivedAssociatedModule B S hS U).obj E₀)
  obtain ⟨P₀, hP₀, ⟨e₁⟩⟩ := exists_isPerfect_representedDerivedAssociatedModule_iso B S hS V' K hK
  let e₂ : (representedDerivedAssociatedModule B S hS V').obj P₀ ≅
      (representedDerivedAssociatedModule B S hS V').obj
        ((derivedPullback ((BigFppfOver.toScheme B S hS).map g).toLRSHom.toShHom).obj E₀) :=
    e₁ ≪≫ eK ≪≫ eC ≪≫
      (representedDerivedAssociatedModulePullbackIso B S hS g hφ).app E₀
  obtain ⟨e₃⟩ := nonempty_iso_of_representedDerivedAssociatedModule_iso B S hS V' P₀ _
    (PerfectApproximation.isQuasicoherent_homology_of_isPerfect _ P₀ hP₀)
    (Stacks.Duality.isQuasicoherent_homology_derivedPullback_anyModel _ E₀ hqc) e₂
  obtain ⟨Pc, hPc, ⟨fP⟩⟩ := hP₀
  refine ⟨V', g, hg, pointsEquivScheme B S hS V' y, ?_, ⟨Pc, hPc,
    ⟨Iso.trans (C := DerivedCategory ((BigFppfOver.toScheme B S hS).obj V').Modules) fP e₃⟩⟩⟩
  apply (pointsEquivScheme B S hS U).symm.injective
  rwa [← ChartBranch.pointsEquivScheme_symm_pointsMap, Equiv.symm_apply_apply]

/-- Let `T` be the scheme underlying an object `U` of the big fppf site over `S`, and let `E` be
an object of `D(𝒪_T)` with quasi-coherent cohomology. If `ε^*E` is perfect on the small étale
site of `h_U`, then `E` is perfect. -/
theorem isPerfect_of_isPerfect_representedDerivedAssociatedModule
    (E₀ : DerivedCategory.{u + 1} ((BigFppfOver.toScheme B S hS).obj U).Modules)
    (hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E₀).IsQuasicoherent)
    (h : (smallEtaleRingedSite B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).IsPerfect
      ((representedDerivedAssociatedModule B S hS U).obj E₀)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := ((BigFppfOver.toScheme B S hS).obj U).toRingedSpace) E₀ := by
  let T := (BigFppfOver.toScheme B S hS).obj U
  refine
    (Stacks.Cohomology.TorAmplitude.isPerfect_iff_isPseudoCoherent_and_locallyHasFiniteTorDimension
      E₀).2 ⟨?_, ?_⟩
  · exact (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_iff_isPseudoCoherent' E₀).2
      ((RingedSpace.isPseudoCoherent_iff_forall E₀).2 fun m =>
        isPseudoCoherentFrom_of_representedDerivedAssociatedModule B S hS U E₀ m
          (RingedSite.isPseudoCoherentFrom_of_isPerfect_anyModuleUniverse _ h m))
  · have hloc : ∀ x : T, ∃ O : T.Opens, x ∈ O ∧
        Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
          (T.toRingedSpace.restrict O.isOpenEmbedding)
          ((RingedSpace.PseudoCoherence.restrictModules T.toRingedSpace O).mapDerivedCategory.obj
            E₀) := by
      intro x
      obtain ⟨V, g, hg, y, hy, hP⟩ := exists_etale_isPerfect_derivedPullback B S hS U E₀ hqc h x
      obtain ⟨I, W, hW, hfin⟩ :=
        Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect _ hP
      obtain ⟨i, hi⟩ : ∃ i, y ∈ W i := Opens.mem_iSup.1 (by rw [hW]; trivial)
      obtain ⟨a, b, hab⟩ := hfin i
      exact ⟨etaleImageOpens ((BigFppfOver.toScheme B S hS).map g) (W i), ⟨y, hi, hy⟩, a, b,
        hasTorAmplitude_image_of_etale _ E₀ (W i) a b hab⟩
    choose O hxO hO using hloc
    exact ⟨T, O, eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hxO x⟩, hO⟩

end Represented

end AlgebraicGeometry.Space
