module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.ThickeningLift
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackAxiomHelpers.ProperSupportThickening
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquareStrict
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeChartReduction
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationOnSiteIff
public import StacksFrontier.Deformation.ToposThickening.FinitePresentationFlatLift

/-!
# Flat lifts across `X_T ⊂ X_{T'}` are lifts of an object of `Coh_{X/Y}`

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB) and `h : T ⟶ T'` a first order
thickening of schemes over `Y`. A flat lift of `𝒢` across the first order thickening of ringed
topoi `i : X_T ⊂ X_{T'}`, in the sense of `Deformation.ToposThickening.FlatLift` along the
morphism `X_{T'} ⟶ (X_{T'}, f'⁻¹𝒪_{T'})` of the relative square, is a lift of `ξ` in the sense of
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift`: an `𝒪_{X_{T'}}`-module `𝒢'` flat
over `T'` with `i^*𝒢' ≅ 𝒢`, which is then automatically quasi-coherent of finite presentation
(Stacks 08VU, as in the proof of Stacks 08W7) with support proper over `T'`. Together with
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toFlatLift` this identifies the two
notions of lift and their isomorphism classes.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.flatLiftFibre`: the comparison `i^*𝒢' ⟶ 𝒢` of a
  flat lift, the adjoint transpose of its map `𝒢' ⟶ i_*𝒢`; it is an isomorphism
  (`AlgebraicGeometry.Space.CoherentSituation.isIso_flatLiftFibre`).
* `AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.ofFlatLift`: the lift of `ξ` attached
  to a flat lift.
* `AlgebraicGeometry.Space.CoherentSituation.thickeningLiftClassEquiv`: the bijection between the
  isomorphism classes of lifts of `ξ` and the isomorphism classes of flat lifts of `𝒢`.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 08VU](https://stacks.math.columbia.edu/tag/08VU)
* [Stacks Project, Tag 08VW](https://stacks.math.columbia.edu/tag/08VW)
* [Stacks Project, Tag 08W7](https://stacks.math.columbia.edu/tag/08W7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor pushforwardModuleFunctor)
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

universe u

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  {ξ : CoherentObject D} {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
  (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))

/-- The flat lifts of `𝒢` across `X_T ⊂ X_{T'}` along the base `(X_{T'}, f'⁻¹𝒪_{T'})` of the
relative square. -/
abbrev ThickeningFlatLift (ξ : CoherentObject D) {T' : SchemesOver D.Y} (h : ξ.T ⟶ T')
    (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left)) :=
  FlatLift.{u, u + 1, u, u, u + 1, u, u + 1, u}
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) (thickenedModule ξ h)

/-- The map `𝒢' ⟶ i_*𝒢` of a flat lift, with its target read as the direct image of modules
along `i`. -/
def flatLiftπ (M : ThickeningFlatLift ξ h hh) :
    M.module' ⟶
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).pushforwardModules.obj
        (objectToposModule ξ) :=
  M.π

/-- **The comparison `i^*𝒢' ⟶ 𝒢` of a flat lift**: the adjoint transpose of its map
`𝒢' ⟶ i_*𝒢` under `i^* ⊣ i_*`. -/
def flatLiftFibre (M : ThickeningFlatLift ξ h hh) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.obj
      M.module' ⟶ objectToposModule ξ :=
  ((smallEtaleRingedToposHom B S hS
    (D.relativeSquareSituation.relativeMap h)).pullbackAdjPushforwardModulesViaComparison.homEquiv
      _ _).symm (flatLiftπ h hh M)

/-- The unit followed by the direct image of the comparison is the map of the flat lift. -/
theorem unit_comp_map_flatLiftFibre (M : ThickeningFlatLift ξ h hh) :
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).pullbackAdjPushforwardModulesViaComparison.unit.app M.module' ≫
      (smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map
        (flatLiftFibre h hh M) = flatLiftπ h hh M :=
  ((smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
    h)).pullbackAdjPushforwardModulesViaComparison.unit_comp_map_eq_iff
      (flatLiftFibre h hh M) (flatLiftπ h hh M)).2 rfl

/-- **The two cokernels of `I·𝒢' ⟶ 𝒢'` of a flat lift**: the unit `𝒢' ⟶ i_*i^*𝒢'` of the
ideal-product sequence (`Deformation.ToposThickening.idealProductShortComplex_shortExact`) and the
map `𝒢' ⟶ i_*𝒢` of the flat lift. -/
def flatLiftCokernelIso (M : ThickeningFlatLift ξ h hh) :
    (idealProductShortComplex (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      M.module').X₃ ≅ (ShortComplex.mk _ _ M.idealProduct_comp).X₃ :=
  IsColimit.coconePointUniqueUpToIso
    (idealProductShortComplex_shortExact
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) M.module').gIsCokernel
    M.shortExact.gIsCokernel

/-- The identification of the two cokernels carries the unit to the map of the flat lift. -/
theorem unit_comp_flatLiftCokernelIso_hom (M : ThickeningFlatLift ξ h hh) :
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).pullbackAdjPushforwardModulesViaComparison.unit.app M.module' ≫
      (flatLiftCokernelIso h hh M).hom = flatLiftπ h hh M :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (idealProductShortComplex_shortExact
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) M.module').gIsCokernel
    M.shortExact.gIsCokernel WalkingParallelPair.one

/-- **The direct image of the comparison of a flat lift is the identification of the two
cokernels of `I·𝒢' ⟶ 𝒢'`**, both being determined by their composite with the unit, which is an
epimorphism. -/
theorem map_flatLiftFibre_eq (M : ThickeningFlatLift ξ h hh) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map
      (flatLiftFibre h hh M) = (flatLiftCokernelIso h hh M).hom := by
  have : Epi ((smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).pullbackAdjPushforwardModulesViaComparison.unit.app M.module') :=
    epi_pullbackAdjPushforward_unit_app
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) M.module'
  exact (cancel_epi ((smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).pullbackAdjPushforwardModulesViaComparison.unit.app M.module')).1
    ((unit_comp_map_flatLiftFibre h hh M).trans (unit_comp_flatLiftCokernelIso_hom h hh M).symm)

/-- The direct image of the comparison of a flat lift is an isomorphism. -/
theorem isIso_map_flatLiftFibre (M : ThickeningFlatLift ξ h hh) :
    IsIso ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map
        (flatLiftFibre h hh M)) := by
  rw [map_flatLiftFibre_eq]
  exact Iso.isIso_hom _

/-- **The comparison of a flat lift is an isomorphism.** The unit `𝒢' ⟶ i_*i^*𝒢'` and the map
`𝒢' ⟶ i_*𝒢` are both cokernels of the inclusion of the ideal product `I·𝒢'`
(`Deformation.ToposThickening.idealProductShortComplex_shortExact` and the short exact sequence
of the flat lift), so the direct image of the comparison, which carries the first to the second,
is an isomorphism; the direct image along the thickening is fully faithful (Stacks 08M3). -/
theorem isIso_flatLiftFibre (M : ThickeningFlatLift ξ h hh) : IsIso (flatLiftFibre h hh M) := by
  have : IsIso ((D.relativeSquareSituation.relativeMapFirstOrderThickening h
      hh).closedRingedImmersion.hom.pushforwardModules.map (flatLiftFibre h hh M)) :=
    isIso_map_flatLiftFibre h hh M
  exact ((AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_fullyFaithful
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h
      hh).closedRingedImmersion).some).isIso_of_isIso_map _

/-- The lifted module of a flat lift, read as an `𝒪_{X_{T'}}`-module. -/
abbrev flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    Modules.{u, u} B S hS (D.space T').1 (D.space T').2 :=
  M.module'

/-- The comparison of a flat lift, read through the inverse image of `𝒪`-modules along `X_h`
(`AlgebraicGeometry.Space.CoherentSituation.relativeMapPullbackIso`). -/
def flatLiftSpaceFibre (M : ThickeningFlatLift ξ h hh) :
    (modulePullback B S hS (D.relativeMap h)).obj (flatLiftModule h hh M) ⟶ ξ.F :=
  (D.relativeMapPullbackIso h).hom.app (flatLiftModule h hh M) ≫ flatLiftFibre h hh M

/-- The comparison of a flat lift, read through the inverse image along `X_h`, is an
isomorphism. -/
instance isIso_flatLiftSpaceFibre (M : ThickeningFlatLift ξ h hh) :
    IsIso (flatLiftSpaceFibre h hh M) :=
  IsIso.comp_isIso' (Iso.isIso_hom ((D.relativeMapPullbackIso h).app _))
    (isIso_flatLiftFibre h hh M)

/-- Stacks 08VU for the lifted module of a flat lift: it is flat over the base of the strict
relative square, so it is of finite presentation exactly when its inverse image along `X_h` is. -/
theorem isFinitePresentation_iff_flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    (M.module').IsFinitePresentation ↔
      ((smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h)).toRingedToposModulesHom.pullbackModules.obj
          M.module').IsFinitePresentation := by
  have := D.relativeSquareSituation.relBaseBottom_hasSheafCompose_forget h
  have := D.relativeSquareSituation.relBaseBottom_hasWeakSheafify h
  have := D.relativeSquareSituation.relBaseBottom_wEqualsLocallyBijective h
  exact isFinitePresentation_iff_pullbackModules_of_isFlat.{u, u + 1, u, u + 1, u, u, u + 1, u, u,
      u + 1, u}
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h) M.module' M.isFlat
    (D.relativeSquareSituation.isStrict_relativeSquare h hh)

/-- **The lifted module of a flat lift is of finite presentation** (Stacks 08VU, as in the proof
of Stacks 08W7): it is flat over the base of the strict relative square, and its inverse image
along `X_h` is isomorphic to `𝒢`, which is of finite presentation. -/
theorem isFinitePresentation_flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    (M.module').IsFinitePresentation := by
  have := isIso_flatLiftFibre h hh M
  exact (isFinitePresentation_iff_flatLiftModule h hh M).2
    (Stacks.SheafOfModules.Intrinsic.isFinitePresentation_of_iso (asIso (flatLiftFibre h hh M)).symm
      ((SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).1
        ξ.finitePresentation))

/-- The lifted module of a flat lift is of finite presentation on the site. -/
theorem isFinitePresentationOnSite_flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    (flatLiftModule h hh M).IsFinitePresentationOnSite :=
  (SheafOfModules.isFinitePresentationOnSite_iff_isFinitePresentation _).2
    (isFinitePresentation_flatLiftModule h hh M)

/-- The lifted module of a flat lift is quasi-coherent. -/
theorem isQuasicoherentOnSite_flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    (flatLiftModule h hh M).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isFinitePresentation _ (isFinitePresentation_flatLiftModule h hh M)

/-- The lifted module of a flat lift is flat over `T'`: flatness over the base
`(X_{T'}, f'⁻¹𝒪_{T'})` of the relative square is flatness over `T'` (Stacks 05VV). -/
theorem isFlatOver_flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    IsFlatOver B S hS (D.space T').2 (D.projection T').hom (flatLiftModule h hh M) := by
  have := isQuasicoherentOnSite_flatLiftModule h hh M
  exact (isFlatOver_iff_isFlat_restrictScalars B S hS (D.relativeSquareSituation.projection T')
    (flatLiftModule h hh M)).2 ((isFlat_restrictScalars_relBaseRight_iff
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')) M.module').1
      M.isFlat)

/-- **The lifted module of a flat lift has support proper over `T'`**: its inverse image along
`X_h` is isomorphic to `𝒢`, whose support is proper over `T`, and proper support descends along
the thickening `T ⊂ T'`
(`AlgebraicGeometry.Space.hasProperSupport_of_isPullback_of_isThickening`). -/
theorem properSupport_flatLiftModule (M : ThickeningFlatLift ξ h hh) :
    ∃ (hp : IsLocallyOfFiniteType B S hS (D.projection T').hom)
      (hU : IsClosed (D.support T' (flatLiftModule h hh M))),
      IsProperOver B S hS (D.space T').2
        ((schemeSpaceFunctor B S hS).obj T'.left).2 (D.projection T').hom hp
        (D.support T' (flatLiftModule h hh M)) hU := by
  obtain ⟨hp, hU, hpr⟩ := ξ.properSupport
  have hsupp :
      D.support ξ.T ((modulePullback B S hS (D.relativeMap h)).obj (flatLiftModule h hh M)) =
        D.support ξ.T ξ.F :=
    supportOfSheaf_eq_of_iso B S hS (D.space ξ.T) (asIso (flatLiftSpaceFibre h hh M))
  have hF' : HasProperSupport B S hS (D.space ξ.T).2 ((schemeSpaceFunctor B S hS).obj ξ.T.left).2
      (D.projection ξ.T).hom hp
      ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS (D.relativeMap h)).obj
        (flatLiftModule h hh M))) := by
    refine ⟨?_, ?_⟩
    · change IsClosed (D.support ξ.T _)
      rwa [hsupp]
    · change IsProperOver B S hS _ _ _ hp (D.support ξ.T _) _
      simpa only [hsupp] using hpr
  obtain ⟨hcl, hprop⟩ := hasProperSupport_of_isPullback_of_isThickening
    (isPullback_baseChangeMap D.f h) hh.isThickening (isLocallyOfFiniteType_projection D T') hp
    (flatLiftModule h hh M) (isQuasicoherentOnSite_flatLiftModule h hh M)
    (isFiniteTypeOnSite_of_isFinitePresentation _ (isFinitePresentation_flatLiftModule h hh M)) hF'
  exact ⟨isLocallyOfFiniteType_projection D T', hcl, hprop⟩

/-- **The lift of `ξ` attached to a flat lift of `𝒢`** across `X_T ⊂ X_{T'}`. -/
def ThickeningLift.ofFlatLift (M : ThickeningFlatLift ξ h hh) : D.ThickeningLift ξ h where
  F := flatLiftModule h hh M
  quasicoherent := isQuasicoherentOnSite_flatLiftModule h hh M
  finitePresentation := isFinitePresentationOnSite_flatLiftModule h hh M
  flat := isFlatOver_flatLiftModule h hh M
  properSupport := properSupport_flatLiftModule h hh M
  fibre := flatLiftSpaceFibre h hh M
  isIso_fibre := isIso_flatLiftSpaceFibre h hh M

/-- The comparison of the lift of a flat lift, read through the morphism of small étale ringed
topoi, is the comparison of the flat lift. -/
theorem toposFibre_ofFlatLift (M : ThickeningFlatLift ξ h hh) :
    (ThickeningLift.ofFlatLift h hh M).toposFibre = flatLiftFibre h hh M :=
  (D.relativeMapPullbackIso h).inv_hom_id_app_assoc _ _

/-- The flat lift of the lift of a flat lift is isomorphic to it, by the identity of the lifted
module. -/
theorem toFlatLift_ofFlatLift_isIsomorphic (M : ThickeningFlatLift ξ h hh) :
    ((ThickeningLift.ofFlatLift h hh M).toFlatLift h hh).IsIsomorphic M :=
  ⟨Iso.refl _, (Category.id_comp _).trans
    (((ThickeningLift.ofFlatLift h hh M).toThickened_eq h).trans
      ((congrArg (fun φ => (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
            h)).pullbackAdjPushforwardModulesViaComparison.unit.app M.module' ≫
          (smallEtaleRingedToposHom B S hS
            (D.relativeSquareSituation.relativeMap h)).pushforwardModules.map φ)
          (toposFibre_ofFlatLift h hh M)).trans
        (unit_comp_map_flatLiftFibre h hh M))).symm⟩

/-- The comparison of a lift is the adjoint transpose of its map `𝒢' ⟶ i_*𝒢`. -/
theorem toposFibre_eq_homEquiv_symm (L : D.ThickeningLift ξ h) :
    L.toposFibre = ((smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
      h)).pullbackAdjPushforwardModulesViaComparison.homEquiv L.toposModule
        (objectToposModule ξ)).symm (L.toThickened h) :=
  ((smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
    h)).pullbackAdjPushforwardModulesViaComparison.unit_comp_map_eq_iff L.toposFibre
      (L.toThickened h)).1 rfl

/-- The lift of the flat lift of a lift is isomorphic to it, by the identity of the lifted module:
the adjoint transpose of `𝒢' ⟶ i_*i^*𝒢' ⟶ i_*𝒢` is the comparison `i^*𝒢' ⟶ 𝒢`. -/
theorem ofFlatLift_toFlatLift_isIsomorphic (L : D.ThickeningLift ξ h) :
    (ThickeningLift.ofFlatLift h hh (L.toFlatLift h hh)).IsIsomorphic L := by
  refine ⟨Iso.refl _, ?_⟩
  refine (congrArg (· ≫ L.fibre)
    ((modulePullback B S hS (D.relativeMap h)).map_id _)).trans ((Category.id_comp _).trans ?_)
  exact ((D.relativeMapPullbackIso h).hom_inv_id_app_assoc _ _).symm.trans
    (congrArg ((D.relativeMapPullbackIso h).hom.app L.F ≫ ·) (toposFibre_eq_homEquiv_symm h L))

/-- Naturality of the adjoint transpose: a map `κ` is compatible with two maps into the
`G`-images exactly when it is compatible with their transposes. -/
private theorem comp_eq_iff_map_comp_homEquiv_symm_eq {C E : Type*} [Category C] [Category E]
    {F : C ⥤ E} {G : E ⥤ C} (adj : F ⊣ G) {A A' : C} {X : E} (κ : A' ⟶ A) (ψ : A ⟶ G.obj X)
    (ψ' : A' ⟶ G.obj X) :
    κ ≫ ψ = ψ' ↔ F.map κ ≫ (adj.homEquiv A X).symm ψ = (adj.homEquiv A' X).symm ψ' := by
  rw [← adj.homEquiv_naturality_left_symm, EmbeddingLike.apply_eq_iff_eq]

/-- The map `𝒢' ⟶ i_*𝒢` of a lift is natural in the lift: a map of lifted modules compatible
with the comparisons commutes with these maps (naturality of the adjoint transpose). -/
theorem toThickened_naturality {L₁ L₂ : D.ThickeningLift ξ h} (e : L₁.toposModule ⟶ L₂.toposModule)
    (he : (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).toRingedToposModulesHom.pullbackModules.map e ≫ L₂.toposFibre = L₁.toposFibre) :
    e ≫ L₂.toThickened h = L₁.toThickened h := by
  refine (comp_eq_iff_map_comp_homEquiv_symm_eq
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).pullbackAdjPushforwardModulesViaComparison
    e _ _).2 ?_
  rw [← toposFibre_eq_homEquiv_symm, ← toposFibre_eq_homEquiv_symm]
  exact he

/-- Isomorphic lifts have isomorphic flat lifts. -/
theorem toFlatLift_isIsomorphic {L₁ L₂ : D.ThickeningLift ξ h}
    (H : L₁.IsIsomorphic L₂) : (L₁.toFlatLift h hh).IsIsomorphic (L₂.toFlatLift h hh) :=
  ⟨H.choose, toThickened_naturality h H.choose.hom
    (ThickeningLift.toposFibre_naturality H.choose.hom H.choose_spec)⟩

/-- The adjoint transpose of the comparison of a flat lift is its map `𝒢' ⟶ i_*𝒢`. -/
theorem homEquiv_flatLiftFibre (M : ThickeningFlatLift ξ h hh) :
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).pullbackAdjPushforwardModulesViaComparison.homEquiv M.module' (objectToposModule ξ)
        (flatLiftFibre h hh M) =
      flatLiftπ h hh M :=
  Equiv.apply_symm_apply _ _

/-- The comparison of a flat lift is natural in the flat lift (naturality of the adjoint transpose
of `i^* ⊣ i_*`). -/
theorem flatLiftFibre_naturality {M₁ M₂ : ThickeningFlatLift ξ h hh} (κ : M₁.module' ⟶ M₂.module')
    (hκ : κ ≫ flatLiftπ h hh M₂ = flatLiftπ h hh M₁) :
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap
        h)).toRingedToposModulesHom.pullbackModules.map κ ≫
        flatLiftFibre h hh M₂ = flatLiftFibre h hh M₁ := by
  unfold flatLiftFibre
  refine (comp_eq_iff_map_comp_homEquiv_symm_eq
    (smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap h)).pullbackAdjPushforwardModulesViaComparison
    κ _ _).1 ?_
  exact hκ

/-- Isomorphic flat lifts have isomorphic lifts. -/
theorem ofFlatLift_isIsomorphic {M₁ M₂ : ThickeningFlatLift ξ h hh} (H : M₁.IsIsomorphic M₂) :
    (ThickeningLift.ofFlatLift h hh M₁).IsIsomorphic (ThickeningLift.ofFlatLift h hh M₂) :=
  ⟨H.choose, (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ flatLiftFibre h hh M₂)
      ((D.relativeMapPullbackIso h).hom.naturality H.choose.hom)).trans
      ((Category.assoc _ _ _).trans (congrArg ((D.relativeMapPullbackIso h).hom.app _ ≫ ·)
        (flatLiftFibre_naturality h hh H.choose.hom H.choose_spec))))⟩

/-- **The isomorphism classes of lifts of `ξ` across `h` are the isomorphism classes of flat lifts
of `𝒢` across `X_T ⊂ X_{T'}`** (along the base of the relative square), by
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.toFlatLift` and
`AlgebraicGeometry.Space.CoherentSituation.ThickeningLift.ofFlatLift`. -/
def thickeningLiftClassEquiv :
    D.ThickeningLiftClass ξ h ≃
      FlatLiftClass.{u, u + 1, u, u, u + 1, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) (thickenedModule ξ h) where
  toFun := Quotient.map (ThickeningLift.toFlatLift h hh)
    (fun _ _ H => toFlatLift_isIsomorphic h hh H)
  invFun := Quotient.map (ThickeningLift.ofFlatLift h hh)
    (fun _ _ H => ofFlatLift_isIsomorphic h hh H)
  left_inv := by
    rintro ⟨L⟩
    exact Quotient.sound (ofFlatLift_toFlatLift_isIsomorphic h hh L)
  right_inv := by
    rintro ⟨M⟩
    exact Quotient.sound (toFlatLift_ofFlatLift_isIsomorphic h hh M)

/-- The bijection of classes sends the class of a lift to the class of its flat lift. -/
theorem thickeningLiftClassEquiv_mk (L : D.ThickeningLift ξ h) :
    thickeningLiftClassEquiv h hh (Quotient.mk (ThickeningLift.setoid D ξ h) L) =
      (Quotient.mk _ (L.toFlatLift h hh) : FlatLiftClass.{u, u + 1, u, u, u + 1, u, u + 1, u}
        (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
        (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh) (thickenedModule ξ h)) :=
  rfl

/-- A lift of `ξ` across `h` exists exactly when `𝒢` has a flat lift across `X_T ⊂ X_{T'}`. -/
theorem nonempty_thickeningLift_iff :
    Nonempty (D.ThickeningLift ξ h) ↔ Nonempty (ThickeningFlatLift ξ h hh) :=
  ⟨fun ⟨L⟩ => ⟨L.toFlatLift h hh⟩, fun ⟨M⟩ => ⟨ThickeningLift.ofFlatLift h hh M⟩⟩

end AlgebraicGeometry.Space.CoherentSituation

end
