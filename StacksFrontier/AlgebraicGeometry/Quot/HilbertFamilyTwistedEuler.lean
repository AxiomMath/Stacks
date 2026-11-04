/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotCoherentCondition
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerSchemeTheoreticSupport
public import StacksFrontier.AlgebraicGeometry.Quot.QuotHilbertPolynomialBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModulePushforward

/-!
# The twisted Euler characteristics of a family of closed subspaces are intrinsic to the family

Let `(T, 𝓕)` be an object of `Coh_{X/Y}` whose module is `𝓕 = i_*𝒪_W` for a closed subspace
`i : W ⟶ X_T` — for instance the object of a family classified by the Hilbert functor
(Stacks 0D00).  At a point `t ∈ T` its twisted Euler characteristics are computed on the fibre
`W_t ⊆ X_t` of the closed subspace:

`χ(X_t, 𝓕_t ⊗ L_t^{⊗ n}) = χ(W_t, (L^{⊗ n})_t|_{W_t})`,

because `𝓕_t = i_{t,*}𝒪_{W_t}` (Stacks 07U8 for the affine `i`) and the cohomology along an affine
morphism is unchanged (Stacks 0D2U).

## Main definitions

* `AlgebraicGeometry.Space.CoherentObject.closedFibre`: the fibre `W_t ⊆ X_t`.

## Main results

* `AlgebraicGeometry.Space.CoherentObject.closedFibreModuleIso`: `i_{t,*}𝒪_{W_t} ≅ 𝓕_t`.
* `AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_of_closedSubspace`: the twisted Euler
  characteristic is the Euler characteristic on `W_t`.

## References

* [Stacks Project, Tag 0DNF](https://stacks.math.columbia.edu/tag/0DNF)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (A : CoherentObject D) (Z : ClosedSubspaces B S hS (D.space A.T).1) (t : A.testScheme)

/-- **The fibre `W_t ⊆ X_t` of a closed subspace `W ⊆ X_T` over a point `t`**: the inverse image
of `W` along `X_t ⟶ X_T`. -/
def closedFibre : ClosedSubspaces B S hS (A.fibreSpace t).1 :=
  ⟨Z.1.preimage (D.relativeMap (A.pointTestHom t)).hom,
    isClosedSubspace_preimage B S hS _ _ (D.space A.T).2 (A.fibreSpace t).2 Z.2⟩

/-- The map `W_t ⟶ W`. -/
def closedFibreToSubspace :
    closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t) ⟶
      closedSubspaceToSpace B S hS (D.space A.T) Z :=
  ObjectProperty.homMk (Z.1.fromPreimage (D.relativeMap (A.pointTestHom t)).hom)

/-- The square `W_t ⟶ W`, `W_t ⟶ X_t`, `W ⟶ X_T`, `X_t ⟶ X_T` is cartesian. -/
theorem isPullback_closedFibre :
    IsPullback (A.closedFibreToSubspace Z t)
      (closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t))
      (closedSubspaceInclusion B S hS (D.space A.T) Z) (D.relativeMap (A.pointTestHom t)) :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    (Subfunctor.isPullback_preimage _ _)

/-- The inclusion `W ⟶ X` of a closed subspace is an affine morphism. -/
theorem isAffineHom_closedSubspaceInclusion {X : AlgebraicSpaces B S hS}
    (W : ClosedSubspaces B S hS X.1) :
    IsAffineHom B S hS (closedSubspaceInclusion B S hS X W).hom :=
  isAffineHom_of_isClosedImmersion B S hS W.1.ι W.2.2

/-- **The twisted Euler characteristic of an object whose module is `i_*𝒪_W`, on the fibre
`W_t`.**  If the module of an object `(T, 𝓕)` of `Coh_{X/Y}` is the direct image `i_*𝒪_W` of the
structure sheaf of a closed subspace `W ⊆ X_T`, then at a point `t ∈ T`

`χ(X_t, 𝓕_t ⊗ (L^{⊗ n})_t) = χ(W_t, 𝒪_{W_t} ⊗ (L^{⊗ n})_t|_{W_t})`.

`𝓕_t = i_{t,*}𝒪_{W_t}` by Stacks 07U8 for the affine morphism `i`, and the comparison of the
Euler characteristics is
`AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_eulerCharacteristicAlong_closedSubspace`. -/
theorem twistedEuler_eq_of_closedSubspace (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (eZ : A.F ≅ pushforwardStructureSheaf B S hS (D.space A.T) Z) (n : ℤ) :
    twistedEuler L A t n =
      eulerCharacteristicAlong B S hS
        (closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t)).1
        (closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t)).2
        (A.testScheme.residueField t)
        (smallerBaseRingHom B S hS
          (closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t))
          (A.testScheme.residueField t) _ (A.pointSchemeHom' t)
          ((closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t)).hom ≫
            A.fibreProjection t))
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          (smallEtaleRingedSite B S hS
            (closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t)).1
            (closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t)).2).O).obj
            (SheafOfModules.unit _)).obj
          ((modulePullback B S hS
            (closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t))).obj
            (fibreTwist L A t n))) := by
  have hiso := isIso_moduleBaseChangeMap_app_of_isAffineHom (A.isPullback_closedFibre Z t)
    (isAffineHom_closedSubspaceInclusion Z) (SheafOfModules.unit _)
    (SheafOfModules.isQuasicoherentOnSite_unit _)
  let e1 := @asIso _ _ _ _ _ hiso
  let e2 := (modulePushforward B S hS
      (closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t))).mapIso
    (modulePullbackUnitIso B S hS (A.closedFibreToSubspace Z t)).symm
  let e3 := (modulePullback B S hS (D.relativeMap (A.pointTestHom t))).mapIso eZ.symm
  exact twistedEuler_eq_eulerCharacteristicAlong_closedSubspace L A t (A.closedFibre Z t) _
    (SheafOfModules.isQuasicoherentOnSite_unit _) (e2 ≪≫ e1.symm ≪≫ e3) n

/-- The projection `W ⟶ T` of a closed subspace `W ⊆ X_T`. -/
abbrev closedSubspaceProjection :
    closedSubspaceToSpace B S hS (D.space A.T) Z ⟶ (schemeSpaceFunctor B S hS).obj A.T.left :=
  closedSubspaceInclusion B S hS (D.space A.T) Z ≫ D.projection A.T

/-- The square `W_t ⟶ W`, `W_t ⟶ Spec κ(t)`, `W ⟶ T`, `Spec κ(t) ⟶ T` is cartesian. -/
theorem isPullback_closedFibre_pointScheme :
    IsPullback (A.closedFibreToSubspace Z t)
      (closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t) ≫
        D.projection (A.pointTest t))
      (A.closedSubspaceProjection Z) ((schemeSpaceFunctor B S hS).map (A.pointSchemeHom t)) :=
  (A.isPullback_closedFibre Z t).paste_vert (isPullback_baseChangeMap D.f (A.pointTestHom t))

/-- Both ways around the cartesian square `W_t ⟶ W`, `W_t ⟶ X_t`, `W ⟶ X_T`, `X_t ⟶ X_T`
agree after projecting to `X`. -/
private theorem closedFibreToSubspace_comp_projection :
    A.closedFibreToSubspace Z t ≫ (closedSubspaceInclusion B S hS (D.space A.T) Z ≫
        baseChangeProjection D.f A.T) =
      closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t) ≫
        baseChangeProjection D.f (A.pointTest t) :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ baseChangeProjection D.f A.T)
    (A.isPullback_closedFibre Z t).w).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (baseChangeMap_comp_projection D.f (A.pointTestHom t)))))

end AlgebraicGeometry.Space.CoherentObject

namespace AlgebraicGeometry.Space.QuotSituation

open CoherentObject

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D D' : QuotSituation B S hS}
  {T : BigFppfOver B S hS}
  {a : (schemeSpaceFunctor B S hS).obj T ⟶ D.Y} {a' : (schemeSpaceFunctor B S hS).obj T ⟶ D'.Y}
  {K : Subobject (D.baseChangeModule (CostructuredArrow.mk a))}
  (hK : K ∈ D.properlySupportedQuotients (CostructuredArrow.mk a))
  {K' : Subobject (D'.baseChangeModule (CostructuredArrow.mk a'))}
  (hK' : K' ∈ D'.properlySupportedQuotients (CostructuredArrow.mk a'))
  {Z : ClosedSubspaces B S hS (D.space (CostructuredArrow.mk a)).1}
  {Z' : ClosedSubspaces B S hS (D'.space (CostructuredArrow.mk a')).1}
  (eZ : D.quotientModule (CostructuredArrow.mk a) K ≅
    pushforwardStructureSheaf B S hS (D.space (CostructuredArrow.mk a)) Z)
  (eZ' : D'.quotientModule (CostructuredArrow.mk a') K' ≅
    pushforwardStructureSheaf B S hS (D'.space (CostructuredArrow.mk a')) Z')
  (φ : closedSubspaceToSpace B S hS (D.space (CostructuredArrow.mk a)) Z ≅
    closedSubspaceToSpace B S hS (D'.space (CostructuredArrow.mk a')) Z')
  (hφ : φ.hom ≫ (D'.cohObject (CostructuredArrow.mk a') K' hK').closedSubspaceProjection Z' =
    (D.cohObject (CostructuredArrow.mk a) K hK).closedSubspaceProjection Z)

include hφ in
/-- The isomorphism `W_t ≅ W'_t` of the fibres over a point `t` induced by an isomorphism
`W ≅ W'` over `T`. -/
theorem exists_closedFibre_iso (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ E : closedSubspaceToSpace B S hS ((D.cohObject (CostructuredArrow.mk a) K hK).fibreSpace t)
        ((D.cohObject (CostructuredArrow.mk a) K hK).closedFibre Z t) ≅
      closedSubspaceToSpace B S hS ((D'.cohObject (CostructuredArrow.mk a') K' hK').fibreSpace t)
        ((D'.cohObject (CostructuredArrow.mk a') K' hK').closedFibre Z' t),
      E.hom ≫ (D'.cohObject (CostructuredArrow.mk a') K' hK').closedFibreToSubspace Z' t =
          (D.cohObject (CostructuredArrow.mk a) K hK).closedFibreToSubspace Z t ≫ φ.hom ∧
        E.hom ≫ (closedSubspaceInclusion B S hS _ _ ≫
            D'.toCoherentSituation.projection
              ((D'.cohObject (CostructuredArrow.mk a') K' hK').pointTest t)) =
          closedSubspaceInclusion B S hS _ _ ≫
            D.toCoherentSituation.projection
              ((D.cohObject (CostructuredArrow.mk a) K hK).pointTest t) := by
  set A := D.cohObject (CostructuredArrow.mk a) K hK
  set A' := D'.cohObject (CostructuredArrow.mk a') K' hK'
  have sq := A.isPullback_closedFibre_pointScheme Z t
  have sq' := A'.isPullback_closedFibre_pointScheme Z' t
  have sqφ : IsPullback φ.inv (A'.closedSubspaceProjection Z') (A.closedSubspaceProjection Z)
      (𝟙 _) := @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id _)
        ⟨((Iso.inv_comp_eq φ).2 hφ.symm).trans (Category.comp_id _).symm⟩
  have sq'' : IsPullback (A'.closedFibreToSubspace Z' t ≫ φ.inv)
      (closedSubspaceInclusion B S hS (A'.fibreSpace t) (A'.closedFibre Z' t) ≫
        D'.toCoherentSituation.projection (A'.pointTest t))
      (A.closedSubspaceProjection Z) ((schemeSpaceFunctor B S hS).map (A.pointSchemeHom t)) :=
    (Category.comp_id ((schemeSpaceFunctor B S hS).map (A'.pointSchemeHom t))) ▸
      sq'.paste_horiz sqφ
  refine ⟨sq.isoIsPullback _ _ sq'', ?_, sq.isoIsPullback_hom_snd _ _ sq''⟩
  exact (Iso.comp_inv_eq φ).1 ((Category.assoc _ _ _).trans (sq.isoIsPullback_hom_fst _ _ sq''))

include hφ eZ eZ' in
/-- **Isomorphic families of closed subspaces have the same twisted Euler characteristics.**  Let
`(T, i_*𝒪_W)` and `(T, i'_*𝒪_{W'})` be objects of `Coh_{X/Y}` and `Coh_{X'/Y'}` over the same
scheme `T`, given by closed subspaces `W ⊆ X_T` and `W' ⊆ X'_T`, and let `W ≅ W'` be an
isomorphism over `T` carrying the restriction of `L^{⊗ n}` to `W` to the restriction of
`L'^{⊗ n}` to `W'` for every `n`.  Then at every point `t ∈ T` the twisted Euler characteristics
of the two objects agree: both are the Euler characteristics on the fibres `W_t ≅ W'_t`
(`AlgebraicGeometry.Space.CoherentObject.twistedEuler_eq_of_closedSubspace`). -/
theorem twistedEuler_cohObject_eq_of_iso (L : Modules.{u, u} B S hS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D.X.1 D.X.2).O)).property L]
    (L' : Modules.{u, u} B S hS D'.X.1 D'.X.2)
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS D'.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS D'.X.1 D'.X.2).O)).property L']
    (eL : ∀ n : ℤ, (modulePullback B S hS
        (closedSubspaceInclusion B S hS (D.space (CostructuredArrow.mk a)) Z ≫
          D.sourceProjection (CostructuredArrow.mk a))).obj
        (invertibleTensorPower B S hS D.X.1 D.X.2 L n) ≅
      (modulePullback B S hS (φ.hom ≫
        closedSubspaceInclusion B S hS (D'.space (CostructuredArrow.mk a')) Z' ≫
          D'.sourceProjection (CostructuredArrow.mk a'))).obj
        (invertibleTensorPower B S hS D'.X.1 D'.X.2 L' n))
    (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS D.toCoherentSituation L hL
        (D.cohObject (CostructuredArrow.mk a) K hK) t n =
      @CoherentObject.twistedEuler B S hS D'.toCoherentSituation L' hL'
        (D'.cohObject (CostructuredArrow.mk a') K' hK') t n := by
  let hLc : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D.toCoherentSituation.X.1 D.toCoherentSituation.X.2).O)).property L := hL
  let hLc' : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B S hS D'.toCoherentSituation.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
        D'.toCoherentSituation.X.1 D'.toCoherentSituation.X.2).O)).property L' := hL'
  set A := D.cohObject (CostructuredArrow.mk a) K hK
  set A' := D'.cohObject (CostructuredArrow.mk a') K' hK'
  obtain ⟨E, hE1, hE2⟩ := exists_closedFibre_iso hK hK' φ hφ t
  let Zt := closedSubspaceToSpace B S hS (A.fibreSpace t) (A.closedFibre Z t)
  let Z't := closedSubspaceToSpace B S hS (A'.fibreSpace t) (A'.closedFibre Z' t)
  let i := closedSubspaceInclusion B S hS (A.fibreSpace t) (A.closedFibre Z t)
  let i' := closedSubspaceInclusion B S hS (A'.fibreSpace t) (A'.closedFibre Z' t)
  let pt := baseChangeProjection D.f (A.pointTest t)
  let p't := baseChangeProjection D'.f (A'.pointTest t)
  let Ln := invertibleTensorPower B S hS D.X.1 D.X.2 L n
  let L'n := invertibleTensorPower B S hS D'.X.1 D'.X.2 L' n
  -- the two ways around the fibre squares
  have h1 := A.closedFibreToSubspace_comp_projection Z t
  have h1' := A'.closedFibreToSubspace_comp_projection Z' t
  have h2 : E.hom ≫ (i' ≫ p't) = A.closedFibreToSubspace Z t ≫ (φ.hom ≫
      closedSubspaceInclusion B S hS (D'.space (CostructuredArrow.mk a')) Z' ≫
        D'.sourceProjection (CostructuredArrow.mk a')) :=
    (congrArg (E.hom ≫ ·) h1'.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (closedSubspaceInclusion B S hS (D'.space (CostructuredArrow.mk a')) Z' ≫
        D'.sourceProjection (CostructuredArrow.mk a'))) hE1).trans (Category.assoc _ _ _)))
  -- the twists correspond
  let tw : (modulePullback B S hS i).obj (fibreTwist L A t n) ≅
      (modulePullback B S hS E.hom).obj ((modulePullback B S hS i').obj (fibreTwist L' A' t n)) :=
    ((modulePullbackTriangle B S hS rfl).app Ln).symm ≪≫
      (modulePullbackTriangle B S hS h1).app Ln ≪≫
      (modulePullback B S hS (A.closedFibreToSubspace Z t)).mapIso (eL n) ≪≫
      ((modulePullbackTriangle B S hS rfl).app L'n).symm ≪≫
      (modulePullbackTriangle B S hS h2).app L'n ≪≫
      (modulePullback B S hS E.hom).mapIso ((modulePullbackTriangle B S hS rfl).app L'n)
  -- the modules on the fibres correspond
  have hinv' := isInvertible_modulePullback B S hS p't L'n
  let Mm := ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS Z't.1 Z't.2).O).obj (SheafOfModules.unit _)).obj
    ((modulePullback B S hS i').obj (fibreTwist L' A' t n))
  let e := ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS Zt.1 Zt.2).O).obj (SheafOfModules.unit _)).mapIso tw ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor
      (smallEtaleRingedSite B S hS Zt.1 Zt.2).O).mapIso
        (modulePullbackUnitIso B S hS E.hom).symm).app _ ≪≫
    (modulePullbackSheafTensorIso B S hS E.hom _ _).symm
  have hM : Mm.IsQuasicoherentOnSite :=
    @Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isQuasicoherentOnSite.{u + 1, u, u}
      _ _ (smallEtaleRingedSite B S hS Z't.1 Z't.2).J _ _ _
      (smallEtaleRingedSite B S hS Z't.1 Z't.2).O _ _ (SheafOfModules.isQuasicoherentOnSite_unit _)
      (isQuasicoherentOnSite_modulePullback_of_isInvertible i' _ hinv')
  -- the ring maps from `κ(t)` are compatible with `E`
  have hproj : E.inv.hom ≫ (i.hom ≫ A.fibreProjection t) = i'.hom ≫ A'.fibreProjection t :=
    congrArg (fun k => k.hom) ((Iso.inv_comp_eq E).2 hE2.symm)
  have hc : GlobalSectionRingHomsCompatible B S hS E.inv
      (relativelyRepresentable_of_isAffineHom B S hS E.inv (isAffineHom_of_isIso E.inv.hom))
      ((globalSectionsRingHom B S hS Zt.1 Zt.2 (i.hom ≫ A.fibreProjection t)).comp
        (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom)
      ((globalSectionsRingHom B S hS Z't.1 Z't.2 (i'.hom ≫ A'.fibreProjection t)).comp
        (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom) := by
    rw [← hproj]
    exact globalSectionRingHomsCompatible_globalSectionsRingHom B S hS E.inv _
      (i.hom ≫ A.fibreProjection t) (Scheme.ΓSpecIso (.of (A.testScheme.residueField t))).inv.hom
  let : Field ↑(A.testScheme.residueField t) :=
    inferInstanceAs (Field ↑(((BigFppfOver.toScheme B S hS).obj T).residueField t))
  refine (A.twistedEuler_eq_of_closedSubspace Z t L eZ n).trans (Eq.trans ?_
    (A'.twistedEuler_eq_of_closedSubspace Z' t L' eZ' n).symm)
  exact (eulerCharacteristicAlong_congr _ _ _ _ _ _ _ e).trans
    (eulerCharacteristicAlong_modulePullback_of_iso E _ _ _ hc Mm hM)

end AlgebraicGeometry.Space.QuotSituation

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (f' : X' ⟶ Y') (hf' : IsFinitePresentation B S hS f'.hom) {T : BigFppfOver B S hS}
  (x : HilbertFamilyOver f T) (x' : HilbertFamilyOver f' T)

/-- The closed subspace of a Hilbert family over a scheme of the site, as an algebraic space. -/
abbrev HilbertFamilyOver.subspace : AlgebraicSpaces B S hS :=
  closedSubspaceToSpace B S hS (schemeBaseChangeSpace f (CostructuredArrow.mk x.toBase))
    ⟨x.family.Z, x.family.closed⟩

/-- Its inclusion into `X_T`. -/
abbrev HilbertFamilyOver.subspaceInclusion :
    x.subspace ⟶ schemeBaseChangeSpace f (CostructuredArrow.mk x.toBase) :=
  closedSubspaceInclusion B S hS (schemeBaseChangeSpace f (CostructuredArrow.mk x.toBase))
    ⟨x.family.Z, x.family.closed⟩

/-- **Isomorphic Hilbert families have the same twisted Euler characteristics.**  Two families
`W ⊆ X_T` and `W' ⊆ X'_T` classified by the Hilbert functors of `f : X ⟶ Y` and `f' : X' ⟶ Y'`
over the same scheme `T`, with an isomorphism `W ≅ W'` over `T` carrying the restriction of
`L^{⊗ n}` to the restriction of `L'^{⊗ n}` for every `n`, have the same twisted Euler
characteristics at every point of `T`, hence the same Hilbert polynomials. -/
theorem twistedEuler_hilbertCohObject_eq_of_iso
    (φ : x.subspace ≅ x'.subspace)
    (hφ : φ.hom ≫ x'.subspaceInclusion ≫ schemeBaseChangeProjectionHom B S hS f'
        (CostructuredArrow.mk x'.toBase) =
      x.subspaceInclusion ≫ schemeBaseChangeProjectionHom B S hS f (CostructuredArrow.mk x.toBase))
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
    (L' : Modules.{u, u} B S hS X'.1 X'.2)
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property L']
    (eL : ∀ n : ℤ, (modulePullback B S hS (x.subspaceInclusion ≫
        (ObjectProperty.homMk (pullback.fst f.hom x.toBase) :
          schemeBaseChangeSpace f (CostructuredArrow.mk x.toBase) ⟶ X))).obj
        (invertibleTensorPower B S hS X.1 X.2 L n) ≅
      (modulePullback B S hS (φ.hom ≫ x'.subspaceInclusion ≫
        (ObjectProperty.homMk (pullback.fst f'.hom x'.toBase) :
          schemeBaseChangeSpace f' (CostructuredArrow.mk x'.toBase) ⟶ X'))).obj
        (invertibleTensorPower B S hS X'.1 X'.2 L' n))
    (t : (BigFppfOver.toScheme B S hS).obj T) (n : ℤ) :
    @CoherentObject.twistedEuler B S hS (structureSheafQuotSituation f hf).toCoherentSituation L hL
        (hilbertCohObject f hf x) t n =
      @CoherentObject.twistedEuler B S hS (structureSheafQuotSituation f' hf').toCoherentSituation
        L' hL' (hilbertCohObject f' hf' x') t n :=
  @QuotSituation.twistedEuler_cohObject_eq_of_iso B S hS (structureSheafQuotSituation f hf)
    (structureSheafQuotSituation f' hf') T (ObjectProperty.homMk x.toBase)
    (ObjectProperty.homMk x'.toBase) _
    (hilbertFamilySubobject_mem f hf (CostructuredArrow.mk x.toBase) x.family) _
    (hilbertFamilySubobject_mem f' hf' (CostructuredArrow.mk x'.toBase) x'.family) _ _
    (hilbertFamilyQuotientIso f hf (CostructuredArrow.mk x.toBase) x.family)
    (hilbertFamilyQuotientIso f' hf' (CostructuredArrow.mk x'.toBase) x'.family) φ hφ L hL L' hL'
    eL t n

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An isomorphism of the inverse images of two invertible modules gives isomorphisms of the
inverse images of all their tensor powers.** -/
def modulePullbackInvertibleTensorPowerCongr {W X X' : AlgebraicSpaces B S hS} (p : W ⟶ X)
    (p' : W ⟶ X') (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property L]
    (L' : Modules.{u, u} B S hS X'.1 X'.2)
    [hL' : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X'.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X'.1 X'.2).O)).property L']
    (e : (modulePullback B S hS p).obj L ≅ (modulePullback B S hS p').obj L') (n : ℤ) :
    (modulePullback B S hS p).obj (invertibleTensorPower B S hS X.1 X.2 L n) ≅
      (modulePullback B S hS p').obj (invertibleTensorPower B S hS X'.1 X'.2 L' n) :=
  haveI := stacksIsInvertible_modulePullback_obj B S hS p L
  haveI := stacksIsInvertible_modulePullback_obj B S hS p' L'
  modulePullbackInvertibleTensorPowerIso B S hS p L n ≪≫
    invertibleTensorPowerCongr B S hS W.1 W.2 e n ≪≫
    (modulePullbackInvertibleTensorPowerIso B S hS p' L' n).symm

end AlgebraicGeometry.Space

end
