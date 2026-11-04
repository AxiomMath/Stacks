module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EtaleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SectionsProjectionUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackLocallyFree
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperFlatSingleDegreeRankLocus
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapLocal
public import StacksFrontier.Homology.Tor.StandardModelExtensionScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTensorSingleSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsOfLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.FlatPullbackSectionsHomotopyColimit

/-!
# The canonical map `RΓ(U, K) ⊗^𝐋_A Aₙ ⟶ RΓ(Uₙ, Fₙ)` of [Stacks, Tag 0CX8]

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], with its
canonical map `φ : K ⟶ (iₙ,* Fₙ)[0]` (`FlatSheafExistenceSituation.derivedLimitProjection`), and
let `j : U ⟶ X` be étale. Put `Uₙ = U ×_X Xₙ`, with projections `i'ₙ : Uₙ ⟶ U` and
`jₙ : Uₙ ⟶ Xₙ`. Write `RΓ_A(U, -)` for the derived sections of a space over `Spec A`, in
`D(Γ(Spec A, 𝒪))`, and `RΓ_{Aₙ}(Uₙ, -)` for those of a space over `Spec Aₙ`.

The **canonical map of [Stacks, Tag 0CX8]** is

`c_U : RΓ_A(U, Lj^*K) ⊗^𝐋_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Ljₙ^*(Fₙ[0]))`,

the adjoint, under `- ⊗^𝐋_A Aₙ ⊣` restriction of scalars, of `RΓ_A(U, Lj^*φ)` followed by the
identification `RΓ_A(U, Lj^*((iₙ,* Fₙ)[0])) ⟶ RΓ_{Aₙ}(Uₙ, Ljₙ^*(Fₙ[0]))` through `X` and `Xₙ`, for
`j` quasi-compact and quasi-separated: the inverse of the projection formula at the unit
`RΓ_A(X, Rj_*𝒪_U ⊗^𝐋 -) ≅ RΓ_A(U, Lj^* -)` ([Stacks, Tag 08IN]), the identification `ψ` of
`RΓ_A(X, Rj_*𝒪_U ⊗^𝐋 (iₙ,* Fₙ)[0])` with `RΓ_{Aₙ}(Xₙ, Liₙ^*Rj_*𝒪_U ⊗^𝐋 Fₙ[0])`, the base change
map `Liₙ^*Rj_*𝒪_U ⟶ Rjₙ,*𝒪_{Uₙ}` of the cartesian square `Uₙ = U ×_X Xₙ` ([Stacks, Tag 08IR]) and
the projection formula at the unit for `jₙ`. This is the route of the source's proof, which
computes `RΓ(U, -)` on `X` through `Rj_*𝒪_U`. It is the instance at the situation of
`AlgebraicGeometry.Space.etaleTensorSectionsBaseChangeMap`, defined over variable spaces.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.etaleStage`: `Uₙ = U ×_X Xₙ`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.etaleStageBaseChangeMap`: `c_U`.

## Main results

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.isIso_etaleStageBaseChangeMap_of_isIso`:
  `c_U` is an isomorphism as soon as the maps of [Stacks, Tag 0CX6] (1) at level `n` are.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)
  {U : AlgebraicSpaces D.B D.S D.containsLimitBase} (j : U ⟶ D.X.left)

/-! ### The stage `Uₙ = U ×_X Xₙ` -/

/-- `Uₙ = U ×_X Xₙ`. -/
abbrev etaleStage : AlgebraicSpaces D.B D.S D.containsLimitBase :=
  AlgebraicSpaces.fiberProduct D.B D.S D.containsLimitBase j (D.closedImmersion n)

/-- The projection `i'ₙ : Uₙ ⟶ U`. -/
abbrev etaleStageProjection : D.etaleStage n j ⟶ U :=
  ObjectProperty.homMk (pullback.fst j.hom (D.closedImmersion n).hom)

/-- The projection `jₙ : Uₙ ⟶ Xₙ`. -/
abbrev etaleStageInclusion : D.etaleStage n j ⟶ D.stage n :=
  ObjectProperty.homMk (pullback.snd j.hom (D.closedImmersion n).hom)

/-- `Uₙ = U ×_X Xₙ` is cartesian, in the orientation of the base change map
`Lj^* Riₙ,* ⟶ Ri'ₙ,* Ljₙ^*`. -/
theorem isPullback_etaleStage :
    IsPullback (D.etaleStageInclusion n j) (D.etaleStageProjection n j) (D.closedImmersion n) j :=
  (AlgebraicSpaces.isPullback_fiberProduct D.B D.S D.containsLimitBase j
    (D.closedImmersion n)).flip

/-- The square `Uₙ ⟶ U ⟶ Spec A = Uₙ ⟶ Xₙ ⟶ Spec Aₙ ⟶ Spec A` commutes. -/
theorem etaleStageProjection_comp :
    D.etaleStageProjection n j ≫ (j ≫ D.X.hom) =
      (D.etaleStageInclusion n j ≫ D.stageToBase n) ≫
        representedSpaceMap D.B D.S D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n) := by
  rw [← Category.assoc, ← (D.isPullback_etaleStage n j).w, Category.assoc,
    D.closedImmersion_comp_hom n]
  exact (Category.assoc _ _ _).symm

/-! ### The canonical map `c_U` -/

/-- **The canonical map `c_U : RΓ_A(U, Lj^*K) ⊗^𝐋_A Aₙ ⟶ RΓ_{Aₙ}(Uₙ, Ljₙ^*(Fₙ[0]))`** of
[Stacks, Tag 0CX8], for `K = DQ_X(L)` and `j` quasi-compact and quasi-separated: the adjoint,
under `- ⊗^𝐋_A Aₙ ⊣` restriction of scalars, of `RΓ_A(U, Lj^*φ)` followed by the identification
`RΓ_A(U, Lj^*((iₙ,* Fₙ)[0])) ⟶ RΓ_{Aₙ}(Uₙ, Ljₙ^*(Fₙ[0]))` through `X` and `Xₙ`
(`AlgebraicGeometry.Space.etaleTensorSectionsBaseChangeMap`), where
`φ = D.derivedLimitProjection adj p n : K ⟶ (iₙ,* Fₙ)[0]`. -/
abbrev etaleStageBaseChangeMap (hjqc : IsQuasiCompact D.B D.S D.containsLimitBase j.hom)
    (hjqs : IsQuasiSeparated D.B D.S D.containsLimitBase j.hom)
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) :=
  etaleTensorSectionsBaseChangeMap D.B D.S D.containsLimitBase
    (T := limitBaseObject D.system D.B D.containsLimitBase)
    (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₀ := D.stage n) (U := U) (U₀ := D.etaleStage n j) D.X.hom
    (D.stageToBase n) (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
    (D.F n) (D.isQuasicoherentOnSite_F n) j (D.etaleStageInclusion n j)
    (D.etaleStageProjection n j) (D.isPullback_etaleStage n j).flip.w hjqc hjqs
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite D.B D.S D.containsLimitBase
      (D.pushforwardModule n) (D.isQuasicoherentOnSite_pushforwardModule n))
    (D.derivedLimitProjection adj p n)

/-- `stageTensorSectionsNatTransOf` is the instance of `tensorSingleSectionsNatTrans` at the
situation. -/
theorem stageTensorSectionsNatTransOf_eq_tensorSingleSectionsNatTrans
    (H : Modules.{u, u} D.B D.S D.containsLimitBase (D.stage n).1 (D.stage n).2)
    (hH : H.IsQuasicoherentOnSite) :
    D.stageTensorSectionsNatTransOf n H hH =
      tensorSingleSectionsNatTrans D.B D.S D.containsLimitBase
        (U := limitBaseObject D.system D.B D.containsLimitBase)
        (U₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
        (X := D.X.left) (X₀ := D.stage n) D.X.hom (D.stageToBase n)
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
        (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
        H hH :=
  rfl

/-- `stageTensorSectionsMap` is the component of the instance of `tensorSingleSectionsNatTrans`
at the situation. -/
theorem stageTensorSectionsMap_eq_tensorSingleSectionsNatTrans_app
    (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) :
    D.stageTensorSectionsMap n E =
      (tensorSingleSectionsNatTrans D.B D.S D.containsLimitBase
        (U := limitBaseObject D.system D.B D.containsLimitBase)
        (U₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
        (X := D.X.left) (X₀ := D.stage n) D.X.hom (D.stageToBase n)
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
        (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
        (D.F n) (D.isQuasicoherentOnSite_F n)).app E :=
  congrArg (fun α => NatTrans.app α E) ((D.stageTensorSectionsNatTrans_eq_natTransOf n).trans
    (D.stageTensorSectionsNatTransOf_eq_tensorSingleSectionsNatTrans n _ _))

/-- The structure maps of `X` and `U` to `Spec A` are of finite presentation, for `j : U ⟶ X`
étale with `U` quasi-compact and quasi-separated. -/
private theorem isFinitePresentation_toBase_of_isEtale
    (hj : IsEtale D.B D.S D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B D.S D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal U.1) :
    IsFinitePresentation D.B D.S D.containsLimitBase
        (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left).hom ∧
      IsFinitePresentation D.B D.S D.containsLimitBase
        (DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase U).hom := by
  have hX : D.X.hom = DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase D.X.left :=
    ObjectProperty.hom_ext _
      ((isTerminal_yoneda_obj_base D.B (limitBase D.system) D.containsLimitBase).hom_ext _ _)
  have hU : j ≫ D.X.hom = DerivedChow.toBase D.B (limitBase D.system) D.containsLimitBase U :=
    ObjectProperty.hom_ext _
      ((isTerminal_yoneda_obj_base D.B (limitBase D.system) D.containsLimitBase).hom_ext _ _)
  have hXfp := D.finitePresentation
  rw [hX] at hXfp
  have hUfp := D.isFinitePresentation_comp_hom_of_isEtale j hj hUqc hUqs
  rw [hU] at hUfp
  exact ⟨hXfp, hUfp⟩

/-- **An étale `j : U ⟶ X` with `U` quasi-compact and quasi-separated is quasi-compact and
quasi-separated**: `U` and `X` are of finite presentation over `A`. -/
theorem isQuasiCompact_isQuasiSeparated_of_isEtale
    (hj : IsEtale D.B D.S D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B D.S D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal U.1) :
    IsQuasiCompact D.B D.S D.containsLimitBase j.hom ∧
      IsQuasiSeparated D.B D.S D.containsLimitBase j.hom := by
  obtain ⟨hXfp, hUfp⟩ := D.isFinitePresentation_toBase_of_isEtale j hj hUqc hUqs
  exact isQuasiCompact_isQuasiSeparated_of_isFinitePresentation_toBase
    D.B (A := ((limit D.system : CommRingCat) : Type u)) D.containsLimitBase j hXfp hUfp

/-- **`c_U` is an isomorphism, given [Stacks, Tag 0CX6] (1) at level `n`**: for `j : U ⟶ X` étale
with `U` quasi-compact and quasi-separated, if `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ)`
(`limitTensorSectionsBaseChangeMap`) is invertible for every perfect `E`, then so is `c_U`. The
input from [Stacks, Tag 0CRW] is a presentation `Rj_*𝒪_U = hocolim Eₘ` by perfect objects
(`exists_isHomotopyColimit_isPerfect_derivedPushforward_of_isFlat`); the comparison is
`isIso_etaleTensorSectionsBaseChangeMap`. -/
theorem isIso_etaleStageBaseChangeMap_of_isIso (hj : IsEtale D.B D.S D.containsLimitBase j.hom)
    (hUqc : IsQuasiCompactSpace D.B D.S D.containsLimitBase U.1)
    (hUqs : IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal U.1)
    (hjqc : IsQuasiCompact D.B D.S D.containsLimitBase j.hom)
    (hjqs : IsQuasiSeparated D.B D.S D.containsLimitBase j.hom)
    {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
      (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
    (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
    {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
    (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)
    (h0CX6 : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n)) :
    IsIso (D.etaleStageBaseChangeMap n j hjqc hjqs adj p) := by
  have hhqc : IsQuasiCompact D.B D.S D.containsLimitBase D.X.hom.hom := D.finitePresentation.2.1
  have hhqs : IsQuasiSeparated D.B D.S D.containsLimitBase D.X.hom.hom := D.finitePresentation.2.2
  obtain ⟨hXfp, hUfp⟩ := D.isFinitePresentation_toBase_of_isEtale j hj hUqc hUqs
  obtain ⟨E, hE, hP⟩ := exists_isHomotopyColimit_isPerfect_derivedPushforward_of_isFlat
    D.B (A := ((limit D.system : CommRingCat) : Type u)) D.containsLimitBase j hXfp hUfp
    (isFlat_of_isEtale D.B (limitBase D.system) D.containsLimitBase hj)
  have := hP.hasCoproduct
  obtain ⟨c, hc⟩ := hP.exists_isHomotopyColimitCocone
  have sqX := AlgebraicSpaces.isPullback_hom D.B D.S D.containsLimitBase
    (isPullback_spaceAt D.system D.B D.containsLimitBase D.containsBaseAt D.X n).flip
  have sqU := AlgebraicSpaces.isPullback_hom D.B D.S D.containsLimitBase
    (D.isPullback_etaleStage n j).flip
  exact isIso_etaleTensorSectionsBaseChangeMap D.B D.S D.containsLimitBase
    (T := limitBaseObject D.system D.B D.containsLimitBase)
    (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₀ := D.stage n) (U := U) (U₀ := D.etaleStage n j) D.X.hom
    (D.stageToBase n) (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
    (D.F n) (D.isQuasicoherentOnSite_F n) j (D.etaleStageInclusion n j)
    (D.etaleStageProjection n j) hjqc hjqs
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite D.B D.S D.containsLimitBase
      (D.pushforwardModule n) (D.isQuasicoherentOnSite_pushforwardModule n))
    (D.derivedLimitProjection adj p n) (D.isPullback_etaleStage n j).flip hhqc hhqs
    (isQuasiCompact_of_isPullback D.B D.S D.containsLimitBase sqX hhqc)
    (isQuasiSeparated_of_isPullback D.B D.S D.containsLimitBase sqX hhqs)
    (isQuasiCompact_of_isPullback D.B D.S D.containsLimitBase sqU hjqc)
    (isQuasiSeparated_of_isPullback D.B D.S D.containsLimitBase sqU hjqs)
    (torIndependent_of_isFlat_left j (D.closedImmersion n)
      (isFlat_of_isEtale D.B D.S D.containsLimitBase hj))
    (DQ.obj L).property E hE c hP.hasCoproduct hc fun m => by
      have h := h0CX6 _ (hE m)
      dsimp only [limitTensorSectionsBaseChangeMap] at h
      rw [stageTensorSectionsMap_eq_tensorSingleSectionsNatTrans_app] at h
      exact (congrArg IsIso (tensorSingleSectionsBaseChangeMap_eq D.B D.S D.containsLimitBase
        (T := limitBaseObject D.system D.B D.containsLimitBase)
        (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
        (X := D.X.left) (X₀ := D.stage n) D.X.hom (D.stageToBase n)
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
        (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
        (D.F n) (D.isQuasicoherentOnSite_F n) (D.derivedLimitProjection adj p n) (E.obj m))).mpr h

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
