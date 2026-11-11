module

public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.BaseObjectAtAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceEtaleStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedAffineAtlasConservative
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# In Situation 0DIK, `τₙ` is invertible once it is on the sections over an affine atlas

In Situation [Stacks, Tag 0DIK] let `K = DQ_X(R lim Kₙ)` be as in [Stacks, Tag 0DIL] and
`τₙ : Ljₙ^* K ⟶ Kₙ` the adjoint of the projection `K ⟶ Rjₙ,* Kₙ`. For `U` affine and
`j : U ⟶ X` étale and surjective, with `Uₙ = Xₙ ×_X U`, if `RΓ(Uₙ, τₙ|_{Uₙ})` is an isomorphism
in `D(Aₙ)`, then `τₙ` is an isomorphism.

## Main results

* `SeparatedDerivedExistenceSystem.isIso_coheratorLimitPullbackMap_of_isIso_etaleStage`: `τₙ` is
  invertible if its restriction to `Uₙ` is on `RΓ(Uₙ, -)`, for one affine `U` étale and
  surjective over `X`.
* `SeparatedDerivedExistenceSystem.isIso_coheratorLimitPullbackMap_of_forall_isAffineSpace`: every
  `τₙ`
  is invertible if it is on `RΓ(Uₙ, -)` for every affine `U` étale over `X`.

## References

* [Stacks Project, Tag 0DIQ](https://stacks.math.columbia.edu/tag/0DIQ)
* [Stacks Project, Tag 0DIP](https://stacks.math.columbia.edu/tag/0DIP)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GrothendieckExistence (limitBase baseAt)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

section Coherator

variable (DQ : spaceDerivedCategory D.B (limitBase D.system) D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).FullSubcategory)
  (adj : (spaceQuasicoherentProp D.B (limitBase D.system) D.containsLimitBase D.X.left).ι ⊣ DQ)

/-- Let `j : U ⟶ X` be étale and surjective with `U` affine, and `Uₙ = Xₙ ×_X U`. If
`RΓ(Uₙ, τₙ|_{Uₙ})`, the derived sections over `Spec Aₙ` of the restriction of
`τₙ : Ljₙ^* K ⟶ Kₙ` to `Uₙ`, is an isomorphism, then so is `τₙ`. -/
theorem isIso_coheratorLimitPullbackMap_of_isIso_etaleStage (n : ℕ)
    {U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase} (j : U ⟶ D.X.left)
    (hj : IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hjs : IsSurjective D.B (limitBase D.system) D.containsLimitBase j.hom)
    (hU : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase U.1)
    (h : IsIso ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
        (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
      ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageBaseProjection j n)).map
        ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
          (D.etaleStageToStage j n)).map (D.coheratorLimitPullbackMap DQ adj n))))) :
    IsIso (D.coheratorLimitPullbackMap DQ adj n) := by
  have hf : IsAffineHom D.B (limitBase D.system) D.containsLimitBase
      (D.etaleStageBaseProjection j n).hom :=
    isAffineHom_of_isPullback' D.B (limitBase D.system) D.containsLimitBase
      (AlgebraicSpaces.isPullback_hom D.B (limitBase D.system) D.containsLimitBase
        (D.isPullback_etaleStage_base j n))
      (AlgebraicGeometry.Space.isAffineHom_of_isAffineSpace D.B (limitBase D.system)
        D.containsLimitBase _ hU
        (isAffineSpace_yoneda D.B (limitBase D.system) D.containsLimitBase _
          D.isAffine_limitBaseObject))
  exact isIso_of_isIso_representedAffineDerivedSections_map (D.etaleStageToStage j n)
    (D.isEtale_etaleStageToStage hj n)
    (isSurjective_of_isPullback D.B (limitBase D.system) D.containsLimitBase
      (D.isPullback_etaleStage j n).flip hjs)
    (D.etaleStageBaseProjection j n) hf _
    (derivedQuasicoherent_smallEtaleDerivedModulePullback D.B (limitBase D.system)
      D.containsLimitBase
      (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) _
      (D.coheratorLimit DQ).property)
    (D.isQuasicoherentOnSite_homology_K n) h

/-- If `RΓ(Uₙ, τₙ|_{Uₙ})` is an isomorphism for every affine `U` étale over `X`, then every `τₙ`
is an isomorphism. -/
theorem isIso_coheratorLimitPullbackMap_of_forall_isAffineSpace
    (h : ∀ (n : ℕ) (U : AlgebraicSpaces D.B (limitBase D.system) D.containsLimitBase)
      (j : U ⟶ D.X.left), IsEtale D.B (limitBase D.system) D.containsLimitBase j.hom →
      IsAffineSpace D.B (limitBase D.system) D.containsLimitBase U.1 →
      IsIso ((representedAffineDerivedSections D.B (limitBase D.system) D.containsLimitBase
          (baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)).map
        ((derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
            (D.etaleStageBaseProjection j n)).map
          ((smallEtaleDerivedModulePullback D.B (limitBase D.system) D.containsLimitBase
            (D.etaleStageToStage j n)).map (D.coheratorLimitPullbackMap DQ adj n)))))
    (n : ℕ) : IsIso (D.coheratorLimitPullbackMap DQ adj n) := by
  obtain ⟨U, f, hUaff, hfsurj, hfet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover D.B (limitBase D.system)
      D.containsLimitBase D.X.left.1 D.X.left.2).mp D.isQuasiCompactSpace_X
  let j : schemeSpace U ⟶ D.X.left := ObjectProperty.homMk f
  have hU : IsAffineSpace D.B (limitBase D.system) D.containsLimitBase (schemeSpace U).1 :=
    isAffineSpace_yoneda D.B (limitBase D.system) D.containsLimitBase U hUaff
  exact D.isIso_coheratorLimitPullbackMap_of_isIso_etaleStage DQ adj n j hfet
    ((presheafSurjective_iff_isSurjective_yoneda D.B (limitBase D.system) D.containsLimitBase
      D.X.left.1 D.X.left.2 U f).1 hfsurj) hU (h n _ j hfet hU)

end Coherator

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
