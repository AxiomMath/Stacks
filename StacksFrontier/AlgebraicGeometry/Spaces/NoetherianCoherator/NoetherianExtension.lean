module

public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.DerivedPushforwardBound
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianCoherator.InjectiveAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedAcyclicPushforward
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# The coherator for Noetherian algebraic spaces: the derived extension of the direct image

Let `f : X ⟶ Y` be a morphism of Noetherian algebraic spaces over a scheme `S`.  This file proves
**Stacks 09TM**: the direct image `f_*` on quasi-coherent modules has a right derived extension
`Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` such that the square

`D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X)`,   `Φ` down the left, `Rf_*` down the right,
`D(QCoh(𝒪_Y)) ⟶ D_QCoh(𝒪_Y)`

with the comparison functors of Stacks 08F1 as horizontal arrows, commutes.

The proof is the source's.  `X` and `Y` being Noetherian, `f` is quasi-compact and
quasi-separated (Stacks 073B), so `f_*` preserves quasi-coherence (Stacks 03M9);
`QCoh(𝒪_X)` is Grothendieck abelian (Stacks 077V), so `Φ` exists and is computed on K-injective
complexes with injective terms (Stacks 079P); this is
`AlgebraicGeometry.Space.quasicoherentPushforwardExtension`.  The square then reduces
(`AlgebraicGeometry.Space.quasicoherentPushforwardExtensionComparison`) to the invertibility of
`f_* I ⟶ Rf_* I` at complexes `I` with injective terms.  Those terms are right acyclic for `f_*`
by Stacks 09TL (2) (`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_injective`),
and `Rf_*` has bounded cohomological amplitude on `D_QCoh` by Stacks 08FA
(`AlgebraicGeometry.Space.exists_isLE_rightDerivedFunctor_obj_modulePushforward`); these are the
two inputs of
`AlgebraicGeometry.Space.isIso_to_rightDerived_of_termwise_acyclic` (Stacks 015E for unbounded
complexes).

## Main results

* `AlgebraicGeometry.Space.pushforwardPreservesQuasicoherence_of_isNoetherian`.
* `AlgebraicGeometry.Space.isIso_app_quotient_of_termwise_injective_of_isNoetherian`: the
  comparison `f_* I ⟶ Rf_* I` is invertible at every complex of quasi-coherent modules with
  injective terms.
* `AlgebraicGeometry.Space.exists_quasicoherentPushforwardExtension_comparison`: **Stacks 09TM**.

## Implementation notes

The comparison functors of Stacks 08F1,
`AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse`, are stated in the standard
model of the derived categories, which is why that model is installed here, as in the file of
Stacks 08F1.  The square is stated after the fully faithful inclusion `D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)`, for
an arbitrary right derived functor `Rf_*` of the direct image of all modules.

## References

* [Stacks Project, Tag 09TM](https://stacks.math.columbia.edu/tag/09TM)
* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 08FA](https://stacks.math.columbia.edu/tag/08FA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The direct image along a morphism of Noetherian algebraic spaces preserves quasi-coherence:
the morphism is quasi-compact and quasi-separated (Stacks 073B), so Stacks 03M9 applies. -/
theorem pushforwardPreservesQuasicoherence_of_isNoetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (hX : IsNoetherian B S hS hZ X.1)
    (hY : IsNoetherian B S hS hZ Y.1) (f : X ⟶ Y) :
    PushforwardPreservesQuasicoherence B S hS f := fun F hF =>
  isQuasicoherentOnSite_modulePushforward_of_qcqs B S hS f
    (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hY.2.1 hX.1 f.hom)
    (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hX.2.1 f.hom) F hF

/-- **Complexes of injective quasi-coherent modules compute the derived direct image** along a
morphism of Noetherian algebraic spaces: for every right derived functor `Rf_*` of the direct
image of all modules, the comparison `f_* I ⟶ Rf_* I` is invertible at every complex `I` of
quasi-coherent `𝒪_X`-modules whose terms are injective objects of `QCoh(𝒪_X)`. -/
theorem isIso_app_quotient_of_termwise_injective_of_isNoetherian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS}
    (hX : IsNoetherian B S hS hZ X.1) (hY : IsNoetherian B S hS hZ Y.1) (f : X ⟶ Y)
    (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
    (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))]
    (K : CochainComplex (QuasicoherentSheaves.{u, u} B S hS X.1 X.2) ℤ)
    (hK : ∀ n, Injective (K.X n)) :
    IsIso (α.app ((HomotopyCategory.quotient (Modules.{u, u} B S hS X.1 X.2)
      (ComplexShape.up ℤ)).obj
        (((quasicoherentSheavesι B S hS X).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))) := by
  obtain ⟨N, hN⟩ := exists_isLE_rightDerivedFunctor_obj_modulePushforward B S hS f hZ hX.1 hX.2.1
    hY.1 hY.2.1
  have := preservesFiniteLimits_modulePushforward B S hS f
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  have := enoughInjectives_modules B S hS X.1 X.2
  refine isIso_to_rightDerived_of_termwise_acyclic B S hS f _ (fun n => (K.X n).2)
    (fun n => ?_) RF α N (fun E d hE hd => hN RF α inferInstance E hE d hd)
  refine (Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat _ _).2 fun m hm => ?_
  obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
  exact isZero_rightDerived_modulePushforward_of_injective B S hS hZ hX f hY.1 hY.2.1 (K.X n)
    (hK n) p

/-- **Stacks 09TM.**  Let `f : X ⟶ Y` be a morphism of Noetherian algebraic spaces over `S`.
Then `f_*` on quasi-coherent modules has a right derived extension
`Φ : D(QCoh(𝒪_X)) ⥤ D(QCoh(𝒪_Y))` — the total right derived functor
`AlgebraicGeometry.Space.quasicoherentPushforwardExtension` of `f_* : QCoh(𝒪_X) ⥤ QCoh(𝒪_Y)`,
with derivation unit `AlgebraicGeometry.Space.quasicoherentPushforwardExtensionUnit` — such that
the square formed with the comparison functors `D(QCoh) ⥤ D_QCoh` of Stacks 08F1 and with `Rf_*`
commutes: for every right derived functor `Rf_*` of the direct image of all modules, the two
composites `D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_Y) ⊆ D(𝒪_Y)` are isomorphic. -/
@[stacks 09TM]
theorem exists_quasicoherentPushforwardExtension_comparison (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (hX : IsNoetherian B S hS hZ X.1)
    (hY : IsNoetherian B S hS hZ Y.1) (f : X ⟶ Y) :
    ∃ hpush : PushforwardPreservesQuasicoherence B S hS f,
      (quasicoherentPushforwardExtension B S hS f hpush).IsRightDerivedFunctor
          (quasicoherentPushforwardExtensionUnit B S hS f hpush)
          (HomotopyCategory.quasiIso (QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
            (ComplexShape.up ℤ)) ∧
        ∀ (RF : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
            DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))
          (α : (modulePushforward B S hS f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF),
          RF.IsRightDerivedFunctor α
              (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) →
            Nonempty (quasicoherentDerivedComparisonSchemeUniverse B S hS X.1 X.2 ⋙
                (DerivedCategoryB.derivedCategoryB
                  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                    (Stacks.SheafOfModules.Tensor.ringSheaf
                      (smallEtaleRingedSite B S hS X.1 X.2).O))).ι ⋙ RF ≅
              quasicoherentPushforwardExtension B S hS f hpush ⋙
                quasicoherentDerivedComparisonSchemeUniverse B S hS Y.1 Y.2 ⋙
                  (DerivedCategoryB.derivedCategoryB
                    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                      (Stacks.SheafOfModules.Tensor.ringSheaf
                        (smallEtaleRingedSite B S hS Y.1 Y.2).O))).ι) := by
  refine ⟨pushforwardPreservesQuasicoherence_of_isNoetherian B S hS hZ hX hY f, inferInstance,
    fun RF α _ => ⟨quasicoherentPushforwardExtensionComparison B S hS f _ RF α
      (isIso_app_quotient_of_termwise_injective_of_isNoetherian B S hS hZ hX hY f RF α)⟩⟩

end AlgebraicGeometry.Space

end
