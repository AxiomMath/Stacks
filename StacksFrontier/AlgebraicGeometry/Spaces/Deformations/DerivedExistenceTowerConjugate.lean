module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.ExactCompositionConjugateOfToposHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.DerivedExistenceLimitProjectionCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.CategoryTheory.Adjunction.CompOfNatIsoRight
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateNaturality

/-!
# The tower of Situation 0DIK through the ringed-topos direct images

In Situation [Stacks, Tag 0DIK] the tower `Rjₙ,* Kₙ` of [Stacks, Tag 0DIL] is built from the
exact direct images `Rjₙ,*`, `Riₙ,*` and their composition isomorphism
`Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*`, while the derived pullbacks compose by
`smallEtaleDerivedModulePullbackCompIso` (Stacks 0D6D). This file shows that the two composition
isomorphisms are conjugate, and reads the transition maps of the tower through the ringed-topos
derived direct images and the conjugate of the derived pullback compositor.

## Main results

* `AlgebraicGeometry.Space.map_homEquiv_comp_hom_app_of_conjugateEquiv`: abstractly, a composite
  `Rg'(φ^♯) ≫ P` with `P⁻¹` the conjugate of `e` along transported adjunctions, read through the
  untransported ones.
* `SeparatedDerivedExistenceSystem.conjugateEquiv_stageDerivedPullbackCompIso_hom`:
  along `Ljₙ^* ⊣ Rjₙ,*` and `Ljₙ₊₁^* ⋙ Liₙ^* ⊣ Riₙ,* ⋙ Rjₙ₊₁,*`, the conjugate of
  `Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` is the inverse of `Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*`.
* `AlgebraicGeometry.Space.SeparatedDerivedExistenceSystem.towerMap_eq`: the transition map
  `Rjₙ₊₁,* Kₙ₊₁ ⟶ Rjₙ,* Kₙ` is the ringed-topos `Rjₙ₊₁,*` of the adjoint of `φₙ` followed by the
  conjugate of `Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*`, read through the identifications of the two direct images.
* `Space.SeparatedDerivedExistenceSystem.stageToposDerivedPushforward_eq`,
  `Space.SeparatedDerivedExistenceSystem.conjugateEquiv_stageDerivedPullbackCompIso_inv_eq`:
  the functor and the conjugate of `towerMap_eq` expressed through
  `AlgebraicGeometry.Space.derivedModulePushforward` and
  `AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunction`.

## Implementation notes

The conjugation identity is proved at abstract ringed topoi
(`Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.conjugateEquiv_hom_eq_inv_of_eq`) and
instantiated here with the two composition isomorphisms passed together with their
identifications, so that Situation 0DIK is only met at the level of isomorphisms. The
vocabularies of the small étale ringed topoi are crossed only between functors and natural
transformations; a component is obtained by `NatTrans.congr_app` at an object shared by both
sides, which is much cheaper for the kernel than comparing components of differently spelled terms.

## References

* [Stacks Project, Tag 0DIK](https://stacks.math.columbia.edu/tag/0DIK)
* [Stacks Project, Tag 0DIL](https://stacks.math.columbia.edu/tag/0DIL)
* [Stacks Project, Tag 0DIM](https://stacks.math.columbia.edu/tag/0DIM)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.RingedToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard

section Abstract

/-- **A composite of transposes, read through the untransported adjunctions.** For adjunctions
`Af`, `Ag`, `Ah` whose right adjoints are replaced along `βf`, `βg`, `βh`, and an isomorphism
`P : Rf' ⋙ Rg' ≅ Rh'` whose inverse is the conjugate of `e : Lg ⋙ Lf ≅ Lh` along the replaced
adjunctions, the composite `Rg'(φ^♯) ≫ P` of the transpose of `φ : Lf Kg ⟶ Kf` is the
untransported composite `Rg(φ^♭) ≫ (conjugate of e⁻¹)`, conjugated by `βg` and `βh`. -/
theorem map_homEquiv_comp_hom_app_of_conjugateEquiv {A B C : Type*} [Category* A] [Category* B]
    [Category* C] {Lf : B ⥤ A} {Rf Rf' : A ⥤ B} {Lg : C ⥤ B} {Rg Rg' : B ⥤ C}
    {Lh : C ⥤ A} {Rh Rh' : A ⥤ C} (Af : Lf ⊣ Rf) (Ag : Lg ⊣ Rg) (Ah : Lh ⊣ Rh)
    (βf : Rf ≅ Rf') (βg : Rg ≅ Rg') (βh : Rh ≅ Rh') (e : Lg ⋙ Lf ≅ Lh) (P : Rf' ⋙ Rg' ≅ Rh')
    (he : conjugateEquiv (Ah.ofNatIsoRight βh)
      ((Ag.ofNatIsoRight βg).comp (Af.ofNatIsoRight βf)) e.hom = P.inv)
    {Kg : B} {Kf : A} (φ : Lf.obj Kg ⟶ Kf) :
    Rg'.map ((Af.ofNatIsoRight βf).homEquiv _ _ φ) ≫ P.hom.app Kf =
      βg.inv.app Kg ≫ (Rg.map (Af.homEquiv _ _ φ) ≫
        (conjugateEquiv (Ag.comp Af) Ah e.inv).app Kf) ≫ βh.hom.app Kf := by
  have hI : conjugateIsoEquiv (Ah.ofNatIsoRight βh)
      ((Ag.ofNatIsoRight βg).comp (Af.ofNatIsoRight βf)) e = P.symm := Iso.ext he
  have hP : P.hom = conjugateEquiv ((Ag.ofNatIsoRight βg).comp (Af.ofNatIsoRight βf))
      (Ah.ofNatIsoRight βh) e.inv := (congrArg Iso.inv hI).symm
  rw [hP, Stacks.CategoryTheory.comp_ofNatIsoRight,
    Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight, Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [NatTrans.comp_app, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [NatTrans.naturality_assoc]

end Abstract

namespace SeparatedDerivedExistenceSystem

variable (D : SeparatedDerivedExistenceSystem.{u})

/-- **The two composition isomorphisms of the tower of Situation 0DIK are conjugate**: along
`Ljₙ^* ⊣ Rjₙ,*` and the composite `Ljₙ₊₁^* ⋙ Liₙ^* ⊣ Riₙ,* ⋙ Rjₙ₊₁,*`, the conjugate of
`Ljₙ₊₁^* ⋙ Liₙ^* ≅ Ljₙ^*` (Stacks 0D6D) is the inverse of the composition isomorphism
`Riₙ,* ⋙ Rjₙ₊₁,* ≅ Rjₙ,*` of the exact direct images. -/
theorem conjugateEquiv_stageDerivedPullbackCompIso_hom (n : ℕ) :
    conjugateEquiv (D.stageAdjunction n)
        ((D.stageAdjunction (n + 1)).comp (D.transitionAdjunction n))
        (D.stageDerivedPullbackCompIso n).hom =
      (D.stagePushforwardCompIso n).inv := by
  have := isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _
    (D.stage n).2
  have := isGrothendieckAbelian_modules D.B (limitBase D.system) D.containsLimitBase _
    (D.stage (n + 1)).2
  have := D.preservesFiniteLimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
  have := D.preservesFiniteColimits_toposPushforward
    (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    ((isClosedImmersion_transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective n))
  have hj (m : ℕ) : PreservesFiniteLimits (D.toposPushforward
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X m)) ∧
      PreservesFiniteColimits (D.toposPushforward
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X m)) :=
    ⟨D.preservesFiniteLimits_toposPushforward _,
      D.preservesFiniteColimits_toposPushforward _
        ((isClosedImmersion_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X
      D.transition_surjective m))⟩
  have hr (m : ℕ) :=
    haveI := (hj m).1
    haveI := (hj m).2
    rightDerivedIsoOfFactors_hom_app (D.stageQh m)
      (HomotopyCategory.quasiIso (D.toposModules (D.stage m)) (ComplexShape.up ℤ)) _ _
      (D.stageToposUnit m) (D.stagePushforwardFactorsh m)
  obtain ⟨_, _⟩ := hj n
  obtain ⟨_, _⟩ := hj (n + 1)
  exact conjugateEquiv_hom_eq_inv_of_eq
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)))
      (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase
        (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n ≫
          spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)))
      (congrArg (smallEtaleRingedToposHom D.B (limitBase D.system) D.containsLimitBase)
        (transitionSpace_spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
      (pushforwardModulesCompTransport D.B (limitBase D.system) D.containsLimitBase
        (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)))
      (D.transitionToposDerivedPushforwardIso n)
      (rightDerivedIsoOfFactors_hom_app (D.stageQh n)
        (HomotopyCategory.quasiIso (D.toposModules (D.stage n)) (ComplexShape.up ℤ)) _ _
        (D.transitionToposUnit n) (D.transitionPushforwardFactorsh n))
      (D.stageToposDerivedPushforwardIso (n + 1))
      (hr (n + 1))
      (D.stageToposDerivedPushforwardIso n)
      (hr n)
      (D.stageDerivedPullbackCompIso n) rfl
      (modulePushforwardCompIso' D.B (limitBase D.system) D.containsLimitBase
        (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) ≪≫
        eqToIso (by rw [transitionSpace_spaceProjection]))
      (congrArg (· ≪≫ _) (modulePushforwardCompIso'_eq_trans D.B (limitBase D.system)
        D.containsLimitBase _ _))


/-- **The transition maps of the tower of Situation 0DIK through the ringed-topos direct
images.** The transition `Rjₙ₊₁,* Kₙ₊₁ ⟶ Rjₙ,* Kₙ` (`towerMap`, built from the exact direct
images) is the ringed-topos `Rjₙ₊₁,*` of the adjoint `Kₙ₊₁ ⟶ Riₙ,* Kₙ` of `φₙ`, followed by the
conjugate `Riₙ,* ⋙ Rjₙ₊₁,* ⟶ Rjₙ,*` of `Ljₙ^* ≅ Liₙ^* Ljₙ₊₁^*` (Stacks 0D6D), read through the
identifications `stageToposDerivedPushforwardIso` of the two direct images. -/
theorem towerMap_eq (n : ℕ) :
    D.towerMap n =
      (D.stageToposDerivedPushforwardIso (n + 1)).inv.app (D.K (n + 1)) ≫
        ((D.stageToposDerivedPushforward (n + 1)).map
            ((transitionToposDerivedAdjunction D.system D.B D.containsLimitBase D.containsBaseAt
              D.X n).homEquiv _ _ (D.φ n)) ≫
          (conjugateEquiv ((D.stageToposDerivedAdjunction (n + 1)).comp
              (transitionToposDerivedAdjunction D.system D.B D.containsLimitBase
                D.containsBaseAt D.X n))
            (D.stageToposDerivedAdjunction n) (D.stageDerivedPullbackCompIso n).inv).app
            (D.K n)) ≫
        (D.stageToposDerivedPushforwardIso n).hom.app (D.K n) :=
  map_homEquiv_comp_hom_app_of_conjugateEquiv
    (transitionToposDerivedAdjunction D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
    (D.stageToposDerivedAdjunction (n + 1)) (D.stageToposDerivedAdjunction n)
    (D.transitionToposDerivedPushforwardIso n) (D.stageToposDerivedPushforwardIso (n + 1))
    (D.stageToposDerivedPushforwardIso n) (D.stageDerivedPullbackCompIso n)
    (D.stagePushforwardCompIso n) (D.conjugateEquiv_stageDerivedPullbackCompIso_hom n) (D.φ n)


/-- The ringed-topos `Rjₙ,*` of Situation 0DIK is `derivedModulePushforward` along `jₙ`. -/
theorem stageToposDerivedPushforward_eq (n : ℕ) :
    D.stageToposDerivedPushforward n =
      derivedModulePushforward D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n) :=
  rfl

/-- The conjugate in `towerMap_eq` is the conjugate of `smallEtaleDerivedModulePullbackCompIso`
along the adjunctions `smallEtaleDerivedModuleAdjunction`, as natural transformations. -/
theorem conjugateEquiv_stageDerivedPullbackCompIso_inv_eq (n : ℕ) :
    conjugateEquiv ((D.stageToposDerivedAdjunction (n + 1)).comp
        (transitionToposDerivedAdjunction D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
      (D.stageToposDerivedAdjunction n) (D.stageDerivedPullbackCompIso n).inv =
    conjugateEquiv ((smallEtaleDerivedModuleAdjunction D.B (limitBase D.system)
        D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1))).comp
        (smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
          (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)))
      (smallEtaleDerivedModuleAdjunction D.B (limitBase D.system) D.containsLimitBase
        (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X n))
      (smallEtaleDerivedModulePullbackCompIso D.B (limitBase D.system) D.containsLimitBase
          (transitionSpace D.system D.B D.containsLimitBase D.containsBaseAt D.X n)
          (spaceProjection D.system D.B D.containsLimitBase D.containsBaseAt D.X (n + 1)) ≪≫
        smallEtaleDerivedModulePullbackCongr D.B (limitBase D.system) D.containsLimitBase
          (transitionSpace_spaceProjection D.system D.B D.containsLimitBase
            D.containsBaseAt D.X n)).inv :=
  rfl

end SeparatedDerivedExistenceSystem

end AlgebraicGeometry.Space

end
