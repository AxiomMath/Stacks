module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SmoothProperSpecializationHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.InvertibleL.FiniteStalksOfIsUnit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.BaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveConstructibility.NoetherianModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperSmoothCurveSpecialization.ConstantCoefficientsSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.DerivedDirectImageHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.Specialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteTypeLocallyConstantModuleConverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ConstantCoefficientsCohomology
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of `ℤ/ℓ` along smooth proper families of curves, `ℓ` invertible

Let `f : X ⟶ S` be a proper smooth morphism with geometrically connected fibres of dimension at
most one and `ℓ` a prime invertible on `S`. Then every cohomology sheaf `H^q(Rf_* ℤ/ℓ)` of the
derived direct image of the constant sheaf `ℤ/ℓ` is a constructible sheaf of `ℤ/ℓ`-modules on
`S_étale`. This is [Stacks, Tag 0GKV] for `ℓ` invertible on the base.

Over a locally Noetherian base the proof is the source's. By Tag 0GKC
(`AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk`) the
sheaf is finite locally constant, hence constructible, as soon as its stalks are finite and its
specialization maps bijective. The stalks are the groups `H^q(X_s̄, ℤ/ℓ)` by proper base change,
finite for a smooth proper curve or a point
(`finite_smallEtaleStalkAb_homology_derivedDirectImage_constantZMod_of_isUnit`);
the specialization maps are bijective because those of `Rf_* ℤ/ℓ` are
(`AlgebraicGeometry.isIso_specializationMap_constantSheaf_of_smooth_of_isProper`).

For a general base, constructibility is local ([Stacks, Tag 095F]), so the base may be taken
affine; an affine family is the base change of one over a Noetherian base on which `ℓ` is still
invertible (`AlgebraicGeometry.exists_isPullback_noetherian_of_isProper_of_smooth_of_isUnit`), and
constructibility of `R^q f_* ℤ/ℓ` passes to base changes ([Stacks, Tag 095G]).

## Main results

* `isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isLocallyNoetherian`:
  the theorem over a locally Noetherian base.
* `isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isAffine`: the theorem
  over an affine base.
* `isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit`: [Stacks, Tag 0GKV] for
  `ℓ` invertible on the base.

## References

* [Stacks Project, Tag 0GKV](https://stacks.math.columbia.edu/tag/0GKV)
* [Stacks Project, Tag 0GKC](https://stacks.math.columbia.edu/tag/0GKC)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance]
  Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

universe u

namespace Stacks.EtaleCohomology

/-- **[Stacks, Tag 0GKV] over a locally Noetherian base on which `ℓ` is invertible.** Let
`f : X ⟶ S` be proper and smooth with geometrically connected fibres of dimension at most one,
`S` locally Noetherian, and `ℓ` a prime which is a unit on `S`. Then every cohomology sheaf
`H^q(Rf_* ℤ/ℓ)` is a constructible sheaf of `ℤ/ℓ`-modules. -/
theorem isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isLocallyNoetherian
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    [IsLocallyNoetherian S]
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) (q : ℤ) :
    IsConstructibleEtaleModule (ZMod ℓ)
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
              (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))) := by
  classical
  let Λ := ZMod ℓ
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({X, S} : Set Scheme.{u})
  have hX : B.Contains X := hB X (by simp)
  have hS : B.Contains S := hB S (by simp)
  let E : ModuleCat.{u + 1} Λ := ModuleCat.of Λ (ULift.{u + 1} Λ)
  let K := (DerivedCategory.singleFunctor (EtaleModules.{u, 0} Λ X) 0).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E)
  let M := (DerivedCategory.homologyFunctor (EtaleModules.{u, 0} Λ S) q).obj
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ f).obj K)
  let A : AddCommGrpCat.{u + 1} := (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj E
  have : Finite A := inferInstanceAs (Finite (ULift.{u + 1} (ZMod ℓ)))
  let Fab := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  let L := (etaleAbelianDerivedDirectImage.{u, 0} f).obj
    ((DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj Fab)
  let Φ : (etaleModuleForgetAb.{u, 0} Λ S).obj M ≅
      (DerivedCategory.homologyFunctor
        (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj L :=
    (etaleModuleForgetHomologyDerivedDirectImageIso.{u, 0} Λ f q).app K ≪≫
      (DerivedCategory.homologyFunctor _ q).mapIso ((etaleAbelianDerivedDirectImage.{u, 0} f).mapIso
        (((etaleModuleForgetAb.{u, 0} Λ X).mapDerivedCategorySingleFunctor 0).app _ ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso
            ((etaleModuleForgetConstantSheafIso.{u, 0} Λ X).app E)))
  refine (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hS M).2 ?_
  refine @isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B (B.obj S hS) Λ _
    (fun _ _ g => SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B Λ g)
    (fun T V => SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B Λ T V) _ ?_
  refine AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk
    B S hS Λ (finite_irreducibleComponents_of_isCompact S) _ ?_ ?_
  · intro s
    have hfin : Finite ((smallEtaleStalkAb s.hom).obj ((etaleModuleForgetAb.{u, 0} Λ S).obj M)) :=
      @Finite.of_equiv _ _
        (finite_smallEtaleStalkAb_homology_derivedDirectImage_constantZMod_of_isUnit f hdim ℓ hℓ
          s q)
        ((smallEtaleStalkAb s.hom).mapIso Φ).symm.addCommGroupIsoToAddEquiv.toEquiv
    have hfin' : Finite ((etaleStalk B S hS s ((etaleModuleToBoundedSite Λ B hS).obj M).obj :
        ModuleCat.{u + 1} Λ)) :=
      @Finite.of_equiv _ _ hfin
        (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hS s M).symm.addCommGroupIsoToAddEquiv.toEquiv
    rw [ModuleCat.isFG_iff]
    exact Module.Finite.of_finite
  · intro s σ
    refine bijective_specializationMapOnStalks_of_isIso Λ B hS s M σ ?_
    refine (NatTrans.isIso_app_iff_of_iso _ Φ).2 ?_
    refine isIso_smallEtaleSpecializationStalkAb_app_homology B S hS s σ.point L ?_ q
    exact AlgebraicGeometry.isIso_specializationMap_constantSheaf_of_smooth_of_isProper B hS f s
      σ.point hdim ℓ hℓ


/-- **[Stacks, Tag 0GKV] over an affine base on which `ℓ` is invertible.** The family is the base
change of one over a Noetherian base on which `ℓ` is invertible
(`AlgebraicGeometry.exists_isPullback_noetherian_of_isProper_of_smooth_of_isUnit`), and
constructibility of `R^q f_* ℤ/ℓ` passes to base changes ([Stacks, Tag 095G]). -/
theorem isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isAffine
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S) [IsProper f] [Smooth f]
    [GeometricallyConnected f]
    (hd : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) (q : ℤ) :
    IsConstructibleEtaleModule (ZMod ℓ)
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
              (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))) := by
  obtain ⟨Y, T, F, g, g', hT, hFp, hFs, hFg, hFd, hTu, sq⟩ :=
    exists_isPullback_noetherian_of_isProper_of_smooth_of_isUnit f hd ℓ hℓ
  have := hT
  have := hFp
  have := hFs
  have := hFg
  exact isConstructibleEtaleModule_homology_derivedDirectImage_constant_of_isPullback.{u, 0}
    (ZMod ℓ) (Fact.out : ℓ.Prime).pos (ZMod.natCast_self ℓ)
    (cohomologyCommutesWithBaseChange_of_isProper F) sq _ q
    (isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isLocallyNoetherian
      F hFd ℓ hTu q)

/-- **[Stacks, Tag 0GKV], for `ℓ` invertible on the base.** Let `f : X ⟶ S` be a proper smooth
morphism of schemes with geometrically connected fibres of dimension at most one, and let `ℓ` be a
prime invertible on `S`. Then `R^q f_* (ℤ/ℓℤ)` is a constructible sheaf of `ℤ/ℓℤ`-modules on
`S_étale` for every `q`.

Constructibility is local on `S` ([Stacks, Tag 095F]) and the formation of `R^q f_*(ℤ/ℓℤ)`
commutes with restriction to an open (proper base change, [Stacks, Tag 095T]), so this is
`isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isAffine` on the affine
opens of `S`. -/
@[sga "4 XIV 1.1" "special case", sga "5 I 3.1.6" "clause a), special case"]
theorem isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (hd : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : Γ(S, ⊤))) (q : ℤ) :
    IsConstructibleEtaleModule (ZMod ℓ)
      ((DerivedCategory.homologyFunctor (EtaleModules.{u, 0} (ZMod ℓ) S) q).obj
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} (ZMod ℓ) f).obj
          ((DerivedCategory.singleFunctor (EtaleModules.{u, 0} (ZMod ℓ) X) 0).obj
            ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod ℓ))).obj
              (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))))))) := by
  have hℓ0 : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  refine (isConstructibleEtaleModule_iff_forall_etaleModuleRestriction_opens (ZMod ℓ) _
    (fun V : S.affineOpens ↦ (V : S.Opens)) (iSup_affineOpens_eq_top S)).2 fun V ↦ ?_
  have hsq := IsPullback.of_hasPullback f (V : S.Opens).ι
  obtain ⟨hVp, hVs, hVg, hVd⟩ :=
    isProper_smooth_geometricallyConnected_fiber_le_of_isPullback hsq hd
  have : IsAffine (V : S.Opens) := V.2
  have hVu : IsUnit ((ℓ : ℕ) : Γ((V : S.Opens), ⊤)) := by
    have := hℓ.map (V : S.Opens).ι.appTop.hom
    rwa [map_natCast] at this
  exact (IsConstructibleEtaleModule _).prop_of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, 0} (ZMod ℓ) (V : S.Opens).ι).app _)
    ((IsConstructibleEtaleModule _).prop_of_iso
      (etaleModuleInverseImageHomologyDerivedDirectImageConstantIso.{u, 0} (ZMod ℓ) hℓ0
        (ZMod.natCast_self ℓ) (cohomologyCommutesWithBaseChange_of_isProper f) hsq _ q).symm
      (isConstructibleEtaleModule_homology_derivedDirectImage_zmod_of_isUnit_of_isAffine
        (pullback.snd f (V : S.Opens).ι) hVd ℓ hVu q))

end Stacks.EtaleCohomology

end
