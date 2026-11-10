module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedFibreSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentTensorProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFiniteOverAffine
public import StacksFrontier.RingTheory.KrullIntersectionKernelBound

/-!
# The local case of Stacks 0D39, from the theorem on formal functions

The situation over a Noetherian local base: `ι : P ⟶ T` a closed immersion of affine objects of
the site with ideal `J`, `f : X ⟶ h_T` proper, `p : h_U ⟶ X` the base change of `ι` with `U ⟶ P`
proper, `ℱ` coherent and `ℒ` invertible on `X` with `ℒ|_U` ample. Given clauses (1) and (3) of
the theorem on formal functions (Stacks 08AY), for `d ≫ 0`, writing `ℱ' = ℱ ⊗ ℒ^{⊗ d}`,
`Hᵖ(X, ℱ') = 0` for `p > 0` and `Γ(X, ℱ') ⟶ Γ(h_U, p^*ℱ')` is surjective.

## Main definitions

* `AlgebraicGeometry.Space.idealPowTransition`: the transition `M/Iⁿ⁺¹M ⟶ M/IⁿM` of the tower
  `M/IⁿM`.
* `AlgebraicGeometry.Space.idealPowTransitionToOne`: the composite transition `M/Iᵐ⁺¹M ⟶ M/IM`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_twistPowFunctor_obj`: the twists of a coherent module by an
  invertible module are coherent.
* `AlgebraicGeometry.Space.exists_local_ampleFibreTwist`: for `d ≫ 0`, the twist `ℱ ⊗ ℒ^{⊗ d}`
  has vanishing higher cohomology and its global sections surject onto those of its pullback to
  `h_U`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The twists of a coherent module by an invertible module are coherent. -/
theorem isCoherent_twistPowFunctor_obj {X : AlgebraicSpaces B S hS}
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (F L : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L] :
    ∀ d, IsCoherent B S hS X.1 X.2 ((twistPowFunctor L d).obj F)
  | 0 => hF
  | d + 1 => by
    have := isCoherent_twistPowFunctor_obj F L hF d
    have : IsCoherent B S hS X.1 X.2 L := isCoherent_of_isInvertible L ‹_›
    rw [twistPowFunctor_obj_succ, modulesTensorRightFunctor_obj]
    let := modulesMonoidalCategory B S hS X.1 X.2
    exact isCoherent_of_iso B S hS X.2
      (tensorModuleIso B S hS X.1 X.2 _ _ ≪≫ modulesTensorObjIso B S hS X.1 X.2 _ _)
      (isCoherent_tensorModule B S hS X.1 X.2 _ _)

/-! ### The transitions of the tower -/

section Transitions

variable {X : AlgebraicSpaces B S hS} (I : IdealSheaves B S hS X.1 X.2)
  (M : Modules.{u, u} B S hS X.1 X.2)

/-- The projection `M ⟶ M/IⁿM`, onto the right term of the `n`-th stage of the tower. -/
abbrev idealPowTowerπ (n : ℕ) : M ⟶ (idealPowTowerShortComplex I M n).X₃ := cokernel.π _

/-- The first factor of `AlgebraicGeometry.Space.idealPowTransition`. -/
def idealPowTransitionIso (n : ℕ) :
    (idealPowTowerShortComplex I M (n + 1)).X₃ ⟶ (idealPowTowerShortComplex I M n).X₂ :=
  (idealPowTowerShortComplexX₃Iso I M n).hom

/-- The second factor of `AlgebraicGeometry.Space.idealPowTransition`. -/
def idealPowTransitionG (n : ℕ) :
    (idealPowTowerShortComplex I M n).X₂ ⟶ (idealPowTowerShortComplex I M n).X₃ :=
  (idealPowTowerShortComplex I M n).g

/-- The transition `M/Iⁿ⁺¹M ⟶ M/IⁿM` of the tower. -/
def idealPowTransition (n : ℕ) :
    (idealPowTowerShortComplex I M (n + 1)).X₃ ⟶ (idealPowTowerShortComplex I M n).X₃ :=
  idealPowTransitionIso I M n ≫ idealPowTransitionG I M n

/-- The projection `M ⟶ M/Iⁿ⁺¹M` followed by the transition `M/Iⁿ⁺¹M ⟶ M/IⁿM` is the projection
`M ⟶ M/IⁿM`. -/
theorem π_idealPowTransition (n : ℕ) :
    idealPowTowerπ I M (n + 1) ≫ idealPowTransition I M n = idealPowTowerπ I M n := by
  change cokernel.π _ ≫ (cokernelIsoOfEq (Stacks.SheafOfModules.Submodule.homOfLE_comp_ι
    (idealPowSubmodule_succ_le I n M))).inv ≫ Stacks.Abelian.cokernelCompπ _ _ = _
  rw [← Category.assoc, π_comp_cokernelIsoOfEq_inv, Stacks.Abelian.π_comp_cokernelCompπ]

/-- The composite transition `M/Iᵐ⁺¹M ⟶ M/IM`. -/
def idealPowTransitionToOne : ∀ m : ℕ,
    (idealPowTowerShortComplex I M (m + 1)).X₃ ⟶ (idealPowTowerShortComplex I M 1).X₃
  | 0 => 𝟙 _
  | m + 1 => idealPowTransition I M (m + 1) ≫ idealPowTransitionToOne m

/-- The projection `M ⟶ M/Iᵐ⁺¹M` followed by the composite transition `M/Iᵐ⁺¹M ⟶ M/IM` is the
projection `M ⟶ M/IM`. -/
theorem π_idealPowTransitionToOne : ∀ m : ℕ,
    idealPowTowerπ I M (m + 1) ≫ idealPowTransitionToOne I M m = idealPowTowerπ I M 1
  | 0 => Category.comp_id _
  | m + 1 => by
    rw [idealPowTransitionToOne, ← Category.assoc, π_idealPowTransition,
      π_idealPowTransitionToOne m]

variable {𝒟 : Type*} [Category 𝒟] (Q : Modules.{u, u} B S hS X.1 X.2 ⥤ 𝒟)

/-- A functor carrying the tower maps to epimorphisms carries the transitions to epimorphisms. -/
theorem epi_map_idealPowTransition (n : ℕ) (h : Epi (Q.map (idealPowTowerShortComplex I M n).g)) :
    Epi (Q.map (idealPowTransition I M n)) := by
  rw [idealPowTransition, Q.map_comp, idealPowTransitionIso, idealPowTransitionG]
  exact epi_comp _ _

/-- A functor carrying the tower maps to epimorphisms carries the composite transitions
`M/Iᵐ⁺¹M ⟶ M/IM` to epimorphisms. -/
theorem epi_map_idealPowTransitionToOne (h : ∀ n, Epi (Q.map (idealPowTowerShortComplex I M n).g)) :
    ∀ m, Epi (Q.map (idealPowTransitionToOne I M m))
  | 0 => by rw [idealPowTransitionToOne, Q.map_id]; infer_instance
  | m + 1 => by
    rw [idealPowTransitionToOne, Q.map_comp]
    have := epi_map_idealPowTransition I M Q (m + 1) (h (m + 1))
    have := epi_map_idealPowTransitionToOne h m
    exact epi_comp _ _

end Transitions

/-! ### The local theorem -/

section Local

variable {X : AlgebraicSpaces B S hS} {P T U : BigFppfOver B S hS} (ι : P ⟶ T)
  (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T)]
  (f : X ⟶ representedAlgebraicSpace B S hS T) (hf : IsProper B S hS f.hom)
  (p : yoneda.obj U ⟶ X.1) (q : U ⟶ P)
  (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map ι))
  {r : ℕ} (x : Fin r → Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  (hx : Ideal.span (Set.range x) = RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
  (J : Ideal (RingCat.sectionsSubring
    (ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).O).obj))

include hsq hx hf in
/-- The local case of Stacks 0D39. Let `ι : P ⟶ T` be a closed immersion of affine objects with
`T` locally Noetherian, `f : X ⟶ h_T` proper, `p : h_U ⟶ X` the base change of `ι` with `U ⟶ P`
proper, `ℱ` coherent and `ℒ` invertible on `X` with `ℒ|_U` ample, and `J` an ideal in the Jacobson
radical. Given clauses (1) and (3) of the theorem on formal functions (Stacks 08AY), for `d ≫ 0`
the twist `ℱ ⊗ ℒ^{⊗ d}` has vanishing cohomology in positive degrees and its global sections
surject onto the global sections of its pullback along `p`. -/
theorem exists_local_ampleFibreTwist
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)]
    (hq : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    [IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)]
    (hamp : IsAmple ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p))
    (hJ : J ≤ Ideal.jacobson ⊥)
    (h08AY1 : ∀ (G : Modules.{u, u} B S hS X.1 X.2), IsCoherent B S hS X.1 X.2 G → ∀ i : ℕ,
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      ∃ c : ℕ, ∀ n, c ≤ n → LinearMap.ker ((globalSectionsRestrictScalars B S hS f).map
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).map
            (idealPowTowerπ (fibreIdeal ι hι f) G n))).hom ≤ J ^ (n - c) • ⊤)
    (h08AY3 : ∀ (G : Modules.{u, u} B S hS X.1 X.2), IsCoherent B S hS X.1 X.2 G →
      have := hasInjectiveResolutions_modules B S hS X.1 X.2
      (∀ m, Epi (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map
            (idealPowTransitionToOne (fibreIdeal ι hι f) G m))) →
        Epi (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map
            (idealPowTowerπ (fibreIdeal ι hι f) G 1))) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      (∀ i, 0 < i → IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj
          ((twistPowFunctor L d).obj F))) ∧
      Function.Surjective (globalSectionsPullbackMap B S hS
        (ObjectProperty.homMk p : representedAlgebraicSpace B S hS U ⟶ X)
          ((twistPowFunctor L d).obj F)).hom := by
  let := hasInjectiveResolutions_modules B S hS X.1 X.2
  obtain ⟨d₀, hd₀⟩ := exists_isZero_rightDerived_idealPowTower_twist ι hι f p q hsq x hx hq F hF L
    hamp
  refine ⟨d₀, fun d hd => ?_⟩
  have hF' := isCoherent_twistPowFunctor_obj F L hF d
  obtain ⟨hvan, hepi⟩ := hd₀ d hd
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨c, hc⟩ := h08AY1 _ hF' i
    have : IsNoetherianRing (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O).obj) :=
      isNoetherianRing_globalSections_schemeSpace B S hS T
    have hfin := hasFiniteGlobalCohomologyOver_of_isProper B S hS B.contains_terminal f hf _ hF'
    have : Module.Finite (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS
        (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T)).O).obj)
        ((globalSectionsRestrictScalars B S hS f).obj (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).obj
            ((twistPowFunctor L d).obj F))) := hfin i
    have hsub := Stacks.subsingleton_of_ker_le_pow_smul_top J hJ
      (fun n => ((globalSectionsRestrictScalars B S hS f).map
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived i).map
            (idealPowTowerπ (fibreIdeal ι hι f) ((twistPowFunctor L d).obj F) n))).hom)
      (fun n => ModuleCat.isZero_iff_subsingleton.1
        (Functor.map_isZero (globalSectionsRestrictScalars B S hS f) (hvan n i hi))) c hc
    exact @ModuleCat.isZero_of_subsingleton _ _ _ hsub
  · have hπe := h08AY3 ((twistPowFunctor L d).obj F) hF'
      (epi_map_idealPowTransitionToOne (fibreIdeal ι hι f) ((twistPowFunctor L d).obj F)
        ((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0) hepi)
    exact surjective_globalSectionsPullbackMap_of_surjective_quotient ι hι f p q hsq _
      (surjective_globalSections_map_of_epi_rightDerived_zero _ hπe)

end Local

end AlgebraicGeometry.Space

end
