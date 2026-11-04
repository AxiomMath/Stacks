module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistGlobalize
public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.StalkPointResidueKernel

/-!
# Stacks 0D39 from clauses (1) and (3) of the theorem on formal functions

This file assembles the proof of Stacks 0D39
(`AlgebraicGeometry.Space.AmpleSchemeFibreTwistStatement`) from the two clauses of the theorem on
formal functions (Stacks 08AY) that the proof uses, stated for proper algebraic spaces over
`Spec 𝒪_{Y,y}` and the ideal of the closed point:

1. the kernels of `Hⁱ(X', 𝒢) ⟶ Hⁱ(X', 𝒢/𝔪ⁿ𝒢)` lie in `𝔪^{n-c} Hⁱ(X', 𝒢)`;
2. in degree zero: if every `H⁰(X', 𝒢/𝔪^{m+1}𝒢) ⟶ H⁰(X', 𝒢/𝔪𝒢)` is surjective, so is
   `H⁰(X', 𝒢) ⟶ H⁰(X', 𝒢/𝔪𝒢)` (the consequence of clause (3) that the proof uses).

The reduction to `Spec 𝒪_{Y,y}` is flat base change along `Spec 𝒪_{Y,y} ⟶ Y` (Stacks 073K),
for the higher direct images
(`AlgebraicGeometry.Space.isZero_stalk_rightDerived_tensorPow_of_isZero`) and for the sections
near the fibre (`AlgebraicGeometry.Space.exists_open_restrictSectionAlong_eq_of_stalkBaseChange`);
the local case is `AlgebraicGeometry.Space.exists_local_ampleFibreTwist`.

## Main results

* `AlgebraicGeometry.Space.ampleSchemeFibreTwistStatement_of_formalFunctions`.

## References

* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Clause (1) of the theorem on formal functions** (Stacks 08AY, part (1)) over `Spec 𝒪_{Y,y}`,
for the ideal of the closed point: for a proper `f' : X' ⟶ Spec 𝒪_{Y,y}` and a coherent `𝒢`,
the kernel of `Hⁱ(X', 𝒢) ⟶ Hⁱ(X', 𝒢/𝔪ⁿ𝒢)` lies in `𝔪^{n-c} Hⁱ(X', 𝒢)` for `n ≥ c`. -/
def FormalFunctionsKernelClause (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (y : (BigFppfOver.toScheme B S hS).obj Y) (X' : AlgebraicSpaces B S hS)
    (f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y)),
    IsProper B S hS f'.hom → ∀ (G : Modules.{u, u} B S hS X'.1 X'.2),
    IsCoherent B S hS X'.1 X'.2 G →
    ∀ i : ℕ,
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      ∃ c : ℕ, ∀ n, c ≤ n → LinearMap.ker ((globalSectionsRestrictScalars B S hS f').map
        (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived i).map
            (idealPowTowerπ (fibreIdeal (residueToStalkPointHom Y y)
              (isClosedImmersion_residueToStalkPointHom Y y) f') G n))).hom ≤
        RingHom.ker (globalSectionsRingHomSite B S hS
          (representedSpaceMap B S hS (residueToStalkPointHom Y y))) ^ (n - c) • ⊤

/-- **Clause (3) of the theorem on formal functions** (Stacks 08AY, part (3)) over `Spec 𝒪_{Y,y}`,
in degree zero, for the ideal of the closed point, in the form the proof of Stacks 0D39 uses: for a
proper `f' : X' ⟶ Spec 𝒪_{Y,y}` and a coherent `𝒢`, if every transition
`H⁰(X', 𝒢/𝔪^{m+1}𝒢) ⟶ H⁰(X', 𝒢/𝔪𝒢)` is surjective, then so is `H⁰(X', 𝒢) ⟶ H⁰(X', 𝒢/𝔪𝒢)`. -/
def FormalFunctionsImageClause (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Prop :=
  ∀ (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    (y : (BigFppfOver.toScheme B S hS).obj Y) (X' : AlgebraicSpaces B S hS)
    (f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y)),
    IsProper B S hS f'.hom → ∀ (G : Modules.{u, u} B S hS X'.1 X'.2),
    IsCoherent B S hS X'.1 X'.2 G →
      have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
      (∀ m, Epi (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived 0).map
            (idealPowTransitionToOne (fibreIdeal (residueToStalkPointHom Y y)
              (isClosedImmersion_residueToStalkPointHom Y y) f') G m))) →
        Epi (((globalSectionsFunctor.{u + 1, u, u, u}
          (ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived 0).map
            (idealPowTowerπ (fibreIdeal (residueToStalkPointHom Y y)
              (isClosedImmersion_residueToStalkPointHom Y y) f') G 1))

/-- Surjectivity of the inverse image of global sections is invariant under isomorphism of the
module. -/
theorem surjective_globalSectionsPullbackMap_of_iso {Z Z' : AlgebraicSpaces B S hS} (k : Z' ⟶ Z)
    {M N : Modules.{u, u} B S hS Z.1 Z.2} (e : M ≅ N)
    (h : Function.Surjective (globalSectionsPullbackMap B S hS k N).hom) :
    Function.Surjective (globalSectionsPullbackMap B S hS k M).hom := by
  intro t
  obtain ⟨σ, hσ⟩ := h (((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
      ((modulePullback B S hS k).map e.hom)).hom t)
  refine ⟨((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)).map e.inv).hom σ, ?_⟩
  refine (globalSectionsPullbackMap_naturality_apply k e.inv σ).trans ?_
  refine (congrArg ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map
      ((modulePullback B S hS k).map e.inv)).hom hσ).trans ?_
  refine (globalSectionsFunctor_map_comp_apply _ _ t).symm.trans ?_
  have eq : (modulePullback B S hS k).map e.hom ≫ (modulePullback B S hS k).map e.inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id]
  exact (congrArg (fun φ => ((globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map φ).hom t) eq).trans
    (congrArg (fun φ => φ.hom t) ((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O)).map_id _))

/-- `AlgebraicGeometry.Space.representedPointHom` is `ObjectProperty.homMk`, for surjectivity of
the inverse image of global sections. -/
theorem surjective_globalSectionsPullbackMap_representedPointHom {X : AlgebraicSpaces B S hS}
    (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ X.1) (M : Modules.{u, u} B S hS X.1 X.2)
    (h : Function.Surjective (globalSectionsPullbackMap B S hS
      (ObjectProperty.homMk j : representedAlgebraicSpace B S hS U ⟶ X) M).hom) :
    Function.Surjective (globalSectionsPullbackMap B S hS (representedPointHom U j) M).hom := by
  unfold representedPointHom
  exact h

/-- **Stacks 0D39 from clauses (1) and (3) of the theorem on formal functions.** -/
theorem ampleSchemeFibreTwistStatement_of_formalFunctions
    (h₁ : FormalFunctionsKernelClause B S hS) (h₃ : FormalFunctionsImageClause B S hS) :
    AmpleSchemeFibreTwistStatement B S hS := by
  intro Y _ X f hf L _ F hF y U p q hsq hL
  obtain ⟨hLinv, hamp⟩ := hL
  have := hLinv
  have hFqc : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  have hfqc : IsQuasiCompact B S hS f.hom := hf.2.1.2
  have hfqs : IsQuasiSeparated B S hS f.hom := isQuasiSeparated_of_isSeparated B S hS hf.1
  -- an affine neighbourhood `W` of `y`, its preimage `X_W`, and `X' = X_W ×_W Spec 𝒪_{Y,y}`
  obtain ⟨W, hWaff, hyW, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (x := y) (U := ⊤) trivial
  obtain ⟨XW, pW, fW, hWpb⟩ : ∃ (XW : AlgebraicSpaces B S hS) (pW : XW ⟶ X)
      (fW : XW ⟶ representedAlgebraicSpace B S hS (openSiteObject B S hS Y W)),
      IsPullback pW fW f (representedSpaceMap B S hS (openSiteObjectHom B S hS Y W)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨X', g', f', hX'⟩ : ∃ (X' : AlgebraicSpaces B S hS) (g' : X' ⟶ XW)
      (f' : X' ⟶ representedAlgebraicSpace B S hS (stalkPointObject Y y)),
      IsPullback g' f' fW (representedSpaceMap B S hS (stalkPointToOpen Y W hyW)) :=
    ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  have sq : IsPullback (g' ≫ pW) f' f (representedSpaceMap B S hS (stalkPointHom Y y)) := by
    have h := hX'.paste_horiz hWpb
    rwa [representedSpaceMap_comp B S hS, stalkPointToOpen_comp_openSiteObjectHom] at h
  -- the fibre over the closed point of `Spec 𝒪_{Y,y}`
  have hsq' := isPullback_fibreToStalkBaseChange hsq sq
  have hp' : fibreToStalkBaseChange hsq sq ≫ (g' ≫ pW).hom = p := fibreToStalkBaseChange_comp hsq sq
  have : Fact (HasEtaleLocalProperty B S hS X'.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_stalkBaseChange hf sq⟩
  have hf' : IsProper B S hS f'.hom := isProper_stalkBaseChange hf sq
  obtain ⟨r, x, hx⟩ := exists_fin_span_eq_ker (residueToStalkPointHom Y y)
  have := isInvertible_modulePullback_stacks (g' ≫ pW) L
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS (g' ≫ pW)).obj L) U
        (fibreToStalkBaseChange hsq sq)) :=
    Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
      (baseChangeModuleStalkIso sq hsq L).symm
  have hamp' : IsAmple ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS ((modulePullback B S hS (g' ≫ pW)).obj L) U
        (fibreToStalkBaseChange hsq sq)) :=
    (isAmple_congr _ _ (baseChangeModuleStalkIso sq hsq L)).2 hamp
  obtain ⟨d₀, hd₀⟩ := exists_local_ampleFibreTwist (residueToStalkPointHom Y y)
    (isClosedImmersion_residueToStalkPointHom Y y) f' hf' (fibreToStalkBaseChange hsq sq) q hsq'
    x hx (RingHom.ker (globalSectionsRingHomSite B S hS
      (representedSpaceMap B S hS (residueToStalkPointHom Y y)))) (isProper_fibreMap hf sq hsq)
    ((modulePullback B S hS (g' ≫ pW)).obj F) (isCoherent_stalkBaseChange hf sq F hF)
    ((modulePullback B S hS (g' ≫ pW)).obj L) hamp'
    (ker_globalSectionsRingHomSite_residueToStalkPointHom_le_jacobson Y y)
    (fun G hG i => h₁ Y y X' f' hf' G hG i) (fun G hG => h₃ Y y X' f' hf' G hG)
  refine ⟨d₀, fun d hd => ?_⟩
  obtain ⟨hvan, hsurj⟩ := hd₀ d hd
  refine ⟨fun i hi => ?_, fun t => ?_⟩
  · exact isZero_stalk_rightDerived_tensorPow_of_isZero Y y f hf F hFqc L (g' ≫ pW) f' sq d i
      (hvan i hi)
  · have hs₁ := surjective_globalSectionsPullbackMap_of_iso
      (ObjectProperty.homMk (fibreToStalkBaseChange hsq sq) :
        representedAlgebraicSpace B S hS U ⟶ X')
      (modulePullbackTensorPowIso (g' ≫ pW) F L d)
    have hs := surjective_globalSectionsPullbackMap_representedPointHom U
      (fibreToStalkBaseChange hsq sq) _ (hs₁ hsurj)
    obtain ⟨s₀, hs₀⟩ := exists_restrictSectionAlong_eq_of_surjective (g' ≫ pW) U
      (fibreToStalkBaseChange hsq sq) p hp' _ hs t
    exact exists_open_restrictSectionAlong_eq_of_stalkBaseChange hyW hWaff f hfqc hfqs _
      (isQuasicoherentOnSite_tensor_tensorPow F L hFqc d) pW fW hWpb g' f' hX' U p
      (fibreToStalkBaseChange hsq sq) hp' t s₀ hs₀

end AlgebraicGeometry.Space

end
