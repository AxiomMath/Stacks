module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseRingUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite

/-!
# Vanishing of the cohomology of a coherent module on a proper algebraic space in large degrees

Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism of algebraic spaces and `F` a
coherent `𝒪_X`-module.  Then `Hⁱ(X, F) = 0` for all `i` large enough.  This file proves it for
`𝒪_X`-modules whose sections lie in the universe of the structure rings, by the dévissage of
Stacks 08AN on the Noetherian algebraic space `X`, exactly as finiteness is proved in
`StacksFrontier.AlgebraicGeometry.Spaces.ProperModuleCohomologyFinite`: the property "the right
derived functors of `Γ(V, f_* −)` vanish beyond some degree" holds on zero modules, satisfies
two-out-of-three by the long exact sequence (with the bound raised by one), passes to direct
summands, and holds for the witness `G = i_* ρ_*(𝓛^{⊗ d})` built from Chow's lemma and Serre's
vanishing theorem, whose cohomology vanishes in every positive degree.

## Main definitions

* `AlgebraicGeometry.Space.HasBoundedCohomologyOver`: the cohomology modules of an `𝒪_X`-module
  along a morphism to an affine scheme vanish beyond some degree.

## Main results

* `AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasBoundedCohomologyOver`: the
  third condition of Stacks 08AN for that property.
* `AlgebraicGeometry.Space.hasBoundedCohomologyOver_of_isProper`: every coherent module has it,
  along a proper morphism to an affine Noetherian scheme.
* `AlgebraicGeometry.Space.exists_forall_isZero_cohomologyOverBaseRingUniverse_of_isProper`:
  `Hⁱ(X, F) = 0` for large `i`, as cohomology over the base ring.

## Implementation notes

The witness is the one of
`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver`; its
construction is repeated here because that declaration records only the finiteness of the
witness' cohomology, while its proof shows the vanishing in positive degrees which is needed
here.

## References

* [Stacks Project, Tag 08AS](https://stacks.math.columbia.edu/tag/08AS)
* [Stacks Project, Tag 08AN](https://stacks.math.columbia.edu/tag/08AN)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪`-modules on the small étale site of an algebraic space, at the universe of the
structure rings, have enough injectives. -/
local instance (priority := 5000) enoughInjectives_modules_vanishing
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    EnoughInjectives (Modules.{u, u} B S hS F hF) :=
  enoughInjectives_modules B S hS F hF

/-- **Vanishing of the cohomology along a morphism to an affine scheme beyond some degree.**
For a morphism `f : X ⟶ Y` to the algebraic space represented by `V`, an `𝒪_X`-module has
bounded cohomology along `f` when the right derived functors of `Γ(V, f_* −)`, read over the
identity chart of `V`, vanish at it in all degrees beyond some bound.  For `V` affine this is
`Hᵖ(X, −) = 0` for all large `p`. -/
def HasBoundedCohomologyOver (V : BigFppfOver B S hS) {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (G : Modules.{u, u} B S hS X.1 X.2) : Prop :=
  have := modulePushforward_additive B S hS f
  have : (SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
      (op (idEtaleChart B S hS V))).Additive :=
    ⟨fun {_ _ _ _} => rfl⟩
  ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
    IsZero (((modulePushforward B S hS f ⋙ SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
        (isAlgebraicSpace_yoneda B S hS V)).O)) (op (idEtaleChart B S hS V))).rightDerived p).obj G)

/-- Evaluation at the identity chart of `V` on the small étale site of `V` is additive. -/
private theorem evaluation_idEtaleChart_additive (V : BigFppfOver B S hS) :
    (SheafOfModules.evaluation.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)).O))
      (op (idEtaleChart B S hS V))).Additive :=
  ⟨fun {_ _ _ _} => rfl⟩

/-- **The witness of the third condition of Stacks 08AN for bounded cohomology along a proper
morphism to an affine Noetherian scheme.**  For every reduced closed subspace `Z ⊆ X` with
irreducible space of points there is a coherent `𝒪_X`-module with scheme-theoretic support `Z`
whose cohomology along `f` vanishes in every positive degree: the module
`G = i_* ρ_*(𝓛^{⊗ d})` of
`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasFiniteCohomologyOver`, whose
cohomology along `f` is the cohomology of `𝓛^{⊗ d}` along `W ⟶ V`, which vanishes in positive
degrees by Serre's theorem. -/
theorem hasCoherentWitnessOnIntegralSubspaces_hasBoundedCohomologyOver (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom) :
    HasCoherentWitnessOnIntegralSubspaces B S hS X (HasBoundedCohomologyOver B S hS V f) := by
  intro Z hZ hZirr
  let Y : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let Zs := closedSubfunctorSpace B S hS hZ
  let i := closedSubfunctorι B S hS hZ
  have hip : IsProper B S hS i.hom := isProper_of_isClosedImmersion B S hS hZ.1 X.2 _ hZ.2
  have hg : IsProper B S hS (i ≫ f).hom :=
    isProper_comp B S hS hZ.1 X.2 Y.2 i.hom f.hom hip hf
  obtain ⟨W, ρ, hρp, hρs, T, t, hT, htq⟩ :=
    exists_properSurjective_hQuasiProjective_schemeCover_of_isProper_toAffine B S hS V hV Zs.2
      (i ≫ f).hom hg
  let Ws : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let ρ' : Ws ⟶ Zs := ObjectProperty.homMk ρ
  have hρrep : yoneda.relativelyRepresentable ρ'.hom :=
    Functor.relativelyRepresentable.of_diag Zs.2.diagonal_representable ρ
  -- The scheme `W` is proper over `V`, and carries an ample invertible module.
  have : IsAffine T := hT
  obtain ⟨L, hLinv, hLample⟩ := exists_isAmple_of_isHQuasiProjective t htq
  let w : W ⟶ V := yoneda.preimage (ρ ≫ (i ≫ f).hom)
  have hwp : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map w) := by
    refine isProper_toScheme_map_of_isProper_yoneda_map B S hS w ?_
    rw [Functor.map_preimage]
    exact isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS W) Zs.2 Y.2 ρ (i ≫ f).hom hρp hg
  have hWln : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B S hS).map w)
  have hXN := isNoetherian_of_isProper_toAffine B S hS V hV f hf
  have hZsN := isNoetherian_closedSubfunctor B S hS B.contains_terminal X hXN hZ
  -- The bounds of Serre's vanishing theorem on `W` and on the base change.
  obtain ⟨m₁, hm₁⟩ := Stacks.AlgebraicGeometry.AmpleTwistAcyclicity.twistAcyclicityOverAffineBase
    _ _ ((BigFppfOver.toScheme B S hS).map w) hV inferInstance hwp L hLample
  have : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj W) L := hLinv
  obtain ⟨m₂, hm₂⟩ :=
    exists_forall_isZero_rightDerived_modulePushforward_representedTensorPow B S hS V hV hZsN
      (i ≫ f).hom hg.1 W ρ' hρrep hρp L hLample
  -- and the bound of global generation of the twists of `𝒪_W`.
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L
    hLample (Stacks.Ample.unitModule _)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _)
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  let d : ℕ := max (max m₁ m₂) n₀.toNat
  have hd₁ : m₁ ≤ d := le_max_of_le_left (le_max_left _ _)
  have hd₂ : m₂ ≤ d := le_max_of_le_left (le_max_right _ _)
  have hd₀ : n₀ ≤ (d : ℤ) := (Int.self_le_toNat n₀).trans (by exact_mod_cast le_max_right _ _)
  let F := Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B S hS).obj W) L (d : ℤ)
  have hFinv : Stacks.Ample.IsInvertibleModule _ F :=
    Stacks.Ample.isInvertibleModule_tensorPowModule _ L d
  have hFqc : SheafOfModules.IsQuasicoherent F :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule L d
  let M := ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj ⟨F, hFqc⟩).obj
  have hMcoh : IsCoherent B S hS Ws.1 Ws.2 M :=
    isCoherent_representedQuasicoherentSchemeEquivalence B S hS W F hFqc
      (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule F)
  -- The higher direct images of `M` along `ρ` vanish.
  have := modulePushforward_additive B S hS ρ'
  have hvan : ∀ q, 0 < q → IsZero (((modulePushforward B S hS ρ').rightDerived q).obj M) :=
    hm₂ d hd₂
  -- The witness `G = i_* ρ_* M`.
  let N := (modulePushforward B S hS ρ').obj M
  have hNcoh : IsCoherent B S hS Zs.1 Zs.2 N :=
    isCoherent_modulePushforward_of_isProper B S hS ρ' hρrep hρp hZsN.2.2 M hMcoh
  refine ⟨(modulePushforward B S hS i).obj N,
    isCoherent_modulePushforward_of_isProper B S hS i hZ.2.rep hip hXN.2.2 N hNcoh, ?_, ?_⟩
  · obtain ⟨σ, -⟩ := hn₀ d hd₀
    exact schemeTheoreticSupport_modulePushforward_representedGenerated B S hS hXN.2.2 hZ hZirr.1
      hZsN.2.2 W ρ' hρrep hρp hρs F hFqc
      (SheafOfModules.GeneratingSections.equivOfIso
        (Stacks.AmpleGlobalGeneration.unitTensorIso L (d : ℤ)) σ)
  -- The cohomology of `G` along `f` is the cohomology of `M` along `W ⟶ V`, zero in positive
  -- degrees.
  refine ⟨1, fun p hp => ?_⟩
  have hterm := isTerminalIdEtaleChart B S hS V
  have := modulePushforward_additive B S hS f
  have := modulePushforward_additive B S hS (i ≫ f)
  have := modulePushforward_additive B S hS (ρ' ≫ (i ≫ f))
  have := evaluation_idEtaleChart_additive B S hS V
  have e₁ := pushforwardEvaluationRightDerivedCompIso B S hS hterm i f N
    (fun q hq => isZero_rightDerived_modulePushforward_of_isAffineHom_of_isQuasicoherentOnSite
      B S hS i (isAffineHom_of_isClosedImmersion B S hS _ hZ.2) N hNcoh.toIsQuasicoherentOnSite
      q hq) p
  have e₂ := pushforwardEvaluationRightDerivedCompIso B S hS hterm ρ' (i ≫ f) M hvan p
  have hz := isZero_rightDerived_pushforwardEvaluation_of_isZero_rightDerived_evaluation B S hS
    hterm (ρ' ≫ (i ≫ f)) (isTerminalIdEtaleChart B S hS W) M p
    (isZero_rightDerived_evaluation_idEtaleChart_of_isZero_hgroup B S hS W F hFqc p hp
      (hm₁ d hd₁ p hp))
  exact hz.of_iso (e₂ ≪≫ e₁).symm

/-- **The cohomology of a coherent module along a proper morphism to an affine Noetherian scheme
vanishes beyond some degree.**  This is the dévissage of Stacks 08AN for
`AlgebraicGeometry.Space.HasBoundedCohomologyOver`: zero modules have it; two-out-of-three is
the long exact sequence of the right derived functors, the bound being raised by one for the
kernel; a direct summand of a module with the property has it, the right derived functors being
additive; and the witness is
`AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasBoundedCohomologyOver`. -/
theorem hasBoundedCohomologyOver_of_isProper (V : BigFppfOver B S hS)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V)] {X : AlgebraicSpaces B S hS}
    (f : X ⟶ (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))
    (hf : IsProper B S hS f.hom) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) : HasBoundedCohomologyOver B S hS V f F := by
  have := modulePushforward_additive B S hS f
  have := evaluation_idEtaleChart_additive B S hS V
  let Q := modulePushforward B S hS f ⋙ SheafOfModules.evaluation
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS (yoneda.obj V)
      (isAlgebraicSpace_yoneda B S hS V)).O)) (op (idEtaleChart B S hS V))
  refine property_of_isCoherent_of_devissage B S hS B.contains_terminal X
    (isNoetherian_of_isProper_toAffine B S hS V hV f hf) (HasBoundedCohomologyOver B S hS V f)
    (fun M hM => ⟨0, fun p _ => Functor.map_isZero (Q.rightDerived p) hM⟩)
    (fun E hE _ _ _ => ⟨fun ⟨N₁, h₁⟩ ⟨N₃, h₃⟩ => ⟨max N₁ N₃, fun n hn =>
        Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₂ hE Q n
          (h₁ n (le_of_max_le_left hn)) (h₃ n (le_of_max_le_right hn))⟩,
      fun ⟨N₂, h₂⟩ ⟨N₃, h₃⟩ => ⟨max N₂ N₃ + 1, fun n hn => by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_succ_X₁ hE Q m
          (h₃ m (by omega)) (h₂ (m + 1) (by omega))⟩,
      fun ⟨N₁, h₁⟩ ⟨N₂, h₂⟩ => ⟨max N₁ N₂, fun n hn =>
        Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_X₃ hE Q n
          (h₂ n (le_of_max_le_right hn)) (h₁ (n + 1) (by omega))⟩⟩)
    (fun M r hr ⟨N, hN⟩ => ⟨N, fun p hp => by
      refine (IsZero.iff_id_eq_zero _).2 ?_
      rw [← (Q.rightDerived p).map_id, ← biproduct.ι_π_self (fun _ : Fin r => M) ⟨0, hr⟩,
        (Q.rightDerived p).map_comp, show (Q.rightDerived p).map
          (biproduct.π (fun _ : Fin r => M) ⟨0, hr⟩) = 0 from (hN p hp).eq_of_src _ _, comp_zero]⟩)
    (hasCoherentWitnessOnIntegralSubspaces_hasBoundedCohomologyOver B S hS V hV f hf) F hF

section ProperVanishing

open Stacks.Cohomology.SiteModules

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))

attribute [local instance] hasInjectiveResolutions_modules in
/-- **The cohomology of a coherent module on a proper algebraic space over a Noetherian ring
vanishes in large degrees.**  Let `A` be a Noetherian ring, `f : X ⟶ Spec A` a proper morphism
of algebraic spaces and `F` a coherent `𝒪_X`-module with sections in the universe of the
structure rings.  Then `Hⁱ(X, F) = 0` for all `i` beyond some bound.

The right derived functors of `Γ(Spec A, f_* −)` vanish at `F` in large degrees
(`AlgebraicGeometry.Space.hasBoundedCohomologyOver_of_isProper`), and `Γ(Spec A, f_* −)` is
`Γ(X, −)` as a functor to `A`-modules (`AlgebraicGeometry.Space.globalSectionsOverBaseIso`);
restriction of scalars and the universe lift are exact, so they pass through the right derived
functors, exactly as in the proof of Stacks 08AS
(`AlgebraicGeometry.Space.moduleFinite_cohomology_of_isProper`). -/
theorem exists_forall_isZero_cohomologyOverBaseRingUniverse_of_isProper [IsNoetherianRing A]
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (F : Modules.{u, u} B (Spec (.of A)) hA X hX) [IsCoherent B (Spec (.of A)) hA X hX F] :
    ∃ N : ℕ, ∀ i : ℕ, N ≤ i → IsZero (cohomologyOverBaseRingUniverse A B hA X hX F i) := by
  let V := baseObject A B hA
  let g : (⟨X, hX⟩ : AlgebraicSpaces B (Spec (.of A)) hA) ⟶
      (⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of A)) hA V⟩ :
        AlgebraicSpaces B (Spec (.of A)) hA) := ObjectProperty.homMk f
  have hV : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V) :=
    inferInstanceAs (IsAffine (Spec (.of A)))
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj V) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  obtain ⟨N, hN⟩ :=
    hasBoundedCohomologyOver_of_isProper B (Spec (.of A)) hA V hV g hf F inferInstance
  refine ⟨N, fun i hi => ?_⟩
  have := modulePushforward_additive B (Spec (.of A)) hA g
  have := evaluation_idEtaleChart_additive B (Spec (.of A)) hA V
  let O := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA
    (yoneda.obj V) (isAlgebraicSpace_yoneda B (Spec (.of A)) hA V)).O)
  have : (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let E := ModuleCat.restrictScalars.{u} (idEtaleChartBaseRingHom V) ⋙
    ModuleCat.uliftFunctor.{u + 1} A
  have : E.PreservesHomology := Functor.preservesHomologyOfExact _
  let Q := modulePushforward B (Spec (.of A)) hA g ⋙
    SheafOfModules.evaluation.{u} O (op (idEtaleChart B (Spec (.of A)) hA V))
  let Γ := globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)
  have e₁ := (Functor.rightDerivedCompIso Γ
    (ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) i).app F
  have e₂ := (Functor.rightDerivedIsoOfNatIso
    (F := Γ ⋙ ModuleCat.restrictScalars.{u + 1} (baseRingHom A B hA X hX)) (G := Q ⋙ E)
    (globalSectionsOverBaseIso V g) i).app F
  have e₃ := (Functor.rightDerivedCompIso Q E i).app F
  have h₁ : IsZero ((Q.rightDerived i ⋙ E).obj F) := E.map_isZero (hN i hi)
  exact ((h₁.of_iso e₃).of_iso e₂).of_iso e₁.symm

end ProperVanishing

end AlgebraicGeometry.Space

end
