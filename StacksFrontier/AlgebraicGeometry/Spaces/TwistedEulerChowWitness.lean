module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlterationAmpleSchemeCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyOverBaseUniverseLift
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseObjectNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedCohomologyPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedEulerDevissage
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.EulerPolynomialProper

/-!
# The witness of the dévissage for the twisted Euler characteristics

This file proves condition (3) of the dévissage of Stacks 08AN for the property of Stacks 0DN4,
by the second construction of the source's proof (the one using Chow's lemma).

## Main results

* `AlgebraicGeometry.Space.hasCoherentWitnessOnIntegralSubspaces_hasTwistedEulerPolynomialAlong`.

## References

* [Stacks Project, Tag 0DN4](https://stacks.math.columbia.edu/tag/0DN4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

universe u w

namespace AlgebraicGeometry.Space

variable {k : Type u} [Field k] {B : BigFppfSite.{u}} {hk : B.Contains (Spec (.of k))}

/-- The cohomology `H^i(Y, 𝒩)` of an `𝒪_Y`-module at the universe of the structure sheaf, as a
`k`-module. -/
private abbrev cohK (Y : AlgebraicSpaces B (Spec (.of k)) hk)
    (N : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2) (i : ℕ) : ModuleCat.{u + 1} k :=
  (ModuleCat.restrictScalars (baseRingHom k B hk Y.1 Y.2)).obj
    (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk Y.1 Y.2).O)).rightDerived i).obj N)

/-- **Twisted cohomology along a closed immersion.**  For a closed immersion `i : Z ⟶ X` and a
quasi-coherent `𝒪_Z`-module `𝒢`, `H^q(X, i_*𝒢 ⊗ L^{⊗ n}) ≅ H^q(Z, 𝒢 ⊗ (i^*L)^{⊗ n})`: the higher
direct images along a closed immersion, which is affine, vanish (Stacks 073H). -/
private def twistedCohKClosedImmersionIso {X Z : AlgebraicSpaces B (Spec (.of k)) hk}
    (g : X ⟶ (schemeSpace (baseObject k B hk) :
        AlgebraicSpaces B (Spec (.of k)) hk))
    (i : Z ⟶ X) (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom) {r : ℕ}
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]
    (G : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2) (hG : G.IsQuasicoherentOnSite)
    (n : Fin r → ℤ) (q : ℕ) :
    haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
    cohK X (twistedModule B (Spec (.of k)) hk X.1 X.2
        ((modulePushforward B (Spec (.of k)) hk i).obj G) L n) q ≅
      cohK Z (twistedModule B (Spec (.of k)) hk Z.1 Z.2 G
        (fun j => (modulePullback B (Spec (.of k)) hk i).obj (L j)) n) q :=
  twistedCohomologyRestrictScalarsIsoOfAcyclic (baseObject k B hk) g i L G
    (fun p hp => isZero_rightDerived_modulePushforward_of_isQuasicoherentOnSite B (Spec (.of k)) hk
      i (isAffineHom_of_isClosedImmersion B (Spec (.of k)) hk _ hi) G hG p hp) n q

attribute [local instance] hasInjectiveResolutions_modules in
/-- The comparison of the twisted cohomology of a module associated with a quasi-coherent module
on a scheme of the site, proper over `k`, with the Zariski cohomology of the corresponding twist
on the scheme.  This is the hypothesis the witness below consumes. -/
def RepresentedTwistedCohomologyComparison (k : Type u) [Field k] (B : BigFppfSite.{u})
    (hk : B.Contains (Spec (.of k))) : Prop :=
  ∀ (U : BigFppfOver B (Spec (.of k)) hk) (w : U ⟶ baseObject k B hk)
    [_root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B (Spec (.of k)) hk).map w)]
    (F : ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Modules)
    (hF : SheafOfModules.IsQuasicoherent F) {r : ℕ}
    (L' : Fin r → Modules.{u, u} B (Spec (.of k)) hk (yoneda.obj U)
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U))
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk (yoneda.obj U))
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk
        (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U)).O).property (L' j)],
    ∃ (L'' : Fin r → ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).Modules)
      (hL'' : ∀ j, SheafOfModules.IsInvertible
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).presheaf
        ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj U).ringCatSheaf.2 (L'' j)),
      ∀ (n : Fin r → ℤ) (i : ℕ),
        Module.finrank k ((ModuleCat.restrictScalars (baseRingHom k B hk (yoneda.obj U)
            (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U))).obj
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B (Spec (.of k)) hk
              (yoneda.obj U) (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U)).O)).rightDerived
                i).obj
            (twistedModule B (Spec (.of k)) hk (yoneda.obj U)
              (isAlgebraicSpace_yoneda B (Spec (.of k)) hk U)
              ((representedQuasicoherentSchemeEquivalence B (Spec (.of k)) hk U).functor.obj
                ⟨F, hF⟩).obj L' n))) =
        Module.finrank k (cohomologyOverField k ((BigFppfOver.toScheme B (Spec (.of k)) hk).map w)
          (@twistedSheaf _ _ F L'' hL'' n) i)

section Witness

/-- A closed immersion followed by a proper morphism is proper. -/
private theorem isProper_comp_closedImmersion {A C D : AlgebraicSpaces B (Spec (.of k)) hk}
    (a : A ⟶ C) (ha : IsClosedImmersion B (Spec (.of k)) hk a.hom) {c : C ⟶ D}
    (hc : IsProper B (Spec (.of k)) hk c.hom) : IsProper B (Spec (.of k)) hk (a ≫ c).hom :=
  isProper_comp B (Spec (.of k)) hk A.2 C.2 D.2 a.hom c.hom
    (isProper_of_isClosedImmersion B (Spec (.of k)) hk A.2 C.2 _ ha) hc

variable (k B hk) (X : AlgebraicSpaces B (Spec (.of k)) hk) {r : ℕ}
    (f : X.1 ⟶ yoneda.obj (baseObject k B hk)) (hf : IsProper B (Spec (.of k)) hk f)
    (L : Fin r → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O)).property (L j)]
    (Z : AlgebraicSpaces B (Spec (.of k)) hk) (i : Z ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)

attribute [local instance] hasInjectiveResolutions_modules in
/-- **Condition (3) of the dévissage of Stacks 08AN for the property of Stacks 0DN4**, granted the
comparison `RepresentedTwistedCohomologyComparison`: on every reduced closed subspace `W ⊆ Z`
with irreducible space of points there is a coherent `𝒪_Z`-module with scheme-theoretic support
`W` whose direct image to `X` has twisted Euler characteristics given by a rational polynomial of
total degree at most `dim Z`. -/
theorem hasCoherentWitnessOnIntegralSubspaces_hasTwistedEulerPolynomialAlong
    (hcomp : RepresentedTwistedCohomologyComparison k B hk) :
    HasCoherentWitnessOnIntegralSubspaces B (Spec (.of k)) hk Z
      (HasTwistedEulerPolynomialAlong.{u, w} k B hk X f hf L Z i hi
        (dimension B (Spec (.of k)) hk Z.1 Z.2)) := by
  intro W hW hWirr
  let V := baseObject k B hk
  let Y : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj V, isAlgebraicSpace_yoneda B (Spec (.of k)) hk V⟩
  have hV : IsAffine ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj V) := by
    change IsAffine (Spec (.of k))
    infer_instance
  let Ws := closedSubfunctorSpace B (Spec (.of k)) hk hW
  let j := closedSubfunctorι B (Spec (.of k)) hk hW
  let fX : X ⟶ Y := ObjectProperty.homMk f
  have hZp : IsProper B (Spec (.of k)) hk (i ≫ fX).hom := isProper_comp_closedImmersion i hi hf
  have hWp : IsProper B (Spec (.of k)) hk (j ≫ i ≫ fX).hom :=
    isProper_comp_closedImmersion j hW.2 hZp
  have hZN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Z.1 Z.2 _ hZp
  have hWsNoeth := isNoetherian_of_isProper_baseObject k B hk Ws.1 Ws.2 _ hWp
  have hWsint : IsIntegralSpace B (Spec (.of k)) hk Ws.1 :=
    ⟨hWirr.1, isDecentSpace_of_isProper_baseObject k B hk Ws.1 Ws.2 _ hWp, hWirr.2⟩
  obtain ⟨P, ρ, LP, hLPinv, hLPamp, hρp, hρs, hdimP⟩ :=
    exists_properSurjective_ampleSchemeCover_dimension_le B (Spec (.of k)) hk V hV Ws.2 hWsint
      hWsNoeth.2.2 _ hWp
  let Ps : AlgebraicSpaces B (Spec (.of k)) hk :=
    ⟨yoneda.obj P, isAlgebraicSpace_yoneda B (Spec (.of k)) hk P⟩
  let ρ' : Ps ⟶ Ws := ObjectProperty.homMk ρ
  have hρrep : yoneda.relativelyRepresentable ρ'.hom :=
    Functor.relativelyRepresentable.of_diag Ws.2.diagonal_representable ρ
  let wP : P ⟶ V := yoneda.preimage (ρ ≫ (j ≫ i ≫ fX).hom)
  have hwPp :
      _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B (Spec (.of k)) hk).map wP) := by
    refine isProper_toScheme_map_of_isProper_yoneda_map B (Spec (.of k)) hk wP ?_
    rw [Functor.map_preimage]
    exact isProper_comp B (Spec (.of k)) hk Ps.2 Ws.2 Y.2 ρ _ hρp hWp
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj V) := by
    change IsLocallyNoetherian (Spec (.of k))
    infer_instance
  have hPln : IsLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj P) :=
    LocallyOfFiniteType.isLocallyNoetherian ((BigFppfOver.toScheme B (Spec (.of k)) hk).map wP)
  obtain ⟨m₂, hm₂⟩ := exists_forall_isZero_rightDerived_modulePushforward_representedTensorPow
    B (Spec (.of k)) hk V hV hWsNoeth (j ≫ i ≫ fX).hom hWp.1 P ρ' hρrep hρp LP hLPamp
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple LP
    hLPamp (Stacks.Ample.unitModule _)
    (Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _)
    (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule _)
  let d : ℕ := max m₂ n₀.toNat
  have hd₀ : n₀ ≤ (d : ℤ) := (Int.self_le_toNat n₀).trans (by exact_mod_cast le_max_right _ _)
  let F := Stacks.Ample.tensorPowModule ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj P) LP
    (d : ℤ)
  have hFqc : SheafOfModules.IsQuasicoherent F :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule LP d
  let M := ((representedQuasicoherentSchemeEquivalence B (Spec (.of k)) hk P).functor.obj
    ⟨F, hFqc⟩).obj
  have hMcoh : IsCoherent B (Spec (.of k)) hk Ps.1 Ps.2 M :=
    isCoherent_representedQuasicoherentSchemeEquivalence B (Spec (.of k)) hk P F hFqc
      (Stacks.AmpleEventualGeneration.isFiniteType_of_isInvertibleModule F)
  let N := (modulePushforward B (Spec (.of k)) hk ρ').obj M
  have hNcoh : IsCoherent B (Spec (.of k)) hk Ws.1 Ws.2 N :=
    isCoherent_modulePushforward_of_isProper B (Spec (.of k)) hk ρ' hρrep hρp hWsNoeth.2.2 M hMcoh
  let G := (modulePushforward B (Spec (.of k)) hk j).obj N
  have hGcoh : IsCoherent B (Spec (.of k)) hk Z.1 Z.2 G :=
    isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk hZN j hW.2 N hNcoh
  obtain ⟨σ, -⟩ := hn₀ d hd₀
  refine ⟨G, hGcoh, schemeTheoreticSupport_modulePushforward_representedGenerated B (Spec (.of k))
    hk hZN hW hWirr.1 hWsNoeth.2.2 P ρ' hρrep hρp hρs F hFqc
    (SheafOfModules.GeneratingSections.equivOfIso
      (Stacks.AmpleGlobalGeneration.unitTensorIso LP (d : ℤ)) σ), hGcoh, ?_⟩
  have hLZ := fun a => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L a)
  let LZ := fun a => (modulePullback B (Spec (.of k)) hk i).obj (L a)
  have hLW := fun a => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk j (LZ a)
  let LW := fun a => (modulePullback B (Spec (.of k)) hk j).obj (LZ a)
  have hLP := fun a => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk ρ' (LW a)
  let LP' := fun a => (modulePullback B (Spec (.of k)) hk ρ').obj (LW a)
  obtain ⟨L'', hL'', hcmp⟩ := hcomp P wP F hFqc LP'
  have hFcoh : _root_.SheafOfModules.IsCoherent F :=
    have : AlgebraicGeometry.SheafOfModules.IsInvertible _ _ F :=
      Stacks.Ample.isInvertibleModule_tensorPowModule _ LP d
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible _ F
  obtain ⟨Q, hQdeg, hQ⟩ := exists_eulerPolynomial_twistedSheaf_of_isProper k
    ((BigFppfOver.toScheme B (Spec (.of k)) hk).map wP) L'' F hFcoh
  refine ⟨Q, fun n => ?_, ?_⟩
  · rw [hQ n]
    congr 1
    rw [eulerCharacteristic_eq_finsum, AlgebraicGeometry.eulerCharacteristic_eq_finsum]
    refine finsum_congr fun q => ?_
    congr 2
    have e := twistedCohKClosedImmersionIso fX i hi L G hGcoh.toIsQuasicoherentOnSite n q ≪≫
      twistedCohKClosedImmersionIso (i ≫ fX) j hW.2 LZ N hNcoh.toIsQuasicoherentOnSite n q ≪≫
      twistedCohomologyRestrictScalarsIsoOfAcyclic V (j ≫ i ≫ fX) ρ' LW M
        (fun p hp => hm₂ d (le_max_left _ _) p hp) n q
    exact ((hcmp n q).symm.trans e.toLinearEquiv.finrank_eq.symm).trans
      (finrank_cohomologyOverBase_uliftForPresentation.{u, w} B k hk X.1 X.2 _ q).symm
  · refine hQdeg.imp id fun hdeg => hdeg.trans ?_
    calc topologicalKrullDim (_root_.SheafOfModules.supp F)
        ≤ topologicalKrullDim ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj P) :=
          topologicalKrullDim_subspace_le _ _
      _ = dimension B (Spec (.of k)) hk Ps.1 Ps.2 :=
          (dimension_yoneda_eq_topologicalKrullDim B (Spec (.of k)) hk P).symm
      _ ≤ dimension B (Spec (.of k)) hk Ws.1 Ws.2 := hdimP
      _ ≤ dimension B (Spec (.of k)) hk Z.1 Z.2 :=
          dimension_le_of_isLocallyQuasiFinite B (Spec (.of k)) hk hW.1 Z.2 j.hom
            (isLocallyQuasiFinite_of_isImmersion B (Spec (.of k)) hk j.hom
              (isImmersion_of_isClosedImmersion B (Spec (.of k)) hk hW.2))

end Witness

end AlgebraicGeometry.Space

end
