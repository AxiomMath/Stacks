module

public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalInvariantsTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionTensorPowers
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSchemeNonAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalAmplenessCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveTwistHigherDirectImageVanishingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleIsoCongr
public import StacksFrontier.AlgebraicGeometry.Spaces.TwistedModuleCoherent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialLargeSite
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Ample invertible modules and cohomology on a proper algebraic space

Let `X` be an algebraic space over a scheme `S`, proper over an affine scheme `V` with Noetherian
ring of functions `R = Γ(V, 𝒪_V)`, and let `𝓛` be an invertible `𝒪_X`-module.  Suppose `X` is a
scheme — there are an object `U` of the site and an isomorphism `h_U ≅ X` — and that the
restriction of `𝓛` to `U` is ample.  Then for every coherent `𝒪_X`-module `𝓕` there is an `n₀`
with

`H ᵖ(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0` for all `n ≥ n₀` and all `p > 0`,

the cohomology being that of the small étale site of `X`.  This is the implication
(1) ⟹ (2) of Stacks 0GFA: the source deduces it from Serre's vanishing theorem on the proper
scheme `U` over `Spec R`, Stacks 0B5T, through the comparison of étale and Zariski cohomology of
quasi-coherent modules on a scheme, Stacks 03DW.

## Main definitions

* `AlgebraicGeometry.Space.isTerminalRepresentingChart`: the étale chart
  `AlgebraicGeometry.Space.representingChart` of an isomorphism `X ≅ h_U` is a terminal object of
  the small étale site.
* `AlgebraicGeometry.Space.invertibleTensorPowerSuccIsoTensorPow`: the positive powers of an
  invertible module of Stacks 01CU are the iterated tensor products.

## Main results

* `Space.isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_isZero_hgroup`:
  for a terminal étale chart `A` of `X` and a quasi-coherent `𝓜`, `H^q(X, 𝓜)` vanishes as soon
  as the Zariski cohomology `H^q(A, 𝓜|_A)` does.
* `AlgebraicGeometry.Space.exists_isZero_rightDerived_twistStep_of_isAmple`: the vanishing above.
* `AlgebraicGeometry.Space.tfae_isAmple_of_isProper_toAffine`: **Stacks 0GFA**, the equivalence
  of "`X` is a scheme and `𝓛` is ample", the vanishing above, and the vanishing of `H¹` of some
  positive twist of every coherent module, the last implication being Stacks 0D2W.

## Implementation notes

The twist `𝓕 ⊗ 𝓛^{⊗ n}` is `AlgebraicGeometry.Space.twistStep`, the spelling of Stacks 0D2W;
for `n ≥ 1` it is identified with the monoidal tensor product `𝓕 ⊗ 𝓛 ⊗ ⋯ ⊗ 𝓛`
(`AlgebraicGeometry.Space.twistStepSuccIsoTensorPow`), whose restriction to an étale chart is
computed by `AlgebraicGeometry.Space.restrictToChartTensorIso`.  The scheme `U` is read as the
étale chart `AlgebraicGeometry.Space.representingChart`; global sections are sections over it
because it is terminal, and over it the étale cohomology of a quasi-coherent module is the
Zariski cohomology of its restriction.

## References

* [Stacks Project, Tag 0GFA](https://stacks.math.columbia.edu/tag/0GFA)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
* [Stacks Project, Tag 0D2W](https://stacks.math.columbia.edu/tag/0D2W)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory Stacks.Cohomology.SiteModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] modulesMonoidalCategory

/-! ### Positive tensor powers -/

/-- **The positive powers `𝓛^{⊗ (d + 1)}` of an invertible module of Stacks 01CU are the iterated
tensor products `𝓛 ⊗ ⋯ ⊗ 𝓛`**, by induction from `𝓛^{⊗ 1} ≅ 𝓛` and the successor comparison
`𝓛^{⊗ k} ⊗ 𝓛 ≅ 𝓛^{⊗ (k + 1)}`. -/
noncomputable def invertibleTensorPowerSuccIsoTensorPow (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L] :
    (d : ℕ) → (invertibleTensorPower B S hS X.1 X.2 L ((d + 1 : ℕ) : ℤ) ≅
      tensorPow B S hS L (d + 1))
  | 0 =>
    @Stacks.SheafOfModules.Invertible.tensorPowerOneIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL)
  | d + 1 =>
    (@Stacks.SheafOfModules.Invertible.tensorPowerReindex.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) _ _
      (by push_cast; ring : ((d + 1 + 1 : ℕ) : ℤ) = ((d + 1 : ℕ) : ℤ) + 1)) ≪≫
    (@Stacks.SheafOfModules.Invertible.tensorPowerSuccIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ L
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL) _).symm ≪≫
    @Stacks.SheafOfModules.Invertible.tensorProductIso.{u, u + 1, u}
      (smallEtaleRingedSite B S hS X.1 X.2).C _ (smallEtaleRingedSite B S hS X.1 X.2).J
      (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).property _ _ _ _ _ _
      (invertibleTensorPowerSuccIsoTensorPow X L d) (Iso.refl L) ≪≫
    (modulesTensorObjIso B S hS X.1 X.2 _ _).symm

/-- **A positive twist `𝓕 ⊗ 𝓛^{⊗ (d + 1)}` is the monoidal tensor product of `𝓕` with
`𝓛 ⊗ ⋯ ⊗ 𝓛`.** -/
noncomputable def twistStepSuccIsoTensorPow (X : AlgebraicSpaces B S hS)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (d : ℕ) (F : Modules.{u, u} B S hS X.1 X.2) :
    twistStep B S hS X.1 X.2 L ((d + 1 : ℕ) : ℤ) F ≅ F ⊗ tensorPow B S hS L (d + 1) :=
  (modulesTensorObjIso B S hS X.1 X.2 F _).symm ≪≫
    whiskerLeftIso F (invertibleTensorPowerSuccIsoTensorPow X L d)

attribute [local instance 5000] SheafOfModules.instAbelian

/-! ### Cohomology over a terminal chart -/

/-- **The cohomology of a quasi-coherent module vanishes with the Zariski cohomology of its
restriction to a terminal étale chart.**  Let `A` be a terminal object of the small étale site of
`X` and `𝓜` a quasi-coherent `𝒪_X`-module.  If `H^q(A, 𝓜|_A) = 0` on the Zariski site of the
scheme of `A`, for some `q > 0`, then `H^q(X, 𝓜) = 0`.

Global sections are sections over `A`, since `A` is terminal
(`Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation`, on underlying abelian
groups, where both forgetful functors are exact), and over the chart `A` the étale cohomology of
`𝓜` is the Zariski cohomology of its restriction
(`AlgebraicGeometry.Space.isZero_rightDerived_evaluation_of_isZero_hgroup`, Stacks 03DW). -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_isZero_hgroup
    {X : AlgebraicSpaces B S hS} (A : SmallEtale B S hS X.1) (hA : IsTerminal A)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) (q : ℕ) (hq : 0 < q)
    (h : IsZero (Hgroup (chartScheme A).ringCatSheaf ⊤ q (restrictToChart B S hS X.2 M A))) :
    have := enoughInjectives_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q).obj M) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  have hX : IsInitial (op A) := hA.op
  let e := Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation.{u + 1, u, u, u}
    O (op A) hX
  have : (SheafOfModules.evaluation O (op A)).Additive := ⟨fun {_ _ _ _} => rfl⟩
  have h0 : IsZero (((SheafOfModules.evaluation O (op A)).rightDerived q).obj M) :=
    isZero_rightDerived_evaluation_of_isZero_hgroup B S hS X A M hM q hq
      (h.of_iso ((Hfunctor (chartScheme A).ringCatSheaf ⊤ q).mapIso
        ((restrictToChartSchemeIsoChartComparisonPushforward B S hS X A M).symm ≪≫
          (restrictToChartIsoRestrictToChartScheme B S hS X.2 M A).symm)))
  have h1 : IsZero ((forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O)) AddCommGrpCat.{u + 1}).obj
      (((globalSectionsFunctor.{u + 1, u, u, u} O).rightDerived q).obj M)) :=
    IsZero.of_iso (Functor.map_isZero (forget₂ (ModuleCat.{u} (O.obj.obj (op A)))
        AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}) h0)
      (((Functor.rightDerivedCompIso (globalSectionsFunctor.{u + 1, u, u, u} O)
          (forget₂ (ModuleCat.{u + 1} ↥(GlobalSectionRing O))
            AddCommGrpCat.{u + 1}) q).app M).symm ≪≫
        (ModuleSheafCohomology.rightDerivedIso e q).app M ≪≫
          (Functor.rightDerivedCompIso (SheafOfModules.evaluation O (op A))
            (forget₂ (ModuleCat.{u} (O.obj.obj (op A))) AddCommGrpCat.{u} ⋙
              AddCommGrpCat.uliftFunctor.{u + 1, u}) q).app M)
  rw [ModuleCat.isZero_iff_subsingleton]
  exact AddCommGrpCat.isZero_iff_subsingleton.1 h1

/-! ### The chart of an algebraic space which is a scheme -/

/-- **The chart of an isomorphism `X ≅ h_T` is terminal** in the small étale site of `X`: it is
isomorphic to the image of the terminal identity chart of `h_T` under the equivalence of small
étale sites `AlgebraicGeometry.Space.SmallEtale.congr` that the isomorphism induces. -/
noncomputable def isTerminalRepresentingChart {X : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (i : X.1 ≅ yoneda.obj T) :
    IsTerminal (representingChart B S hS X T i) :=
  ((isTerminalIdEtaleChart B S hS T).isTerminalObj (SmallEtale.congr B S hS i.symm).functor).ofIso
    ((ObjectProperty.fullyFaithfulι _).preimageIso (CostructuredArrow.isoMk (Iso.refl _)
      (by
        change yoneda.map (𝟙 _) ≫ i.inv = 𝟙 _ ≫ i.inv
        simp)))

/-! ### Serre vanishing on an algebraic space which is a scheme -/

/-- **The implication (1) ⟹ (2) of Stacks 0GFA.**  Let `X` be an algebraic space proper over an
affine scheme `V` with Noetherian ring of functions, and `𝓛` an invertible `𝒪_X`-module.  If `X`
is a scheme `U`, through an isomorphism `e : h_U ≅ X`, and the restriction of `𝓛` to `U` is
ample, then for every coherent `𝒪_X`-module `𝓕` there is an `n₀` with
`H ᵖ(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0` for all `n ≥ n₀` and `p > 0`.

The scheme `U` is proper over `Spec Γ(V)` (Stacks 03ZM read on representable morphisms), so
Serre's vanishing theorem, Stacks 0B5T clause (4)
(`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`), applies to
the restrictions of `𝓕` and `𝓛` to `U`; the restriction of the twist is the twist of the
restrictions (`AlgebraicGeometry.Space.restrictToChartTensorIso`), and the étale cohomology of
`X` is the Zariski cohomology of `U`, `U` being a terminal chart
(`isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_isZero_hgroup`). -/
theorem exists_isZero_rightDerived_twistStep_of_isAmple
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L]
    (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
    [Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U eX.hom)]
    (hamp : Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U eX.hom))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) :
    have := enoughInjectives_modules B S hS X.1 X.2
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p).obj
          (twistStep B S hS X.1 X.2 L n F)) := by
  have := enoughInjectives_modules B S hS X.1 X.2
  let A := representingChart B S hS X U eX.symm
  have hA : IsTerminal A := isTerminalRepresentingChart eX.symm
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom
  have hN := isNoetherian_of_isProper_toAffine B S hS V inferInstance f hf
  have hUln : IsLocallyNoetherian (chartScheme A) := isLocallyNoetherian_chart B S hS hN.2.2 A
  have hFqc : F.IsQuasicoherentOnSite := hF.toIsQuasicoherentOnSite
  let G := chartSchemeModule B S hS X F hFqc A
  have : SheafOfModules.IsCoherent G :=
    isCoherent_chartSchemeModule_of_isLocallyNoetherian B S hS X F hF A hUln
  have hLqc : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertible B S hS X L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L hL)
  let L' := baseChangeModule B S hS L U eX.hom
  have eL : restrictToChart B S hS X.2 L A ≅ L' :=
    restrictToChartIsoChartSpaceIdEtaleChart B S hS X A L hLqc
  -- the scheme `U` is proper over `Spec Γ(V)`
  let g : U ⟶ V := yoneda.preimage (eX.hom ≫ f.hom)
  have hg : IsProper B S hS (yoneda.map g) := by
    rw [Functor.map_preimage]
    exact isProper_comp' B S hS eX.hom f.hom X.2 (schemeSpace V).2 (isProper_of_isIso B S hS _) hf
  have : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map g) :=
    isProper_toScheme_map_of_isProper_yoneda_map B S hS g hg
  have : Stacks.Ample.IsInvertibleModule (chartScheme A) L' :=
    inferInstanceAs (Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) L')
  have hπ : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map g ≫
      ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom) := inferInstance
  obtain ⟨π, hπeq⟩ : ∃ π : chartScheme A ⟶
      Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
      π = (BigFppfOver.toScheme B S hS).map g ≫
        ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom := ⟨_, rfl⟩
  have : _root_.AlgebraicGeometry.IsProper π := hπeq ▸ hπ
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist π G L' hamp
  refine ⟨d₀ + 1, fun n hn p hp => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have hPqc := isQuasicoherentOnSite_tensorPow_of_pos L hLqc (d + 1) (Nat.succ_pos d)
  have hMqc : (F ⊗ tensorPow B S hS L (d + 1)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 F _
  obtain ⟨eP⟩ :=
    nonempty_restrictToChart_tensorPow_iso_tensorPowModule A L hLqc L' eL (d + 1) (Nat.succ_pos d)
  have eM : restrictToChart B S hS X.2 (F ⊗ tensorPow B S hS L (d + 1)) A ≅
      Stacks.RelativeVeryAmple.tensorModules (chartScheme A) G
        (Stacks.Ample.tensorPowModule (chartScheme A) L' ((d + 1 : ℕ) : ℤ)) :=
    restrictToChartTensorIso B S hS X A F (tensorPow B S hS L (d + 1)) ≪≫
      Stacks.RelativeVeryAmple.tensorModulesMapIso (chartScheme A)
        (restrictToChartIsoChartSchemeModule B S hS X F hFqc A) eP
  exact (isZero_rightDerived_globalSectionsFunctor_of_isTerminal_of_isZero_hgroup A hA _ hMqc p hp
    ((hd₀ (d + 1) p (by omega) hp).of_iso ((Hfunctor (chartScheme A).ringCatSheaf ⊤ p).mapIso
      eM))).of_iso
    (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p).mapIso
      (twistStepSuccIsoTensorPow X L d F))

/-! ### Stacks 0GFA -/

/-- **Stacks 0GFA.**  Let `X` be an algebraic space proper over a Noetherian ring `R` — here an
affine object `V` of the site with `Γ(V, 𝒪_V) = R` Noetherian and a proper `f : X ⟶ h_V` — and let
`𝓛` be an invertible `𝒪_X`-module.  The following are equivalent:

1. `X` is a scheme and `𝓛` is ample on it: there are an object `U` of the site and an
   isomorphism `e : h_U ≅ X` for which the restriction of `𝓛` to `U` is an invertible and ample
   module;
2. for every coherent `𝒪_X`-module `𝓕` there is an `n₀ ≥ 0` with `H ᵖ(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0` for
   all `n ≥ n₀` and `p > 0`;
3. for every coherent `𝒪_X`-module `𝓕` there is an `n ≥ 1` with `H¹(X, 𝓕 ⊗ 𝓛^{⊗ n}) = 0`.

(1) ⟹ (2) is `AlgebraicGeometry.Space.exists_isZero_rightDerived_twistStep_of_isAmple` (Serre's
vanishing theorem on the scheme, Stacks 0B5T), (2) ⟹ (3) is immediate, and (3) ⟹ (1) is Stacks
0D2W (`exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep`), `X` being
Noetherian as it is proper over a Noetherian affine scheme. -/
@[stacks 0GFA]
theorem tfae_isAmple_of_isProper_toAffine
    (V : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace V) (hf : IsProper B S hS f.hom)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property L] :
    have := enoughInjectives_modules B S hS X.1 X.2
    List.TFAE [
      ∃ (U : BigFppfOver B S hS) (eX : yoneda.obj U ≅ X.1)
        (_ : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U eX.hom)),
        Stacks.Ample.IsAmple ((BigFppfOver.toScheme B S hS).obj U)
          (baseChangeModule B S hS L U eX.hom),
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
          IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p).obj
              (twistStep B S hS X.1 X.2 L n F)),
      ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F →
        ∃ n : ℕ, 1 ≤ n ∧ IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 1).obj
            (twistStep B S hS X.1 X.2 L n F))] := by
  have := enoughInjectives_modules B S hS X.1 X.2
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) :=
    isLocallyNoetherian_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).obj V).isoSpec.hom
  tfae_have 1 → 2 := fun ⟨U, eX, _, hamp⟩ F hF =>
    exists_isZero_rightDerived_twistStep_of_isAmple V f hf L U eX hamp F hF
  tfae_have 2 → 3 := fun h F hF => by
    obtain ⟨n₀, hn₀⟩ := h F hF
    exact ⟨n₀ + 1, by omega, hn₀ (n₀ + 1) (by omega) 1 one_pos⟩
  tfae_have 3 → 1 := fun h =>
    exists_isAmple_of_forall_isCoherent_isZero_rightDerived_one_twistStep B.contains_terminal X
      (isNoetherian_of_isProper_toAffine B S hS V inferInstance f hf) L h
  tfae_finish

end AlgebraicGeometry.Space

end
