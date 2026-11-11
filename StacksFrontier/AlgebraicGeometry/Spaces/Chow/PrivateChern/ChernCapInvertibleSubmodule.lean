module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SubbundleZeroSchemeCartier
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreCapVanishingLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreClassesFlatPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernCapChowTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FirstChernClassOfRankOne
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.WhitneyAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SegreCapInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ProjectiveBundleSegreZero
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeTwistTensorPower
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingInduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.FilteredTotalChernClass

/-!
# Chern classes of an extension of a finite locally free module by an invertible one

Let `X` be a good algebraic space over `B` and `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` a short exact sequence of
`𝒪_X`-modules with `ℒ` invertible and `ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`.
Then **`c(ℰ) = c(ℒ) c(ℱ)`**, degree by degree

  `c_{n+1}(ℰ) = c_{n+1}(ℱ) + c₁(ℒ) c_n(ℱ)`.

On `π : 𝐏(ℰ) ⟶ X` the composite `π^*ℒ ⟶ π^*ℰ ⟶ 𝒪(1)` is a section `σ` of
`𝒩 = 𝒪(1) ⊗ π^*ℒ^{-1}` whose zero scheme is `𝐏(ℱ)`, a relative effective Cartier divisor
(`AlgebraicGeometry.Space.PrivateChern.isRelativeEffectiveCartierDivisor_subbundleZeroScheme`),
and `c₁(𝒪(1)) = c₁(𝒩) + c₁(π^*ℒ)`. Hence, by
`AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_succ_eq_vanishingLocusDatum`,
the Segre operations satisfy `t_{n+1}(ℰ) = t_{n+1}(ℱ) + t_n(ℰ) ∘ c₁(ℒ)`, which is the relation
`s(ℰ) c(ℒ) = s(ℱ)` between the Segre series; inverting it gives the statement. For `r = 0`, `ℰ ≅ ℒ`
and the relation is
`AlgebraicGeometry.Space.PrivateChern.segreCapOfModule_succ_of_isInvertibleModule`.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_shortExact`: the degree-wise
  relation `c_{n+1}(ℰ) = c_{n+1}(ℱ) + c₁(ℒ) c_n(ℱ)` on `CH_*(X)`, from which Stacks 0ES8 in
  `A^*(X)` is deduced
  (`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_eq_mul_of_shortExact`).
* `AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_shortComplex`: the same for a short
  exact short complex.
* `AlgebraicGeometry.Space.PrivateChern.segreCapOfModule_succ_of_shortExact`: the relation
  `t_{n+1}(ℰ) = t_{n+1}(ℱ) + t_n(ℰ) ∘ c₁(ℒ)` between the Segre operations.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_eq_of_isPullback_id`:
  projective bundle data identified over `X` compatibly with the twists have the same Segre
  operations.

## References

* [Stacks Project, Tag 0ES8](https://stacks.math.columbia.edu/tag/0ES8)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance] modulesMonoidalCategory

variable {D : BaseSpaceDimensionSituation.{u}}

section Subbundle

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {E F L : Modules.{u, u} B S hS X.1 X.2}
  [hE : E.IsQuasicoherentOnSite] [hF : F.IsQuasicoherentOnSite]
  (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite E)
  (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite F) (q : E ⟶ F)
  (hq : ∀ V : SmallEtale B S hS X.1, Epi (chartModuleMap q V)) (i : L ⟶ E)
  (hL : IsInvertibleModule X L)

include hE hF hq in
/-- **`𝐏(ℱ) ≅ Z(σ)` over `X`, compatibly with the twists**: the isomorphism `e` of
`AlgebraicGeometry.Space.PrivateChern.exists_iso_subbundleZeroScheme` lies over `X`, and the
restriction of `𝒪_{𝐏(ℰ)}(1)` to `Z(σ)` is the pullback of `𝒪_{𝐏(ℱ)}(1)` along `e⁻¹`. -/
theorem exists_iso_subbundleZeroScheme_twist (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite) :
    ∃ e : projectiveBundle F hfreeF ≅ (⟨(subbundleZeroScheme hfreeE i hL).1.toFunctor,
        (subbundleZeroScheme hfreeE i hL).2.1⟩ : AlgebraicSpaces B S hS),
      (subbundleZeroScheme hfreeE i hL).1.ι ≫ (projectiveBundleProj E hfreeE).hom =
          e.inv.hom ≫ (projectiveBundleProj F hfreeF).hom ∧
        Nonempty ((modulePullback B S hS e.inv).obj (projectiveBundleTwist F hfreeF).obj ≅
          (modulePullback B S hS (closedSubspaceHom B S hS (projectiveBundle E hfreeE).2
            (subbundleZeroScheme hfreeE i hL).1 (subbundleZeroScheme hfreeE i hL).2)).obj
              (projectiveBundleTwist E hfreeE).obj) := by
  have : Epi q := hC.epi_g
  obtain ⟨e, he⟩ := exists_iso_subbundleZeroScheme hfreeE hfreeF q hq i hL hiq hC hLq
  obtain ⟨θ, -⟩ := exists_projectiveBundleEmbedding_twistIso hfreeE hfreeF q hq
  have h1 : e.inv ≫ projectiveBundleEmbedding hfreeE hfreeF q hq =
      ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι := by
    rw [← he, Iso.inv_hom_id_assoc]
  have h2 : ObjectProperty.homMk (subbundleZeroScheme hfreeE i hL).1.ι ≫
      projectiveBundleProj E hfreeE = e.inv ≫ projectiveBundleProj F hfreeF := by
    rw [← h1, Category.assoc, projectiveBundleEmbedding_comp_proj]
  have h3 : e.inv ≫ projectiveBundleEmbedding hfreeE hfreeF q hq =
      closedSubspaceHom B S hS (projectiveBundle E hfreeE).2
        (subbundleZeroScheme hfreeE i hL).1 (subbundleZeroScheme hfreeE i hL).2 := h1
  exact ⟨e, congrArg (fun m => m.hom) h2,
    ⟨(modulePullback B S hS _).mapIso θ.symm ≪≫
      (QuasiCoherentDescent.pullbackComparison B S hS _
        (projectiveBundleEmbedding hfreeE hfreeF q hq) _ h3 _).symm⟩⟩

include hE hF hq in
/-- `AlgebraicGeometry.Space.PrivateChern.exists_iso_subbundleZeroScheme_twist` with the projective
bundles, the zero scheme, the projections and the twists given up to equality. -/
theorem exists_iso_subbundleZeroScheme_twist_of_eq (hiq : i ≫ q = 0)
    (hC : (ShortComplex.mk i q hiq).ShortExact) (hLq : L.IsQuasicoherentOnSite)
    {PE PF : AlgebraicSpaces B S hS} (hPE : PE = projectiveBundle E hfreeE)
    (hPF : PF = projectiveBundle F hfreeF) {Y : ClosedSubspaces B S hS PE.1}
    (hY : HEq Y (subbundleZeroScheme hfreeE i hL)) {πE : PE.1 ⟶ X.1} {πF : PF.1 ⟶ X.1}
    (hπE : HEq πE (projectiveBundleProj E hfreeE).hom)
    (hπF : HEq πF (projectiveBundleProj F hfreeF).hom)
    {ME : Modules.{u, u} B S hS PE.1 PE.2} {MF : Modules.{u, u} B S hS PF.1 PF.2}
    (hME : HEq ME (projectiveBundleTwist E hfreeE).obj)
    (hMF : HEq MF (projectiveBundleTwist F hfreeF).obj) :
    ∃ e : PF ≅ (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS),
      Y.1.ι ≫ πE = e.inv.hom ≫ πF ∧
        Nonempty ((modulePullback B S hS e.inv).obj MF ≅
          (modulePullback B S hS (closedSubspaceHom B S hS PE.2 Y.1 Y.2)).obj ME) := by
  subst hPE hPF
  obtain rfl := eq_of_heq hY
  obtain rfl := eq_of_heq hπE
  obtain rfl := eq_of_heq hπF
  obtain rfl := eq_of_heq hME
  obtain rfl := eq_of_heq hMF
  exact exists_iso_subbundleZeroScheme_twist hfreeE hfreeF q hq i hL hiq hC hLq

end Subbundle


/-- **Projective bundle data identified over `X` compatibly with the twists have the same Segre
operations**: if `f' : P' ⟶ P` is an isomorphism over `X` (a cartesian square over the identity)
with `f'^*𝒪_P(1) ≅ 𝒪_{P'}(1)`, then `t_i(P') = t_i(P)`. -/
theorem ProjectiveBundleDatum.segreCap_eq_of_isPullback_id {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {d : ℕ} (P P' : ProjectiveBundleDatum D sX hX d)
    {f' : P'.space ⟶ P.space} (sq : IsPullback f' P'.proj P.proj (𝟙 X))
    (e : pullbackLine D P'.toBase P'.isGood P.toBase P.isGood f' P.twist ≅ P'.twist) (i : ℕ) :
    P'.segreCap.{u, u + 1} i = P.segreCap i := by
  have het : IsEtale D.site D.base D.base_mem (𝟙 X) := isEtale_of_isIso D.site D.base D.base_mem _
  have hflat := isFlat_of_isEtale D.site D.base D.base_mem het
  have hr := hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem (𝟙 X) hX.1 het
  refine AddMonoidHom.ext fun α => ?_
  have h := P.segreCap_flatPullbackChow P' (Category.id_comp sX) 0 hflat hr sq e i α
  rwa [flatPullbackChow_id, flatPullbackChow_id] at h

/-- **Projective bundle data isomorphic over `X` compatibly with the twists have the same Segre
operations**:
`AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_eq_of_isPullback_id` for an
isomorphism `e : P ≅ P'` of algebraic spaces over `X` with `(e⁻¹)^*𝒪_P(1) ≅ 𝒪_{P'}(1)`. -/
theorem ProjectiveBundleDatum.segreCap_eq_of_iso {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {d : ℕ} (P P' : ProjectiveBundleDatum D sX hX d)
    (e : (⟨P.space, P.isGood.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ≅
      ⟨P'.space, P'.isGood.1⟩) (hproj : P'.proj = e.inv.hom ≫ P.proj)
    (θ : (modulePullback D.site D.base D.base_mem e.inv).obj P.twist ≅ P'.twist) (i : ℕ) :
    P'.segreCap.{u, u + 1} i = P.segreCap i := by
  have hiso : IsIso e.inv.hom := (ObjectProperty.ι _).map_isIso e.inv
  exact P.segreCap_eq_of_isPullback_id P' (f' := e.inv.hom)
    (@IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ hiso inferInstance
      ⟨hproj.symm.trans (Category.comp_id _).symm⟩) θ i

variable {X : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX}

/-- **The vanishing locus datum of `σ` has the Segre operations of `ℱ`**: it is isomorphic to
the projective bundle datum of `ℱ` over `X`, compatibly with the twists. -/
theorem segreCap_vanishingLocusDatum_subbundle
    (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)) (hT : T.ShortExact)
    (h₁ : IsInvertibleModule (goodSpace hX) T.X₁) (d : ℕ)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (d + 2))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ (d + 1)) [T.X₂.IsQuasicoherentOnSite]
    [T.X₃.IsQuasicoherentOnSite] (hfreeE : SheafOfModules.IsFiniteLocallyFreeOnSite T.X₂)
    (hfreeF : SheafOfModules.IsFiniteLocallyFreeOnSite T.X₃)
    (hLq : T.X₁.IsQuasicoherentOnSite)
    (hq : ∀ V : SmallEtale D.site D.base D.base_mem (goodSpace hX).1,
      Epi (chartModuleMap (X := goodSpace hX) T.g V))
    (hA : IsInvertibleModule (projectiveBundle (X := goodSpace hX) T.X₂ hfreeE)
      ((modulePullback D.site D.base D.base_mem
        (projectiveBundleProj (X := goodSpace hX) T.X₂ hfreeE)).obj T.X₁))
    (hE : IsRelativeEffectiveCartierDivisor D.site D.base D.base_mem
      (ObjectProperty.homMk (projectiveBundleDatum T.X₂ (d + 1) h₂).proj :
        (⟨(projectiveBundleDatum T.X₂ (d + 1) h₂).space,
          (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood.1⟩ :
            AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩)
      (vanishingLocus D (projectiveBundleDatum T.X₂ (d + 1) h₂).toBase
        (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood
        (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
        (morphismSection hA (subbundleMorphism (X := goodSpace hX) hfreeE T.f)))) (i : ℕ) :
    ((projectiveBundleDatum T.X₂ (d + 1) h₂).vanishingLocusDatum
        (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
        (morphismSection hA (subbundleMorphism (X := goodSpace hX) hfreeE T.f))
          hE).segreCap.{u, u + 1} i = (projectiveBundleDatum T.X₃ d h₃).segreCap i := by
  obtain ⟨e, hι, ⟨θ⟩⟩ := exists_iso_subbundleZeroScheme_twist_of_eq (X := goodSpace hX) hfreeE
    hfreeF T.g hq T.f h₁ T.zero hT hLq (PE := ⟨(projectiveBundleDatum T.X₂ (d + 1) h₂).space,
      (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood.1⟩)
    (PF := ⟨(projectiveBundleDatum T.X₃ d h₃).space, (projectiveBundleDatum T.X₃ d h₃).isGood.1⟩)
    rfl rfl (Y := vanishingLocus D (projectiveBundleDatum T.X₂ (d + 1) h₂).toBase
      (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood
      (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
      (morphismSection hA (subbundleMorphism (X := goodSpace hX) hfreeE T.f))) HEq.rfl
    (πE := (projectiveBundleDatum T.X₂ (d + 1) h₂).proj)
    (πF := (projectiveBundleDatum T.X₃ d h₃).proj) HEq.rfl HEq.rfl
    (ME := (projectiveBundleDatum T.X₂ (d + 1) h₂).twist)
    (MF := (projectiveBundleDatum T.X₃ d h₃).twist) HEq.rfl HEq.rfl
  exact ProjectiveBundleDatum.segreCap_eq_of_iso (projectiveBundleDatum T.X₃ d h₃)
    ((projectiveBundleDatum T.X₂ (d + 1) h₂).vanishingLocusDatum
      (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
      (morphismSection hA (subbundleMorphism (X := goodSpace hX) hfreeE T.f)) hE) e hι θ i

/-- **The Segre operations of an extension by an invertible module**: for
`0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` short exact with `ℒ` invertible and `ℰ`, `ℱ` finite locally free of
ranks `d + 2` and `d + 1`, `t_{n+1}(ℰ) = t_{n+1}(ℱ) + t_n(ℰ) ∘ c₁(ℒ)`, with `c₁(ℒ)` the first Chern
class `AlgebraicGeometry.Space.PrivateChern.chernCap` of `ℒ` as a module of rank one. -/
theorem segreCapOfModule_succ_of_shortExact
    (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)) (hT : T.ShortExact)
    (h₁ : IsInvertibleModule (goodSpace hX) T.X₁) (d : ℕ)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (d + 2))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ (d + 1)) (n : ℕ) :
    segreCapOfModule.{u, u + 1} T.X₂ (d + 2) h₂ (n + 1) =
      segreCapOfModule.{u, u + 1} T.X₃ (d + 1) h₃ (n + 1) +
        segreCapOfModule.{u, u + 1} T.X₂ (d + 2) h₂ n *
          chernCap.{u, u + 1} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁) 1 := by
  let := isQuasicoherentOnSite_of_rank T.X₂ h₂
  let := isQuasicoherentOnSite_of_rank T.X₃ h₃
  have hfreeE := isFiniteLocallyFreeOnSite_of_rank T.X₂ h₂
  have hfreeF := isFiniteLocallyFreeOnSite_of_rank T.X₃ h₃
  have hLq : T.X₁.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_rank (sX := sX) (hX := hX)
    T.X₁ (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁)
  have hq := epi_chartModuleMap (X := goodSpace hX) T.g T.f T.zero hT hLq
  have hE := isRelativeEffectiveCartierDivisor_subbundleZeroScheme (X := goodSpace hX) hfreeE
    hfreeF T.g hq T.f h₁ T.zero hT hLq d h₃
  have hA := isInvertibleModule_subbundleSource (X := goodSpace hX) hfreeE h₁
  have hM := isInvertibleModule_projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE
  have hNi := isInvertibleModule_morphismSectionModule hA
    (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj hM
  have hN : IsInvertibleSheaf D (projectiveBundleDatum T.X₂ (d + 1) h₂).toBase
      (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood
      (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hNi
  have : Stacks.SheafOfModules.IsInvertible _ _ ((modulePullback D.site D.base D.base_mem
      (projectiveBundleProj (X := goodSpace hX) T.X₂ hfreeE)).obj T.X₁) := hA
  have : Stacks.SheafOfModules.IsInvertible _ _ (morphismSectionModule hA
      (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj) := hNi
  have hAN := isInvertible_modulesTensorObj ((modulePullback D.site D.base D.base_mem
      (projectiveBundleProj (X := goodSpace hX) T.X₂ hfreeE)).obj T.X₁)
    (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
  have c1 := firstChernCapChow_congr_iso D (projectiveBundleDatum T.X₂ (d + 1) h₂).toBase
    (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood _ _ hAN hM
    (morphismSectionTensorIso hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
  have c2 := firstChernCapChow_tensorObj (projectiveBundleDatum T.X₂ (d + 1) h₂).isGood _ _
    hA hNi hAN
  have key := fun α => ProjectiveBundleDatum.segreCap_succ_eq_vanishingLocusDatum
    (projectiveBundleDatum T.X₂ (d + 1) h₂)
    (morphismSectionModule hA (projectiveBundleTwist (X := goodSpace hX) T.X₂ hfreeE).obj)
    (morphismSection hA (subbundleMorphism (X := goodSpace hX) hfreeE T.f)) hE T.X₁ h₁ hN
    (fun β => (congrArg (fun f => f β) (c1.symm.trans c2)).trans (add_comm _ _)) n α
  have hcmp := segreCap_vanishingLocusDatum_subbundle T hT h₁ d h₂ h₃ hfreeE hfreeF hLq hq hA hE
    (n + 1)
  refine AddMonoidHom.ext fun α => ?_
  rw [chernCap_one_eq_firstChernCapChow T.X₁ _ h₁]
  exact (key α).trans (congrArg (· + _) (congrArg (fun f => f α) hcmp))

/-- The abelian structure of the `𝒪_X`-modules, at the universe of the schemes. -/
local instance : Abelian (Modules.{u, u} D.site D.base D.base_mem X hX.1) :=
  SheafOfModules.instAbelian _

/-- **The Segre operations of an invertible module extended by zero**: for
`0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` short exact with `ℒ` invertible, `ℰ` of rank one and `ℱ` of rank zero,
`t_{n+1}(ℰ) = t_n(ℰ) ∘ c₁(ℒ)`: `ℱ = 0`, so `ℰ ≅ ℒ`. -/
theorem segreCapOfModule_succ_of_shortExact_rank_zero
    (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1)) (hT : T.ShortExact)
    (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ 1)
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ 0) (n : ℕ) :
    segreCapOfModule.{u, u + 1} T.X₂ 1 h₂ (n + 1) =
      segreCapOfModule.{u, u + 1} T.X₃ 0 h₃ (n + 1) +
        segreCapOfModule.{u, u + 1} T.X₂ 1 h₂ n *
          chernCap.{u, u + 1} T.X₁ 1
            (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule (goodSpace hX) h₁) 1 := by
  have hfi : IsIso T.f := (hT.isIso_f_iff).2
    (RingedSite.IsFiniteLocallyFreeOfRank.isZero_of_rank_zero _ h₃)
  have e : T.X₁ ≅ T.X₂ := @asIso _ _ _ _ T.f hfi
  have : Stacks.SheafOfModules.IsInvertible _ _ T.X₁ := h₁
  have h₂' : IsInvertibleModule (goodSpace hX) T.X₂ :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ e
  rw [segreCapOfModule_succ_of_isInvertibleModule T.X₂ h₂ h₂' n,
    chernCap_one_eq_firstChernCapChow T.X₁ _ h₁,
    firstChernCapChow_congr_iso D sX hX T.X₂ T.X₁ h₂' h₁ e.symm]
  exact (zero_add _).symm

/-- **The degree-wise relation of Stacks 0ES8 on `CH_*(X)`.** Let `X/B` be a good algebraic space
(Situation 0EDT) and `0 ⟶ ℒ ⟶ ℰ ⟶ ℱ ⟶ 0` a short exact sequence of `𝒪_X`-modules with `ℒ`
invertible and `ℰ`, `ℱ` finite locally free of ranks `r + 1` and `r`. Then, for the operations
`c_n(-) ∩ -` on `CH_*(X)` of `AlgebraicGeometry.Space.PrivateChern.chernCap`,

  `c_{n+1}(ℰ) ∩ - = c_{n+1}(ℱ) ∩ - + c₁(ℒ) ∩ (c_n(ℱ) ∩ -)` on `CH_*(X)`.

This is an identity of operations on the Chow homology of `X` itself, not yet the statement of
Stacks 0ES8 in `A^*(X)`. That statement, `c(ℰ) = c(ℒ) c(ℱ)` for the total Chern classes in the
Chow cohomology ring, is
`AlgebraicGeometry.Space.ChowCohomologyAlgebra.totalChernClass_eq_mul_of_shortExact`, which
applies this relation on every good test space `g : Y ⟶ X` to the inverse image of the sequence
(`AlgebraicGeometry.Space.shortExact_map_modulePullback_of_isFiniteLocallyFreeOfRank`), after
identifying the cap operations of the bivariant Chern classes on `CH_*(Y)` with these operations
for `g^*ℰ` (`AlgebraicGeometry.Space.chowGroupCanonicalToChowHomology_chernCap`). -/
theorem chernCap_succ_eq_of_shortExact {L E F : Modules.{u, u} D.site D.base D.base_mem X hX.1}
    (i : L ⟶ E) (q : E ⟶ F) (hiq : i ≫ q = 0) (hC : (ShortComplex.mk i q hiq).ShortExact)
    (hL : IsInvertibleModule (goodSpace hX) L) (r : ℕ)
    (hE : IsFiniteLocallyFreeOfRank D sX hX E (r + 1)) (hF : IsFiniteLocallyFreeOfRank D sX hX F r)
    (n : ℕ) :
    chernCap.{u, u + 1} E (r + 1) hE (n + 1) =
      chernCap.{u, u + 1} F r hF (n + 1) +
        chernCap.{u, u + 1} L 1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
          (goodSpace hX) hL) 1 * chernCap.{u, u + 1} F r hF n := by
  cases r with
  | zero =>
    exact chernCap_succ_eq_of_segreCap_mul E F 1 0 hE hF _
      (segreCapOfModule_succ_zero E 0 hE)
      (segreCapOfModule_succ_of_shortExact_rank_zero (ShortComplex.mk i q hiq) hC hL hE hF) n
  | succ d =>
    exact chernCap_succ_eq_of_segreCap_mul E F (d + 2) (d + 1) hE hF _
      (segreCapOfModule_succ_zero E (d + 1) hE)
      (segreCapOfModule_succ_of_shortExact (ShortComplex.mk i q hiq) hC hL d hE hF) n

/-- `AlgebraicGeometry.Space.PrivateChern.chernCap_succ_eq_of_shortExact` for a short exact
short complex, in the form used by the Whitney formula. -/
theorem chernCap_succ_eq_of_shortComplex {X : D.Ambient} {sX : X ⟶ D.space} (hX : D.IsGood sX)
    (r : ℕ) (T : ShortComplex (Modules.{u, u} D.site D.base D.base_mem X hX.1))
    (hT : T.ShortExact) (h₁ : IsInvertibleModule (goodSpace hX) T.X₁)
    (h₂ : IsFiniteLocallyFreeOfRank D sX hX T.X₂ (r + 1))
    (h₃ : IsFiniteLocallyFreeOfRank D sX hX T.X₃ r) (n : ℕ) :
    chernCap.{u, u + 1} T.X₂ (r + 1) h₂ (n + 1) =
      chernCap.{u, u + 1} T.X₃ r h₃ (n + 1) +
        chernCap.{u, u + 1} T.X₁ 1 (isFiniteLocallyFreeOfRank_one_of_isInvertibleModule
          (goodSpace hX) h₁) 1 * chernCap.{u, u + 1} T.X₃ r h₃ n :=
  chernCap_succ_eq_of_shortExact T.f T.g T.zero hT h₁ r h₂ h₃ n

end AlgebraicGeometry.Space.PrivateChern

end
