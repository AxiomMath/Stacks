module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedFibreIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerTowerCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiTwistReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiRestrictionGeneration
public import StacksFrontier.AlgebraicGeometry.CommutingFamilyAmpleTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerModuleCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCoverTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty

/-!
# Vanishing of the cohomology of the twisted graded pieces along the closed fibre

Let `ι : P ⟶ T` be a closed immersion of affine objects of the site, cutting out
`J = ker(Γ(T) ⟶ Γ(P))`, let `f : X ⟶ h_T` be proper, and let `p : h_U ⟶ X` be the base change of
`ι` along `f`, with `U` a scheme.  For a coherent `ℱ` and an invertible `ℒ` on `X` whose
restriction to `U` is ample, there is one `d₀` with

`Hᵠ(X, Iⁿ(ℱ ⊗ ℒ^{⊗ d}) / Iⁿ⁺¹(ℱ ⊗ ℒ^{⊗ d})) = 0`  for `d ≥ d₀`, all `n` and all `q > 0`,

where `I = J 𝒪_X` (`AlgebraicGeometry.Space.fibreIdeal`).  This is the first displayed vanishing of
the proof of Stacks 0D39.

## The argument

The graded pieces `IⁿF/Iⁿ⁺¹F` of the twist are the twists of those of `ℱ`
(`AlgebraicGeometry.Space.idealPowGradedPieceTwistIso`); they are killed by `I`, so their
cohomology on `X` is the Zariski cohomology on `U` of their pullbacks
(`AlgebraicGeometry.Space.isZero_rightDerived_globalSections_of_annihilatedByKerIdeal`), and
there the pullback of the twist is the twist of the pullback
(`AlgebraicGeometry.Space.zariskiModuleTwistPowSuccIso`).  On `U`, the pullbacks of the graded
pieces of `ℱ` form a commuting family of coherent modules generated in degree `0`, and uniform
Serre vanishing applies
(`Stacks.CommutingFamily.exists_isZero_Hgroup_tensorPowTwist_of_isGenerated`).

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_idealPowGradedPiece_twist_of_isZero_Hgroup`: the
  transfer of a single vanishing from `U` to `X`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.SiteModules (globalSectionsFunctor)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An equivalence from an abelian category to a preadditive one is additive. -/
theorem additive_of_isEquivalence {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Abelian 𝒜]
    [Preadditive ℬ] (Φ : 𝒜 ⥤ ℬ) [Φ.IsEquivalence] : Φ.Additive := by
  have : Φ.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint Φ
  exact Functor.additive_of_preserves_binary_products Φ

section Setting

variable {X : AlgebraicSpaces B S hS} {P T U : BigFppfOver B S hS} (ι : P ⟶ T)
  (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (f : X ⟶ representedAlgebraicSpace B S hS T) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ P)
  (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map ι))
  {r : ℕ} (x : Fin r → Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  (hx : Ideal.span (Set.range x) = RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)

include hx in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The pulled-back generators of `J` lie in the ideal of the fibre. -/
theorem baseScalar_mem_fibreIdeal (i : Fin r) (W : SmallEtale B S hS X.1) :
    (baseScalar f (x i)).1 (op W) ∈ (fibreIdeal ι hι f).obj (op W) :=
  baseScalar_val_mem_fibreIdeal f ι hι (x i) (hx ▸ Ideal.subset_span ⟨i, rfl⟩) W

include hx in
/-- On affine charts the pulled-back generators of `J` generate the ideal of the fibre. -/
theorem exists_eq_sum_baseScalar (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A))
    (b : (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op A))
    (hb : b ∈ (fibreIdeal ι hι f).obj (op A)) :
    ∃ c : Fin r → (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj (op A),
      b = ∑ i, c i * (baseScalar f (x i)).1 (op A) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  rw [fibreIdeal_obj_eq_span (ι := ι) (hι := hι) (f := f) (x := x) (hx := hx) (W := A)] at hb
  exact (Ideal.mem_span_range_iff_exists_fun.1 hb).imp fun _ hc => hc.symm

include hsq hι in
omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The base change `p` of the closed immersion `ι` is a closed immersion. -/
theorem isClosedImmersion_of_fibreSquare : IsClosedImmersion B S hS p := by
  have hιc : IsClosedImmersion B S hS (yoneda.map ι) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@AlgebraicGeometry.IsClosedImmersion.{u}) ι).2 hι
  exact (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback hsq.flip hιc

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- The graded pieces of a coherent module along the fibre are coherent. -/
theorem isCoherent_idealPowGradedPiece_fibreIdeal
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (n : ℕ) :
    IsCoherent B S hS X.1 X.2 (idealPowGradedPiece (fibreIdeal ι hι f) F n) :=
  have h (m : ℕ) := isCoherent_idealPowModule_of_isQuasicoherentOnSite B S hS X.1 X.2 _ m F hF
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X _)
  isCoherent_cokernel B S hS X.1 X.2 (h (n + 1)) (h n) _

include hsq hx in
/-- **A single vanishing on the fibre gives the vanishing on `X`.**  If the Zariski cohomology
`Hᵠ(U, (p^* IⁿF/Iⁿ⁺¹F)|_U ⊗ ℒ_U^{⊗ (d+1)})` vanishes, so does
`Hᵠ(X, Iⁿ(ℱ ⊗ ℒ^{⊗ (d+1)})/Iⁿ⁺¹(ℱ ⊗ ℒ^{⊗ (d+1)}))`. -/
theorem isZero_rightDerived_idealPowGradedPiece_twist_of_isZero_Hgroup
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    [IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)]
    (n q' d : ℕ)
    (h : IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⊤ q'
      (Stacks.RelativeVeryAmple.tensorModules ((BigFppfOver.toScheme B S hS).obj U)
        (zariskiModule U ((modulePullback B S hS (ObjectProperty.homMk p :
          representedAlgebraicSpace B S hS U ⟶ X)).obj
            (idealPowGradedPiece (fibreIdeal ι hι f) F n)))
        (tensorPowModule ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)
          ((d + 1 : ℕ) : ℤ))))) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q').obj
        (idealPowGradedPiece (fibreIdeal ι hι f) ((twistPowFunctor L (d + 1)).obj F) n)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let P' : representedAlgebraicSpace B S hS U ⟶ X := ObjectProperty.homMk p
  let Φ := twistPowFunctor L (d + 1)
  have : Φ.Additive := additive_of_isEquivalence Φ
  let I := fibreIdeal ι hι f
  -- the graded pieces of the twist are the twists of the graded pieces
  have e₁ : Φ.obj (idealPowGradedPiece I F n) ≅ idealPowGradedPiece I (Φ.obj F) n :=
    idealPowGradedPieceTwistIso I (fun i => baseScalar f (x i))
      (baseScalar_mem_fibreIdeal ι hι f x hx) (exists_eq_sum_baseScalar ι hι f x hx) Φ
      (twistPowLinear L (d + 1)).map_globalSmul F n
  -- they are killed by the ideal of the fibre
  have hK : AnnihilatedByKerIdeal B S hS P' (idealPowGradedPiece I (Φ.obj F) n) := by
    intro W a ha m
    rw [kerIdeal_structureSharp_eq_fibreIdeal ι hι f p q hsq] at ha
    exact smul_idealPowGradedPiece_eq_zero I (Φ.obj F) n W a ha m
  -- quasi-coherence
  have hL : L.IsQuasicoherentOnSite := isQuasicoherentOnSite_of_isInvertible B S hS X L
    (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ L ‹_›)
  have hGr := isCoherent_idealPowGradedPiece_fibreIdeal ι hι f F hF n
  have hKqc : (idealPowGradedPiece I (Φ.obj F) n).IsQuasicoherentOnSite :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso e₁
      (isQuasicoherentOnSite_twistPowFunctor_obj _ L hGr.toIsQuasicoherentOnSite hL (d + 1))
  refine isZero_rightDerived_globalSections_of_annihilatedByKerIdeal P'
    (isClosedImmersion_of_fibreSquare ι hι f p q hsq) _ hK hKqc q' ?_
  -- on the fibre, the pullback of the twist is the twist of the pullback
  have hpb : ((modulePullback B S hS P').obj (idealPowGradedPiece I F n)).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS P' _
      hGr.toIsQuasicoherentOnSite
  have hpL : ((modulePullback B S hS P').obj L).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS P' _ hL
  have : IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (zariskiModule U ((modulePullback B S hS P').obj L)) :=
    ‹IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)›
  have e₂ := (modulePullback B S hS P').mapIso e₁.symm ≪≫
    modulePullbackTwistPowIso P' L (idealPowGradedPiece I F n) (d + 1)
  have e₃ := zariskiModuleTwistPowSuccIso U ((modulePullback B S hS P').obj
    (idealPowGradedPiece I F n)) ((modulePullback B S hS P').obj L) hpb hpL d
  exact h.of_iso ((Hfunctor ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf ⊤ q').mapIso
    ((zariskiFunctor U).mapIso e₂ ≪≫ e₃))

include hsq hx in
/-- **Uniform vanishing of the cohomology of the twisted graded pieces along the closed fibre.**
Let `ι : P ⟶ T` be a closed immersion of affine objects of the site, `P` with Noetherian ring of
functions, `f : X ⟶ h_T` with `X` locally Noetherian, and `p : h_U ⟶ X` the base change of `ι`,
with `U ⟶ P` proper.  For a coherent `ℱ` and an invertible `ℒ` on `X` whose restriction to `U` is
ample, there is one `d₀` such that `Hᵠ(X, Iⁿ(ℱ ⊗ ℒ^{⊗ d})/Iⁿ⁺¹(ℱ ⊗ ℒ^{⊗ d})) = 0` for all
`d ≥ d₀`, all `n` and all `q > 0`, where `I = J 𝒪_X`. -/
theorem exists_isZero_rightDerived_idealPowGradedPiece_twist
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)]
    (hq : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    [IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)]
    (hamp : IsAmple ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ n q', 0 < q' →
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q').obj
          (idealPowGradedPiece (fibreIdeal ι hι f) ((twistPowFunctor L d).obj F) n)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  let P' : representedAlgebraicSpace B S hS U ⟶ X := ObjectProperty.homMk p
  let I := fibreIdeal ι hι f
  let G₀ := idealPowGradedFamily I F (fun i => baseScalar f (x i))
    (baseScalar_mem_fibreIdeal ι hι f x hx)
  -- the scheme `U` is Noetherian and proper over `Spec Γ(P)`
  let fU : (BigFppfOver.toScheme B S hS).obj U ⟶
      Spec (CommRingCat.of Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)) :=
    (BigFppfOver.toScheme B S hS).map q ≫ ((BigFppfOver.toScheme B S hS).obj P).isoSpec.hom
  have : _root_.AlgebraicGeometry.IsProper fU := by
    have := hq
    unfold fU
    infer_instance
  have hUn : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian fU
  have : Fact (HasEtaleLocalProperty B S hS (representedAlgebraicSpace B S hS U).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_of_representable B S hS _ _ U (Iso.refl _) hUn⟩
  have hGr := isCoherent_idealPowGradedPiece_fibreIdeal ι hι f F hF
  have hpb : ∀ n, IsCoherent B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)
      ((modulePullback B S hS P').obj (idealPowGradedPiece I F n)) := fun n =>
    isCoherent_modulePullback B S hS P' _ (hGr n)
  -- the family of the graded pieces, read on the fibre
  let G := (G₀.map (modulePullback B S hS P')).map (zariskiFunctor U)
  have hG : G.IsGenerated := ⟨0, generatedFrom_map_restrictToChartScheme (idEtaleChart B S hS U)
    (G₀.map (modulePullback B S hS P')) (fun n => (hpb n).toIsQuasicoherentOnSite)
    (Stacks.CommutingFamily.generatedFrom_map_of_adjunction (modulePullbackAdjunction B S hS P')
      G₀ (generatedFrom_idealPowGradedFamily I F _ _ (exists_eq_sum_baseScalar ι hι f x hx)))⟩
  have hqc : ∀ n, (G.obj n).IsQuasicoherent := fun n => by
    have := isQuasicoherent_restrictToChart B S hS (representedAlgebraicSpace B S hS U) _
      (hpb n).toIsQuasicoherentOnSite (idEtaleChart B S hS U)
    rwa [restrictToChart_eq_restrictToChartScheme] at this
  have : IsLocallyNoetherian (chartScheme (idEtaleChart B S hS U)) := hUn
  have hcoh : ∀ n, _root_.SheafOfModules.IsCoherent (G.obj n) := fun n =>
    Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_iso
      (restrictToChartSchemeIdEtaleChartIso B S hS U _ ≪≫ selfOpensPushforwardIso B S hS U _).symm
      (isCoherent_representedZariskiDirectImage B S hS U _ (hpb n))
  obtain ⟨d₀, hd₀⟩ := Stacks.CommutingFamily.exists_isZero_Hgroup_tensorPowTwist_of_isGenerated
    fU (baseChangeModule B S hS L U p) hamp G hqc hcoh hG
  refine ⟨d₀ + 1, fun d hd n q' hq' => ?_⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  exact isZero_rightDerived_idealPowGradedPiece_twist_of_isZero_Hgroup ι hι f p q hsq x hx F hF L
    n q' d' (hd₀ (d' + 1) (by omega) n q' hq')

include hsq hx in
/-- **The two numbered conclusions of the proof of Stacks 0D39, on the tower of quotients.**  In
the situation of `AlgebraicGeometry.Space.exists_isZero_rightDerived_idealPowGradedPiece_twist`,
there is one `d₀` such that for every `d ≥ d₀`, writing `ℱ' = ℱ ⊗ ℒ^{⊗ d}`:

1. `Hᵖ(X, ℱ'/Iⁿℱ') = 0` for all `n` and all `p > 0`;
2. `H⁰(X, ℱ'/Iⁿ⁺¹ℱ') ⟶ H⁰(X, ℱ'/Iⁿℱ')` is surjective for all `n`. -/
theorem exists_isZero_rightDerived_idealPowTower_twist
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj P)]
    [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj P, ⊤)]
    (hq : _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme B S hS).map q))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    [IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)]
    (hamp : IsAmple ((BigFppfOver.toScheme B S hS).obj U) (baseChangeModule B S hS L U p)) :
    have := hasInjectiveResolutions_modules B S hS X.1 X.2
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d →
      (∀ n p', 0 < p' → IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived p').obj
          (idealPowTowerShortComplex (fibreIdeal ι hι f) ((twistPowFunctor L d).obj F) n).X₃)) ∧
      (∀ n, Epi (((globalSectionsFunctor.{u + 1, u, u, u}
        (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived 0).map
          (idealPowTowerShortComplex (fibreIdeal ι hι f) ((twistPowFunctor L d).obj F) n).g)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  obtain ⟨d₀, hd₀⟩ := exists_isZero_rightDerived_idealPowGradedPiece_twist ι hι f p q hsq x hx
    hq F hF L hamp
  refine ⟨d₀, fun d hd => ⟨?_, fun n => ?_⟩⟩
  · exact Stacks.Cohomology.RightDerivedDelta.isZero_rightDerived_tower _
      (idealPowTowerShortComplex (fibreIdeal ι hι f) ((twistPowFunctor L d).obj F))
      (idealPowTowerShortComplex_shortExact _ _)
      (idealPowTowerShortComplexX₃Iso _ _) (isZero_idealPowTowerShortComplex_zero_X₃ _ _)
      (hd₀ d hd)
  · exact Stacks.Cohomology.RightDerivedDelta.epi_rightDerived_zero_map_g _
      (idealPowTowerShortComplex_shortExact _ _ n) (hd₀ d hd n 1 one_pos)

end Setting

end AlgebraicGeometry.Space

end
