module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageLift
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageAdicnessStage
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageAdic
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAuxGenerators
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalAssembly
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitFormalChart

/-!
# The contraction functor is limit preserving

For a contraction situation `c`, the functor `F = AlgebraicGeometry.Artin.contractionFunctor c` is
limit preserving: for a cofiltered limit `V = lim V_λ` of affine locally Noetherian objects over
`S`, `colim F(V_λ) ⟶ F(V)` is bijective.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.limitPreserving_contractionFunctor`: the functor
  `F` is limit preserving on cofiltered limits of affine locally Noetherian objects over `S`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_stage_of_factorsThroughAffineChart`: an
  element of `F(V)` whose formal component factors through an affine chart of `W` over an affine
  open of `S` comes from some `F(V_λ)`.

## References

* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.Artin.LimitStages

open Space FormalSpace FormalDictionary FormalRing ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

variable {c : ContractionSituation B S hS} {I : Type u} [Category.{u} I] [IsCofiltered I]
  {D : I ⥤ LocallyNoetherianOver B S hS} {κ : Cone D} {ξ : Triple c κ.pt.obj}
  {w : CompatibilityWitness c κ.pt.obj ξ.Z ξ.u ξ.xhat} {k₀ : I}
  (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
  [hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj)]
  [hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj)]
  (W : StageWitness c κ ξ w k₀)
  {I₀ : Ideal Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)}
  (hZI₀ : ∀ x, x ∈ W.Z ↔ Space.pointsToScheme B S hS (D.obj k₀).obj x ∈
    ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj).zeroLocus
      (I₀ : Set Γ((BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj, ⊤)))
  (O : S.Opens) [IsAffine (O : Scheme.{u})] (hOC : B.Contains (O : Scheme.{u}))
  (f₀ : (BigFppfOver.toScheme B S hS).obj (D.obj k₀).obj ⟶ (O : Scheme.{u}))
  (hf₀ : f₀ ≫ O.ι = (D.obj k₀).obj.hom.hom)

omit [IsCofiltered I] in
/-- A lift `φ_k : B → A_k^∧` continuous for the `I_k`-adic filtration stays continuous after
restriction to a later stage. -/
theorem continuous_cres_comp_lift {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt]
    [IsTopologicalRing Bt] {k k' : Over k₀} (f : k' ⟶ k)
    (φk : Bt →+* (completionSystem (D := D) I₀).obj (op k))
    (h₄ : ∀ n : ℕ, (φk ⁻¹' ((stageIdealHat I₀ k ^ n :
        Ideal ((completionSystem (D := D) I₀).obj (op k))) :
      Set ((completionSystem (D := D) I₀).obj (op k)))) ∈ 𝓝 (0 : Bt)) :
    Continuous ((cres I₀ f).comp ((ULift.ringEquiv : ULift.{u + 1}
      (AdicCompletion (stageIdeal I₀ k)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) ≃+* _).toRingHom.comp
      φk)) := by
  obtain ⟨htop, -, hIadic', -, -⟩ := FormalSpace.adicCompletion_isAdic_of_fg (stageIdeal I₀ k')
    (stageIdeal I₀ k').fg_of_isNoetherianRing
  refine continuous_of_preimage_pow_mem_nhds hIadic' _ fun n ↦
    Filter.mem_of_superset (h₄ n) fun b hb ↦ ?_
  exact completionRingHom_mem_map_pow
    (A := Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (A' := Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤)) (f := res D f)
    (stageIdeal_map_le I₀ f) (mem_stageIdealHat_pow.1 hb)

section Lift

variable {W₀ : FormalSpace.FppfSheaf B S hS}
  (ℓ : Space.completionSheaf B S hS W.Y (Space.pointsMap B S hS W.Y W.q ⁻¹' W.Z) ⟶ W₀)
  {Bt : Type u} [CommRing Bt] [TopologicalSpace Bt] [IsTopologicalRing Bt]
  [IsLinearTopology Bt Bt] (hB : TopologicalRing.IsWeaklyAdmissible Bt)
  {DB : FormalSpace.QuotientSystem B S hS Bt} (e : W₀ ≅ FormalSpace.formalSpectrum DB)
  (ρ : Γ((O : Scheme.{u}), ⊤) →+* Bt)
  (hρ : ∀ J : { J : Ideal Bt // TopologicalRing.IsWeakIdealOfDefinition J },
    DB.overS J = Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J.1).comp ρ)) ≫
      (O : Scheme.{u}).isoSpec.inv ≫ O.ι)
  {x₀ : Space.completionSheaf B S hS (yoneda.obj κ.pt.obj) ξ.Z ⟶ W₀}
  (hℓ : Space.completionSheafRestrict B S hS W.a _ _ W.toStageModel.subset_preimage_preimage ≫ ℓ =
      Space.completionSheafRestrict B S hS w.p _ ξ.Z (fun _ h => h) ≫ x₀)

omit [IsCofiltered I] in
include hρ hf₀ hOC in
/-- After restriction to a later stage `k'`, a lift `φ_k : B → A_k^∧` satisfying `h₃` sends `ρ r`
to the image of `r` under the structure map `Γ(O, ⊤) → A_{k'}^∧`. -/
theorem cres_lift_ρ {k₂ k k' : Over k₀} (f₂ : k₂ ⟶ topStage k₀) (g : k ⟶ k₂) (f : k' ⟶ k)
    (φk : Bt →+* (completionSystem (D := D) I₀).obj (op k))
    (h₃ : ∀ b (x : (completionSystem (D := D) I₀).obj (op k₂)),
      (completionToLimit (κ := κ) I₀ k₂).hom x = limitPhi W hZI₀ hB e (x₀ := x₀) b →
      ((alphaSystem W hZI₀).app (op k₂)).hom x =
        ((towerSystem W I₀).map f₂.op).hom (stagePsiSys W hZI₀ ℓ hB e b) →
      ((completionSystem (D := D) I₀).map g.op).hom x = φk b)
    (r : Γ((O : Scheme.{u}), ⊤)) :
    cres I₀ f (φk (ρ r)).down =
      algebraMap _ (AdicCompletion (stageIdeal I₀ k')
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤))
        ((stageToOpen' O f₀ k').appTop.hom r) := by
  have hg := h₃ (ρ r) (ULift.up (algebraMap _ _ ((stageToOpen' O f₀ k₂).appTop.hom r)))
    (completionToLimit_algebraMap_stageToOpen' W hZI₀ O f₀ hf₀ hB e ρ hρ k₂ r)
    (alpha_algebraMap_stageToOpen' W hZI₀ O hOC f₀ hf₀ ℓ hB e ρ hρ f₂ r)
  have key : ∀ {a b : Over k₀} (f : b ⟶ a), cres I₀ f (algebraMap _ (AdicCompletion
      (stageIdeal I₀ a) Γ((BigFppfOver.toScheme B S hS).obj (D.obj a.left).obj, ⊤))
        ((stageToOpen' O f₀ a).appTop.hom r)) = algebraMap _ (AdicCompletion (stageIdeal I₀ b)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj b.left).obj, ⊤))
        ((stageToOpen' O f₀ b).appTop.hom r) := fun f ↦
    (completionRingHom_algebraMap _ _ _).trans (congrArg _ (res_stageToOpen' O f₀ f r))
  exact (congrArg (cres I₀ f) ((congrArg ULift.down hg).symm.trans (key g))).trans (key f)

omit [IsCofiltered I] hpt in
/-- The lift `φ_k` restricted to a later stage is compatible with `ψ`. -/
theorem stageAlpha_cres_lift {k₂ k k' : Over k₀} (f₂ : k₂ ⟶ topStage k₀) (g : k ⟶ k₂) (f : k' ⟶ k)
    (φk : Bt →+* (completionSystem (D := D) I₀).obj (op k))
    (h₂ : ∀ b, ((alphaSystem W hZI₀).app (op k)).hom (φk b) =
      ((towerSystem W I₀).map (g ≫ f₂).op).hom (stagePsiSys W hZI₀ ℓ hB e b)) (b : Bt) :
    stageAlpha W hZI₀ k' (cres I₀ f (φk b).down) =
      towerRingMap (D.map (f ≫ g ≫ f₂).left).hom (stageIdeal_map_le I₀ (f ≫ g ≫ f₂))
        (stageQ W (topStage k₀)) (stageQ W k') (stageHom W (f ≫ g ≫ f₂))
        (stageHom_q W (f ≫ g ≫ f₂)) (stagePsi W ℓ hZI₀ hB e (topStage k₀) b) := by
  have e₁ := congrArg (fun φ ↦ φ (φk b).down) (towerRingMap_comp_alpha (stageQ W k)
    (stage_hZI hZI₀ k) (stage_hqc W k) (D.map f.left).hom (stageIdeal_map_le I₀ f) (stageQ W k')
    (stageHom W f) (stageHom_q W f) (stage_hZI hZI₀ k') (stage_hqc W k'))
  have e₂ : stageAlpha W hZI₀ k (φk b).down = towerRingMap (D.map (g ≫ f₂).left).hom
      (stageIdeal_map_le I₀ (g ≫ f₂)) (stageQ W (topStage k₀)) (stageQ W k) (stageHom W (g ≫ f₂))
      (stageHom_q W (g ≫ f₂)) (stagePsi W ℓ hZI₀ hB e (topStage k₀) b) := h₂ b
  have e₃ := congrArg (fun φ ↦ φ (stagePsi W ℓ hZI₀ hB e (topStage k₀) b))
    (towerRingMap_comp (stageQ W (topStage k₀)) (stageQ W k) (stageQ W k')
      (D.map (g ≫ f₂).left).hom (D.map f.left).hom (D.map (f ≫ g ≫ f₂).left).hom
      (stageIdeal_map_le I₀ (g ≫ f₂)) (stageIdeal_map_le I₀ f) (stageIdeal_map_le I₀ (f ≫ g ≫ f₂))
      (stageHom W (g ≫ f₂)) (stageHom W f) (stageHom W (f ≫ g ≫ f₂)) (stageHom_q W (g ≫ f₂))
      (stageHom_q W f) (stageHom_q W (f ≫ g ≫ f₂)) (stageHom_comp W (g ≫ f₂) f))
  refine e₁.symm.trans ?_
  show towerRingMap (D.map f.left).hom (stageIdeal_map_le I₀ f) (stageQ W k) (stageQ W k')
    (stageHom W f) (stageHom_q W f) (stageAlpha W hZI₀ k (φk b).down) = _
  rwa [e₂]

include hκ hρ hf₀ hℓ hOC in
/-- The continuous ring map `φ = (x̂)^♯ : B → A^∧` descends to a continuous `R`-algebra map
`φ_k : B → A_k^∧` at a stage `k`, compatible with the lift `ℓ` on `V'_k`, and adic if `x₀` is. -/
theorem exists_stage_continuousHom [IsNoetherianRing Bt] (hBadic : TopologicalRing.IsAdic Bt)
    (hW₀ : IsAffineFormalAlgebraicSpace B S hS W₀) {Wc : FormalSpace.FppfSheaf B S hS}
    (ω : W₀ ⟶ Wc) (hω : FormalSpace.IsRepresentableEtale B S hS ω)
    (hadic : FormalSpace.IsAdicMorphism B S hS (x₀ ≫ ω)) (s : Finset Bt)
    (hdense : Dense (Subring.closure ((ρ.range : Set Bt) ∪ (s : Set Bt)) : Set Bt)) :
    ∃ (k : Over k₀) (φc : FormalSpace.ContinuousHom DB
        (completionQuotientSystem (D.obj k.left).obj (stageIdeal I₀ k))),
      ((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom)).toRingHom =
          (cresL I₀ κ k).comp φc.toRingHom ∧
        FormalSpace.IsAdicMorphism B S hS
          (continuousHomEquiv (stage_hZI hZI₀ k) hB φc ≫ e.inv ≫ ω) ∧
        Space.completionSheafRestrict B S hS (stageQ W k)
            (Space.pointsMap B S hS _ (stageQ W k) ⁻¹' (W.baseChange k.hom).Z)
            (W.baseChange k.hom).Z (fun _ hx => hx) ≫ continuousHomEquiv (stage_hZI hZI₀ k) hB φc =
          stageFormal W ℓ k ≫ e.hom := by
  obtain ⟨k₂, f₂, k, g, φk, h₁, h₂, h₃, h₄⟩ :=
    exists_stage_lift_system hκ W hZI₀ O hOC f₀ hf₀ ℓ hB e ρ hρ hℓ s hdense
  let φk' : Bt →+* AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤) :=
    (ULift.ringEquiv : ULift.{u + 1}
      (AdicCompletion (stageIdeal I₀ k)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) ≃+* _).toRingHom.comp φk
  have hlim : (cresL I₀ κ k).comp φk' =
      ((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom)).toRingHom :=
    RingHom.ext fun b ↦ congrArg ULift.down (h₁ b)
  obtain ⟨J, N, hJ, hN⟩ := exists_pow_le_map_of_isAdicMorphism (limit_hZI hZI₀) hB hBadic e hW₀ ω
    x₀ hadic
  obtain ⟨k', f, hk'⟩ := exists_stage_pow_le_map hκ I₀ k φk' J N
    (le_of_le_of_eq hN (congrArg (fun φ ↦ J.map φ) hlim.symm))
  let φc := continuousHomOfComp O ρ hρ (stageIdeal I₀ k') (stageToOpen' O f₀ k')
    (stageToOpen'_ι O f₀ hf₀ k') ((cres I₀ f).comp φk') (continuous_cres_comp_lift f φk h₄)
    (RingHom.ext fun r ↦ cres_lift_ρ W hZI₀ O hOC f₀ hf₀ ℓ hB e ρ hρ f₂ g f φk h₃ r)
  refine ⟨k', φc, ?_, isAdicMorphism_continuousHomEquiv_comp (stage_hZI hZI₀ k') hB e ω hω φc
    (isAdic_toRingHom_of_pow_le_map φc hJ hk'), ?_⟩
  · exact RingHom.ext fun b ↦
      (congrArg (fun φ ↦ φ b) hlim).symm.trans (cresL_cres I₀ f (φk' b)).symm
  · exact completionSheafRestrict_comp_continuousHomEquiv_eq W ℓ hZI₀ hB e k' φc (f ≫ g ≫ f₂)
      (RingHom.ext fun b ↦ stageAlpha_cres_lift W hZI₀ ℓ hB e f₂ g f φk h₂ b)

end Lift

end AlgebraicGeometry.Artin.LimitStages

namespace AlgebraicGeometry.Artin.ContractionSituation

open LimitStages Space FormalSpace FormalDictionary FormalRing

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance]
  AlgebraicGeometry.Artin.FormalDictionary.instTopologicalSpaceAdicCompletion

/-- An element `ξ ∈ F(V)` of a cofiltered limit `V = lim V_j` of affine locally Noetherian objects,
whose formal component factors through an affine chart of `W` lying over an affine open of `S`, is
the image of an element of some `F(V_j)`. -/
theorem exists_stage_of_factorsThroughAffineChart (c : ContractionSituation B S hS)
    {J : Type u} [Category.{u} J] [IsCofiltered J] {D : J ⥤ LocallyNoetherianOver B S hS}
    {κ : Cone D} (hκ : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone κ))
    (hD : ∀ j, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj j)))
    (hpt : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj κ.pt))
    (ξ : Triple c κ.pt.obj) (hP : FactorsThroughAffineChart c κ.pt ξ) :
    ∃ (j : J) (y : Triple c (D.obj j).obj), mapTriple c (κ.π.app j).hom y = ξ := by
  obtain ⟨O, hOaff, hOC, hrange, W₀, ω, hW₀a, hW₀n, hω, ⟨π⟩, x₀, hx₀⟩ := hP
  have : IsAffine (O : Scheme.{u}) := hOaff
  obtain ⟨Bt, _, _, _, _, DB, hB, hBnoeth, hBadic, ⟨e⟩⟩ :=
    exists_iso_formalSpectrum_of_isNoetherian hW₀n
  obtain ⟨ρ, hρ, s, hdense⟩ :=
    exists_ringHom_overS_dense_subring_closure c O hOC ω hω π hB hBadic e
  have hD' : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj j).obj) := hD
  have hpt' : IsAffine ((BigFppfOver.toScheme B S hS).obj κ.pt.obj) := hpt
  obtain ⟨j, ⟨W⟩⟩ := exists_stageWitness c ξ ξ.compatible.some hκ hD hpt
  obtain ⟨j', hj', hrange'⟩ := exists_stage_range_subset_of_isLimit hκ hD O hrange j
  obtain ⟨k₀, g₀, ℓ, hℓω, hℓ⟩ := StageWitness.exists_stage_lift c
    (nonempty_chartAlgebraization c ω hW₀a hω).some hκ hD hpt (W.baseChange hj') hx₀
  let W₁ := (W.baseChange hj').baseChange g₀
  have hw : B.inclusion.map (D.map g₀).hom.left ≫ B.inclusion.map (D.obj j').obj.hom =
      B.inclusion.map (D.obj k₀).obj.hom := by
    rw [← B.inclusion.map_comp]
    exact congrArg B.inclusion.map (Over.w (D.map g₀).hom)
  have hrange₀ : Set.range (B.inclusion.map (D.obj k₀).obj.hom).base ⊆ (O : Set S) := by
    rintro _ ⟨x, rfl⟩
    rw [← hw, Scheme.Hom.comp_apply]
    exact hrange' ⟨_, rfl⟩
  obtain ⟨f₀, hf₀⟩ := exists_comp_ι_eq_of_range_subset _ O hrange₀
  obtain ⟨I₀, hZI₀⟩ := Space.exists_ideal_mem_iff_mem_zeroLocus B S hS (D.obj k₀).obj
    W₁.isClosed_Z
  have hadic : FormalSpace.IsAdicMorphism B S hS (x₀ ≫ ω) := by
    rw [hx₀]
    exact ξ.adic_xhat
  obtain ⟨k, φc, hφ, hadick, hformal⟩ := exists_stage_continuousHom hκ W₁ hZI₀ O hOC f₀ hf₀ ℓ hB e
    ρ hρ hℓ hBadic hW₀a ω hω hadic s hdense
  have hformal' : Space.completionSheafRestrict B S hS (W₁.baseChange k.hom).q
      (Space.pointsMap B S hS (W₁.baseChange k.hom).Y (W₁.baseChange k.hom).q ⁻¹'
        (W₁.baseChange k.hom).Z) (W₁.baseChange k.hom).Z (fun _ hz ↦ hz) ≫
        continuousHomEquiv (stage_hZI hZI₀ k) hB φc ≫ e.inv ≫ ω =
      Space.completionSheafRestrict B S hS (W₁.baseChange k.hom).y
        (Space.pointsMap B S hS (W₁.baseChange k.hom).Y (W₁.baseChange k.hom).q ⁻¹'
          (W₁.baseChange k.hom).Z) c.T' (W₁.baseChange k.hom).subset_T' ≫ c.g := by
    have h1 : Space.completionSheafRestrict B S hS (stageToBase W₁ k) _ _
        (subset_stageToBase W₁ k) ≫
        Space.completionSheafRestrict B S hS W₁.y _ c.T' W₁.subset_T' =
          Space.completionSheafRestrict B S hS (W₁.baseChange k.hom).y _ c.T'
            (W₁.baseChange k.hom).subset_T' :=
      (Space.completionSheafRestrict_comp B S hS _ _ _ _ _ _ _
        (W₁.baseChange k.hom).subset_T').symm
    calc _ = (Space.completionSheafRestrict B S hS (stageQ W₁ k)
            (Space.pointsMap B S hS _ (stageQ W₁ k) ⁻¹' (W₁.baseChange k.hom).Z)
            (W₁.baseChange k.hom).Z (fun _ hx ↦ hx) ≫
              continuousHomEquiv (stage_hZI hZI₀ k) hB φc) ≫ e.inv ≫ ω :=
          (Category.assoc _ _ _).symm
      _ = stageFormal W₁ ℓ k ≫ ω := by
          rw [hformal, Category.assoc, Iso.hom_inv_id_assoc]
      _ = _ := by
          rw [stageFormal, Category.assoc, hℓω, ← Category.assoc, h1]
          rfl
  exact ⟨k.left, (W₁.baseChange k.hom).exists_mapTriple_eq_of_continuousHom c
    (limit_hZI hZI₀) (stage_hZI hZI₀ k) (stageIdeal_map_limit I₀ k).le hB e ω x₀ hx₀ φc hφ
    hadick hformal'⟩

/-- For a contraction situation `c`, the functor `contractionFunctor c` is limit preserving: for
every cofiltered limit `V = lim V_λ` of affine locally Noetherian objects over `S`, the map
`colim F(V_λ) ⟶ F(V)` is bijective. -/
@[stacks 0GI5]
theorem limitPreserving_contractionFunctor (c : ContractionSituation B S hS) :
    LimitPreserving.{u, u + 1, u, u, u + 1, u} (LocallyNoetherianOver.toScheme B S hS)
      (contractionFunctor c) :=
  limitPreserving_contractionFunctor_of_affineChart c fun _ _ _ _ _ hκ hD hpt ξ hP ↦
    exists_stage_of_factorsThroughAffineChart c hκ hD hpt ξ hP

end AlgebraicGeometry.Artin.ContractionSituation

end
