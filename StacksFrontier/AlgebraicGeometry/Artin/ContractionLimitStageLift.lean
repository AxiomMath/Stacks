module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageFormal
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageArtinRees
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitStageCokerRange
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitAlgebraClosure

/-!
# The lifting argument for the descended system of a stage witness

The inputs of `AlgebraicGeometry.Artin.StageLift.exists_stage_continuous_ringHom` for the systems
`k ↦ A_k^∧` and `k ↦ C_k^∧` of a stage witness, in the proof of Stacks 0GI5, and the resulting
continuous lift `B → A_k^∧` at a stage.

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

section Generic

/-- `ULift R` is precomplete for the lifted ideal `J` whenever `R` is `J`-precomplete. -/
theorem isPrecomplete_uliftIdeal {R : Type u} [CommRing R] (J : Ideal R) [h : IsPrecomplete J R] :
    IsPrecomplete (uliftIdeal J) (ULift.{u + 1} R) := by
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec' (fun n => (f n).down) (fun {m n} hmn => by
    have h1 := hf hmn
    rw [StageLift.smodEq_pow_iff, uliftIdeal_pow, mem_uliftIdeal] at h1
    rwa [StageLift.smodEq_pow_iff])
  refine ⟨ULift.up L, fun n => ?_⟩
  rw [StageLift.smodEq_pow_iff, uliftIdeal_pow, mem_uliftIdeal]
  exact (StageLift.smodEq_pow_iff _ _ _ _).1 (hL n)

/-- An element of `ULift R` lying in every lifted power of `J` is zero when `R` is `J`-adically
Hausdorff. -/
theorem eq_zero_of_forall_mem_uliftIdeal_pow {R : Type u} [CommRing R] (J : Ideal R)
    [h : IsHausdorff J R] (y : ULift.{u + 1} R) (hy : ∀ n, y ∈ uliftIdeal (J ^ n)) : y = 0 := by
  refine ULift.ext (h.haus' y.down fun n => ?_)
  rw [StageLift.smodEq_pow_iff, sub_zero]
  exact (mem_uliftIdeal _ _).1 (hy n)

/-- A ring map into an `J`-adic ring is continuous as soon as the preimages of the powers of `J`
are neighbourhoods of `0`. -/
theorem continuous_of_preimage_pow_mem_nhds {A R : Type*} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] {J : Ideal R}
    (hJ : _root_.IsAdic J) (φ : A →+* R) (h : ∀ n, φ ⁻¹' ((J ^ n : Ideal R) : Set R) ∈ 𝓝 0) :
    Continuous φ := by
  refine continuous_of_continuousAt_zero φ.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  exact hJ.hasBasis_nhds_zero.tendsto_right_iff.2 fun n _ => h n

end Generic

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

/-! ### The inputs of the lifting argument for the descended system -/

include hκ hZI₀ in
/-- The `hcoker` input. -/
theorem system_hcoker : ∃ (k₁ : Over k₀) (f₁ : k₁ ⟶ topStage k₀),
    ∀ c : (towerSystem W I₀).obj (op (topStage k₀)),
      (towerToLimit W I₀ (topStage k₀)).hom c ∈ (limitAlphaHom W hZI₀).hom.range →
        ((towerSystem W I₀).map f₁.op).hom c ∈ ((alphaSystem W hZI₀).app (op k₁)).hom.range := by
  obtain ⟨k₁, f₁, hk⟩ := exists_stage_mem_range_stageAlpha hκ W hZI₀ (topStage k₀)
  refine ⟨k₁, f₁, fun c hc => ?_⟩
  obtain ⟨y, hy⟩ := hc
  obtain ⟨z, hz⟩ := hk c ⟨y.down, hy⟩
  exact ⟨ULift.up z, hz⟩

include hκ hZI₀ in
/-- The `hker` input. -/
theorem system_hker (y : limitCompletion (κ := κ) I₀) (hy : (limitAlphaHom W hZI₀).hom y = 0) :
    ∃ (k : Over k₀) (z : (completionSystem (D := D) I₀).obj (op k)),
      ((alphaSystem W hZI₀).app (op k)).hom z = 0 ∧
        (completionToLimit (κ := κ) I₀ k).hom z = y := by
  obtain ⟨k, z, h1, h2⟩ := exists_stage_of_limitAlpha_eq_zero hκ W hZI₀ y.down hy
  exact ⟨k, ULift.up z, h1, ULift.ext h2⟩

include hκ hZI₀ in
/-- The `hL` input. -/
theorem system_hL (k : Over k₀) : ∃ (k' : Over k₀) (g : k' ⟶ k),
    ∀ x : (completionSystem (D := D) I₀).obj (op k), ((alphaSystem W hZI₀).app (op k)).hom x = 0 →
      (completionToLimit (κ := κ) I₀ k).hom x = 0 →
        ((completionSystem (D := D) I₀).map g.op).hom x = 0 := by
  obtain ⟨k', g, hg⟩ := exists_stage_cres_eq_zero hκ W hZI₀ k
  exact ⟨k', g, fun x hx hxl => ULift.ext (hg x.down hx (congrArg ULift.down hxl))⟩

variable (I₀) in
/-- The ideal `I_k A_k^∧` of `A_k^∧`, in the universe of the system `k ↦ A_k^∧`. -/
def stageIdealHat (k : Over k₀) : Ideal ((completionSystem (D := D) I₀).obj (op k)) :=
  uliftIdeal (R := AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    ((stageIdeal I₀ k).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k)
      Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))))

variable (I₀) in
/-- The ideal `I^n A^∧` of `A^∧`, in the universe of the system. -/
def limitIdealPow (n : ℕ) : Ideal (limitCompletion (κ := κ) I₀) :=
  uliftIdeal (R := AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))
    (((limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) ^ n)

omit [IsCofiltered I] hD in
/-- Membership in a power of `stageIdealHat I₀ k`, read on the underlying completion. -/
theorem mem_stageIdealHat_pow {k : Over k₀} {n : ℕ}
    {x : (completionSystem (D := D) I₀).obj (op k)} :
    x ∈ stageIdealHat I₀ k ^ n ↔
      x.down ∈ ((stageIdeal I₀ k).map (algebraMap _ (AdicCompletion (stageIdeal I₀ k)
        Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)))) ^ n :=
  (congrArg (x ∈ ·) (uliftIdeal_pow (R := AdicCompletion (stageIdeal I₀ k)
    Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) _ n)).to_iff.trans
      (mem_uliftIdeal _ _)

omit [IsCofiltered I] hD hpt in
/-- Membership in `limitIdealPow I₀ n`, read on the underlying completion. -/
theorem mem_limitIdealPow {n : ℕ} {y : limitCompletion (κ := κ) I₀} :
    y ∈ limitIdealPow (κ := κ) I₀ n ↔
      y.down ∈ ((limitIdeal (κ := κ) I₀).map (algebraMap _ (AdicCompletion (limitIdeal (κ := κ) I₀)
        Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) ^ n :=
  mem_uliftIdeal _ _

omit [IsCofiltered I] in
variable (I₀) in
/-- The `hpre` input. -/
theorem system_hpre (k : Over k₀) :
    IsPrecomplete (stageIdealHat I₀ k) ((completionSystem (D := D) I₀).obj (op k)) := by
  have := AdicCompletion.isAdicComplete_self (stageIdeal I₀ k)
    (stageIdeal I₀ k).fg_of_isNoetherianRing
  exact isPrecomplete_uliftIdeal (R := AdicCompletion (stageIdeal I₀ k)
    Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤)) _

omit [IsCofiltered I] hD in
variable (I₀) in
/-- The `hsepA` input. -/
theorem system_hsepA (y : limitCompletion (κ := κ) I₀) (hy : ∀ n, y ∈ limitIdealPow (κ := κ) I₀ n) :
    y = 0 := by
  have := AdicCompletion.isAdicComplete_self (limitIdeal (κ := κ) I₀)
    (limitIdeal (κ := κ) I₀).fg_of_isNoetherianRing
  exact eq_zero_of_forall_mem_uliftIdeal_pow (R := AdicCompletion (limitIdeal (κ := κ) I₀)
    Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)) _ y hy

omit [IsCofiltered I] hD hpt in
variable (I₀) in
/-- The `hFA` input. -/
theorem system_hFA : Antitone (limitIdealPow (κ := κ) I₀) :=
  fun _ _ h => Ideal.map_mono (Ideal.pow_le_pow_right h)

omit [IsCofiltered I] hD hpt in
variable (I₀) in
/-- The `hρI` input. -/
theorem system_hρI (k : Over k₀) (n : ℕ) (x : (completionSystem (D := D) I₀).obj (op k))
    (hx : x ∈ stageIdealHat I₀ k ^ n) :
    (completionToLimit (κ := κ) I₀ k).hom x ∈ limitIdealPow (κ := κ) I₀ n :=
  mem_limitIdealPow.2 (completionRingHom_mem_map_pow
    (A := Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (A' := Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))
    (f := ((BigFppfOver.toScheme B S hS).map (limitMap κ k)).appTop.hom)
    (stageIdeal_map_limit I₀ k).le (mem_stageIdealHat_pow.1 hx))

variable (I₀) in
/-- The filtration `C_k^∧ ⊇ F^1 ⊇ F^2 ⊇ …` of the tower ring, in the system `k ↦ C_k^∧`. -/
def towerFiltrationSys (k : Over k₀) (n : ℕ) : Ideal ((towerSystem W I₀).obj (op k)) :=
  towerFiltration (stageIdeal I₀ k) (stageQ W k) n

omit [IsCofiltered I] hpt in
/-- The `hαI` input. -/
theorem system_hαI (k : Over k₀) (n : ℕ) (x : (completionSystem (D := D) I₀).obj (op k))
    (hx : x ∈ stageIdealHat I₀ k ^ n) :
    ((alphaSystem W hZI₀).app (op k)).hom x ∈ towerFiltrationSys W I₀ k n :=
  alpha_mem_towerFiltration (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k)
    (mem_stageIdealHat_pow.1 hx)

omit [IsCofiltered I] hpt in
/-- The `hsepC` input. -/
theorem system_hsepC (k : Over k₀) (y : (towerSystem W I₀).obj (op k))
    (hy : ∀ n, y ∈ towerFiltrationSys W I₀ k n) : y = 0 :=
  eq_zero_of_mem_towerFiltration (stageQ W k) y hy

omit [IsCofiltered I] hpt in
/-- The `hFC` input. -/
theorem system_hFC (k : Over k₀) : Antitone (towerFiltrationSys W I₀ k) :=
  antitone_towerFiltration (stageQ W k)

omit [IsCofiltered I] hpt in
/-- The `hmapC` input. -/
theorem system_hmapC {k k' : Over k₀} (f : k' ⟶ k) (n : ℕ) (y : (towerSystem W I₀).obj (op k))
    (hy : y ∈ towerFiltrationSys W I₀ k n) :
    ((towerSystem W I₀).map f.op).hom y ∈ towerFiltrationSys W I₀ k' n :=
  (congrArg (fun φ : (towerSystem W I₀).obj (op k) ⟶ (towerSystem W I₀).obj (op k') =>
      φ.hom y ∈ towerFiltrationSys W I₀ k' n) (towerSystem_map (I₀ := I₀) W f)).mpr
    (towerRingMap_mem_towerFiltration (D.map f.left).hom (stageIdeal_map_le I₀ f)
      (stageQ W k) (stageQ W k') (stageHom W f) (stageHom_q W f) (x := y) (n := n) hy)

omit [IsCofiltered I] hD in
variable (I₀) in
/-- The `hmapA` input. -/
theorem system_hmapA {k k' : Over k₀} (g : k' ⟶ k) (n : ℕ)
    (x : (completionSystem (D := D) I₀).obj (op k)) (hx : x ∈ stageIdealHat I₀ k ^ n) :
    ((completionSystem (D := D) I₀).map g.op).hom x ∈ stageIdealHat I₀ k' ^ n :=
  mem_stageIdealHat_pow.2 (completionRingHom_mem_map_pow
    (A := Γ((BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj, ⊤))
    (A' := Γ((BigFppfOver.toScheme B S hS).obj (D.obj k'.left).obj, ⊤))
    (f := ((BigFppfOver.toScheme B S hS).map (D.map g.left).hom).appTop.hom)
    (stageIdeal_map_le I₀ g) (mem_stageIdealHat_pow.1 hx))

omit [IsCofiltered I] in
/-- The `hAR` input. -/
theorem system_hAR (k : Over k₀) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : (completionSystem (D := D) I₀).obj (op k)),
    ((alphaSystem W hZI₀).app (op k)).hom x ∈ towerFiltrationSys W I₀ k (n + c) →
      (completionToLimit (κ := κ) I₀ k).hom x ∈ limitIdealPow (κ := κ) I₀ (n + c) →
        ∃ y ∈ stageIdealHat I₀ k ^ n, ((alphaSystem W hZI₀).app (op k)).hom (x - y) = 0 ∧
            (completionToLimit (κ := κ) I₀ k).hom (x - y) = 0 := by
  obtain ⟨c, hc⟩ := exists_stage_artinRees W hZI₀ k
  refine ⟨c, fun n x hxC hxA => ?_⟩
  obtain ⟨y, hy, h1, h2⟩ := hc n x.down hxC (mem_limitIdealPow.1 hxA)
  exact ⟨ULift.up y, mem_stageIdealHat_pow.2 hy, h1, ULift.ext h2⟩

section OverO

/-- `V_k ⟶ O`. -/
abbrev stageToOpen' (k : Over k₀) : (BigFppfOver.toScheme B S hS).obj (D.obj k.left).obj ⟶
    (O : Scheme.{u}) :=
  (BigFppfOver.toScheme B S hS).map (D.map k.hom).hom ≫ f₀

omit [IsCofiltered I] hD [IsAffine (O : Scheme.{u})] in
include hf₀ in
/-- `V_k ⟶ O ⟶ S` is the structure morphism of `V_k`. -/
theorem stageToOpen'_ι (k : Over k₀) :
    stageToOpen' O f₀ k ≫ O.ι = (D.obj k.left).obj.hom.hom := by
  rw [Category.assoc, hf₀]
  exact congrArg (fun k => k.hom) (Over.w (D.map k.hom).hom)

/-- `V ⟶ O`. -/
abbrev limitToOpen : (BigFppfOver.toScheme B S hS).obj κ.pt.obj ⟶ (O : Scheme.{u}) :=
  (BigFppfOver.toScheme B S hS).map (κ.π.app k₀).hom ≫ f₀

omit [IsCofiltered I] hD hpt [IsAffine (O : Scheme.{u})] in
include hf₀ in
/-- `V ⟶ O ⟶ S` is the structure morphism of `V`. -/
theorem limitToOpen_ι : limitToOpen (κ := κ) O f₀ ≫ O.ι = κ.pt.obj.hom.hom := by
  rw [Category.assoc, hf₀]
  exact congrArg (fun k => k.hom) (Over.w (κ.π.app k₀).hom)

omit [IsCofiltered I] hD [IsAffine (O : Scheme.{u})] in
/-- The transition maps of the system `k ↦ Γ(V_k)` are compatible with the maps from `Γ(O)`. -/
theorem res_stageToOpen' {k k' : Over k₀} (f : k' ⟶ k) (r : Γ((O : Scheme.{u}), ⊤)) :
    res D f ((stageToOpen' O f₀ k).appTop.hom r) = (stageToOpen' O f₀ k').appTop.hom r := by
  have e : (BigFppfOver.toScheme B S hS).map (D.map f.left).hom ≫ stageToOpen' O f₀ k =
      stageToOpen' O f₀ k' := by
    rw [stageToOpen', stageToOpen', ← Category.assoc, ← Functor.map_comp, map_left_hom_comp]
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

omit [IsCofiltered I] hD hpt [IsAffine (O : Scheme.{u})] in
/-- The maps `Γ(V_k) → Γ(V)` are compatible with the maps from `Γ(O)`. -/
theorem resL_stageToOpen' (k : Over k₀) (r : Γ((O : Scheme.{u}), ⊤)) :
    resL κ k ((stageToOpen' O f₀ k).appTop.hom r) = (limitToOpen (κ := κ) O f₀).appTop.hom r := by
  have e : (BigFppfOver.toScheme B S hS).map (κ.π.app k.left).hom ≫ stageToOpen' O f₀ k =
      limitToOpen (κ := κ) O f₀ := by
    rw [stageToOpen', limitToOpen, ← Category.assoc, ← Functor.map_comp, cone_π_hom_comp]
  rw [← e, Scheme.Hom.comp_appTop]
  rfl

end OverO

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

/-- The ring map `φ = (x̂)^♯ : B → A^∧` of `x₀`, lifted to the universe of the tower rings. -/
def limitPhi : Bt →+* limitCompletion (κ := κ) I₀ :=
  (ULift.ringEquiv.symm : AdicCompletion (limitIdeal (κ := κ) I₀)
      Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤) ≃+* ULift.{u + 1} _).toRingHom.comp
    ((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom)).toRingHom

omit [IsCofiltered I] hD in
include hρ hf₀ in
/-- The image in `A^∧` of an element `r` of `Γ(O)`, through `A_k^∧`, is `φ (ρ r)`. -/
theorem completionToLimit_algebraMap_stageToOpen' (k : Over k₀) (r : Γ((O : Scheme.{u}), ⊤)) :
    (completionToLimit (κ := κ) I₀ k).hom
        (ULift.up (algebraMap _ _ ((stageToOpen' O f₀ k).appTop.hom r))) =
      limitPhi W hZI₀ hB e (x₀ := x₀) (ρ r) := by
  refine ULift.ext ?_
  have h1 := congrArg (fun φ => φ r) (toRingHom_comp_eq_of_isOver O ρ hρ (limitIdeal (κ := κ) I₀)
    (limitToOpen (κ := κ) O f₀) (limitToOpen_ι O f₀ hf₀) hB
    ((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom)))
  refine (completionRingHom_algebraMap (resL κ k) (stageIdeal_map_limit I₀ k).le _).trans ?_
  exact (congrArg (algebraMap _ _) (resL_stageToOpen' O f₀ k r)).trans h1.symm

omit [IsCofiltered I] hpt in
include hρ hf₀ hOC in
/-- The image in `C_k^∧` of an element `r` of `Γ(O)`, through `A_k^∧`, is the transport of
`ψ (ρ r)` along `k ⟶ topStage k₀`. -/
theorem alpha_algebraMap_stageToOpen' {k : Over k₀} (f : k ⟶ topStage k₀)
    (r : Γ((O : Scheme.{u}), ⊤)) :
    stageAlpha W hZI₀ k (algebraMap _ _ ((stageToOpen' O f₀ k).appTop.hom r)) =
      towerRingMap (D.map f.left).hom (stageIdeal_map_le I₀ f) (stageQ W (topStage k₀))
        (stageQ W k) (stageHom W f) (stageHom_q W f)
        (stagePsi W ℓ hZI₀ hB e (topStage k₀) (ρ r)) := by
  have h1 := alpha_algebraMap (stageQ W k) (stage_hZI hZI₀ k) (stage_hqc W k)
    ((stageToOpen' O f₀ k).appTop.hom r)
  have h2 := towerRingHom_ρ O hOC hB ρ hρ (stageQ W (topStage k₀)) (stage_hZI hZI₀ _)
    (stage_hqc W _) (stageFormal W ℓ (topStage k₀) ≫ e.hom) (stageToOpen' O f₀ (topStage k₀))
    (stageToOpen'_ι O f₀ hf₀ _) r
  have h3 := congrArg (fun φ => φ (pullbackRingHom B _ (spaceHom _ (stageQ W (topStage k₀)))
    ((stageToOpen' O f₀ (topStage k₀)).appTop.hom r))) (towerRingMap_comp_towerOf
      (stageQ W (topStage k₀)) (D.map f.left).hom (stageIdeal_map_le I₀ f) (stageQ W k)
      (stageHom W f) (stageHom_q W f))
  have h4 := globalSectionsRingHomSite_stageHom_pullbackRingHom W f
    ((stageToOpen' O f₀ (topStage k₀)).appTop.hom r)
  rw [res_stageToOpen'] at h4
  refine h1.trans ?_
  rw [stagePsi, h2]
  exact ((congrArg (towerOf (stageIdeal I₀ k) (stageQ W k)) h4).symm.trans h3.symm)

omit [IsCofiltered I] in
include hρ hf₀ hOC in
/-- **The elements of `R` are liftable at every stage**: `φ` and `ψ` are `R`-linear. -/
theorem isGoodAt_ρ {k : Over k₀} (f : k ⟶ topStage k₀) (r : Γ((O : Scheme.{u}), ⊤)) :
    StageLift.IsGoodAt (alphaSystem W hZI₀) (completionToLimit (κ := κ) I₀)
      (limitPhi W hZI₀ hB e (x₀ := x₀)) (stagePsi W ℓ hZI₀ hB e (topStage k₀)) f (ρ r) :=
  ⟨ULift.up (algebraMap _ _ ((stageToOpen' O f₀ k).appTop.hom r)),
    completionToLimit_algebraMap_stageToOpen' W hZI₀ O f₀ hf₀ hB e ρ hρ k r,
    alpha_algebraMap_stageToOpen' W hZI₀ O hOC f₀ hf₀ ℓ hB e ρ hρ f r⟩

/-- `ψ` as a map to the first ring of the system `k ↦ C_k^∧`. -/
def stagePsiSys : Bt →+* (towerSystem W I₀).obj (op (topStage k₀)) :=
  stagePsi W ℓ hZI₀ hB e (topStage k₀)

omit [IsCofiltered I] in
include hℓ in
/-- The `hφψ` input. -/
theorem system_hφψ (b : Bt) :
    (limitAlphaHom W hZI₀).hom (limitPhi W hZI₀ hB e (x₀ := x₀) b) =
      (towerToLimit W I₀ (topStage k₀)).hom (stagePsiSys W hZI₀ ℓ hB e b) :=
  limitAlpha_continuousHomEquiv_symm W ℓ hZI₀ hB e hℓ (topStage k₀) b

omit [IsCofiltered I] hpt in
/-- The `hψc` input. -/
theorem system_hψc (n : ℕ) :
    (stagePsiSys W hZI₀ ℓ hB e ⁻¹' (towerFiltrationSys W I₀ (topStage k₀) n :
      Set ((towerSystem W I₀).obj (op (topStage k₀))))) ∈ 𝓝 (0 : Bt) :=
  towerRingHom_preimage_mem_nhds (stageQ W (topStage k₀)) (stage_hZI hZI₀ _)
    (stage_hqc W _) hB (stageFormal W ℓ (topStage k₀) ≫ e.hom) n

omit [IsCofiltered I] in
include hρ hf₀ hOC in
/-- The `hR₀` input. -/
theorem system_hR₀ {k : Over k₀} (f : k ⟶ topStage k₀) (b : Bt) (hb : b ∈ ρ.range) :
    StageLift.IsGoodAt (alphaSystem W hZI₀) (completionToLimit (κ := κ) I₀)
      (limitPhi W hZI₀ hB e (x₀ := x₀)) (stagePsiSys W hZI₀ ℓ hB e) f b := by
  obtain ⟨r, rfl⟩ := hb
  exact isGoodAt_ρ W hZI₀ O hOC f₀ hf₀ ℓ hB e ρ hρ f r

omit [IsCofiltered I] hD in
/-- `φ = (x̂)^♯` is continuous for the `I`-adic filtration of `A^∧`. -/
theorem limitPhi_preimage_mem_nhds (n : ℕ) :
    limitPhi W hZI₀ hB e (x₀ := x₀) ⁻¹'
        ((limitIdealPow (κ := κ) I₀ n : Ideal (limitCompletion (κ := κ) I₀)) :
          Set (limitCompletion (κ := κ) I₀)) ∈ 𝓝 (0 : Bt) := by
  obtain ⟨htop, -, hIadicl, -, -⟩ :=
    FormalSpace.adicCompletion_isAdic_of_fg (limitIdeal (κ := κ) I₀)
      (limitIdeal (κ := κ) I₀).fg_of_isNoetherianRing
  have := htop
  have hopen : IsOpen ((((limitIdeal (κ := κ) I₀).map (algebraMap _
      (AdicCompletion (limitIdeal (κ := κ) I₀)
        Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤)))) ^ n :
      Ideal (AdicCompletion (limitIdeal (κ := κ) I₀)
        Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))) :
      Set (AdicCompletion (limitIdeal (κ := κ) I₀)
        Γ((BigFppfOver.toScheme B S hS).obj κ.pt.obj, ⊤))) :=
    (isAdic_iff.mp hIadicl).1 n
  exact Filter.mem_of_superset ((hopen.preimage
    ((continuousHomEquiv (limit_hZI hZI₀) hB).symm (x₀ ≫ e.hom)).continuous).mem_nhds (by
      rw [Set.mem_preimage, RingHom.map_zero]
      exact Submodule.zero_mem _)) (fun b hb => mem_limitIdealPow.2 hb)

include hκ hρ hf₀ hℓ hOC in
/-- **The continuous lift for the descended system** (`StageLift.exists_stage_continuous_ringHom`
applied to `k ↦ A_k^∧`, `k ↦ C_k^∧`, `φ = (x̂)^♯` and `ψ`). -/
theorem exists_stage_lift_system (s : Finset Bt)
    (hdense : Dense (Subring.closure ((ρ.range : Set Bt) ∪ (s : Set Bt)) : Set Bt)) :
    ∃ (k₂ : Over k₀) (f₂ : k₂ ⟶ topStage k₀) (k : Over k₀) (g : k ⟶ k₂)
      (φk : Bt →+* (completionSystem (D := D) I₀).obj (op k)),
      (∀ b, (completionToLimit (κ := κ) I₀ k).hom (φk b) = limitPhi W hZI₀ hB e (x₀ := x₀) b) ∧
      (∀ b, ((alphaSystem W hZI₀).app (op k)).hom (φk b) =
        ((towerSystem W I₀).map (g ≫ f₂).op).hom (stagePsiSys W hZI₀ ℓ hB e b)) ∧
      (∀ b (x : (completionSystem (D := D) I₀).obj (op k₂)),
        (completionToLimit (κ := κ) I₀ k₂).hom x = limitPhi W hZI₀ hB e (x₀ := x₀) b →
        ((alphaSystem W hZI₀).app (op k₂)).hom x =
          ((towerSystem W I₀).map f₂.op).hom (stagePsiSys W hZI₀ ℓ hB e b) →
        ((completionSystem (D := D) I₀).map g.op).hom x = φk b) ∧
      ∀ n : ℕ,
        (φk ⁻¹' ((stageIdealHat I₀ k ^ n : Ideal ((completionSystem (D := D) I₀).obj (op k))) :
        Set ((completionSystem (D := D) I₀).obj (op k)))) ∈ 𝓝 (0 : Bt) :=
  StageLift.exists_stage_continuous_ringHom (K := Over k₀) (Ah := completionSystem (D := D) I₀)
    (Ch := towerSystem W I₀) (Al := limitCompletion (κ := κ) I₀) (Cl := limitTower (w := w) I₀)
    (B := Bt) (k₀ := topStage k₀)
    (alphaSystem W hZI₀) (limitAlphaHom W hZI₀) (completionToLimit (κ := κ) I₀) (towerToLimit W I₀)
    (fun f => completionSystem_map_comp_completionToLimit f)
    (fun f => towerSystem_map_comp_towerToLimit W f)
    (limitPhi W hZI₀ hB e (x₀ := x₀)) (stagePsiSys W hZI₀ ℓ hB e)
    (stageIdealHat I₀) (limitIdealPow (κ := κ) I₀)
    (towerFiltrationSys W I₀)
    (fun x => limitAlpha_completionToLimit W hZI₀ _ x)
    (system_hφψ W hZI₀ ℓ hB e hℓ)
    (system_hcoker hκ W hZI₀) (system_hker hκ W hZI₀) (fun {k} => system_hL hκ W hZI₀ k)
    (system_hpre I₀) (system_hsepA I₀) (system_hsepC W)
    (system_hFA I₀) (system_hFC W) (system_hρI I₀) (system_hαI W hZI₀)
    (system_hAR W hZI₀) (fun g n x hx => system_hmapA I₀ g n x hx)
    (fun f n y hy => system_hmapC W f n y hy)
    (limitPhi_preimage_mem_nhds W hZI₀ hB e)
    (system_hψc W hZI₀ ℓ hB e)
    ρ.range s hdense
    (fun f b hb => system_hR₀ W hZI₀ O hOC f₀ hf₀ ℓ hB e ρ hρ f b hb)

end Lift

end AlgebraicGeometry.Artin.LimitStages

end
