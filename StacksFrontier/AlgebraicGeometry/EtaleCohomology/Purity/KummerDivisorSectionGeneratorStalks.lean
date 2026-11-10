module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDivisorSectionGenerator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerChartGenerator
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerBaseChangeStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.BaseChangeAllDegrees
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.DerivedConnectingModelComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurvePurityLAdic

/-!
# The fundamental class of an étale divisor generates `R¹ j_* μ_N` on the stalks over the divisor

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement and `N` invertible in `k`.
The fundamental class `s` of `Z` in `R¹ j_* μ_N`
(`Stacks.EtaleCohomology.Purity.kummerDivisorSection`) generates the stalk of `R¹ j_* μ_N` freely
over `ℤ/N` at every geometric point over `Z`: `σ_s : ℤ/N ⟶ R¹ j_* μ_N` is invertible on these
stalks (`isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection_standard`).

Near a point of `Z`, a chart `V ⊆ U` with a smooth `φ : V ⟶ 𝔸¹_k` cuts out `Z ∩ V` by
`t = φ^* x` (`Stacks.EtaleCohomology.Purity.exists_smooth_affineLine_chart`). On `V` the class `s`
is the Kummer class of `t` (`Stacks.EtaleCohomology.Purity.kummerDivisorSection_restrict`), and
the degree-one base change map along the open immersion `ι : V ⟶ U`, an isomorphism since `ι` is
étale, carries it to the Kummer class of `t` on `V`
(`Stacks.EtaleCohomology.Purity.map_homEquiv_kummerBaseChangeMap_localKummerClass`): so
`ι⁻¹ σ_s` is `σ_{∂ t}` up to isomorphisms, and `σ_{∂ t}` is invertible on the stalks over `Z ∩ V`
by the Kummer generator of a smooth chart
(`Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine`).
A geometric point of `U` over `Z ∩ V` factors through `V`, and the stalk of `σ_s` there is the
stalk of `ι⁻¹ σ_s`.

This file works in the standard model of the derived categories, in which the base change maps
are defined; the model-independent form is
`Stacks.EtaleCohomology.Purity.isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection`.

## Main results

* `isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection_standard`: the morphism
  `σ_s : ℤ/N ⟶ R¹ j_* μ_N` is invertible on the stalks at geometric points over `Z`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w₁ w₂ u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- An endomorphism of the base change of the final object of the small étale site is the
identity. -/
theorem smallEtaleBaseChange_top_endo_eq_id {X S : Scheme.{u}} (f : X ⟶ S)
    (a : (smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤) ⟶
      (smallEtaleBaseChange f).obj ((opensToEtale S).obj ⊤)) : a = 𝟙 _ :=
  (isTerminalSmallEtaleBaseChangeObj f (isTerminal_opensToEtale_top S)).hom_ext _ _

/-- Two local Kummer classes of equal functions agree. -/
theorem localKummerClass_congr {U₀ U : Scheme.{u}} (j : U₀ ⟶ U)
    [HasDerivedCategory (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
    [HasDerivedCategory (Sheaf (smallEtaleTopology U) Ab.{u + 1})] {N : ℕ} (hN0 : N ≠ 0)
    (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (V : U.Opens) {t t' : Γ(U, V)} (e : t = t')
    (ht : IsUnit (puncturedFunction j V t)) (ht' : IsUnit (puncturedFunction j V t')) :
    localKummerClass j hN0 hN V t ht = localKummerClass j hN0 hN V t' ht' := by
  subst e
  rfl

section Generator

-- The standard model of the derived categories, in which the base change maps of the étale
-- direct images are defined (for the comparison with another model,
-- `Stacks.EtaleCohomology.Purity.exists_iso_rightDerivedConnecting_comp` suffices here).
attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] (N : ℕ) [NeZero N] (hN : IsUnit (N : k)) {U W Z U₀ : Scheme.{u}}
  (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
  (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range i.base)ᶜ)
  (hN₀ : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
  (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)

include hN pW g in
attribute [-instance] CategoryTheory.catToReflQuiver in
/-- **The fundamental class generates `R¹ j_* μ_N` along the divisor**, in the standard model:
`σ_s : ℤ/N ⟶ R¹ j_* μ_N` is invertible on the stalks at the geometric points over `Z`. -/
theorem isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection_standard :
    IsIsoStalksOver (Set.range i.base)
      (torsionSectionSheafHom (kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov)
        (nsmul_kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov)) := by
  intro Ω _ _ x hx
  have hN0 : N ≠ 0 := NeZero.ne N
  have : Smooth g := SmoothOfRelativeDimension.smooth 1 g
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian (g ≫ pW)
  have : QuasiCompact j := inferInstance
  have : IsSeparated j := IsSeparated.isSeparated_of_mono _
  have : QuasiSeparated j := AlgebraicGeometry.IsSeparated.instQuasiSeparated _
  obtain ⟨z, hz⟩ := hx ⟨default, rfl⟩
  obtain ⟨V, hzV, π, ψ, hπ, -, hsm, hpb⟩ := exists_smooth_affineLine_chart k pW g i z
  have : Smooth (π ≫ affineLineBaseMap k pW) := hsm
  have sq : IsPullback (pullback.snd j V.ι) (pullback.fst j V.ι) V.ι j :=
    (IsPullback.of_hasPullback j V.ι).flip
  have : QuasiCompact (pullback.snd j V.ι) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback j V.ι)
      inferInstance
  obtain ⟨φ₀, sqS⟩ := exists_isPullback_punctured_of_mem_range_iff (π ≫ affineLineBaseMap k pW)
    (pullback.snd j V.ι) fun v => by
      rw [Scheme.Pullback.range_snd]
      have := (mem_punctured_iff_of_chart i j hj V (π ≫ affineLineBaseMap k pW) ψ hpb (𝟙 _) v).symm
      simpa only [Category.id_comp, Set.mem_preimage] using this
  set t' := (π ≫ affineLineBaseMap k pW).appTop (coordinate k) with ht'def
  have hloc := isLocalEquation_of_isPullback_origin k i V (π ≫ affineLineBaseMap k pW) ψ hpb
  have hO : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := fun p _ => p.2
  have happ := appLE_ι_topIso_hom V hO t'
  have hNY : IsUnit ((N : ℕ) : Γ(pullback j V.ι, ⊤)) :=
    isUnit_natCast_globalSections_of_over (pullback.snd j V.ι ≫ V.ι ≫ g ≫ pW) hN
  have ht' := isUnit_puncturedFunction_of_isPullback_punctured (π ≫ affineLineBaseMap k pW)
    (pullback.snd j V.ι) φ₀ sqS
  have ht'' : IsUnit (puncturedFunction (pullback.snd j V.ι) ⊤
      (V.ι.appLE V ⊤ hO (V.topIso.hom t'))) := by rw [happ]; exact ht'
  let m : (opensToEtale V.toScheme).obj ⊤ ⟶
      (smallEtaleBaseChange V.ι).obj ((opensToEtale U).obj V) :=
    MorphismProperty.Over.homMk (pullback.lift (⊤ : V.toScheme.Opens).ι (⊤ : V.toScheme.Opens).ι
      rfl) (pullback.lift_snd _ _ _)
  have hmain := map_homEquiv_kummerBaseChangeMap_localKummerClass V.ι j (pullback.snd j V.ι)
    (pullback.fst j V.ι) sq.w hN0 hN₀ hNY V (V.topIso.hom t')
    (isUnit_puncturedFunction j hj.subset hloc.diff_range_subset_basicOpen) ⊤ hO ht'' m
  rw [localKummerClass_congr (pullback.snd j V.ι) hN0 hNY ⊤ happ ht'' ht'] at hmain
  -- the transposed base change map on the fundamental class
  set s := kummerDivisorSection j hN0 hN₀ hNU i hj.subset hcov with hs
  set Ψ := (smallEtaleAdjunctionAb V.ι).homEquiv _ _
    (kummerBaseChangeMap V.ι j (pullback.snd j V.ι) (pullback.fst j V.ι) sq.w N) with hΨ
  have hres := kummerDivisorSection_restrict j hN0 hN₀ hNU i hj.subset hcov V
    (V.topIso.hom t') hloc
  have hnat : Ψ.hom.app (op ((opensToEtale U).obj V)) (localKummerClass j hN0 hN₀ V
        (V.topIso.hom t') (isUnit_puncturedFunction j hj.subset hloc.diff_range_subset_basicOpen)) =
      (kummerTarget (pullback.snd j V.ι) N).obj.map
        ((smallEtaleBaseChange V.ι).map ((opensToEtale U).map (homOfLE (le_top : V ≤ ⊤)))).op
        (Ψ.hom.app (op ((opensToEtale U).obj ⊤)) s) := by
    rw [← hres]
    exact NatTrans.naturality_apply Ψ.hom ((opensToEtale U).map (homOfLE (le_top : V ≤ ⊤))).op s
  rw [hnat] at hmain
  have e : (kummerTarget (pullback.snd j V.ι) N).obj.map
        ((smallEtaleBaseChange V.ι).map ((opensToEtale U).map (homOfLE (le_top : V ≤ ⊤)))).op ≫
      (kummerTarget (pullback.snd j V.ι) N).obj.map m.op ≫
        (kummerTarget (pullback.snd j V.ι) N).obj.map ((isTerminal_opensToEtale_top V.toScheme).from
          ((smallEtaleBaseChange V.ι).obj ((opensToEtale U).obj ⊤))).op = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, ← op_comp, ← op_comp,
      smallEtaleBaseChange_top_endo_eq_id V.ι (((isTerminal_opensToEtale_top V.toScheme).from
        ((smallEtaleBaseChange V.ι).obj ((opensToEtale U).obj ⊤)) ≫ m) ≫
          (smallEtaleBaseChange V.ι).map ((opensToEtale U).map (homOfLE (le_top : V ≤ ⊤)))),
      op_id, CategoryTheory.Functor.map_id]
  have hglob : Ψ.hom.app (op ((opensToEtale U).obj ⊤)) s =
      (kummerTarget (pullback.snd j V.ι) N).obj.map ((isTerminal_opensToEtale_top V.toScheme).from
        ((smallEtaleBaseChange V.ι).obj ((opensToEtale U).obj ⊤))).op
        (localKummerClass (pullback.snd j V.ι) hN0 hNY ⊤ t' ht') := by
    rw [← hmain]
    have h1 := ConcreteCategory.congr_hom e (Ψ.hom.app (op ((opensToEtale U).obj ⊤)) s)
    exact h1.symm
  -- the degree-one base change map along the open immersion `V ⊆ U` is invertible
  have : IsIso ((higherBaseChangeMapAb V.ι j (pullback.snd j V.ι) (pullback.fst j V.ι) sq.w
      (0 + 1)).app (kummerSequence.{u, 0} U₀ N).X₁) :=
    SmoothBaseChange.isIso_higherBaseChangeMapAb_of_etale
      SmoothBaseChange.etaleLocalHigherBaseChange
      V.ι (pullback.snd j V.ι) (pullback.fst j V.ι) j sq _ (0 + 1)
  have : IsIso (rootsOfUnityInverseImageComparison.{u, 0} (pullback.fst j V.ι) N) :=
    isIso_rootsOfUnityInverseImageComparison (pullback.fst j V.ι) N hN₀
  have : IsIso (kummerSequencePullbackMap (pullback.fst j V.ι) N).τ₁ := by
    change IsIso
      (((smallEtalePullbackAbIsoEtaleAbelianInverseImage (pullback.fst j V.ι)).hom.app _) ≫
        rootsOfUnityInverseImageComparison.{u, 0} (pullback.fst j V.ι) N)
    infer_instance
  have : IsIso (kummerBaseChangeMap V.ι j (pullback.snd j V.ι) (pullback.fst j V.ι) sq.w N) := by
    unfold kummerBaseChangeMap
    infer_instance
  let β : (smallEtalePullbackAb V.ι).obj (kummerTarget j N) ⟶
      ((smallEtalePushforwardAb (pullback.snd j V.ι)).rightDerived (0 + 1)).obj
        (kummerSequence.{u, 0} (pullback j V.ι) N).X₁ :=
    kummerBaseChangeMap V.ι j (pullback.snd j V.ι) (pullback.fst j V.ι) sq.w N
  have hβ : IsIso β := ‹IsIso (kummerBaseChangeMap V.ι j (pullback.snd j V.ι) (pullback.fst j V.ι)
    sq.w N)›
  have key := pullback_map_torsionSectionSheafHom_comp V.ι β s
    (nsmul_kummerDivisorSection j hN0 hN₀ hNU i hj.subset hcov) _
    (nsmul_localKummerClass (pullback.snd j V.ι) hN0 hNY ⊤ t' ht') hglob
  -- the Kummer generator of the chart
  have hσ' : IsIsoStalksOver (Set.range (pullback.snd j V.ι).base)ᶜ _ :=
    isIsoStalksOver_torsionSectionSheafHom_of_isPullback_affineLine
      (π ≫ affineLineBaseMap k pW) (pullback.snd j V.ι) φ₀ sqS hN hNY ht'
  -- the geometric point factors through `V`, off `V ×_U U₀`
  have hxV : Set.range x.base ⊆ Set.range V.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hp : p = default := Subsingleton.elim _ _
    rw [hp, ← hz]
    exact hzV
  obtain ⟨x', rfl⟩ : ∃ x' : Spec (.of Ω) ⟶ V.toScheme, x' ≫ V.ι = x :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hxV⟩
  have hx'' : Set.range x'.base ⊆ (Set.range (pullback.snd j V.ι).base)ᶜ := by
    rintro _ ⟨p, rfl⟩ ⟨q, hq⟩
    have h1 : (x' ≫ V.ι).base p ∈ Set.range i.base := hx ⟨p, rfl⟩
    have h2 : (x' ≫ V.ι).base p ∈ Set.range j.base := by
      refine ⟨(pullback.fst j V.ι).base q, ?_⟩
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hq,
        Scheme.Hom.comp_apply]
    rw [hj] at h2
    exact h2 h1
  set σs := torsionSectionSheafHom s (nsmul_kummerDivisorSection j hN0 hN₀ hNU i hj.subset hcov)
    with hσs
  have hc := congrArg (smallEtaleStalkAb x').map key
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at hc
  have h5 : IsIso ((smallEtaleStalkAb x').map (torsionSectionSheafHom
      (localKummerClass (pullback.snd j V.ι) hN0 hNY ⊤ t' ht')
      (nsmul_localKummerClass (pullback.snd j V.ι) hN0 hNY ⊤ t' ht'))) := hσ' x' hx''
  have h6 : IsIso ((smallEtaleStalkAb x').map ((smallEtalePullbackAbConstantIso V.ι).hom.app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod N))))) := Functor.map_isIso _ _
  have h7 : IsIso ((smallEtaleStalkAb x').map ((smallEtalePullbackAb V.ι).map σs)) := by
    have : IsIso ((smallEtaleStalkAb x').map ((smallEtalePullbackAb V.ι).map σs) ≫
        (smallEtaleStalkAb x').map β) := by
      rw [hc]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ h6 h5
    exact IsIso.of_isIso_comp_right _ ((smallEtaleStalkAb x').map β)
  exact (NatIso.isIso_map_iff (smallEtalePullbackStalkAbIso V.ι x') σs).1 h7

end Generator

section ModelTransfer

variable {S : Scheme.{u}} {N : ℕ} [NeZero N]

/-- **`σ_s` is natural in the sheaf**: `σ_s ≫ f = σ_{f(s)}`. -/
theorem torsionSectionSheafHom_comp_eq {F F' : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    (f : F ⟶ F') (s : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))) (hs : N • s = 0)
    (hs' : N • f.hom.app (op ((opensToEtale S).obj ⊤)) s = 0) :
    torsionSectionSheafHom s hs ≫ f =
      torsionSectionSheafHom (f.hom.app (op ((opensToEtale S).obj ⊤)) s) hs' := by
  rw [torsionSectionSheafHom, torsionSectionSheafHom, ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  ext ⟨n⟩
  change f.hom.app (op ((opensToEtale S).obj ⊤)) (torsionSectionHom s hs (ULift.up n)) =
    torsionSectionHom (f.hom.app (op ((opensToEtale S).obj ⊤)) s) hs' (ULift.up n)
  rw [torsionSectionHom_apply, torsionSectionHom_apply, map_nsmul]

omit [NeZero N] in
/-- `σ_s` depends only on `s`. -/
theorem torsionSectionSheafHom_congr {F : Sheaf (smallEtaleTopology S) Ab.{u + 1}}
    {s s' : ToType (F.obj.obj (op ((opensToEtale S).obj ⊤)))} (e : s = s') (hs : N • s = 0)
    (hs' : N • s' = 0) : torsionSectionSheafHom s hs = torsionSectionSheafHom s' hs' := by
  subst e
  rfl

variable {U₀ U : Scheme.{u}} (j : U₀ ⟶ U) (hN0 : N ≠ 0) (hN : IsUnit ((N : ℕ) : Γ(U₀, ⊤)))
  (I₁ : HasDerivedCategory.{w₁} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
  (J₁ : HasDerivedCategory.{w₁} (Sheaf (smallEtaleTopology U) Ab.{u + 1}))
  (I₂ : HasDerivedCategory.{w₂} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
  (J₂ : HasDerivedCategory.{w₂} (Sheaf (smallEtaleTopology U) Ab.{u + 1}))

omit [NeZero N] in
/-- **The Kummer coboundaries of two models of the derived categories differ by the comparison
of the models** (`Stacks.EtaleCohomology.Purity.rightDerivedModelComparison`). -/
theorem kummerDirectImageδ_comp_rightDerivedModelComparison :
    @kummerDirectImageδ _ _ j I₁ J₁ _ hN0 hN ≫
        (rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁ I₂ J₂ 1).app
          (rootsOfUnitySheaf.{u, 0} U₀ N) =
      @kummerDirectImageδ _ _ j I₂ J₂ _ hN0 hN := by
  have h := δ_comp_rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁ I₂ J₂
    (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0
  have h' : (rightDerivedZeroIsoOfModel (smallEtalePushforwardAb j) I₁ J₁).hom.app
        (kummerSequence.{u, 0} U₀ N).X₃ ≫
      (rightDerivedDeltaOfModel (smallEtalePushforwardAb j) I₁ J₁).δ
        (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0 ≫
      (rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁ I₂ J₂ (0 + 1)).app
        (kummerSequence.{u, 0} U₀ N).X₁ =
      (rightDerivedZeroIsoOfModel (smallEtalePushforwardAb j) I₂ J₂).hom.app
        (kummerSequence.{u, 0} U₀ N).X₃ ≫
      (rightDerivedDeltaOfModel (smallEtalePushforwardAb j) I₂ J₂).δ
        (kummerSequence_shortExact.{u, 0} U₀ hN0 hN) 0 := by
    rw [h, rightDerivedModelComparison_zero, NatTrans.comp_app, Category.assoc,
      Iso.hom_inv_id_app_assoc]
  rw [@kummerDirectImageδ_eq _ _ j I₁ J₁ _ hN0 hN, @kummerDirectImageδ_eq _ _ j I₂ J₂ _ hN0 hN]
  exact (Category.assoc _ _ _).trans h'

omit [NeZero N] in
/-- **The local Kummer classes of two models differ by the comparison of the models.** -/
theorem rightDerivedModelComparison_localKummerClass (V : U.Opens) (t : Γ(U, V))
    (ht : IsUnit (puncturedFunction j V t)) :
    ((rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁ I₂ J₂ 1).app
        (rootsOfUnitySheaf.{u, 0} U₀ N)).hom.app (op ((opensToEtale U).obj V))
        (@localKummerClass _ _ j I₁ J₁ _ hN0 hN V t ht) =
      @localKummerClass _ _ j I₂ J₂ _ hN0 hN V t ht := by
  change _ = (@kummerDirectImageδ _ _ j I₂ J₂ _ hN0 hN).hom.app (op ((opensToEtale U).obj V))
    (ofUnit.{u, 0} (X := U₀) (U := puncturedOpen j V) ht.unit)
  rw [← kummerDirectImageδ_comp_rightDerivedModelComparison j hN0 hN I₁ J₁ I₂ J₂]
  rfl

omit [NeZero N] in
/-- **The fundamental classes of two models differ by the comparison of the models.** -/
theorem rightDerivedModelComparison_kummerDivisorSection (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
    {Z : Scheme.{u}} (i : Z ⟶ U) [IsClosedImmersion i]
    (hj : Set.range j.base ⊆ (Set.range i.base)ᶜ)
    (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t) :
    ((rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁ I₂ J₂ 1).app
        (rootsOfUnitySheaf.{u, 0} U₀ N)).hom.app (op ((opensToEtale U).obj ⊤))
        (@kummerDivisorSection _ _ j I₁ J₁ _ hN0 hN hNU _ i _ hj hcov) =
      @kummerDivisorSection _ _ j I₂ J₂ _ hN0 hN hNU _ i _ hj hcov := by
  refine @eq_kummerDivisorSection _ _ j I₂ J₂ _ hN0 hN hNU _ i _ hj hcov _ (fun V t ht => ?_)
  exact ((NatTrans.naturality_apply ((rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁
    I₂ J₂ 1).app (rootsOfUnitySheaf.{u, 0} U₀ N)).hom ((opensToEtale U).map
      (homOfLE (le_top : V ≤ ⊤))).op _).symm.trans (congrArg _
        (@kummerDivisorSection_restrict _ _ j I₁ J₁ _ hN0 hN hNU _ i _ hj hcov V t ht))).trans
    (rightDerivedModelComparison_localKummerClass j hN0 hN I₁ J₁ I₂ J₂ V t _)

/-- The comparison of two models of the derived categories is invertible. -/
theorem isIso_rightDerivedModelComparison_app (n : ℕ)
    (X : Sheaf (smallEtaleTopology U₀) Ab.{u + 1}) :
    IsIso ((rightDerivedModelComparison (smallEtalePushforwardAb j) I₁ J₁ I₂ J₂ n).app X) :=
  ⟨⟨(rightDerivedModelComparison (smallEtalePushforwardAb j) I₂ J₂ I₁ J₁ n).app X,
    NatTrans.congr_app (rightDerivedModelComparison_comp _ I₁ J₁ I₂ J₂ n) X,
    NatTrans.congr_app (rightDerivedModelComparison_comp _ I₂ J₂ I₁ J₁ n) X⟩⟩

end ModelTransfer

section Generic

variable (k : Type u) [Field k] (N : ℕ) [NeZero N] (hN : IsUnit (N : k)) {U W Z U₀ : Scheme.{u}}
  (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W) [SmoothOfRelativeDimension 1 g]
  (i : Z ⟶ U) [IsClosedImmersion i] [Etale (i ≫ g)] (j : U₀ ⟶ U) [IsOpenImmersion j]
  (hj : Set.range j.base = (Set.range i.base)ᶜ)
  [I₀ : HasDerivedCategory.{w₂} (Sheaf (smallEtaleTopology U₀) Ab.{u + 1})]
  [I : HasDerivedCategory.{w₂} (Sheaf (smallEtaleTopology U) Ab.{u + 1})]
  (hN₀ : IsUnit ((N : ℕ) : Γ(U₀, ⊤))) (hNU : IsUnit ((N : ℕ) : Γ(U, ⊤)))
  (hcov : ∀ x : U, ∃ (V : U.Opens) (t : Γ(U, V)), x ∈ V ∧ IsLocalEquation i V t)

include hN pW g in
/-- **The fundamental class generates `R¹ j_* μ_N` along the divisor**: for `W` smooth over a
field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a closed immersion with
`Z ⟶ W` étale, `j : U₀ ⟶ U` the open complement and `N` invertible in `k`, the morphism
`σ_s : ℤ/N ⟶ R¹ j_* μ_N` of the fundamental class `s` of `Z` is invertible on the stalks at the
geometric points over `Z`, in any model of the derived categories. -/
theorem isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection :
    IsIsoStalksOver (Set.range i.base)
      (torsionSectionSheafHom (kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov)
        (nsmul_kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov)) := by
  have hstd : IsIsoStalksOver (Set.range i.base) _ :=
    isIsoStalksOver_torsionSectionSheafHom_kummerDivisorSection_standard k N hN pW g i j
      hj hN₀ hNU hcov
  have hc := rightDerivedModelComparison_kummerDivisorSection j (NeZero.ne N) hN₀
    (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
    (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1}))
    I₀ I hNU i hj.subset hcov
  have e := torsionSectionSheafHom_comp_eq
    ((rightDerivedModelComparison (smallEtalePushforwardAb j)
      (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
      (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) I₀ I 1).app
        (rootsOfUnitySheaf.{u, 0} U₀ N))
    (@kummerDivisorSection _ _ j
      (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
      (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) N (NeZero.ne N) hN₀
      hNU _ i _ hj.subset hcov)
    (@nsmul_kummerDivisorSection _ _ j N
      (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
      (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) (NeZero.ne N) hN₀
      hNU _ i _ hj.subset hcov)
    (nsmul_kummerTarget_section j _)
  have hiso := isIso_rightDerivedModelComparison_app j
    (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
    (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) I₀ I 1
    (rootsOfUnitySheaf.{u, 0} U₀ N)
  have e2 : torsionSectionSheafHom (kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov)
        (nsmul_kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov) =
      torsionSectionSheafHom (@kummerDivisorSection _ _ j
          (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
          (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) N (NeZero.ne N)
          hN₀ hNU _ i _ hj.subset hcov)
        (@nsmul_kummerDivisorSection _ _ j N
          (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
          (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) (NeZero.ne N)
          hN₀ hNU _ i _ hj.subset hcov) ≫
        (rightDerivedModelComparison (smallEtalePushforwardAb j)
          (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U₀) Ab.{u + 1}))
          (HasDerivedCategory.standard (Sheaf (smallEtaleTopology U) Ab.{u + 1})) I₀ I 1).app
            (rootsOfUnitySheaf.{u, 0} U₀ N) :=
    (e.trans (torsionSectionSheafHom_congr hc _
      (nsmul_kummerDivisorSection j (NeZero.ne N) hN₀ hNU i hj.subset hcov))).symm
  rw [e2]
  exact @IsIsoStalksOver.comp_of_isIso _ _ _ _ _ _ hstd _ hiso

end Generic

end Stacks.EtaleCohomology.Purity

end
