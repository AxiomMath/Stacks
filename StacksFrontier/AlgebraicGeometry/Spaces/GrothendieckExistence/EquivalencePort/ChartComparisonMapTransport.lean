module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartAdjointIsoTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartFormalFunctionsTransport
public import StacksFrontier.AlgebraicGeometry.C1573Port.FormalGeometry.CompletionProper.ExceptionalComparisonMapAdjoint

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# The comparison map of Stacks 08BD over an affine chart

Let `α : (𝒢_n) ⟶ ((f_*𝓕)/𝒥ⁿ⁺¹(f_*𝓕))` be a map of inverse systems on `Y` whose composite with the
comparison `c : (f_*𝓕)^∧ ⟶ f_*(𝓕^∧)` is the system `γ` of Stacks 08BD.  Over an affine étale chart
`V` of `Y` with Noetherian ring of functions, the maps `α_n` on the sections over `V` are, through
the identification of `((f_*𝓕)/𝒥ⁿ⁺¹)(V)` with the global sections of `(f_{V*}𝓕|_U)/𝒥(V)ⁿ⁺¹`, the
global sections of a map of coherent adic systems `α' : (𝒢_n(V)~) ⟶ (f_{V*}𝓕|_U)^∧` on the
affine scheme `V` (`AlgebraicGeometry.Space.C1573.chartAdicSystemMap`), and `α' ≫ c' = γ'`
(`AlgebraicGeometry.Space.C1573.chartAdicSystemMap_comp`), with `γ'` the system of
`AlgebraicGeometry.Space.C1573.chartGamma`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

open _root_.CategoryTheory.C1573
attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
  (F : Modules.{u, u} B S hS X.1 X.2)
  (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
  (α : G.obj ⟶ adicQuotientSystem B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F))
  (V : SmallEtale B S hS Y.1) [IsAffine (chartScheme V)]
  [IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
  (hF : IsCoherent B S hS X.1 X.2 F)
  [IsNoetherianRing Γ(chartScheme V, ⊤)] (hfp : IsProper B S hS f.hom)
  (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
  (hM : IsCartesianOnAffineCharts ((modulePushforward B S hS f).obj F))

/-- `α_n` on the sections over `V`, read through the identification of
`((f_*𝓕)/𝒥ⁿ⁺¹)(V)` with the global sections of `(f_{V*}𝓕|_U)/𝒥(V)ⁿ⁺¹`. -/
def C1573.chartAdicSystemMapSections (n : ℕ) :
    (chartSectionsTop B S hS V).obj (G.obj.obj (op n)) ⟶
      (SheafOfModules.evaluation (chartScheme V).ringCatSheaf (op ⊤)).obj
        (((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.obj (op n)) :=
  (chartSectionsTop B S hS V).map (α.app (op n)) ≫
    (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n).toModuleIso.hom

/-- `chartAdicSystemMapSections` sends a section `m` of `𝒢_n` over `V` to the image of
`α_n(V)(m)` under `chartPushforwardAdicQuotientEquiv`. -/
theorem C1573.chartAdicSystemMapSections_apply (n : ℕ) (m : (G.obj.obj (op n)).val.obj (op V)) :
    (chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM n).hom m =
      chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n
        ((α.app (op n)).val.app (op V) m) :=
  rfl

/-- The maps `chartAdicSystemMapSections` commute with the transition maps `n + 1 → n` of the
sections of `𝒢` over `V` and of the completion of `f_{V*}𝓕|_U`. -/
theorem C1573.chartAdicSystemMapSections_naturality (n : ℕ) :
    (chartSectionsTop B S hS V).map (G.obj.map (homOfLE (Nat.le_add_right n 1)).op) ≫
        chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM n =
      chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM (n + 1) ≫
        (SheafOfModules.evaluation (chartScheme V).ringCatSheaf (op ⊤)).map
          (((Stacks.Algebraization.completionFunctor _
            (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
              (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.map
                (homOfLE (Nat.le_add_right n 1)).op) := by
  refine ModuleCat.hom_ext (DFunLike.ext _ _ fun m => ?_)
  have h1 := congrArg (fun k => k.val.app (op V) m)
    (α.naturality (homOfLE (Nat.le_add_right n 1)).op)
  have h2 := congrArg (fun k => k.val.app (op V) ((α.app (op (n + 1))).val.app (op V) m))
    (adicQuotientSystem_map_succ B S hS Y.1 Y.2 J ((modulePushforward B S hS f).obj F) n)
  have h3 := chartPushforwardAdicQuotientEquiv_transition B S hS f hf V J F hF hfp hJ hM n
    ((α.app (op (n + 1))).val.app (op V) m)
  show chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n
      ((α.app (op n)).val.app (op V) ((G.obj.map (homOfLE (Nat.le_add_right n 1)).op).val.app
        (op V) m)) = _
  exact (congrArg (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n) h1).trans
    ((congrArg (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n) h2).trans h3)

variable (hJqc : J.toSheafOfModules.IsQuasicoherentOnSite)

/-- **The map `α' : (𝒢_n(V)~) ⟶ (f_{V*}𝓕|_U)^∧` of coherent adic systems on the affine scheme
`V`** adjoint to `α_n` on the sections over `V`. -/
def C1573.chartAdicSystemMap : chartTildeSystem B S hS V J hJqc G ⟶
    ((Stacks.Algebraization.completionFunctor _
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
        (chartPushforwardCoherent B S hS f hf V F hF hfp)) :=
  ObjectProperty.homMk (NatTrans.ofOpSequence
    (fun n => ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _).symm
      (chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM n))
    (fun n => by
      change (Stacks.Coherent.affineTilde (chartScheme V)).map ((chartSectionsTop B S hS V).map
        (G.obj.map (homOfLE (Nat.le_add_right n 1)).op)) ≫ _ = _ ≫ _
      exact ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_naturality_left_symm
        _ _).symm.trans ((congrArg (fun k => ((Stacks.Coherent.affineTildeAdjunction
          (chartScheme V)).homEquiv _ _).symm k)
            (chartAdicSystemMapSections_naturality B S hS f hf J F G α V hF hfp hJ hM n)).trans
          ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_naturality_right_symm
            _ _))))

/-- The `n`-th component of `α'` is the map adjoint, under the tilde–global-sections
adjunction on `V`, to `chartAdicSystemMapSections` at `n`. -/
theorem C1573.chartAdicSystemMap_hom_app (n : ℕ) :
    (chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app (op n) =
      ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _).symm
        (chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM n) :=
  rfl

/-- **`α' ≫ c' = γ'`**: the scheme map `α'` composed with the comparison
`(f_{V*}𝓕|_U)^∧ ⟶ f_{V*}(𝓕|_U^∧)` of Stacks 088B is the system `γ'` of
`AlgebraicGeometry.Space.C1573.chartGamma`, as soon as `α ≫ c = γ` on `Y`. -/
theorem C1573.chartAdicSystemMap_comp
    (β : G.obj ⋙ modulePullback B S hS f ≅
      adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG)
    (hα : α ≫ directImageCompletionComparison B S hS f hf J F =
      directImageUnitComparison B S hS f hf J F G β) :
    haveI := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
      inferInstance
    haveI := isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp
    (chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom ≫
        Stacks.Coherent.pushforwardCompletionComparison (chartBaseChangeSchemeHom B S hS f hf V)
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
          ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F) =
      chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc := by
  have := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
    inferInstance
  have := isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp
  refine NatTrans.ext (funext fun n => ?_)
  obtain ⟨n⟩ := n
  apply ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _).injective
  refine ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_naturality_right _
    _).trans (Eq.trans ?_ (((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _
      _).apply_symm_apply (chartGammaSections B S hS f hf J F G β V hF hJ hJfg n)).symm)
  refine (congrArg (· ≫ _) (((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _
    _).apply_symm_apply (chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM n))).trans ?_
  refine ModuleCat.hom_ext (DFunLike.ext _ _ fun m => ?_)
  have h1 := congrArg (fun k => k.val.app (op V) m) (congrArg (fun k => k.app (op n)) hα)
  have h2 := chartDirectImageAdicQuotientIso_comparison B S hS f hf V J F hF hfp hJ hM hJfg n
    ((α.app (op n)).val.app (op V) m)
  exact h2.symm.trans
    (congrArg (chartDirectImageAdicQuotientIso B S hS f hf V J F hF hJ hJfg n).hom h1)

/-- The global sections of `α'_n` on the image of a section of `𝒢_n(V)` are `α_n` on the
sections over `V`. -/
theorem C1573.chartAdicSystemMap_app_top (n : ℕ) (m : (G.obj.obj (op n)).val.obj (op V)) :
    Scheme.Modules.Hom.app ((chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app
        (op n)) ⊤ ((Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op n)))).hom.hom m) =
      chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM n
        ((α.app (op n)).val.app (op V) m) := by
  have h1 : ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _)
      ((chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app (op n)) =
        chartAdicSystemMapSections B S hS f hf J F G α V hF hfp hJ hM n :=
    ((Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv _ _).apply_symm_apply _
  have h2 := (Stacks.Coherent.affineTildeAdjunction (chartScheme V)).homEquiv_unit
    ((chartSectionsTop B S hS V).obj (G.obj.obj (op n))) _
    ((chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app (op n))
  exact (ConcreteCategory.congr_hom (h1.symm.trans h2) m).symm

include hF hfp hJ hM hJqc in
/-- **Stacks 088B over an affine chart.**  If `f_V` is an isomorphism over the complement of
`V(𝒦(V))`, one power of `𝒦(V)` kills the kernels of the maps `α_k(V)` of sections over `V` and
pushes every section of `((f_*𝓕)/𝒥ᵏ⁺¹)(V)` into their images, for every `k`. -/
theorem C1573.exists_chartTopIdeal_pow_annihilates
    (K : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hK : IsIso ((chartBaseChangeSchemeHom B S hS f hf V) ∣_
      (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V K)).support.compl))
    (β : G.obj ⋙ modulePullback B S hS f ≅
      adicQuotientSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) F)
    (hJfg : ∀ Q : SmallEtale B S hS Y.1, IsAffine (chartScheme Q) →
      (chartSectionsIdeal B S hS Y J Q).FG)
    (hα : α ≫ directImageCompletionComparison B S hS f hf J F =
      directImageUnitComparison B S hS f hf J F G β) :
    ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
      (∀ r ∈ chartTopIdeal B S hS V K ^ t,
        ∀ x : (chartSectionsTop B S hS V).obj (G.obj.obj (op k)),
          ((chartSectionsTop B S hS V).map (α.app (op k))).hom x = 0 → r • x = 0) ∧
      (∀ r ∈ chartTopIdeal B S hS V K ^ t,
        ∀ y : (chartSectionsTop B S hS V).obj (smallEtaleAdicQuotient B S hS Y.1 Y.2 J (k + 1)
          ((modulePushforward B S hS f).obj F)),
          ∃ x : (chartSectionsTop B S hS V).obj (G.obj.obj (op k)),
            ((chartSectionsTop B S hS V).map (α.app (op k))).hom x = r • y) := by
  have := isProper_chartBaseChangeSchemeHom B S hS f hf V hfp
  have := isCoherent_chartZariskiModule B S hS X F hF ((smallBaseChange B S hS f hf).obj V)
    inferInstance
  have := isCoherent_pushforward_chartZariskiModule B S hS f hf V F hF hfp
  obtain ⟨t, ht, h⟩ := Stacks.Coherent.C1573.isKernelCokernelAnnihilatedByPower_of_isIso_adjoint
    (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))
    (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V K))
    (chartBaseChangeSchemeHom B S hS f hf V) hK (chartTildeSystem B S hS V J hJqc G)
    ((chartZariskiModule B S hS X ((smallBaseChange B S hS f hf).obj V)).obj F)
    (chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc)
    (fun n => isIso_adjoint_chartGamma B S hS f hf J F G β V hF hJ hJfg hJqc n.unop)
    (chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc)
    (chartAdicSystemMap_comp B S hS f hf J F G α V hF hfp hJ hM hJqc β hJfg hα)
  have hr' : ∀ r ∈ chartTopIdeal B S hS V K ^ t, r ∈ (Scheme.IdealSheafData.ofIdealTop
      (chartTopIdeal B S hS V K)).ideal ⟨⊤, isAffineOpen_top (chartScheme V)⟩ ^ t :=
    fun r hr => by rwa [Stacks.Coherent.ofIdealTop_ideal_top]
  refine ⟨t, ht, fun k => ⟨fun r hr x hx => ?_, fun r hr y => ?_⟩⟩
  · have h0 := Stacks.Coherent.smul_eq_zero_of_app_eq_zero_affine
      ((chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app (op k)) (h k).1
      ⟨⊤, isAffineOpen_top (chartScheme V)⟩ (hr' r hr)
      (x := (Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op k)))).hom.hom x)
      ((chartAdicSystemMap_app_top B S hS f hf J F G α V hF hfp hJ hM hJqc k x).trans
        ((congrArg (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM k)
          hx).trans (map_zero _)))
    exact (Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
      ((chartSectionsTop B S hS V).obj (G.obj.obj (op k)))).toLinearEquiv.injective
        (((map_smul _ r x).trans h0).trans (map_zero _).symm)
  · have : ((chartTildeSystem B S hS V J hJqc G).obj.obj (op k)).IsQuasicoherent :=
      Stacks.Coherent.affineTilde_quasicoherent (chartScheme V) _
    have : (((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.obj (op k)).IsCoherent :=
      ((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).property.1 k
    have : (((Stacks.Algebraization.completionFunctor _
          (Scheme.IdealSheafData.ofIdealTop (chartTopIdeal B S hS V J))).obj
            (chartPushforwardCoherent B S hS f hf V F hF hfp)).obj.obj (op k)).IsQuasicoherent :=
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
    obtain ⟨s, hs⟩ := Stacks.Coherent.smul_mem_range_of_cokernel_eq_bot_affine
      ((chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app (op k)) (h k).2
      ⟨⊤, isAffineOpen_top (chartScheme V)⟩ (hr' r hr)
      (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM k y)
    refine ⟨(Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op k)))).toLinearEquiv.symm s, ?_⟩
    apply (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM k).injective
    refine Eq.trans ?_ (map_smul (chartPushforwardAdicQuotientEquiv B S hS f hf V J F hF hfp hJ hM
      k) r y).symm
    refine (chartAdicSystemMap_app_top B S hS f hf J F G α V hF hfp hJ hM hJqc k _).symm.trans ?_
    refine Eq.trans ?_ hs
    exact congrArg (Scheme.Modules.Hom.app
      ((chartAdicSystemMap B S hS f hf J F G α V hF hfp hJ hM hJqc).hom.app (op k)) ⊤)
      ((Stacks.Coherent.affineTildeSectionsIso (chartScheme V)
          ((chartSectionsTop B S hS V).obj (G.obj.obj (op k)))).toLinearEquiv.apply_symm_apply s)

end AlgebraicGeometry.Space

end
