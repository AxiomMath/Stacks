module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicDirectImageChartLimit

/-!
# The scheme-side data of Stacks 08BD on an affine chart

Let `V` be an affine étale chart of the algebraic space `Y`.  This file transports to the
chart's scheme of `V` (and of `V ×_Y X`) the data the scheme-level Stacks 088B is about:

* `AlgebraicGeometry.Space.chartTildeSystem` — the tower of sections over `V` of a coherent adic
  system `(𝓖_n)` on `Y`, made into a coherent adic system on the chart's scheme by `affineTilde`;
* `AlgebraicGeometry.Space.chartTildeMap` — the transpose, along `affineTilde`, of the sections
  over `V` of a morphism `α : (𝓖_n) ⟶ (f_*𝓕)^∧`;
* `AlgebraicGeometry.Space.chartBetaSystem` — the transpose of the sections over `V` of the maps
  `γ_n`, along `affineTilde` and then along `g^* ⊣ g_*`.

## Main definitions

* `CategoryTheory.Adjunction.transposeSystem` — the levelwise transpose of a morphism of inverse
  systems along an adjunction.
* `AlgebraicGeometry.Space.affineTildeChartGlobalSectionsAdjunction` — `affineTilde ⊣ Γ(-, ⊤)`
  on the chart's scheme, with the global sections read as modules over the functions on the
  chart.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {Y : AlgebraicSpaces B S hS}
    (J : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : IsCartesianOnAffineCharts J.toSheafOfModules)
    (V : SmallEtale B S hS Y.1) [hV : IsAffine (chartScheme V)]
    [hVN : IsNoetherianRing Γ(chartScheme V, ⊤)]
    (G : CoherentAdicSystems B S hS Y.1 Y.2 J)

/-- A module all of whose elements are killed by an ideal power has vanishing ideal-power
multiple. -/
theorem _root_.ModuleCat.pow_smul_top_eq_bot_of_forall {R : Type u} [CommRing R]
    (M : ModuleCat.{u} R)
    (I : Ideal R) (k : ℕ) (h : ∀ r ∈ I ^ k, ∀ x : M, r • x = 0) :
    I ^ k • (⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.mpr (Submodule.smul_le.mpr fun r hr x _ => (Submodule.mem_bot _).mpr (h r hr x))

include hJ hV in
/-- **The tower of sections of a coherent adic system over an affine chart, made into a coherent
adic system on the chart's scheme.** -/
def chartTildeSystem :
    Stacks.Coherent.CoherentAdicSystems
      (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V)) := by
  refine ⟨chartSectionsSystem B S hS Y.1 Y.2 G.obj V ⋙ Stacks.Coherent.affineTilde (chartScheme V),
    fun n => ?_, fun n => ?_, fun n => ?_⟩
  · exact @Stacks.Coherent.affineTilde_coherent (chartScheme V) hV hVN
      ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))
      (moduleFinite_chartSectionsSystem_obj B S hS Y.1 Y.2 J G.property hV n)
  · have := Stacks.Coherent.affineTilde_quasicoherent (chartScheme V)
      ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))
    refine @Stacks.Coherent.affine_idealPowerMultiple_eq_bot (chartScheme V) hV _ _
      ((Stacks.Coherent.affineTilde (chartScheme V)).obj
        ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n))) this ?_
    refine @Stacks.Coherent.affineTilde_power_annihilates (chartScheme V) hV
      (chartSectionsIdeal B S hS Y J V) (n + 1)
      ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n)) ?_
    have hann := (idealPowerMultiple_eq_bot_iff B S hS Y.1 Y.2 J (n + 1) (G.obj.obj (op n))).mp
      (G.property.2.1 n) V
    exact ModuleCat.pow_smul_top_eq_bot_of_forall (R := Γ(chartScheme V, ⊤))
      ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).obj (op n)) _ _ hann
  · obtain ⟨e, he⟩ := Stacks.Coherent.affineTildeQuotientIso (chartScheme V)
      (chartSectionsIdeal B S hS Y J V) (n + 1)
      ((chartSectionsSystem B S hS Y.1 Y.2 G.obj V).map (homOfLE (Nat.le_succ n)).op)
      (surjective_chartSectionsSystem_map B S hS Y.1 Y.2 J G.property hV n)
      (ker_chartSectionsSystem_map_eq_pow_smul B S hS Y.1 Y.2 J G.property hJ hV n)
    exact ⟨e, he⟩

/-- **The adjoint of a morphism of inverse systems along an adjunction**, levelwise. -/
@[simps]
def _root_.CategoryTheory.Adjunction.transposeSystem {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {E : ℕᵒᵖ ⥤ C} {P : ℕᵒᵖ ⥤ D} (φ : E ⟶ P ⋙ R) :
    E ⋙ L ⟶ P where
  app n := (adj.homEquiv _ _).symm (φ.app n)
  naturality m n g := by
    change L.map (E.map g) ≫ (adj.homEquiv _ _).symm (φ.app n) =
      (adj.homEquiv _ _).symm (φ.app m) ≫ P.map g
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact φ.naturality g

/-- `affineTilde` is left adjoint to the global sections over the chart's scheme of `V`, read as
modules over the functions on the chart `V`. -/
def affineTildeChartGlobalSectionsAdjunction :
    Stacks.Coherent.affineTilde (chartScheme V) ⊣ chartGlobalSections B S hS V :=
  (Stacks.Coherent.affineTildeAdjunction (chartScheme V)).ofNatIsoRight
    ((Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (SheafOfModules.evaluation (chartScheme V).ringCatSheaf (op ⊤))
        (ModuleCat.restrictScalarsId' (RingHom.id Γ(chartScheme V, ⊤)) rfl).symm)

/-- The transpose along `g^* ⊣ g_*` of a morphism `φ : M ⟶ g_*N`, on the pullback of a section,
is the restriction of the value of `φ` on that section. -/
theorem homEquiv_symm_pullbackSection {T T' : Scheme.{u}} (g : T' ⟶ T) {M : T.Modules}
    {N : T'.Modules} (φ : M ⟶ (Scheme.Modules.pushforward g).obj N) (U : T.Opens) (O : T'.Opens)
    (h : O ≤ g ⁻¹ᵁ U) (a : M.val.obj (op U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N).symm φ).val.app (op O)
        (Scheme.Modules.pullbackSection g M U O h a) =
      N.val.map (homOfLE h).op (φ.val.app (op U) a) := by
  set ψ := ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N).symm φ
  have hφ : φ = (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M ≫
      (Scheme.Modules.pushforward g).map ψ :=
    (((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv M N).apply_symm_apply φ).symm.trans
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_unit _ _ _)
  have h1 := congrArg (fun k => k a) (congrArg (fun t => (t.val.app (op U)).hom) hφ)
  have h2 := congrArg (fun k => k
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (op U) a))
    (congrArg (fun t => t.hom) (ψ.val.naturality (homOfLE h).op))
  exact h2.trans (congrArg (N.val.map (homOfLE h).op) h1.symm)

/-- The transpose along an adjunction, followed by the right adjoint and preceded by the unit, is
the original morphism. -/
theorem _root_.CategoryTheory.Adjunction.unit_comp_map_homEquiv_symm {C D : Type*} [Category* C]
    [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {c : C} {d : D} (φ : c ⟶ R.obj d) :
    adj.unit.app c ≫ R.map ((adj.homEquiv c d).symm φ) = φ :=
  (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv c d).apply_symm_apply φ)

section SchemeData

variable {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hIcart : IsCartesianOnAffineCharts (hF := X.2)
      (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules)
    [hXloc : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIq : (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules.IsQuasicoherentOnSite)
    [hWN : IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj V))]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    [hVN : IsLocallyNoetherian (chartScheme V)]
    [hgp : _root_.AlgebraicGeometry.IsProper (chartBaseChangeMorphism B S hS f hf V)]
    [hYloc : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hJq : J.toSheafOfModules.IsQuasicoherentOnSite)
    (hFF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F))

include hJ hV in
/-- **The scheme-side map `α`**: the transpose along `affineTilde` of the sections over `V` of a
morphism `α : (𝓖_n) ⟶ (f_*𝓕)^∧`, read through the base tower isomorphism. -/
def chartTildeMap (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJq).obj ⟨_, hFF⟩) :
    chartTildeSystem B S hS J hJ V G ⟶
      (Stacks.Algebraization.completionFunctor (chartScheme V)
        (Scheme.IdealSheafData.ofIdealTop (chartSectionsIdeal B S hS Y J V))).obj
        (chartDirectImageCoherent B S hS f hf V F hF) :=
  ObjectProperty.homMk ((affineTildeChartGlobalSectionsAdjunction B S hS V).transposeSystem
    (Functor.whiskerRight α.hom (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)) ≫
      (completionDirectImageTowerIso B S hS f hf J hJ V F hF hJq hFF).hom))

variable (β : G.obj ⋙ modulePullback B S hS f ≅
      ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) hIq).obj
        ⟨F, hF⟩).obj)

/-- The sections over `V` of the maps `γ_n`, read in the global sections of the completion of the
chart restriction. -/
def chartGammaTower :
    chartSectionsSystem B S hS Y.1 Y.2 G.obj V ⟶ chartCompletionTower B S hS f hf J V F hF :=
  Functor.whiskerRight (directImageChartComparison B S hS f hf (pullbackIdealSubsheaf B S hS f hf J)
      hIq G.obj ⟨F, hF⟩ β)
    (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) (op V)) ≫
    (directImageCompletionTowerIso B S hS f hf J hJ hIcart hIq V F hF).hom

include hJ hV in
/-- **The scheme-side `β`**: the transpose of the maps `γ_n`, along `affineTilde` and then along
`g^* ⊣ g_*`, a morphism `g^*𝓖̄_n ⟶ 𝓕̄^∧_n` on the chart's scheme of `V ×_Y X`. -/
def chartBetaSystem :
    (chartTildeSystem B S hS J hJ V G).obj ⋙
        Scheme.Modules.pullback (chartBaseChangeMorphism B S hS f hf V) ⟶
      ((Stacks.Algebraization.completionFunctor (chartScheme ((smallBaseChange B S hS f hf).obj V))
        (chartBaseChangeIdeal B S hS f hf J V)).obj
        (chartRestrictionCoherent B S hS X F hF ((smallBaseChange B S hS f hf).obj V))).obj :=
  (Scheme.Modules.pullbackPushforwardAdjunction
      (chartBaseChangeMorphism B S hS f hf V)).transposeSystem
    ((affineTildeChartGlobalSectionsAdjunction B S hS V).transposeSystem
      (chartGammaTower B S hS J hJ V G f hf hIcart hIq F hF β))

end SchemeData

end AlgebraicGeometry.Space

end
