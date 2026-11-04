module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChartDirectImageTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSectionGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSpellingBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.InverseImageIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.DirectImageCompletionComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleTargetModuleFMapRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback

namespace CategoryTheory.Adjunction.C1573
end CategoryTheory.Adjunction.C1573
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Pullback of modules is compatible with ideal-power multiples

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces, `𝓙 ⊆ 𝒪_Y` a sheaf of ideals
cartesian on affine charts and `M` a quasi-coherent `𝒪_Y`-module.  A morphism `φ : f^*M ⟶ N`
kills the image of `f^*(𝓙ⁿM)` exactly when it kills `(f⁻¹𝓙)ⁿ f^*M`
(`AlgebraicGeometry.Space.C1573.modulePullback_idealPowerMultiple_ι_comp_eq_zero_iff`).
Consequently the termwise pullback of a coherent `𝓙`-adic system is a coherent `f⁻¹𝓙`-adic
system (`AlgebraicGeometry.Space.C1573.isCoherentAdicSystem_modulePullback_of_representable`),
which is the algebraic-spaces form of the lemma on pullbacks of adic systems used in the proof
of Stacks 08BE.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- For an adjunction `L ⊣ R` whose left adjoint preserves zero morphisms, `L.map i ≫ φ`
vanishes exactly when `i` followed by the transpose of `φ` does. -/
theorem CategoryTheory.Adjunction.C1573.map_comp_eq_zero_iff {C D : Type*} [Category* C]
    [Category* D]
    [HasZeroMorphisms C] [HasZeroMorphisms D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [L.PreservesZeroMorphisms] {P M : C} {N : D} (i : P ⟶ M) (φ : L.obj M ⟶ N) :
    L.map i ≫ φ = 0 ↔ i ≫ adj.homEquiv M N φ = 0 := by
  have h0 : adj.homEquiv P N 0 = 0 := by
    have : (0 : L.obj P ⟶ N) = L.map 0 ≫ φ := by rw [Functor.map_zero, zero_comp]
    rw [this, adj.homEquiv_naturality_left, zero_comp]
  rw [← adj.homEquiv_naturality_left, ← h0]
  exact (adj.homEquiv P N).apply_eq_iff_eq.symm

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
  (J : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)

/-- The vertical pullback of regular functions of the base-change chart diagram is the pullback
`f♯` along small-chart base change. -/
theorem C1573.chartDiagramPullback_baseChangeChartDiagram (V : SmallEtale B S hS Y.1)
    (r : chartRing B S hS Y.1 Y.2 V) :
    chartDiagramPullback B S hS f (baseChangeChartDiagram B S hS f hf V) r =
      chartIdealPullbackHom B S hS f hf V r := rfl

/-- The canonical map of sections into the direct image vanishes at zero. -/
theorem C1573.modulePushforwardCounitApp_apply_zero (N : Modules.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    modulePushforwardCounitApp B S hS f N d 0 = 0 := by
  have h := modulePushforwardCounitApp_add B S hS f N d 0 0
  rw [add_zero] at h
  exact add_left_cancel (h.symm.trans (add_zero _).symm)

/-- The chartwise transpose of a morphism out of a module pullback is the canonical map of
sections into the direct image applied to its first transpose. -/
theorem C1573.modulePullbackHomFMap_app_eq_counitApp (M : Modules.{u, u} B S hS Y.1 Y.2)
    {N : Modules.{u, u} B S hS X.1 X.2} (φ : (modulePullback B S hS f).obj M ⟶ N)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) (s : M.val.obj (op d.V)) :
    (modulePullbackHomFMap B S hS f M N φ).app d s =
      modulePushforwardCounitApp B S hS f N d
        (((modulePullbackAdjunction B S hS f).homEquiv M N φ).val.app (op d.V) s) :=
  rfl

/-- **The pullback of `𝓙ⁿM ⟶ M` is killed by `φ : f^*M ⟶ N` exactly when `φ` kills the unit
sections of the products `r • m`** over the base-change charts, `r ∈ 𝓙(V)ⁿ`. -/
theorem C1573.modulePullback_map_idealPowerMultiple_ι_comp_eq_zero_iff (n : ℕ)
    (M : Modules.{u, u} B S hS Y.1 Y.2) {N : Modules.{u, u} B S hS X.1 X.2}
    (φ : (modulePullback B S hS f).obj M ⟶ N) :
    (modulePullback B S hS f).map (idealPowerMultiple B S hS Y.1 Y.2 J n M).ι ≫ φ = 0 ↔
      ∀ (V : SmallEtale B S hS Y.1) (r : chartRing B S hS Y.1 Y.2 V),
        r ∈ chartIdeal B S hS Y J V ^ n → ∀ m : M.val.obj (op V),
          φ.val.app (op (baseChangeChartDiagram B S hS f hf V).U)
            (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V)
              (r • m)) = 0 := by
  have := preservesZeroMorphisms_modulePullback B S hS f
  let adj := modulePullbackAdjunction B S hS f
  have e1 : (modulePullback B S hS f).map (idealPowerMultiple B S hS Y.1 Y.2 J n M).ι ≫ φ = 0 ↔
      (idealPowerMultiple B S hS Y.1 Y.2 J n M).ι ≫ adj.homEquiv M N φ = 0 :=
    (CategoryTheory.Adjunction.C1573.map_comp_eq_zero_iff (adj := adj)) _ φ
  rw [e1, idealPowerMultiple_ι_comp_eq_zero_iff]
  refine forall_congr' fun V => forall_congr' fun r => forall_congr' fun _ =>
    forall_congr' fun m => ?_
  have hinj := (bijective_modulePushforwardCounitApp_baseChangeChartDiagram B S hS f hf V N).1
  have key := (modulePullbackHomFMap_app_eq_counitApp B S hS f M φ
      (baseChangeChartDiagram B S hS f hf V) (r • m)).symm.trans
    ((modulePullbackHomFMap_app B S hS f M N φ (baseChangeChartDiagram B S hS f hf V)
      (r • m)).trans
      (congrArg (φ.val.app (op (baseChangeChartDiagram B S hS f hf V).U))
        (modulePullbackUnitSection_eq_modulePullbackChartSection B S hS f M
          (baseChangeChartDiagram B S hS f hf V) (r • m))))
  refine ⟨fun h => key.symm.trans ?_, fun h => hinj ((key.trans h).trans
    (modulePushforwardCounitApp_apply_zero B S hS f N _).symm)⟩
  exact (congrArg (modulePushforwardCounitApp B S hS f N
    (baseChangeChartDiagram B S hS f hf V)) h).trans
      (modulePushforwardCounitApp_apply_zero B S hS f N _)

/-- The chart diagram of a chart `T` of `X` mapping to the base change `Q ×_Y X` of a chart `Q`
of `Y`. -/
def C1573.baseChangeChartDiagramOfHom {T : SmallEtale B S hS X.1} {Q : SmallEtale B S hS Y.1}
    (v : T ⟶ (smallBaseChange B S hS f hf).obj Q) : ChartDiagram B S hS X.1 Y.1 f.hom where
  U := T
  V := Q
  g := (SmallEtale.toOver B S hS X.1).map v ≫ hf.snd Q.1.hom
  comm := by
    have h2 : ((smallBaseChange B S hS f hf).obj Q).1.hom ≫ f.hom =
        yoneda.map (hf.snd Q.1.hom) ≫ Q.1.hom := hf.w Q.1.hom
    calc _ = (yoneda.map v.hom.left ≫ ((smallBaseChange B S hS f hf).obj Q).1.hom) ≫ f.hom :=
          (congrArg (· ≫ f.hom) (CostructuredArrow.w v.hom)).symm
      _ = yoneda.map v.hom.left ≫ (yoneda.map (hf.snd Q.1.hom) ≫ Q.1.hom) :=
        (Category.assoc _ _ _).trans (congrArg (yoneda.map v.hom.left ≫ ·) h2)
      _ = _ := by
        refine (Category.assoc _ _ _).symm.trans ?_
        exact congrArg (· ≫ Q.1.hom) (yoneda.map_comp v.hom.left (hf.snd Q.1.hom)).symm

/-- The chart section of the unit over a chart `T` mapping to `Q ×_Y X` is the restriction of
the one over the base-change chart. -/
theorem C1573.modulePullbackChartSection_baseChangeChartDiagramOfHom
    (M : Modules.{u, u} B S hS Y.1 Y.2) {T : SmallEtale B S hS X.1} {Q : SmallEtale B S hS Y.1}
    (v : T ⟶ (smallBaseChange B S hS f hf).obj Q) (m : M.val.obj (op Q)) :
    modulePullbackChartSection B S hS f M (baseChangeChartDiagramOfHom B S hS f hf v) m =
      ((modulePullback B S hS f).obj M).val.map v.op
        (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf Q) m) := by
  have hc : (SmallEtale.toOver B S hS X.1).map v ≫ (baseChangeChartDiagram B S hS f hf Q).g =
      (baseChangeChartDiagramOfHom B S hS f hf v).g ≫ (SmallEtale.toOver B S hS Y.1).map (𝟙 Q) := by
    refine Eq.trans ?_ (congrArg ((baseChangeChartDiagramOfHom B S hS f hf v).g ≫ ·)
      ((SmallEtale.toOver B S hS Y.1).map_id Q).symm)
    exact (Category.comp_id _).symm
  have h := (modulePullbackChartFMap B S hS f M).naturality
    (baseChangeChartDiagram B S hS f hf Q) (baseChangeChartDiagramOfHom B S hS f hf v) v (𝟙 Q) hc m
  have hm : M.val.map (𝟙 Q).op m = m := val_map_id_apply B S hS M Q m
  exact (modulePullbackChartFMap_app B S hS f M (baseChangeChartDiagramOfHom B S hS f hf v)
      m).symm.trans
    ((congrArg ((modulePullbackChartFMap B S hS f M).app
      (baseChangeChartDiagramOfHom B S hS f hf v)) hm).symm.trans
      (h.trans (congrArg (((modulePullback B S hS f).obj M).val.map v.op)
        (modulePullbackChartFMap_app B S hS f M (baseChangeChartDiagram B S hS f hf Q) m))))

/-- A ring map sending `I` into `K` sends `Iⁿ` into `Kⁿ`. -/
private theorem map_mem_pow_of_forall_mem {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    {I : Ideal R} {K : Ideal S} (h : ∀ a ∈ I, g a ∈ K) (n : ℕ) {r : R} (hr : r ∈ I ^ n) :
    g r ∈ K ^ n :=
  Ideal.le_comap_pow g n (Ideal.pow_right_mono (fun a ha => h a ha) n hr)

/-- The pullback `f♯` of a section of `𝓙ⁿ` lies in `(f⁻¹𝓙)ⁿ` over the base-change chart. -/
theorem C1573.chartIdealPullbackHom_mem_pow (n : ℕ) (V : SmallEtale B S hS Y.1)
    {r : chartRing B S hS Y.1 Y.2 V} (hr : r ∈ chartIdeal B S hS Y J V ^ n) :
    chartIdealPullbackHom B S hS f hf V r ∈
      chartIdeal B S hS X (inverseImageIdeal B S hS f hf J)
        ((smallBaseChange B S hS f hf).obj V) ^ n := by
  exact map_mem_pow_of_forall_mem _ (fun a ha =>
    chartIdealPullbackHom_mem_pullbackIdealSubsheaf B S hS f hf J V ha) n hr

/-- **Pullback of modules is compatible with ideal-power multiples.**  For a representable
morphism `f : X ⟶ Y`, a sheaf of ideals `𝓙 ⊆ 𝒪_Y` cartesian on affine charts and a
quasi-coherent `𝒪_Y`-module `M`, a morphism `φ : f^*M ⟶ N` kills the image of `f^*(𝓙ⁿM)` exactly
when it kills `(f⁻¹𝓙)ⁿ f^*M`. -/
theorem C1573.modulePullback_idealPowerMultiple_ι_comp_eq_zero_iff
    (hJ : IsCartesianOnAffineCharts (hF := Y.2) J.toSheafOfModules) (n : ℕ)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (hM : M.IsQuasicoherentOnSite)
    {N : Modules.{u, u} B S hS X.1 X.2} (φ : (modulePullback B S hS f).obj M ⟶ N) :
    (modulePullback B S hS f).map (idealPowerMultiple B S hS Y.1 Y.2 J n M).ι ≫ φ = 0 ↔
      (idealPowerMultiple B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) n
        ((modulePullback B S hS f).obj M)).ι ≫ φ = 0 := by
  rw [modulePullback_map_idealPowerMultiple_ι_comp_eq_zero_iff B S hS f hf J n M φ,
    idealPowerMultiple_ι_comp_eq_zero_iff]
  constructor
  · intro C
    have haff : ∀ (T : SmallEtale B S hS X.1), IsAffine (chartScheme T) →
        ∀ (Q : SmallEtale B S hS Y.1), IsAffine (chartScheme Q) →
        ∀ (v : T ⟶ (smallBaseChange B S hS f hf).obj Q) (y : chartRing B S hS X.1 X.2 T),
          y ∈ chartIdeal B S hS X (inverseImageIdeal B S hS f hf J) T ^ n →
          ∀ s : ((modulePullback B S hS f).obj M).val.obj (op T),
            φ.val.app (op T) (y • s) = 0 := by
      intro T hT Q hQ v y hy s
      have hI := pullbackIdealSubsheaf_obj_of_isAffine B S hS f hf J hJ Q hQ T v hT
      let g : chartRing B S hS Y.1 Y.2 Q →+* chartRing B S hS X.1 X.2 T :=
        (chartSectionsRestrict B S hS X v).comp (chartIdealPullbackHom B S hS f hf Q)
      have hy' : y ∈ Ideal.map g (chartIdeal B S hS Y J Q ^ n) := by
        have e : chartIdeal B S hS X (inverseImageIdeal B S hS f hf J) T =
            Ideal.map g (chartIdeal B S hS Y J Q) := hI.trans (Ideal.map_map _ _)
        rw [Ideal.map_pow, ← e]
        exact hy
      have hgen : ∀ r ∈ chartIdeal B S hS Y J Q ^ n,
          ∀ s : ((modulePullback B S hS f).obj M).val.obj (op T),
            φ.val.app (op T) (g r • s) = 0 := by
        intro r hr s
        let d := baseChangeChartDiagramOfHom B S hS f hf v
        have hnat := modulePullbackChartSection_baseChangeChartDiagramOfHom B S hS f hf M v
        have hcore : ∀ (m : M.val.obj (op Q))
            (z : ((modulePullback B S hS f).obj M).val.obj (op T)),
            z = ((modulePullback B S hS f).obj M).val.map v.op
              (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf Q) m) →
            φ.val.app (op T) (g r • z) = 0 := by
          intro m z hz
          have e2 : ((modulePullback B S hS f).obj M).val.map v.op
              (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf Q)
                (r • m)) = g r • z :=
            (congrArg (((modulePullback B S hS f).obj M).val.map v.op)
              (modulePullbackChartSection_smul B S hS f M (baseChangeChartDiagram B S hS f hf Q)
                r m)).trans
              ((((modulePullback B S hS f).obj M).val.map_smul v.op _ _).trans
                (congrArg (fun w : ((modulePullback B S hS f).obj M).val.obj (op T) => g r • w)
                  hz.symm))
          refine (congrArg (φ.val.app (op T)) e2.symm).trans ?_
          refine (PresheafOfModules.naturality_apply φ.val v.op _).trans ?_
          exact (congrArg (N.val.map v.op) (C Q r hr m)).trans (map_zero _)
        let := chartDiagramAlgebra B S hS f d
        obtain ⟨t, rfl⟩ :=
          (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS f
            M hM d hT hQ).2 s
        induction t using TensorProduct.induction_on with
        | zero =>
          exact (congrArg (fun w : ((modulePullback B S hS f).obj M).val.obj (op T) =>
            φ.val.app (op T) (g r • w)) (map_zero _)).trans
            ((congrArg (φ.val.app (op T)) (smul_zero (g r))).trans (map_zero _))
        | tmul a₀ m =>
          let a : chartRing B S hS X.1 X.2 T := a₀
          have e : ∀ z : ((modulePullback B S hS f).obj M).val.obj (op T),
              z = ((modulePullback B S hS f).obj M).val.map v.op
                (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf Q) m) →
              modulePullbackChartBaseChange B S hS f M d (a₀ ⊗ₜ m) = a • z := fun z hz =>
            (modulePullbackChartBaseChange_tmul B S hS f M d a₀ m).trans
              (congrArg (fun w : ((modulePullback B S hS f).obj M).val.obj (op T) => a • w)
                ((hnat m).trans hz.symm))
          refine (congrArg (fun w : ((modulePullback B S hS f).obj M).val.obj (op T) =>
            φ.val.app (op T) (g r • w)) (e _ rfl)).trans ?_
          refine (congrArg (φ.val.app (op T)) (smul_comm (g r) a _)).trans ?_
          refine ((φ.val.app (op T)).hom.map_smul a _).trans ?_
          exact (congrArg (a • ·) (hcore m _ rfl)).trans (smul_zero a)
        | add t₁ t₂ h₁ h₂ =>
          refine (congrArg (fun w : ((modulePullback B S hS f).obj M).val.obj (op T) =>
            φ.val.app (op T) (g r • w)) (map_add _ t₁ t₂)).trans ?_
          refine (congrArg (φ.val.app (op T)) (smul_add (g r) _ _)).trans ?_
          exact ((φ.val.app (op T)).hom.map_add _ _).trans ((congrArg₂ (· + ·) h₁ h₂).trans
            (add_zero 0))
      revert s
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hy'
      · rintro _ ⟨r, hr, rfl⟩ s
        exact hgen r hr s
      · intro s
        rw [zero_smul, map_zero]
      · intro a b _ _ ha hb s
        rw [add_smul, map_add, ha, hb, add_zero]
      · intro c a _ ha s
        rw [smul_eq_mul, mul_smul, map_smul, ha, smul_zero]
    intro T y hy s
    have hmem : y • s ∈ (SheafOfModules.Submodule.ker φ).obj (op T) := by
      refine (SheafOfModules.Submodule.ker φ).isSheaf (y • s) ?_
      refine mem_topology_of_affine_over_smallBaseChange B S hS f hf T _
        fun {T₁} g hT₁ Q hQ v => ?_
      have hρ : (smallEtaleRingSheaf B S hS X.1 X.2).obj.map g.op y ∈
          chartIdeal B S hS X (inverseImageIdeal B S hS f hf J) T₁ ^ n := by
        exact map_mem_pow_of_forall_mem
          ((smallEtaleRingSheaf B S hS X.1 X.2).obj.map g.op).hom
          (fun a ha => (inverseImageIdeal B S hS f hf J).map g.op ha) n hy
      refine (SheafOfModules.Submodule.mem_ker φ _ _).2 ?_
      exact (congrArg (φ.val.app (op T₁))
        (((modulePullback B S hS f).obj M).val.map_smul g.op y s)).trans
        (haff T₁ hT₁ Q hQ v _ hρ _)
    exact hmem
  · intro H V r hr m
    exact (congrArg (φ.val.app (op (baseChangeChartDiagram B S hS f hf V).U))
      (modulePullbackChartSection_smul B S hS f M (baseChangeChartDiagram B S hS f hf V) r m)).trans
      (H _ _ (chartIdealPullbackHom_mem_pow B S hS f hf J n V hr) _)

/-- **The termwise pullback of a coherent adic system along a representable morphism is a
coherent adic system** along the inverse-image ideal `f⁻¹𝓙 · 𝒪_X`, for a quasi-coherent sheaf of
ideals `𝓙` and a locally Noetherian source. -/
theorem C1573.isCoherentAdicSystem_modulePullback_of_representable
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hJ : J.toSheafOfModules.IsQuasicoherentOnSite)
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS Y.1 Y.2} (hE : IsCoherentAdicSystem B S hS Y.1 Y.2 J E) :
    IsCoherentAdicSystem B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J)
      (E ⋙ modulePullback B S hS f) := by
  have := preservesZeroMorphisms_modulePullback B S hS f
  have := preservesFiniteColimits_modulePullback B S hS f
  have hJc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hJ
  have hw : ∀ (n k : ℕ) {N : Modules.{u, u} B S hS X.1 X.2}
      (φ : (modulePullback B S hS f).obj (E.obj (op k)) ⟶ N),
      (modulePullback B S hS f).map (idealPowerMultiple B S hS Y.1 Y.2 J n (E.obj (op k))).ι ≫
          φ = 0 ↔
        (idealPowerMultiple B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) n
          ((modulePullback B S hS f).obj (E.obj (op k)))).ι ≫ φ = 0 := fun n k _ φ =>
    modulePullback_idealPowerMultiple_ι_comp_eq_zero_iff B S hS f hf J hJc n _
      (hE.1 k).toIsQuasicoherentOnSite φ
  refine ⟨fun n => isCoherent_modulePullback B S hS f _ (hE.1 n), fun n => ?_, fun n => ?_⟩
  · show idealPowerMultiple B S hS X.1 X.2 (inverseImageIdeal B S hS f hf J) (n + 1)
      ((modulePullback B S hS f).obj (E.obj (op n))) = ⊥
    refine (submodule_ι_eq_zero_iff B S hS X.1 X.2 _).mp ?_
    have hp := (submodule_ι_eq_zero_iff B S hS Y.1 Y.2 _).mpr (hE.2.1 n)
    have h := (hw (n + 1) n (𝟙 _)).mp
      (by rw [hp, Category.comp_id, Functor.map_zero])
    exact (Category.comp_id _).symm.trans h
  · obtain ⟨q, hq⟩ := exists_functor_idealPowerQuotient_iso B S hS (modulePullback B S hS f) J
      (inverseImageIdeal B S hS f hf J) (n + 1) (E.obj (op (n + 1))) (hw (n + 1) (n + 1))
    obtain ⟨ei, hei⟩ := hE.2.2 n
    refine ⟨q.symm ≪≫ (modulePullback B S hS f).mapIso ei, ?_⟩
    show cokernel.π _ ≫ (q.inv ≫ (modulePullback B S hS f).map ei.hom) = _
    refine Eq.trans (congrArg (fun τ => τ ≫ (q.inv ≫ (modulePullback B S hS f).map ei.hom))
      hq.symm) ?_
    refine (Category.assoc _ q.hom _).trans ?_
    refine (congrArg (fun τ => (modulePullback B S hS f).map (cokernel.π (idealPowerMultiple
      B S hS Y.1 Y.2 J (n + 1) (E.obj (op (n + 1)))).ι) ≫ τ) (Iso.hom_inv_id_assoc q _)).trans ?_
    exact ((modulePullback B S hS f).map_comp _ _).symm.trans
      (congrArg (modulePullback B S hS f).map hei)

end AlgebraicGeometry.Space

end
