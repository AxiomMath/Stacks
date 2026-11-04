module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicDirectImageComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartDiagramBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffineSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnitTransport

public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsPushforward

/-!
# The comparison maps of Stacks 08BD on the sections over étale charts

Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a scheme `S`, let
`𝓙 ⊆ 𝒪_Y` be a sheaf of ideals and `𝓘 = f⁻¹𝓙 · 𝒪_X` its inverse image, let `(𝓖_n)` be an inverse
system of `𝒪_Y`-modules, let `𝓕` be a coherent `𝒪_X`-module and let `β : (f^*𝓖_n) ≅ 𝓕^∧`.  The
proof of Stacks 08BD compares the maps

`γ_n : 𝓖_n ⟶ f_*f^*𝓖_n ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)` and `c_n : f_*𝓕/𝓙 ⁿ⁺¹f_*𝓕 ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)`.

This file builds both with the direct image taken as
`AlgebraicGeometry.Space.smallBaseChangeModulePushforward`, whose sections over an étale chart
`V` of `Y` are, on the nose, the sections over the base-changed chart `V ×_Y X`.  In that
reading `γ_n` sends a section `x` of `𝓖_n` over `V` to `β_n` of the chart section of `x`, the
component of the unit of Stacks 03D7 at the chart diagram `V ×_Y X ⟶ V`
(`AlgebraicGeometry.Space.baseChangeChartDiagram`); so every assertion
about `γ` becomes an assertion about sections over charts.

## Main definitions

* `AlgebraicGeometry.Space.directImageChartHom` — the morphism `M ⟶ f_*N` adjoint to a morphism
  `b : f^*M ⟶ N`, built from the chart sections of `M`.
* `AlgebraicGeometry.Space.directImageChartComparison` — the maps `γ_n`.
* `AlgebraicGeometry.Space.directImageCompletionComparison` — the maps `c_n`.

## Main results

* `AlgebraicGeometry.Space.homEquiv_comp_modulePushforwardChartIso` — the adjoint of `b` along
  `f^* ⊣ f_*` of Stacks 03LU, read through the chart comparison
  `AlgebraicGeometry.Space.modulePushforwardChartIso` of the two direct images, *is*
  `AlgebraicGeometry.Space.directImageChartHom b`; so `γ_n` is the map of the source.
* `AlgebraicGeometry.Space.idealPowerMultiple_ι_comp_pushforward_map_π` — `𝓙 ⁿ⁺¹f_*𝓕` dies in
  `f_*(𝓕/𝓘 ⁿ⁺¹𝓕)`, which is what makes `c_n` well defined.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)

/-! ### The chart diagram of a base change -/

/-- `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` with its source and target read as
the categories `AlgebraicGeometry.Space.Modules`, so that their abelian structure is the one
instance search finds. -/
abbrev baseChangeDirectImage : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  smallBaseChangeModulePushforward.{u, u} B S hS f hf

/-! ### The chart-section form of an adjoint map -/

/-- The additive presheaf map underlying `directImageChartHom`. -/
def directImageChartPresheafHom {M : Modules.{u, u} B S hS Y.1 Y.2}
    {N : Modules.{u, u} B S hS X.1 X.2} (b : (modulePullback B S hS f).obj M ⟶ N) :
    M.val.presheaf ⟶ ((baseChangeDirectImage B S hS f hf).obj N).val.presheaf where
  app V := AddCommGrpCat.ofHom
    { toFun x := b.val.app (op ((smallBaseChange B S hS f hf).obj V.unop))
        (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V.unop) x)
      map_zero' := by
        refine (congrArg (b.val.app (op ((smallBaseChange B S hS f hf).obj V.unop)))
          (show modulePullbackChartSection B S hS f M
            (baseChangeChartDiagram B S hS f hf (V.unop : SmallEtale B S hS Y.1)) 0 = 0 from
                ?_)).trans
          (map_zero _)
        have h := modulePullbackChartSection_add B S hS f M
          (baseChangeChartDiagram B S hS f hf (V.unop : SmallEtale B S hS Y.1)) 0 0
        rw [add_zero] at h
        exact left_eq_add.mp h
      map_add' x y :=
        (congrArg (b.val.app (op ((smallBaseChange B S hS f hf).obj V.unop)))
          (modulePullbackChartSection_add B S hS f M
            (baseChangeChartDiagram B S hS f hf (V.unop : SmallEtale B S hS Y.1)) x y)).trans
          (map_add _ _ _) }
  naturality {V W} k := by
    refine AddCommGrpCat.ext fun x => ?_
    have h1 := modulePullbackChartSection_naturality B S hS f M
      (baseChangeChartDiagram B S hS f hf V.unop)
      (baseChangeChartDiagram B S hS f hf W.unop) ((smallBaseChange B S hS f hf).map k.unop)
      k.unop (smallBaseChange_map_snd B S hS f hf k.unop) x
    have h2 := congrArg (fun φ => φ (modulePullbackChartSection B S hS f M
      (baseChangeChartDiagram B S hS f hf V.unop) x)) (congrArg (fun ψ => ψ.hom)
        (b.val.naturality ((smallBaseChange B S hS f hf).map k.unop).op))
    exact (congrArg (b.val.app (op ((smallBaseChange B S hS f hf).obj W.unop))) h1).trans h2

/-- The chart-section form of the adjoint of `b : f^*M ⟶ N`, a morphism `M ⟶ f'_*N` whose
section over a chart `V` sends `x` to `b` of the chart section of `x` over `V ×_Y X`. -/
def directImageChartHom {M : Modules.{u, u} B S hS Y.1 Y.2}
    {N : Modules.{u, u} B S hS X.1 X.2} (b : (modulePullback B S hS f).obj M ⟶ N) :
    M ⟶ (baseChangeDirectImage B S hS f hf).obj N where
  val := PresheafOfModules.homMk (directImageChartPresheafHom B S hS f hf b) fun V r x => by
    have h := modulePullbackChartSection_smul B S hS f M
      (baseChangeChartDiagram B S hS f hf (V.unop : SmallEtale B S hS Y.1)) r x
    dsimp only [baseChangeChartDiagram] at h
    exact (congrArg (b.val.app (op ((smallBaseChange B S hS f hf).obj V.unop))) h).trans
      (map_smul _ _ _)

/-- The section of `directImageChartHom b` over a chart `V` sends `x` to `b` of the chart section
of `x` over `V ×_Y X`. -/
theorem directImageChartHom_val_app {M : Modules.{u, u} B S hS Y.1 Y.2}
    {N : Modules.{u, u} B S hS X.1 X.2} (b : (modulePullback B S hS f).obj M ⟶ N)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    (directImageChartHom B S hS f hf b).val.app (op V) x =
      b.val.app (op ((smallBaseChange B S hS f hf).obj V))
        (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V) x) := rfl

/-- `directImageChartHom` is natural: a commuting square `f^*a ≫ b' = b ≫ c` gives
`a ≫ directImageChartHom b' = directImageChartHom b ≫ f_*c`. -/
theorem directImageChartHom_naturality {M M' : Modules.{u, u} B S hS Y.1 Y.2}
    {N N' : Modules.{u, u} B S hS X.1 X.2} (b : (modulePullback B S hS f).obj M ⟶ N)
    (b' : (modulePullback B S hS f).obj M' ⟶ N') (a : M ⟶ M') (c : N ⟶ N')
    (w : (modulePullback B S hS f).map a ≫ b' = b ≫ c) :
    a ≫ directImageChartHom B S hS f hf b' =
      directImageChartHom B S hS f hf b ≫ (baseChangeDirectImage B S hS f hf).map c := by
  refine Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop (fun V x => ?_)
  have h1 := modulePullbackChartSection_map B S hS f M a (baseChangeChartDiagram B S hS f hf V) x
  have h2 := congrArg (fun φ : (modulePullback B S hS f).obj M ⟶ N' =>
    φ.val.app (op ((smallBaseChange B S hS f hf).obj V))
      (modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V) x)) w
  exact (congrArg (b'.val.app (op ((smallBaseChange B S hS f hf).obj V))) h1.symm).trans h2

/-- The cartesian form of the base-change chart diagram is the comparison of the two base
changes. -/
theorem chartLift_baseChangeChartDiagram (V : SmallEtale B S hS Y.1) :
    chartLift B S hS f (baseChangeChartDiagram B S hS f hf V) =
      (smallBaseChangeComparisonIso B S hS f hf V).hom :=
  (chartLift_unique B S hS f (baseChangeChartDiagram B S hS f hf V) _
    (congrArg (fun q => q.hom) (smallBaseChangeComparisonIso_hom_projection B S hS f hf V))).symm

/-- The index of the base-change chart diagram over `V` is the initial index
`smallBaseChangeIndex`. -/
theorem indexOfChartDiagram_baseChangeChartDiagram (V : SmallEtale B S hS Y.1) :
    indexOfChartDiagram B S hS f (baseChangeChartDiagram B S hS f hf V) =
      smallBaseChangeIndex B S hS f hf V := by
  unfold indexOfChartDiagram smallBaseChangeIndex
  rw [chartLift_baseChangeChartDiagram]
  rfl

/-- The chart projection at the base-change chart diagram is the projection to the initial
index. -/
theorem moduleChartProjection_baseChangeChartDiagram (V : SmallEtale B S hS Y.1)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (z : ((smallEtaleDirectImage B S hS f).obj P).obj.obj (op V)) :
    (moduleChartProjection B S hS f V
        (indexOfChartDiagram B S hS f (baseChangeChartDiagram B S hS f hf V))).app P z =
      chartSetProj B S hS f hf P V z := by
  refine (moduleChartProjection_app B S hS f V _ P z).trans ?_
  have key : ∀ (j j' : StructuredArrow (op (chartBaseChange B S hS f V))
      (comparisonFunctor B S hS X).op) (e : j = j')
      (a : ((comparisonFunctor B S hS X).op.ran.obj P.obj).obj (op (chartBaseChange B S hS f V))),
      HEq ((ranChartCone B S hS X P.obj (chartBaseChange B S hS f V)).π.app j a)
        ((ranChartCone B S hS X P.obj (chartBaseChange B S hS f V)).π.app j' a) := by
    intro j j' e a; subst e; rfl
  exact eq_of_heq (key _ _ (indexOfChartDiagram_baseChangeChartDiagram B S hS f hf V) _)

open Stacks.Sheaves.RingedToposModules in
/-- **The unit of `f^* ⊣ f_*` read through the chart comparison of direct images is the chart
section.** -/
theorem modulePushforwardChartIso_unit (M : Modules.{u, u} B S hS Y.1 Y.2)
    (V : SmallEtale B S hS Y.1) (x : M.val.obj (op V)) :
    ((modulePushforwardChartIso B S hS f hf).hom.app ((modulePullback B S hS f).obj M)).val.app
        (op V) (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x) =
      modulePullbackChartSection B S hS f M (baseChangeChartDiagram B S hS f hf V) x := by
  rw [modulePushforwardChartIso_hom_app_chartSetProj, chartSetProj_modulePullbackAdjunction_unit]
  exact (moduleChartProjection_baseChangeChartDiagram B S hS f hf V _ _).symm

/-- **The adjoint of `b : f^*M ⟶ N` read through the chart comparison is the chart-section
morphism of `b`.** -/
theorem homEquiv_comp_modulePushforwardChartIso {M : Modules.{u, u} B S hS Y.1 Y.2}
    {N : Modules.{u, u} B S hS X.1 X.2} (b : (modulePullback B S hS f).obj M ⟶ N) :
    (modulePullbackAdjunction B S hS f).homEquiv M N b ≫
        (modulePushforwardChartIso B S hS f hf).hom.app N =
      directImageChartHom B S hS f hf b := by
  refine Stacks.ChartUnitTransport.hom_ext_val_app_apply_unop (fun V x => ?_)
  rw [Adjunction.homEquiv_unit]
  have hnat := congrArg (fun φ : (modulePushforward B S hS f).obj ((modulePullback B S hS f).obj
      M) ⟶
      (baseChangeDirectImage B S hS f hf).obj N =>
      φ.val.app (op V) (((modulePullbackAdjunction B S hS f).unit.app M).val.app (op V) x))
    ((modulePushforwardChartIso B S hS f hf).hom.naturality b)
  refine hnat.trans ?_
  exact congrArg (b.val.app (op ((smallBaseChange B S hS f hf).obj V)))
    (modulePushforwardChartIso_unit B S hS f hf M V x)

/-! ### The maps `γ_n` -/

section Gamma

variable (𝓘 : (SheafOfModules.unit.{u} (smallEtaleRingSheaf B S hS X.1 X.2)).Submodule)
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (G : ℕᵒᵖ ⥤ Modules.{u, u} B S hS Y.1 Y.2) (F : CoherentModules.{u, u} B S hS X.1 X.2)
    (β : G ⋙ modulePullback B S hS f ≅ ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj)

/-- **The maps `γ_n : 𝓖_n ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)` of the proof of Stacks 08BD**, with the direct image
read on the base-changed charts: the section of `γ_n` over a chart `V` sends `x` to `β_n` of the
chart section of `x` over `V ×_Y X`.  By `homEquiv_comp_modulePushforwardChartIso` this is the
adjunction map followed by `f_*β_n`. -/
def directImageChartComparison :
    G ⟶ ((completionFunctor B S hS X.1 X.2 𝓘 hI).obj F).obj ⋙
      baseChangeDirectImage B S hS f hf where
  app n := directImageChartHom B S hS f hf (β.hom.app n)
  naturality _ _ g := directImageChartHom_naturality B S hS f hf (β.hom.app _) (β.hom.app _)
    (G.map g) _ (β.hom.naturality g)

/-- The section of `γ_n` over a chart is `β_n` applied to the chart section. -/
theorem directImageChartComparison_app_val_app (n : ℕᵒᵖ) (V : SmallEtale B S hS Y.1)
    (x : (G.obj n).val.obj (op V)) :
    ((directImageChartComparison B S hS f hf 𝓘 hI G F β).app n).val.app (op V) x =
      (β.hom.app n).val.app (op ((smallBaseChange B S hS f hf).obj V))
        (modulePullbackChartSection B S hS f (G.obj n) (baseChangeChartDiagram B S hS f hf V) x) :=
  rfl

end Gamma

/-! ### The maps `c_n` -/

section Comparison

variable (𝓙 : (SheafOfModules.unit.{u}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)

/-- **The direct image of a module annihilated by `(f⁻¹𝓙 𝒪_X) ^ k` is annihilated by `𝓙 ^ k`.**
On the sections over a chart `V` of `Y`, which are the sections over `V ×_Y X`, a section `r` of
`𝓙 ^ k` acts through its pullback, a section of `(f⁻¹𝓙 𝒪_X) ^ k`. -/
theorem isPowAnnihilated_baseChangeDirectImage (k : ℕ)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (hN : IsPowAnnihilated B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf 𝓙) k N) :
    IsPowAnnihilated B S hS Y.1 Y.2 𝓙 k
      ((baseChangeDirectImage B S hS f hf).obj N) := by
  intro V r hr x
  refine hN ((smallBaseChange B S hS f hf).obj V) (chartIdealPullbackHom B S hS f hf V r) ?_ x
  have hle : chartSectionsIdeal B S hS Y 𝓙 V ≤
      (chartSectionsIdeal B S hS X (pullbackIdealSubsheaf B S hS f hf 𝓙)
        ((smallBaseChange B S hS f hf).obj V)).comap (chartIdealPullbackHom B S hS f hf V) :=
    fun a ha => chartIdealPullbackHom_mem_pullbackIdealSubsheaf B S hS f hf 𝓙 V ha
  exact ((pow_le_pow_left' hle k).trans (Ideal.le_comap_pow _ k)) hr

/-- **`𝓙 ^ k f_*𝓕` dies in `f_*(𝓕/(f⁻¹𝓙 𝒪_X) ^ k 𝓕)`.** -/
theorem idealPowerMultiple_ι_comp_pushforward_map_π (k : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) :
    (idealPowerMultiple B S hS Y.1 Y.2 𝓙 k
        ((baseChangeDirectImage B S hS f hf).obj M)).ι ≫
      (baseChangeDirectImage B S hS f hf).map
        (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (idealPowerMultiple B S hS X.1 X.2
          (pullbackIdealSubsheaf B S hS f hf 𝓙) k M).ι) = 0 := by
  refine (idealPowerMultiple_ι_comp_eq_zero_iff B S hS Y.1 Y.2 𝓙 k _).mpr fun V r hr x => ?_
  rw [map_smul]
  exact isPowAnnihilated_baseChangeDirectImage B S hS f hf 𝓙 k _
    (isPowAnnihilated_idealPowerQuotient B S hS X.1 X.2 _ k M) V r hr _

variable [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hJ : 𝓙.toSheafOfModules.IsQuasicoherentOnSite)
    (hI : (pullbackIdealSubsheaf B S hS f hf 𝓙).toSheafOfModules.IsQuasicoherentOnSite)
    (F : CoherentModules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F.obj))

/-- **The maps `c_n : f_*𝓕/𝓙 ⁿ⁺¹f_*𝓕 ⟶ f_*(𝓕/𝓘 ⁿ⁺¹𝓕)`**, the direct image of the projection
of `𝓕` factored through the projection of `f_*𝓕`. -/
def directImageCompletionComparison :
    ((completionFunctor B S hS Y.1 Y.2 𝓙 hJ).obj ⟨_, hF⟩).obj ⟶
      ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf 𝓙) hI).obj F).obj ⋙
        baseChangeDirectImage B S hS f hf where
  app n := cokernel.desc _ ((baseChangeDirectImage B S hS f hf).map
    (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (idealPowerMultiple B S hS X.1 X.2
      (pullbackIdealSubsheaf B S hS f hf 𝓙) (n.unop + 1) F.obj).ι))
    (idealPowerMultiple_ι_comp_pushforward_map_π B S hS f hf 𝓙 (n.unop + 1) F.obj)
  naturality i j a := by
    have hle := Nat.add_le_add_right (leOfHom a.unop) 1
    have h1 := π_comp_idealPowerQuotientMapOfLE B S hS Y.1 Y.2 𝓙 hle
      ((baseChangeDirectImage B S hS f hf).obj F.obj)
    have h2 := π_comp_idealPowerQuotientMapOfLE B S hS X.1 X.2
      (pullbackIdealSubsheaf B S hS f hf 𝓙) hle F.obj
    refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 𝓙 (i.unop + 1)
      ((baseChangeDirectImage B S hS f hf).obj F.obj)).ι)).mp ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) h1).trans ?_
    refine (cokernel.π_desc _ _ _).trans ?_
    refine (congrArg (baseChangeDirectImage B S hS f hf).map h2.symm).trans ?_
    refine ((baseChangeDirectImage B S hS f hf).map_comp _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (· ≫ _) (cokernel.π_desc _ _ _).symm

/-- The projection of `f_*𝓕` followed by `c_n` is the direct image of the projection of `𝓕`. -/
theorem π_comp_directImageCompletionComparison_app (n : ℕ) :
    cokernel.π (idealPowerMultiple B S hS Y.1 Y.2 𝓙 (n + 1)
        ((baseChangeDirectImage B S hS f hf).obj F.obj)).ι ≫
      (directImageCompletionComparison B S hS f hf 𝓙 hJ hI F hF).app (op n) =
    (baseChangeDirectImage B S hS f hf).map
      (cokernel.π (C := Modules.{u, u} B S hS X.1 X.2) (idealPowerMultiple B S hS X.1 X.2
        (pullbackIdealSubsheaf B S hS f hf 𝓙) (n + 1) F.obj).ι) :=
  cokernel.π_desc _ _ _

end Comparison

end AlgebraicGeometry.Space

end
