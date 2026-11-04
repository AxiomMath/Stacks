module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramSieveRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicFunctionsLocalUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionNumerator
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionRegularFreeGenerator
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartGeneratorMultiple

/-!
# The pullback of a regular meromorphic section is regular

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B` for
which pullbacks of meromorphic functions are defined, and let `L` be an invertible `𝒪_Y`-module.
If `s` is a regular meromorphic section of `L`, then its pullback `f^*s` is a regular meromorphic
section of `f^*L`.

## Main definitions

* `AlgebraicGeometry.Space.unitPresentationSieve`: the sieve of charts over which a meromorphic
  section is a unit multiple of a free generator.

## Main results

* `AlgebraicGeometry.Space.unitPresentationSieve_mem`: for a regular meromorphic section of an
  invertible module, `AlgebraicGeometry.Space.unitPresentationSieve` is a covering sieve of every
  chart.
* `AlgebraicGeometry.Space.isRegularMeromorphicSection_pullbackMeromorphicSection`: the pullback
  of a regular meromorphic section of an invertible module is regular.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0ENB](https://stacks.math.columbia.edu/tag/0ENB)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] chartMeromorphicAlgebra
attribute [local instance] meromorphicSectionModuleRingedSiteModule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The charts carrying a unit presentation -/

/-- A family of sections compatible with restriction stays compatible after precomposition with a
morphism `p`. -/
private theorem map_family_comp_compat {Y : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Y.1 Y.2) {V₀ W : SmallEtale B S hS Y.1}
    (e : (W' : SmallEtale B S hS Y.1) → (W' ⟶ V₀) → L.val.obj (op W'))
    (hecompat : ∀ (W₁ W₂ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ V₀) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k₁) = e W₂ (g ≫ k₁))
    (p : W ⟶ V₀) (W₁ W₂ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ W) (g : W₂ ⟶ W₁) :
    (L.val.map g.op).hom (e W₁ (k₁ ≫ p)) = e W₂ ((g ≫ k₁) ≫ p) :=
  (hecompat W₁ W₂ (k₁ ≫ p) g).trans (congrArg (e W₂) (Category.assoc g k₁ p).symm)

section Target

variable (Y : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS Y.1 Y.2)
  (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)

/-- The sieve of charts over which a meromorphic section is a unit multiple of a free generator:
a chart `W` of `Y` belongs to this sieve of `V` when there is a family `e` of sections of `L` over
the charts over `W`, compatible with restriction and each generating `L` freely there, and a
unit `c` of `𝒦_Y(W)`, with `s|_W` the image of `c ⊗ e`. -/
def unitPresentationSieve (V : SmallEtale B S hS Y.1) : Sieve V where
  arrows W _ := ∃ (e : (W' : SmallEtale B S hS Y.1) → (W' ⟶ W) → L.val.obj (op W'))
      (c : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.obj (op W)),
    (∀ (W₁ W₂ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ W) (g : W₂ ⟶ W₁),
        (L.val.map g.op).hom (e W₁ k₁) = e W₂ (g ≫ k₁)) ∧
      (∀ (W₁ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ W),
        Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W₁ ↦ r • e W₁ k₁) ∧
      IsUnit c ∧
      s.eval (op W) = toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W
        (c ⊗ₜ[chartRing B S hS Y.1 Y.2 W] e W (𝟙 W) :
          (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W))
  downward_closed := by
    rintro W W₀ k ⟨e, c, hecompat, hebij, hcunit, hpres⟩ j
    refine ⟨fun W' k' ↦ e W' (k' ≫ j),
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map j.op).hom c, ?_, ?_, hcunit.map _, ?_⟩
    · intro W₁ W₂ k₁ g
      exact (hecompat W₁ W₂ (k₁ ≫ j) g).trans
        (congrArg (e W₂) (Category.assoc g k₁ j).symm)
    · exact fun W₁ k₁ ↦ hebij W₁ (k₁ ≫ j)
    · refine Eq.trans (eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS Y.1 Y.2 L s W e
        hecompat c hpres W₀ j) ?_
      refine congrArg (toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W₀) ?_
      exact congrArg (fun z : L.val.obj (op W₀) ↦
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map j.op).hom c) ⊗ₜ[
            chartRing B S hS Y.1 Y.2 W₀] z :
          (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W₀)))
        (congrArg (e W₀) (Category.id_comp j).symm)

/-- Let `s` be a regular meromorphic section of `L`. Over a chart `W` of `Y` which maps to a
member `V₀` of a trivializing cover of `V`, with free generators `e` of `L` over the charts over
`V₀`, and over which `s` is the image of an element `y` of `L ⊗_{𝒪_Y} 𝒦_Y`, the sieve of unit
presentations pulled back to `W` is covering. -/
private theorem unitPresentationSieve_pullback_mem {Y : AlgebraicSpaces B S hS}
    (L : Modules.{u, u} B S hS Y.1 Y.2) (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s)
    (V V₀ : SmallEtale B S hS Y.1) (α : V₀ ⟶ V)
    (e : (W' : SmallEtale B S hS Y.1) → (W' ⟶ V₀) → L.val.obj (op W'))
    (hecompat : ∀ (W₁ W₂ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ V₀) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k₁) = e W₂ (g ≫ k₁))
    (hebij : ∀ (W₁ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ V₀),
      Function.Bijective fun r : chartRing B S hS Y.1 Y.2 W₁ ↦ r • e W₁ k₁)
    (W : SmallEtale B S hS Y.1) (p : W ⟶ V₀)
    (y : (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W))
    (hy : toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W y =
      ((meromorphicSectionSheaf.{u, u} B S hS Y.1 Y.2 L).val.map (p ≫ α).op).hom
        (s.eval (op V))) :
    (unitPresentationSieve B S hS Y L s V).pullback (p ≫ α) ∈
      SmallEtale.topology B S hS Y.1 W := by
  obtain ⟨c, hc⟩ := (bijective_meromorphicSectionModule_tmul B S hS Y.1 Y.2 L W (e W p)
    (hebij W p)).2 y
  have he'compat := map_family_comp_compat B S hS L e hecompat p
  have hsW : s.eval (op W) = toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W
      (c ⊗ₜ[chartRing B S hS Y.1 Y.2 W] e W (𝟙 W ≫ p) :
        (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W)) := by
    refine Eq.trans (PresheafOfModules.sections_property
      (M := (meromorphicSectionSheaf.{u, u} B S hS Y.1 Y.2 L).val) s (p ≫ α).op).symm ?_
    refine Eq.trans hy.symm ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W) ?_
    refine Eq.trans hc.symm ?_
    exact congrArg (fun z : L.val.obj (op W) ↦
      (c ⊗ₜ[chartRing B S hS Y.1 Y.2 W] z :
        (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W)))
      (congrArg (e W) (Category.id_comp p).symm)
  have hrestrict := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS Y.1 Y.2 L s W
    (fun W₁ k₁ ↦ e W₁ (k₁ ≫ p)) he'compat c hsW
  have hinj : ∀ (W₁ : SmallEtale B S hS Y.1) (k₁ : W₁ ⟶ W), Function.Injective
      fun z : (meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.obj (op W₁) ↦
        z * ((meromorphicFunctionSheaf B S hS Y.1 Y.2).obj.map k₁.op).hom c := by
    intro W₁ k₁ z z' hzz'
    have hsmul : ∀ x : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.obj (op W₁),
        x • s.eval (op W₁) = toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W₁
          ((x * (((Stacks.SheafOfModules.Tensor.ringSheaf
            (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map k₁.op).hom c)) ⊗ₜ[
              chartRing B S hS Y.1 Y.2 W₁] e W₁ (k₁ ≫ p) :
            (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W₁)) := by
      intro x
      refine Eq.trans (congrArg
        (fun w : (meromorphicSectionSheaf.{u, u} B S hS Y.1 Y.2 L).val.obj (op W₁) ↦ x • w)
        (hrestrict W₁ k₁)) ?_
      refine Eq.trans (toMeromorphicSectionSheaf_smul B S hS Y.1 Y.2 L W₁ x _).symm ?_
      exact congrArg (toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W₁)
        (meromorphicSectionModule_smul_tmul B S hS Y.1 Y.2 L W₁ _ x _ (e W₁ (k₁ ≫ p)) rfl)
    refine hs W₁ (((hsmul z).trans ?_).trans (hsmul z').symm)
    exact congrArg (fun w : (Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.obj (op W₁) ↦
      toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W₁
        (w ⊗ₜ[chartRing B S hS Y.1 Y.2 W₁] e W₁ (k₁ ≫ p) :
          (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W₁))) hzz'
  obtain ⟨T₁, hT₁, hunit⟩ := exists_sieve_isUnit_of_injective_mul B S hS Y.1 Y.2 W c hinj
  refine (SmallEtale.topology B S hS Y.1).superset_covering ?_ hT₁
  intro W₁ k₁ hk₁
  refine ⟨fun W₂ k₂ ↦ e W₂ (k₂ ≫ k₁ ≫ p),
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map k₁.op).hom c, ?_, ?_, hunit k₁ hk₁, ?_⟩
  · exact map_family_comp_compat B S hS L e hecompat (k₁ ≫ p)
  · exact fun W₂ k₂ ↦ hebij W₂ (k₂ ≫ k₁ ≫ p)
  · refine Eq.trans (hrestrict W₁ k₁)
      (congrArg (toMeromorphicSectionSheaf B S hS Y.1 Y.2 L W₁) ?_)
    exact congrArg (fun z : L.val.obj (op W₁) ↦
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS Y.1 Y.2).O).obj.map k₁.op).hom c) ⊗ₜ[
          chartRing B S hS Y.1 Y.2 W₁] z :
        (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op W₁)))
      (congrArg (e W₁) (Category.id_comp (k₁ ≫ p)).symm)

/-- A regular meromorphic section of an invertible module is locally a unit multiple of a free
generator: `AlgebraicGeometry.Space.unitPresentationSieve` is a covering sieve of every étale
scheme chart of `Y`. -/
theorem unitPresentationSieve_mem
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s)
    (V : SmallEtale B S hS Y.1) :
    unitPresentationSieve B S hS Y L s V ∈ SmallEtale.topology B S hS Y.1 V := by
  obtain ⟨T₀, hT₀, hsheafify⟩ := exists_eval_toMeromorphicSectionSheaf_sieve_mem B S hS Y.1 Y.2 L
    V (s.eval (op V))
  obtain ⟨I, V₀, α, hcov, hgen⟩ :=
    exists_generator_cover_smul_of_isInvertible B S hS Y L hL V
  refine (SmallEtale.topology B S hS Y.1).transitive
    ((SmallEtale.topology B S hS Y.1).intersection_covering hT₀ hcov) _ ?_
  rintro W k ⟨hk₀, W', p, q, ⟨i⟩, rfl⟩
  obtain ⟨e, hecompat, hebij⟩ := hgen i
  obtain ⟨y, hy⟩ := hsheafify (p ≫ α i) hk₀
  exact unitPresentationSieve_pullback_mem B S hS L s hs V (V₀ i) (α i) e hecompat hebij W p y hy

end Target

/-! ### The pullback of a regular meromorphic section -/

variable {X Y : AlgebraicSpaces B S hS}

/-- Let `f : X ⟶ Y` be a morphism of algebraic spaces for which pullbacks of meromorphic
functions are defined, let `L` be an invertible `𝒪_Y`-module and let `s` be a regular meromorphic
section of `L`. Then the pullback `f^*s` is a regular meromorphic section of the invertible
`𝒪_X`-module `f^*L`. -/
@[stacks 0ENC "part (2)"]
theorem isRegularMeromorphicSection_pullbackMeromorphicSection (f : X ⟶ Y)
    (hf : PullbacksMeromorphicSections B S hS f.hom) (L : Modules.{u, u} B S hS Y.1 Y.2)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS Y)
      (structureRingSheaf B S hS Y).property L)
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 L)
    (hs : IsRegularMeromorphicSection.{u, u} B S hS Y.1 Y.2 L s) :
    IsRegularMeromorphicSection.{u, u} B S hS X.1 X.2 ((modulePullback B S hS f).obj L)
      (pullbackMeromorphicSection B S hS f L hf s) := by
  refine isRegularMeromorphicSection_of_chartDiagram B S hS f ((modulePullback B S hS f).obj L)
    (pullbackMeromorphicSection B S hS f L hf s) ?_
  intro d hdU hdV
  obtain ⟨n, d', a, κ, -, -, hκ, -, hcov⟩ :=
    exists_affine_chartDiagram_cover_of_sieve B S hS f d hdU hdV
      (unitPresentationSieve_mem B S hS Y L s hL hs d.V)
  refine injective_smul_eval_of_cover B S hS X.1 X.2 ((modulePullback B S hS f).obj L)
    (pullbackMeromorphicSection B S hS f L hf s) d.U (fun i ↦ (d' i).U) a hcov fun i ↦ ?_
  obtain ⟨e, c, hecompat, hebij, hcunit, hpres⟩ := hκ i
  have hEid : modulePullbackChartSectionRestrict B S hS f L (d' i) (e (d' i).V (𝟙 (d' i).V))
        (𝟙 (d' i).U) =
      (modulePullbackChartFMap B S hS f L).app (d' i) (e (d' i).V (𝟙 (d' i).V)) :=
    CategoryTheory.congr_fun
      (((modulePullback B S hS f).obj L).val.presheaf.map_id (op (d' i).U))
      ((modulePullbackChartFMap B S hS f L).app (d' i) (e (d' i).V (𝟙 (d' i).V)))
  have hvalue : (pullbackMeromorphicSection B S hS f L hf s).eval (op (d' i).U) =
      toMeromorphicSectionSheaf B S hS X.1 X.2 ((modulePullback B S hS f).obj L) (d' i).U
        ((chartMeromorphicPullbackHom B S hS f hf (d' i) c) ⊗ₜ[
            chartRing B S hS X.1 X.2 (d' i).U]
          modulePullbackChartSectionRestrict B S hS f L (d' i) (e (d' i).V (𝟙 (d' i).V))
            (𝟙 (d' i).U) :
          (meromorphicSectionModule B S hS X.1 X.2
            ((modulePullback B S hS f).obj L)).obj (op (d' i).U)) := by
    refine Eq.trans (pullbackMeromorphicSection_eval_chartDiagram B S hS f L hf s (d' i)
      (c ⊗ₜ[chartRing B S hS Y.1 Y.2 (d' i).V] e (d' i).V (𝟙 (d' i).V) :
        (meromorphicSectionModule B S hS Y.1 Y.2 L).obj (op (d' i).V)) hpres) ?_
    refine congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2
      ((modulePullback B S hS f).obj L) (d' i).U) ?_
    refine Eq.trans (chartPullbackMeromorphicSectionsSheaf_tmul B S hS f L hf (d' i) c
      (e (d' i).V (𝟙 (d' i).V))) ?_
    exact congrArg (fun z : ((modulePullback B S hS f).obj L).val.obj (op (d' i).U) ↦
      ((chartMeromorphicPullbackHom B S hS f hf (d' i) c) ⊗ₜ[
          chartRing B S hS X.1 X.2 (d' i).U] z :
        (meromorphicSectionModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj L)).obj (op (d' i).U))) hEid.symm
  have hEcompat : ∀ (W₁ W₂ : SmallEtale B S hS X.1) (k₁ : W₁ ⟶ (d' i).U) (g : W₂ ⟶ W₁),
      (((modulePullback B S hS f).obj L).val.map g.op).hom
          (modulePullbackChartSectionRestrict B S hS f L (d' i) (e (d' i).V (𝟙 (d' i).V)) k₁) =
        modulePullbackChartSectionRestrict B S hS f L (d' i) (e (d' i).V (𝟙 (d' i).V))
          (g ≫ k₁) := fun W₁ W₂ k₁ g ↦
    modulePullbackChartSectionRestrict_map B S hS f L (d' i) (e (d' i).V (𝟙 (d' i).V)) k₁ g
  have hXrestrict := eval_eq_toMeromorphicSectionSheaf_tmul_restrict B S hS X.1 X.2
    ((modulePullback B S hS f).obj L) (pullbackMeromorphicSection B S hS f L hf s) (d' i).U
    (fun W₁ k₁ ↦ modulePullbackChartSectionRestrict B S hS f L (d' i)
      (e (d' i).V (𝟙 (d' i).V)) k₁)
    hEcompat (chartMeromorphicPullbackHom B S hS f hf (d' i) c) hvalue
  obtain ⟨T', hT', hT'bij⟩ := exists_sieve_bijective_smul_modulePullbackChartSection B S hS f L
    hL (d' i) e hecompat hebij
  refine injective_smul_eval_of_sieve B S hS X.1 X.2 ((modulePullback B S hS f).obj L)
    (pullbackMeromorphicSection B S hS f L hf s) (d' i).U T' hT' fun Z ι hι ↦ ?_
  have hpresZ : (pullbackMeromorphicSection B S hS f L hf s).eval (op Z) =
      toMeromorphicSectionSheaf B S hS X.1 X.2 ((modulePullback B S hS f).obj L) Z
        ((((Stacks.SheafOfModules.Tensor.ringSheaf
          (meromorphicRingedSite B S hS X.1 X.2).O).obj.map ι.op).hom
            (chartMeromorphicPullbackHom B S hS f hf (d' i) c)) ⊗ₜ[
              chartRing B S hS X.1 X.2 Z]
          modulePullbackChartSectionRestrict B S hS f L (d' i) (e (d' i).V (𝟙 (d' i).V))
            (𝟙 Z ≫ ι) :
          (meromorphicSectionModule B S hS X.1 X.2
            ((modulePullback B S hS f).obj L)).obj (op Z)) := by
    refine Eq.trans (hXrestrict Z ι) (congrArg (toMeromorphicSectionSheaf B S hS X.1 X.2
      ((modulePullback B S hS f).obj L) Z) ?_)
    exact congrArg (fun z : ((modulePullback B S hS f).obj L).val.obj (op Z) ↦
      ((((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X.1 X.2).O).obj.map ι.op).hom
          (chartMeromorphicPullbackHom B S hS f hf (d' i) c)) ⊗ₜ[
            chartRing B S hS X.1 X.2 Z] z :
        (meromorphicSectionModule B S hS X.1 X.2
          ((modulePullback B S hS f).obj L)).obj (op Z)))
      (congrArg (modulePullbackChartSectionRestrict B S hS f L (d' i)
        (e (d' i).V (𝟙 (d' i).V))) (Category.id_comp ι).symm)
  refine injective_smul_eval_of_tmul_isUnit B S hS X.1 X.2 ((modulePullback B S hS f).obj L)
    (pullbackMeromorphicSection B S hS f L hf s) Z
    (fun W₁ h ↦ modulePullbackChartSectionRestrict B S hS f L (d' i)
      (e (d' i).V (𝟙 (d' i).V)) (h ≫ ι))
    ?_ (fun W₁ k₁ ↦ hT'bij ι hι W₁ k₁) _ _ rfl ?_ hpresZ
  · exact map_family_comp_compat B S hS ((modulePullback B S hS f).obj L) _ hEcompat ι
  · exact (hcunit.map (chartMeromorphicPullbackHom B S hS f hf (d' i))).map
      (((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS X.1 X.2).O).obj.map ι.op).hom)

end AlgebraicGeometry.Space

end
