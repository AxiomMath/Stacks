module

public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.RestrictUnit
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections

/-!
# Base change of the restriction `M ⟶ i_* i^* M` along an arbitrary open immersion

`StacksFrontier/AlgebraicGeometry/ClosedPushforward/RestrictUnit.lean` compares the unit of
`i^* ⊣ i_*`, read over the opens of an open `V` of `X`, with the unit of the base change
`i ∣_ V : i ⁻¹ᵁ V ⟶ V`. That is the comparison for the *inclusion of an open*.

A chart of a relative `Proj` is not the inclusion of an open: it is an open immersion
`c : Y ⟶ Proj_S(𝒜)` out of an abstract scheme, the absolute `Proj` of the section ring over an
affine open of the base, and the fibre of `i` over it is `pullback.snd i c`. This file carries
the comparison across, for an arbitrary morphism `i : Z ⟶ X` and an arbitrary open immersion
`c : Y ⟶ X` — the same proof, with `(i ⁻¹ᵁ V).ι` replaced by `pullback.fst i c`, `V.ι` by `c`
and `i ∣_ V` by `pullback.snd i c`, the commutativity `morphismRestrict_ι` by
`CategoryTheory.Limits.pullback.condition` and the range `(i ⁻¹ᵁ V).ι.opensRange = i ⁻¹ᵁ V` by
`AlgebraicGeometry.Scheme.Hom.opensRange_pullbackFst`.

## Main results

* `Stacks.AlgebraicGeometry.ChartUnit.unit_chartRestrictIso`: **the comparison, as an equality of
  morphisms of `𝒪_X`-modules.**
* `Stacks.AlgebraicGeometry.ChartUnit.app_unit_eq_zero_iff`: a local section of `M` over an open
  `W` inside the range of `c` restricts to zero on `Z` if and only if its avatar over `c`
  restricts to zero on `pullback i c`.
* `Stacks.AlgebraicGeometry.ChartUnit.pullbackGlobalSections_restrict_eq_zero_iff`: **the form the
  chart comparison of Tag 0801 consumes.** A global section of the restriction of `M` to the
  chart — that is, a section of `M` over the range of `c` — pulls back to zero along
  `pullback.snd i c` exactly when it restricts to zero on `Z`.

## Implementation notes

The two adjunctions below have the *same* right adjoint `(pullback.fst i c ≫ i)_*`, and the
comparison of their left adjoints is `CategoryTheory.Adjunction.leftAdjointUniq`, so the
comparison of their units is `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` and costs
nothing. All the work is in reading it on sections, and the two frictions the sibling file
records apply verbatim: a composite of maps on sections written out by hand is not type-correct
at `instance` transparency, so each decomposition is reached once as a named equation and used
only through `CategoryTheory.ConcreteCategory.congr_hom` and
`CategoryTheory.ConcreteCategory.comp_apply` as terms; and an `IsIso` hypothesis in the local
context is not found by instance synthesis at these spellings, so everything goes through
`Stacks.AlgebraicGeometry.RestrictUnit.apply_eq_zero_iff_of_isIso`.

`AlgebraicGeometry.pullbackGlobalSections` is the unit on global sections followed by the
restriction along `f ⁻¹ᵁ ⊤ = ⊤`, and that restriction is invertible, so the two statements about
vanishing agree. The index `c ⁻¹ᵁ (c ''ᵁ ⊤)` that the adjunction produces is moved to `⊤` by the
naturality of the unit together with the invertibility of a restriction map between two opens
that are equal.

No `@[stacks]` attribute is attached: this is a base-change compatibility of an adjunction unit,
not a numbered result of the Stacks project.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ChartUnit

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (c : Y ⟶ X) [IsOpenImmersion c]

/-! ### The two adjunctions -/

/-- The adjunction exhibiting `pullback i ⋙ restrictFunctor (pullback.fst i c)` as a left adjoint
of the direct image along `pullback.fst i c ≫ i`. -/
def pullbackChartAdjunction :
    Scheme.Modules.pullback i ⋙ Scheme.Modules.restrictFunctor (pullback.fst i c) ⊣
      Scheme.Modules.pushforward (pullback.fst i c ≫ i) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
      (Scheme.Modules.restrictAdjunction (pullback.fst i c))).ofNatIsoRight
    (Scheme.Modules.pushforwardComp (pullback.fst i c) i)

/-- The adjunction exhibiting `restrictFunctor c ⋙ pullback (pullback.snd i c)` as a left adjoint
of the direct image along `pullback.snd i c ≫ c`. -/
def chartPullbackAdjunction :
    Scheme.Modules.restrictFunctor c ⋙ Scheme.Modules.pullback (pullback.snd i c) ⊣
      Scheme.Modules.pushforward (pullback.snd i c ≫ c) :=
  ((Scheme.Modules.restrictAdjunction c).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c))).ofNatIsoRight
    (Scheme.Modules.pushforwardComp (pullback.snd i c) c)

/-- Restriction to the fibre over a chart commutes with the inverse image: the restriction to
`pullback i c` of `i^* M` is the inverse image along `pullback.snd i c` of the restriction of `M`
to the chart. -/
def chartRestrictIso :
    Scheme.Modules.pullback i ⋙ Scheme.Modules.restrictFunctor (pullback.fst i c) ≅
      Scheme.Modules.restrictFunctor c ⋙ Scheme.Modules.pullback (pullback.snd i c) :=
  (pullbackChartAdjunction i c).leftAdjointUniq
    ((chartPullbackAdjunction i c).ofNatIsoRight
      (Scheme.Modules.pushforwardCongr (pullback.condition (f := i) (g := c)).symm))

/-- **The unit `M ⟶ i_* i^* M`, read over the opens inside the range of a chart, is the unit of
the base change along the chart.** The two adjunctions have the same right adjoint and
`chartRestrictIso` is the comparison of their left adjoints, so this is
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`. -/
theorem unit_chartRestrictIso (M : X.Modules) :
    (pullbackChartAdjunction i c).unit.app M ≫
        (Scheme.Modules.pushforward (pullback.fst i c ≫ i)).map
          ((chartRestrictIso i c).hom.app M) =
      ((chartPullbackAdjunction i c).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr
          (pullback.condition (f := i) (g := c)).symm)).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

/-! ### The two units on sections -/

/-- The unit of `pullbackChartAdjunction` on sections: the unit of `i^* ⊣ i_*`, the unit of the
restriction adjunction at `pullback.fst i c`, and the composition law for direct images. -/
theorem pullbackChartAdjunction_unit_app_app (M : X.Modules) (W : X.Opens) :
    ((pullbackChartAdjunction i c).unit.app M).app W =
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W ≫
        ((Scheme.Modules.restrictAdjunction (pullback.fst i c)).unit.app
          ((Scheme.Modules.pullback i).obj M)).app (i ⁻¹ᵁ W) ≫
        ((Scheme.Modules.pushforwardComp (pullback.fst i c) i).hom.app
          ((Scheme.Modules.restrictFunctor (pullback.fst i c)).obj
            ((Scheme.Modules.pullback i).obj M))).app W := by
  rw [pullbackChartAdjunction, Adjunction.ofNatIsoRight_unit]
  simp only [Adjunction.comp_unit_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app, Functor.comp_obj,
    Category.assoc]
  rfl

/-- The unit of `chartPullbackAdjunction`, corrected by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, on sections: restriction of the section
along the chart, the unit of `(pullback.snd i c)^* ⊣ (pullback.snd i c)_*`, and a transport along
an equality of morphisms. -/
theorem chartPullbackAdjunction_unit_app_app (M : X.Modules) (W : X.Opens) :
    (((chartPullbackAdjunction i c).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr
          (pullback.condition (f := i) (g := c)).symm)).unit.app M).app W =
      ((Scheme.Modules.restrictAdjunction c).unit.app M).app W ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          ((Scheme.Modules.restrictFunctor c).obj M)).app (c ⁻¹ᵁ W) ≫
        ((Scheme.Modules.pushforwardCongr
            (pullback.condition (f := i) (g := c)).symm).hom.app
          ((Scheme.Modules.pullback (pullback.snd i c)).obj
            ((Scheme.Modules.restrictFunctor c).obj M))).app W := by
  rw [chartPullbackAdjunction, Adjunction.ofNatIsoRight_unit, Adjunction.ofNatIsoRight_unit]
  simp [Adjunction.comp_unit_app]

/-! ### The comparison on sections -/

/-- A local section is killed by the unit of `pullbackChartAdjunction` over an open inside the
range of the chart exactly when it is killed by the unit of `i^* ⊣ i_*`. -/
theorem app_pullbackChartAdjunction_unit_eq_zero_iff (M : X.Modules) {W : X.Opens}
    (hW : W ≤ c.opensRange) (a : Γ(M, W)) :
    ((pullbackChartAdjunction i c).unit.app M).app W a = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W a = 0 := by
  have hη : IsIso (((Scheme.Modules.restrictAdjunction (pullback.fst i c)).unit.app
      ((Scheme.Modules.pullback i).obj M)).app (i ⁻¹ᵁ W)) :=
    RestrictUnit.isIso_restrictAdjunction_unit_app_app (pullback.fst i c) _
      (by rw [Scheme.Hom.opensRange_pullbackFst]; exact fun x hx => hW hx)
  have hpc : IsIso (((Scheme.Modules.pushforwardComp (pullback.fst i c) i).hom.app
      ((Scheme.Modules.restrictFunctor (pullback.fst i c)).obj
        ((Scheme.Modules.pullback i).obj M))).app W) :=
    RestrictUnit.isIso_iso_hom_app
      ((Scheme.Modules.pushforwardComp (pullback.fst i c) i).app _) W
  have hc := ((ConcreteCategory.congr_hom
      (pullbackChartAdjunction_unit_app_app i c M W) a).trans
    (ConcreteCategory.comp_apply _ _ a)).trans (ConcreteCategory.comp_apply _ _ _)
  rw [hc]
  exact (RestrictUnit.apply_eq_zero_iff_of_isIso _ hpc _).trans
    (RestrictUnit.apply_eq_zero_iff_of_isIso _ hη _)

/-- A local section is killed by the corrected unit of `chartPullbackAdjunction` exactly when its
avatar over the chart is killed by the unit of
`(pullback.snd i c)^* ⊣ (pullback.snd i c)_*`. -/
theorem app_chartPullbackAdjunction_unit_eq_zero_iff (M : X.Modules) (W : X.Opens)
    (a : Γ(M, W)) :
    (((chartPullbackAdjunction i c).ofNatIsoRight
        (Scheme.Modules.pushforwardCongr
          (pullback.condition (f := i) (g := c)).symm)).unit.app M).app W a = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          ((Scheme.Modules.restrictFunctor c).obj M)).app (c ⁻¹ᵁ W)
        (((Scheme.Modules.restrictAdjunction c).unit.app M).app W a) = 0 := by
  have hτ : IsIso (((Scheme.Modules.pushforwardCongr
      (pullback.condition (f := i) (g := c)).symm).hom.app
      ((Scheme.Modules.pullback (pullback.snd i c)).obj
        ((Scheme.Modules.restrictFunctor c).obj M))).app W) :=
    RestrictUnit.isIso_iso_hom_app
      ((Scheme.Modules.pushforwardCongr
        (pullback.condition (f := i) (g := c)).symm).app _) W
  have hc := ((ConcreteCategory.congr_hom
      (chartPullbackAdjunction_unit_app_app i c M W) a).trans
    (ConcreteCategory.comp_apply _ _ a)).trans (ConcreteCategory.comp_apply _ _ _)
  rw [hc]
  exact RestrictUnit.apply_eq_zero_iff_of_isIso _ hτ _

/-- Postcomposing with the direct image of `chartRestrictIso` does not change which local
sections are killed. -/
theorem app_comp_chartRestrictIso_eq_zero_iff (M : X.Modules) (W : X.Opens) (a : Γ(M, W)) :
    ((pullbackChartAdjunction i c).unit.app M ≫
          (Scheme.Modules.pushforward (pullback.fst i c ≫ i)).map
            ((chartRestrictIso i c).hom.app M)).app W a = 0 ↔
      ((pullbackChartAdjunction i c).unit.app M).app W a = 0 := by
  have hθ : IsIso (((Scheme.Modules.pushforward (pullback.fst i c ≫ i)).map
      ((chartRestrictIso i c).hom.app M)).app W) :=
    RestrictUnit.isIso_iso_hom_app
      ((Scheme.Modules.pushforward (pullback.fst i c ≫ i)).mapIso
        ((chartRestrictIso i c).app M)) W
  have hc := (ConcreteCategory.congr_hom (Scheme.Modules.Hom.comp_app
      ((pullbackChartAdjunction i c).unit.app M)
      ((Scheme.Modules.pushforward (pullback.fst i c ≫ i)).map
        ((chartRestrictIso i c).hom.app M)) (U := W)) a).trans
    (ConcreteCategory.comp_apply _ _ a)
  rw [hc]
  exact RestrictUnit.apply_eq_zero_iff_of_isIso _ hθ _

/-- **The vanishing comparison: a local section of `M` over an open inside the range of the chart
restricts to zero on `Z` exactly when its avatar over the chart restricts to zero on
`pullback i c`.** -/
theorem app_unit_eq_zero_iff (M : X.Modules) {W : X.Opens} (hW : W ≤ c.opensRange)
    (a : Γ(M, W)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          ((Scheme.Modules.restrictFunctor c).obj M)).app (c ⁻¹ᵁ W)
        (((Scheme.Modules.restrictAdjunction c).unit.app M).app W a) = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app W a = 0 := by
  rw [← app_chartPullbackAdjunction_unit_eq_zero_iff i c M W a,
    ← unit_chartRestrictIso i c M, app_comp_chartRestrictIso_eq_zero_iff i c M W a,
    app_pullbackChartAdjunction_unit_eq_zero_iff i c M hW a]

/-! ### The form the chart comparison consumes -/

/-- Pulling back a global section vanishes exactly when the adjunction unit kills it: the
restriction along `f ⁻¹ᵁ ⊤ = ⊤` that `AlgebraicGeometry.pullbackGlobalSections` composes with is
invertible. -/
theorem pullbackGlobalSections_eq_zero_iff {P T : Scheme.{u}} (p : P ⟶ T) (F : T.Modules)
    (s : Γ(F, ⊤)) :
    pullbackGlobalSections p F s = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app ⊤ s = 0 := by
  have e : (⊤ : P.Opens) = p ⁻¹ᵁ ⊤ := by simp
  have hdef : pullbackGlobalSections p F =
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app F).app ⊤ ≫
        ((Scheme.Modules.pullback p).obj F).presheaf.map (eqToHom e).op := rfl
  have hiso : IsIso (((Scheme.Modules.pullback p).obj F).presheaf.map (eqToHom e).op) :=
    RestrictUnit.isIso_presheaf_map_of_eq _ _ (congrArg op e.symm)
  rw [(ConcreteCategory.congr_hom hdef s).trans (ConcreteCategory.comp_apply _ _ s)]
  exact RestrictUnit.apply_eq_zero_iff_of_isIso _ hiso _

/-- The unit of `(pullback.snd i c)^* ⊣ (pullback.snd i c)_*` kills a global section of
`M.restrict c` exactly when it kills the section's avatar over `c ⁻¹ᵁ (c ''ᵁ ⊤)`, that open being
the whole space. This is the naturality of the unit, the restriction map between the two equal
opens being invertible. -/
private theorem app_unit_top_eq_zero_iff (M : X.Modules)
    (hle : c ⁻¹ᵁ (c ''ᵁ (⊤ : Y.Opens)) ≤ ⊤) (a : Γ(M, c ''ᵁ ⊤)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          (Scheme.Modules.restrict M c)).app (c ⁻¹ᵁ (c ''ᵁ (⊤ : Y.Opens)))
        (((Scheme.Modules.restrictAdjunction c).unit.app M).app (c ''ᵁ (⊤ : Y.Opens)) a) = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          (Scheme.Modules.restrict M c)).app ⊤ a = 0 := by
  have hnat := ConcreteCategory.congr_hom
      (((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
        (Scheme.Modules.restrict M c)).mapPresheaf.naturality (homOfLE hle).op) a
  have hstep := (ConcreteCategory.comp_apply _ _ a).symm.trans
    (hnat.trans (ConcreteCategory.comp_apply _ _ a))
  have hstep2 : ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          (Scheme.Modules.restrict M c)).app (c ⁻¹ᵁ (c ''ᵁ (⊤ : Y.Opens)))
        (((Scheme.Modules.restrictAdjunction c).unit.app M).app (c ''ᵁ (⊤ : Y.Opens)) a) =
      ((Scheme.Modules.pullback (pullback.snd i c) ⋙
            Scheme.Modules.pushforward (pullback.snd i c)).obj
          (Scheme.Modules.restrict M c)).presheaf.map (homOfLE hle).op
        (((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd i c)).unit.app
          (Scheme.Modules.restrict M c)).app ⊤ a) := hstep
  rw [hstep2]
  exact RestrictUnit.apply_eq_zero_iff_of_isIso _
    (RestrictUnit.isIso_presheaf_map_of_eq _ _ (congrArg op (c.preimage_image_eq ⊤).symm)) _

/-- **The chart comparison on global sections.** A section of `M` over the range of the chart —
equivalently, a global section of the restriction of `M` to the chart — pulls back to zero along
`pullback.snd i c` exactly when it restricts to zero on `Z`.

This is `Stacks.AlgebraicGeometry.ChartUnit.app_unit_eq_zero_iff` at the open `c ''ᵁ ⊤`, with the
index `c ⁻¹ᵁ (c ''ᵁ ⊤)` that the adjunction produces moved to `⊤`. -/
theorem pullbackGlobalSections_restrict_eq_zero_iff (M : X.Modules) (a : Γ(M, c ''ᵁ ⊤)) :
    pullbackGlobalSections (pullback.snd i c) (Scheme.Modules.restrict M c) a = 0 ↔
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app (c ''ᵁ ⊤) a = 0 := by
  have hW : c ''ᵁ (⊤ : Y.Opens) ≤ c.opensRange := by
    rw [Scheme.Hom.image_top_eq_opensRange]
  exact (pullbackGlobalSections_eq_zero_iff (pullback.snd i c)
      (Scheme.Modules.restrict M c) a).trans
    ((app_unit_top_eq_zero_iff i c M le_top a).symm.trans (app_unit_eq_zero_iff i c M hW a))

end Stacks.AlgebraicGeometry.ChartUnit

end
