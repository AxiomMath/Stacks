module

public import StacksFrontier.AlgebraicGeometry.TateMap.BaseChangeChartsPrescribed
public import StacksFrontier.AlgebraicGeometry.TateMap.Glue
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.MorphismSections
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ChartRefinement
public import StacksFrontier.RingTheory.TateMap.ChartBaseChangeShrink

/-!
# Chart base changes of a morphism of Section 0FKB, and glueing along them

Let `b/a : Y'/X' → Y/X` be a morphism of the category of Stacks, Section 0FKB. A *chart* of it is
a quadruple of affine opens `U ⊆ X`, `V ⊆ Y`, `U' ⊆ X'`, `V' ⊆ Y'` compatible with the four maps,
with a chart base change datum from `Γ(U) → Γ(V)` to `Γ(U') → Γ(V')`. The opens `V'` of the charts
form a basis of `Y'`, any two charts have a common refinement by principal opens of all four affine
opens around every point of the overlap, and so a family of linear isomorphisms of the sections of
two `𝒪_{Y'}`-modules over the `V'`, compatible with restriction to principal refinements, glues to
an isomorphism.

## Main definitions

* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.Chart`: the charts.
* `AlgebraicGeometry.TateMap.pullbackSectionsTensorEquiv`: the sections over an affine open of the
  pullback of a quasi-coherent module, as a base change.

## Main results

* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.Chart.nonempty_chartBaseChange_of_basicOpen`:
  principal-open refinements of a chart are charts.
* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.Chart.exists_common_refinement`: common
  refinements of two charts.
* `AlgebraicGeometry.TateMap.OpenBaseChangeSquare.exists_iso_of_chart`: the glueing.

## References

* [Stacks Project, Section 0FKB](https://stacks.math.columbia.edu/tag/0FKB)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.TateMap

open Stacks.TateMap (ChartBaseChange)


/-- The sections over an affine open `V` of the pullback of a quasi-coherent module along a
morphism mapping `V` into an affine open `U`, as the base change `Γ(V) ⊗_{Γ(U)} Γ(F, U)`. -/
def pullbackSectionsTensorEquiv {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    Γ(Y, V.1) ⊗[Γ(X, U.1)] Γ(F, U.1) ≃ₗ[Γ(Y, V.1)]
      Γ((Scheme.Modules.pullback f).obj F, V.1) :=
  letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  letI : Module Γ(X, U.1) Γ((Scheme.Modules.pullback f).obj F, V.1) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(Y, V.1))
  haveI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ((Scheme.Modules.pullback f).obj F, V.1) :=
    IsScalarTower.of_compHom _ _ _
  let ρ : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ((Scheme.Modules.pullback f).obj F, V.1) :=
    { toFun := Scheme.Modules.pullbackSection f F U.1 V.1 hVU
      map_add' := fun a b ↦ map_add (pullbackSectionHom f F U.1 V.1 hVU).hom a b
      map_smul' := fun r a ↦ pullbackSectionHom_smul f F U.1 V.1 hVU r a }
  (isBaseChange_pullbackSection_of_isAffineOpen f F U.2 V.2 hVU (fun _ ↦ rfl) ρ
    (fun _ ↦ rfl)).equiv

/-- `AlgebraicGeometry.TateMap.pullbackSectionsTensorEquiv` sends `t ⊗ s` to `t` times the
pullback of `s`. -/
theorem pullbackSectionsTensorEquiv_tmul {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (t : Γ(Y, V.1)) (s : Γ(F, U.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    pullbackSectionsTensorEquiv f F U V hVU (t ⊗ₜ s) =
      t • pullbackSectionHom f F U.1 V.1 hVU s := by
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
  let : Module Γ(X, U.1) Γ((Scheme.Modules.pullback f).obj F, V.1) :=
    Module.compHom _ (algebraMap Γ(X, U.1) Γ(Y, V.1))
  have : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ((Scheme.Modules.pullback f).obj F, V.1) :=
    IsScalarTower.of_compHom _ _ _
  let ρ : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ((Scheme.Modules.pullback f).obj F, V.1) :=
    { toFun := Scheme.Modules.pullbackSection f F U.1 V.1 hVU
      map_add' := fun a b ↦ map_add (pullbackSectionHom f F U.1 V.1 hVU).hom a b
      map_smul' := fun r a ↦ pullbackSectionHom_smul f F U.1 V.1 hVU r a }
  exact (isBaseChange_pullbackSection_of_isAffineOpen f F U.2 V.2 hVU (fun _ ↦ rfl) ρ
    (fun _ ↦ rfl)).equiv_tmul t s

/-- `AlgebraicGeometry.TateMap.pullbackSectionsTensorEquiv` sends `1 ⊗ s` to the pullback of
`s`. -/
theorem pullbackSectionsTensorEquiv_one_tmul {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] (U : X.affineOpens) (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (s : Γ(F, U.1)) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    pullbackSectionsTensorEquiv f F U V hVU ((1 : Γ(Y, V.1)) ⊗ₜ s) =
      Scheme.Modules.pullbackSection f F U.1 V.1 hVU s :=
  (pullbackSectionsTensorEquiv_tmul f F U V hVU 1 s).trans (one_smul _ _)

variable {X Y X' Y' : Scheme.{u}} {f : Y ⟶ X} {f' : Y' ⟶ X'}

section towers

variable {S T : Scheme.{u}} (g : S ⟶ T)

/-- Restricting after a map on sections over a pair of opens is a scalar tower. -/
theorem isScalarTower_appLE_restrict {O : T.Opens} {W W' : S.Opens} (e : W ≤ g ⁻¹ᵁ O)
    (h : W' ≤ W) :
    letI : Algebra Γ(T, O) Γ(S, W) := (g.appLE O W e).hom.toAlgebra
    letI : Algebra Γ(S, W) Γ(S, W') := (S.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : Algebra Γ(T, O) Γ(S, W') := (g.appLE O W' (h.trans e)).hom.toAlgebra
    IsScalarTower Γ(T, O) Γ(S, W) Γ(S, W') := by
  let : Algebra Γ(T, O) Γ(S, W) := (g.appLE O W e).hom.toAlgebra
  let : Algebra Γ(S, W) Γ(S, W') := (S.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : Algebra Γ(T, O) Γ(S, W') := (g.appLE O W' (h.trans e)).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (g.appLE O W' _).hom = (S.presheaf.map (homOfLE h).op).hom.comp (g.appLE O W e).hom
  rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

/-- A map on sections after restricting is a scalar tower. -/
theorem isScalarTower_restrict_appLE {O O' : T.Opens} {W : S.Opens} (h : O' ≤ O)
    (e : W ≤ g ⁻¹ᵁ O') :
    letI : Algebra Γ(T, O) Γ(T, O') := (T.presheaf.map (homOfLE h).op).hom.toAlgebra
    letI : Algebra Γ(T, O') Γ(S, W) := (g.appLE O' W e).hom.toAlgebra
    letI : Algebra Γ(T, O) Γ(S, W) := (g.appLE O W (e.trans (g.preimage_mono h))).hom.toAlgebra
    IsScalarTower Γ(T, O) Γ(T, O') Γ(S, W) := by
  let : Algebra Γ(T, O) Γ(T, O') := (T.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : Algebra Γ(T, O') Γ(S, W) := (g.appLE O' W e).hom.toAlgebra
  let : Algebra Γ(T, O) Γ(S, W) := (g.appLE O W (e.trans (g.preimage_mono h))).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq' ?_
  change (g.appLE O W _).hom = (g.appLE O' W e).hom.comp (T.presheaf.map (homOfLE h).op).hom
  rw [← CommRingCat.hom_comp, Scheme.Hom.map_appLE]

end towers

/-- **A chart base change of a morphism of the category of Section 0FKB**: affine opens
`U ⊆ X`, `V ⊆ Y`, `U' ⊆ X'`, `V' ⊆ Y'` compatible with the four maps, with a chart base change
datum from `Γ(U) → Γ(V)` to `Γ(U') → Γ(V')`. -/
structure OpenBaseChangeSquare.Chart (sq : OpenBaseChangeSquare f f') where
  /-- The affine open of `X`. -/
  U : X.affineOpens
  /-- The affine open of `Y`. -/
  V : Y.affineOpens
  /-- The affine open of `X'`. -/
  U' : X'.affineOpens
  /-- The affine open of `Y'`. -/
  V' : Y'.affineOpens
  /-- `f` maps `V` into `U`. -/
  hVU : V.1 ≤ f ⁻¹ᵁ U.1
  /-- The base map `X' ⟶ X` maps `U'` into `U`. -/
  hU'U : U'.1 ≤ sq.base ⁻¹ᵁ U.1
  /-- `f'` maps `V'` into `U'`. -/
  hV'U' : V'.1 ≤ f' ⁻¹ᵁ U'.1
  /-- The cover map `Y' ⟶ Y` maps `V'` into `V`. -/
  hV'V : V'.1 ≤ sq.cover ⁻¹ᵁ V.1
  /-- The chart base change datum. -/
  D : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U.1 V.1 hVU).hom.toAlgebra
    letI : Algebra Γ(X, U.1) Γ(X', U'.1) := (sq.base.appLE U.1 U'.1 hU'U).hom.toAlgebra
    letI : Algebra Γ(X', U'.1) Γ(Y', V'.1) := (f'.appLE U'.1 V'.1 hV'U').hom.toAlgebra
    letI : Algebra Γ(Y, V.1) Γ(Y', V'.1) := (sq.cover.appLE V.1 V'.1 hV'V).hom.toAlgebra
    ChartBaseChange Γ(X, U.1) Γ(Y, V.1) Γ(X', U'.1) Γ(Y', V'.1)

namespace OpenBaseChangeSquare.Chart

variable {sq : OpenBaseChangeSquare f f'}

/-- **Chart base changes restrict to principal opens.** If the square is a chart base change on
`U, V, U', V'`, it is one on principal opens `U₀ ⊆ U`, `V₀ ⊆ V`, `U'₀ ⊆ U'`, `V'₀ ⊆ V'`
compatible with the four maps. -/
theorem nonempty_chartBaseChange_of_basicOpen (k : sq.Chart) (U₀ : X.affineOpens)
    (V₀ : Y.affineOpens) (U'₀ : X'.affineOpens) (V'₀ : Y'.affineOpens)
    (hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1) (hU'₀U₀ : U'₀.1 ≤ sq.base ⁻¹ᵁ U₀.1)
    (hV'₀U'₀ : V'₀.1 ≤ f' ⁻¹ᵁ U'₀.1) (hV'₀V₀ : V'₀.1 ≤ sq.cover ⁻¹ᵁ V₀.1)
    (a : Γ(X, k.U.1)) (b : Γ(Y, k.V.1)) (a' : Γ(X', k.U'.1)) (b' : Γ(Y', k.V'.1))
    (ha : U₀.1 = X.basicOpen a) (hb : V₀.1 = Y.basicOpen b) (ha' : U'₀.1 = X'.basicOpen a')
    (hb' : V'₀.1 = Y'.basicOpen b') :
    letI : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀.1 V₀.1 hV₀U₀).hom.toAlgebra
    letI : Algebra Γ(X, U₀.1) Γ(X', U'₀.1) := (sq.base.appLE U₀.1 U'₀.1 hU'₀U₀).hom.toAlgebra
    letI : Algebra Γ(X', U'₀.1) Γ(Y', V'₀.1) := (f'.appLE U'₀.1 V'₀.1 hV'₀U'₀).hom.toAlgebra
    letI : Algebra Γ(Y, V₀.1) Γ(Y', V'₀.1) := (sq.cover.appLE V₀.1 V'₀.1 hV'₀V₀).hom.toAlgebra
    Nonempty (ChartBaseChange Γ(X, U₀.1) Γ(Y, V₀.1) Γ(X', U'₀.1) Γ(Y', V'₀.1)) := by
  have hU₀ : U₀.1 ≤ k.U.1 := ha ▸ X.basicOpen_le a
  have hV₀ : V₀.1 ≤ k.V.1 := hb ▸ Y.basicOpen_le b
  have hU'₀ : U'₀.1 ≤ k.U'.1 := ha' ▸ X'.basicOpen_le a'
  have hV'₀ : V'₀.1 ≤ k.V'.1 := hb' ▸ Y'.basicOpen_le b'
  -- the chart `k`
  let : Algebra Γ(X, k.U.1) Γ(Y, k.V.1) := (f.appLE k.U.1 k.V.1 k.hVU).hom.toAlgebra
  let : Algebra Γ(X, k.U.1) Γ(X', k.U'.1) := (sq.base.appLE k.U.1 k.U'.1 k.hU'U).hom.toAlgebra
  let : Algebra Γ(X', k.U'.1) Γ(Y', k.V'.1) := (f'.appLE k.U'.1 k.V'.1 k.hV'U').hom.toAlgebra
  let : Algebra Γ(Y, k.V.1) Γ(Y', k.V'.1) := (sq.cover.appLE k.V.1 k.V'.1 k.hV'V).hom.toAlgebra
  -- shrinking the target chart
  let : Algebra Γ(X', k.U'.1) Γ(X', U'₀.1) := (X'.presheaf.map (homOfLE hU'₀).op).hom.toAlgebra
  let : Algebra Γ(X', U'₀.1) Γ(Y', V'₀.1) := (f'.appLE U'₀.1 V'₀.1 hV'₀U'₀).hom.toAlgebra
  let : Algebra Γ(Y', k.V'.1) Γ(Y', V'₀.1) := (Y'.presheaf.map (homOfLE hV'₀).op).hom.toAlgebra
  let E' := chartBaseChangeBasicOpen f' k.U' k.V' k.hV'U' U'₀.1 V'₀.1 a' b' ha' hb' hU'₀ hV'₀
    hV'₀U'₀
  let : Algebra Γ(X, k.U.1) Γ(X', U'₀.1) :=
    (sq.base.appLE k.U.1 U'₀.1 (hU'₀.trans k.hU'U)).hom.toAlgebra
  have : IsScalarTower Γ(X, k.U.1) Γ(X', k.U'.1) Γ(X', U'₀.1) :=
    isScalarTower_appLE_restrict sq.base k.hU'U hU'₀
  let : Algebra Γ(Y, k.V.1) Γ(Y', V'₀.1) :=
    (sq.cover.appLE k.V.1 V'₀.1 (hV'₀.trans k.hV'V)).hom.toAlgebra
  have : IsScalarTower Γ(Y, k.V.1) Γ(Y', k.V'.1) Γ(Y', V'₀.1) :=
    isScalarTower_appLE_restrict sq.cover k.hV'V hV'₀
  let D₁ := E'.comp k.D
  -- shrinking the source chart
  let : Algebra Γ(Y, k.V.1) Γ(Y, V₀.1) := (Y.presheaf.map (homOfLE hV₀).op).hom.toAlgebra
  let : Algebra Γ(X, k.U.1) Γ(Y, V₀.1) := (f.appLE k.U.1 V₀.1 (hV₀.trans k.hVU)).hom.toAlgebra
  have : IsScalarTower Γ(X, k.U.1) Γ(Y, k.V.1) Γ(Y, V₀.1) :=
    isScalarTower_appLE_restrict f k.hVU hV₀
  let : Algebra Γ(Y, V₀.1) Γ(Y', V'₀.1) := (sq.cover.appLE V₀.1 V'₀.1 hV'₀V₀).hom.toAlgebra
  have : IsScalarTower Γ(Y, k.V.1) Γ(Y, V₀.1) Γ(Y', V'₀.1) :=
    isScalarTower_restrict_appLE sq.cover hV₀ hV'₀V₀
  have : IsLocalization.Away b Γ(Y, V₀.1) :=
    k.V.2.isLocalization_of_eq_basicOpen b (homOfLE hV₀) hb
  let D₂ := D₁.ofSourceAway (B₀ := Γ(Y, V₀.1)) b
  -- shrinking the base chart
  let : Algebra Γ(X, k.U.1) Γ(X, U₀.1) := (X.presheaf.map (homOfLE hU₀).op).hom.toAlgebra
  let : Algebra Γ(X, U₀.1) Γ(Y, V₀.1) := (f.appLE U₀.1 V₀.1 hV₀U₀).hom.toAlgebra
  have : IsScalarTower Γ(X, k.U.1) Γ(X, U₀.1) Γ(Y, V₀.1) :=
    isScalarTower_restrict_appLE f hU₀ hV₀U₀
  let : Algebra Γ(X, U₀.1) Γ(X', U'₀.1) := (sq.base.appLE U₀.1 U'₀.1 hU'₀U₀).hom.toAlgebra
  have : IsScalarTower Γ(X, k.U.1) Γ(X, U₀.1) Γ(X', U'₀.1) :=
    isScalarTower_restrict_appLE sq.base hU₀ hU'₀U₀
  have : IsLocalization.Away a Γ(X, U₀.1) :=
    k.U.2.isLocalization_of_eq_basicOpen a (homOfLE hU₀) ha
  exact ⟨D₂.ofBaseAway (A₀ := Γ(X, U₀.1)) a⟩

/-- **Common principal refinements of two charts.** Around a point `y` of the overlap of the
opens `V'` of two charts `k` and `l` there is a chart `m` whose four affine opens are principal
opens of those of `k` and of those of `l`. -/
theorem exists_common_refinement (k l : sq.Chart) (y : Y') (hyk : y ∈ k.V'.1) (hyl : y ∈ l.V'.1) :
    ∃ (m : sq.Chart) (a : Γ(X, k.U.1)) (b : Γ(Y, k.V.1)) (a' : Γ(X', k.U'.1))
      (b' : Γ(Y', k.V'.1)) (c : Γ(X, l.U.1)) (d : Γ(Y, l.V.1)) (c' : Γ(X', l.U'.1))
      (d' : Γ(Y', l.V'.1)), m.U.1 = X.basicOpen a ∧ m.V.1 = Y.basicOpen b ∧
        m.U'.1 = X'.basicOpen a' ∧ m.V'.1 = Y'.basicOpen b' ∧ m.U.1 = X.basicOpen c ∧
        m.V.1 = Y.basicOpen d ∧ m.U'.1 = X'.basicOpen c' ∧ m.V'.1 = Y'.basicOpen d' ∧
        y ∈ m.V'.1 := by
  obtain ⟨a, c, b, d, hac, hbd, hyb, hba, -⟩ := exists_common_basicOpen f k.U l.U k.V l.V k.hVU
    l.hVU (sq.cover y) (k.hV'V hyk) (l.hV'V hyl) ⊤ trivial
  have hx : sq.base (f' y) ∈ X.basicOpen a := by
    rw [← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]
    exact hba hyb
  obtain ⟨a', c', hac', hya', hle'⟩ := Stacks.Discriminant.exists_common_basicOpen_le k.U' l.U'
    (k.U'.1 ⊓ l.U'.1 ⊓ sq.base ⁻¹ᵁ X.basicOpen a) inf_le_left (f' y)
    ⟨⟨k.hV'U' hyk, l.hV'U' hyl⟩, hx⟩
  obtain ⟨b', d', hbd', hyb', hle''⟩ := Stacks.Discriminant.exists_common_basicOpen_le k.V' l.V'
    (k.V'.1 ⊓ l.V'.1 ⊓ (f' ⁻¹ᵁ X'.basicOpen a' ⊓ sq.cover ⁻¹ᵁ Y.basicOpen b)) inf_le_left y
    ⟨⟨hyk, hyl⟩, hya', hyb⟩
  let U₀ : X.affineOpens := ⟨X.basicOpen a, k.U.2.basicOpen a⟩
  let V₀ : Y.affineOpens := ⟨Y.basicOpen b, k.V.2.basicOpen b⟩
  let U'₀ : X'.affineOpens := ⟨X'.basicOpen a', k.U'.2.basicOpen a'⟩
  let V'₀ : Y'.affineOpens := ⟨Y'.basicOpen b', k.V'.2.basicOpen b'⟩
  have hV₀U₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1 := hba
  have hU'₀U₀ : U'₀.1 ≤ sq.base ⁻¹ᵁ U₀.1 := hle'.trans inf_le_right
  have hV'₀U'₀ : V'₀.1 ≤ f' ⁻¹ᵁ U'₀.1 := hle''.trans (inf_le_right.trans inf_le_left)
  have hV'₀V₀ : V'₀.1 ≤ sq.cover ⁻¹ᵁ V₀.1 := hle''.trans (inf_le_right.trans inf_le_right)
  obtain ⟨D⟩ := k.nonempty_chartBaseChange_of_basicOpen U₀ V₀ U'₀ V'₀ hV₀U₀ hU'₀U₀ hV'₀U'₀
    hV'₀V₀ a b a' b' rfl rfl rfl rfl
  exact ⟨⟨U₀, V₀, U'₀, V'₀, hV₀U₀, hU'₀U₀, hV'₀U'₀, hV'₀V₀, D⟩, a, b, a', b', c, d, c', d', rfl,
    rfl, rfl, rfl, hac, hbd, hac', hbd', hyb'⟩

end OpenBaseChangeSquare.Chart

/-- **The opens `V'` of the charts form a basis of `Y'`.** -/
theorem OpenBaseChangeSquare.exists_chart_le (sq : OpenBaseChangeSquare f f') (O : Y'.Opens)
    (y : Y') (hy : y ∈ O) : ∃ k : sq.Chart, y ∈ k.V'.1 ∧ k.V'.1 ≤ O := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hyU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (sq.cover y))) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (show sq.cover y ∈ f ⁻¹ᵁ U from hyU)
      (f ⁻¹ᵁ U).isOpen
  obtain ⟨U', V', hU'U, hV'U', hV'V, hyV', hV'O, ⟨D⟩⟩ :=
    sq.exists_chartBaseChange_of_le ⟨U, hU⟩ ⟨V, hV⟩ hVU y hyV O hy
  exact ⟨⟨⟨U, hU⟩, ⟨V, hV⟩, U', V', hVU, hU'U, hV'U', hV'V, D⟩, hyV', hV'O⟩

/-- **Glueing along the charts.** A family of linear isomorphisms between the sections over the
opens `V'` of the charts of two `𝒪_{Y'}`-modules, compatible with restriction to principal-open
refinements of charts, is the family of sections of an isomorphism. -/
theorem OpenBaseChangeSquare.exists_iso_of_chart (sq : OpenBaseChangeSquare f f')
    {M N : Y'.Modules} (e : ∀ k : sq.Chart, Γ(M, k.V'.1) ≃ₗ[Γ(Y', k.V'.1)] Γ(N, k.V'.1))
    (he : ∀ (k m : sq.Chart) (a : Γ(X, k.U.1)) (b : Γ(Y, k.V.1)) (a' : Γ(X', k.U'.1))
      (b' : Γ(Y', k.V'.1)), m.U.1 = X.basicOpen a → m.V.1 = Y.basicOpen b →
        m.U'.1 = X'.basicOpen a' → m.V'.1 = Y'.basicOpen b' →
        ∀ (hle : m.V'.1 ≤ k.V'.1) (s : Γ(M, k.V'.1)),
          e m (M.presheaf.map (homOfLE hle).op s) = N.presheaf.map (homOfLE hle).op (e k s)) :
    ∃ c : M ≅ N, ∀ (k : sq.Chart) (s : Γ(M, k.V'.1)), c.hom.app k.V'.1 s = e k s := by
  refine exists_iso_of_basis (fun k : sq.Chart ↦ k.V'.1)
    sq.exists_chart_le e fun k l hlk s ↦ ?_
  refine (Scheme.Modules.isSheaf N).section_ext fun y hy ↦ ?_
  obtain ⟨m, a, b, a', b', c, d, c', d', ha, hb, ha', hb', hc, hd, hc', hd', hym⟩ :=
    Chart.exists_common_refinement k l y (hlk hy) hy
  have hml : m.V'.1 ≤ l.V'.1 := hd' ▸ Y'.basicOpen_le d'
  refine ⟨m.V'.1, hml, hym, ?_⟩
  have h₁ := he l m c d c' d' hc hd hc' hd' hml (M.presheaf.map (homOfLE hlk).op s)
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← h₁, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  exact he k m a b a' b' ha hb ha' hb' (hml.trans hlk) s

end AlgebraicGeometry.TateMap
