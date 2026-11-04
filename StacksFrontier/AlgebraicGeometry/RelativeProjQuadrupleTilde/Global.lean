module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.LocalHom
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ShrinkBase
public import StacksFrontier.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatumExists

/-!
# The global comparison `ℳ̃_T ≅ h^*ℳ̃`

Let `(f : T → S, d, L, ψ)` be a twisting and `h : T ⟶ Proj_S(𝒜)` a morphism over `S` such that
every point of `T` has an open neighbourhood `V` carrying a chart datum of the restriction of
`(f, ψ, h)` to `V`. The local comparisons of these chart data glue to an isomorphism
`ℳ̃_T ≅ h^*ℳ̃`, whose pullback along any morphism `a : Z ⟶ T` carrying a chart datum `D` is the
local comparison of `D`; it is the only isomorphism with this property on the opens of `T`.

The local comparisons agree on overlaps because the restriction of a local comparison is the
local comparison of the restricted chart datum
(`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.localHom_restrict`) and any two chart data
give the same comparison (`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.ChartDatum.iso_eq`).

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.tildeComparison`: the glued isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.Quadruple.tildeComparison`: the same for a
  quadruple and its classifying morphism.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.pullback_map_tildeComparison_hom`: the
  pullback of the glued isomorphism along a morphism carrying a chart datum is the local
  comparison of that datum.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.tildeComparison_chart`: the chart formula,
  in the form of the comparison of the chart datum.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.eq_tildeComparison`: uniqueness.
* `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.Quadruple.tildeComparison_chart` and
  `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.Quadruple.eq_tildeComparison`: the chart
  formula and uniqueness for a quadruple, the chart data being those of
  `Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.exists_chartDatum`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  MonoidalCategory
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.RelativeProj.Situation.QuadrupleChart Stacks.RelativeProj.Situation

universe u

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory
attribute [local instance] LaurentSections.gcommRing

namespace Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

/-- A morphism of inverse images along `g` is determined, after a further pullback along `k`, by
its restriction along `k`. -/
theorem pullback_map_eq_of_pullbackRestrictAlong_eq {T Z Z' : Scheme.{u}} {M N : T.Modules}
    {g : Z ⟶ T} (k : Z' ⟶ Z)
    {X Y : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N}
    (e : pullbackRestrictAlong k rfl X = pullbackRestrictAlong k rfl Y) :
    (Scheme.Modules.pullback k).map X = (Scheme.Modules.pullback k).map Y := by
  have key : ∀ Q : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N,
      (Scheme.Modules.pullback k).map Q =
        (Scheme.Modules.pullbackComp k g).hom.app M ≫ pullbackRestrictAlong k rfl Q ≫
          (Scheme.Modules.pullbackComp k g).inv.app N := by
    intro Q
    simp [pullbackRestrictAlong, Scheme.Modules.pullbackCongr]
  rw [key X, key Y, e]

private theorem conj_of_eq {C : Type*} [Category C] {P Q R S : C} (a : P ≅ Q) (Y : P ⟶ S)
    (c : S ≅ R) (X : Q ⟶ R) (hY : Y = a.hom ≫ X ≫ c.inv) : a.inv ≫ Y ≫ c.hom = X := by
  subst hY
  simp

section General

variable {s : Stacks.RelativeProj.Situation.{u}}
  {ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra}
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {d : ℕ} {hd : 0 < d}
  {T : Scheme.{u}} {f : T ⟶ s.base}
  {L : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [instL : Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  {ψ : Twisting f s.algebra (d : ℤ) L} {h : T ⟶ relativeProj s}

/-- A chart datum along `a`, pulled back along `k` and transported along `k^*a^*L ≅ (k ≫ a)^*L`,
as a chart datum along `k ≫ a`. -/
def chartDatumAlong {Z Z' : Scheme.{u}} {a : Z ⟶ T}
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) (k : Z' ⟶ Z) :
    ChartDatum ((k ≫ a) ≫ f) (ψ.pullback (k ≫ a)) ((k ≫ a) ≫ h) :=
  (D.pullback k).congr (LaurentComposition.compCmp k a L) (ψ.pullback (k ≫ a))
    (fun n => ψ.pullbackApp_comp a k n)

/-- **Any two chart data along `a` give the same local comparison.** -/
theorem localHom_eq_of_chartDatum (hπ : h ≫ relativeProjToBase s = f) {Z : Scheme.{u}} (a : Z ⟶ T)
    (D D' : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    localHom ℳ hd a D = localHom ℳ hd a D' :=
  localHom_eq_of_iso_hom_eq ℳ hd a D D'
    (congrArg Iso.hom (ChartDatum.iso_eq ℳ hd D D' (by rw [Category.assoc, hπ])))

/-- **The restriction of a local comparison along `k` is the local comparison of any chart datum
along the composite.** -/
theorem pullbackRestrictAlong_localHom (hπ : h ≫ relativeProjToBase s = f) {Z Z' : Scheme.{u}}
    (a : Z ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) (k : Z' ⟶ Z) {a' : Z' ⟶ T}
    (hk : k ≫ a = a') (D' : ChartDatum (a' ≫ f) (ψ.pullback a') (a' ≫ h)) :
    pullbackRestrictAlong k hk (localHom ℳ hd a D) = localHom ℳ hd a' D' := by
  have h1 := localHom_restrict ℳ hd a D k
  have h2 := localHom_congr ℳ hd (k ≫ a) a' hk ((D.pullback k).congr
    (LaurentComposition.compCmp k a L) (ψ.pullback (k ≫ a)) (fun n => ψ.pullbackApp_comp a k n))
  have h3 := localHom_eq_of_chartDatum (ℳ := ℳ) (hd := hd) hπ a' (hk ▸ (D.pullback k).congr
    (LaurentComposition.compCmp k a L) (ψ.pullback (k ≫ a)) (fun n => ψ.pullbackApp_comp a k n)) D'
  rw [← h3, ← h2, ← h1]
  simp only [pullbackRestrictAlong, Category.assoc]

variable (hex : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
  Nonempty (ChartDatum (V.ι ≫ f) (ψ.pullback V.ι) (V.ι ≫ h)))

/-- The open neighbourhood of `t` carrying the chosen chart datum. -/
def chartCoverOpen (t : T) : T.Opens := (hex t).choose

/-- Every point `t` lies in `chartCoverOpen hex t`. -/
theorem mem_chartCoverOpen (t : T) : t ∈ chartCoverOpen hex t := (hex t).choose_spec.1

/-- The chosen chart datum over `chartCoverOpen hex t`. -/
def chartCoverDatum (t : T) :
    ChartDatum ((chartCoverOpen hex t).ι ≫ f) (ψ.pullback (chartCoverOpen hex t).ι)
      ((chartCoverOpen hex t).ι ≫ h) :=
  (hex t).choose_spec.2.some

variable (ℳ hd) in
/-- The local comparisons of the chosen chart data. -/
abbrev chartCoverHom (t : T) :
    (Scheme.Modules.pullback (chartCoverOpen hex t).ι).obj (src ℳ f ψ) ⟶
      (Scheme.Modules.pullback (chartCoverOpen hex t).ι).obj
        ((Scheme.Modules.pullback h).obj (moduleSheaf ℳ)) :=
  localHom ℳ hd (chartCoverOpen hex t).ι (chartCoverDatum hex t)

/-- The local comparisons of the chosen chart data agree on the overlaps. -/
theorem chartCoverHom_compatible (hπ : h ≫ relativeProjToBase s = f) (i j : T) (W : T.Opens)
    (hi : W ≤ chartCoverOpen hex i) (hj : W ≤ chartCoverOpen hex j) :
    pullbackRestrictLocal W hi (chartCoverHom ℳ hd hex i) =
      pullbackRestrictLocal W hj (chartCoverHom ℳ hd hex j) := by
  have key : ∀ (t : T) (hW : W ≤ chartCoverOpen hex t),
      pullbackRestrictLocal W hW (chartCoverHom ℳ hd hex t) =
        localHom ℳ hd W.ι
          (T.homOfLE_ι hi ▸ chartDatumAlong (chartCoverDatum hex i) (T.homOfLE hi)) :=
    fun t hW => (pullbackRestrictLocal_eq_pullbackRestrictAlong W hW _).trans
      (pullbackRestrictAlong_localHom (ℳ := ℳ) (hd := hd) hπ _ (chartCoverDatum hex t)
        (T.homOfLE hW) (T.homOfLE_ι hW) _)
  exact (key i hi).trans (key j hj).symm

variable (ℳ hd) in
/-- **The comparison `ℳ̃_T ≅ h^*ℳ̃`**, glued from the local comparisons of chart data chosen
around every point of `T`. -/
def tildeComparison (hπ : h ≫ relativeProjToBase s = f) :
    src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ) :=
  glueIsoOfCover (chartCoverOpen hex) (fun t => ⟨t, mem_chartCoverOpen hex t⟩)
    (chartCoverHom ℳ hd hex) (chartCoverHom_compatible hex hπ)

/-- **The pullback of the comparison along any morphism `a : Z ⟶ T` carrying a chart datum `D`
is the local comparison of `D`.** -/
theorem pullback_map_tildeComparison_hom (hπ : h ≫ relativeProjToBase s = f) {Z : Scheme.{u}}
    (a : Z ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    (Scheme.Modules.pullback a).map (tildeComparison ℳ hd hex hπ).hom = localHom ℳ hd a D := by
  refine hom_ext_of_pullbackCover (fun z : Z => a ⁻¹ᵁ chartCoverOpen hex (a z))
    (fun z => ⟨z, mem_chartCoverOpen hex (a z)⟩) fun z => ?_
  set V := chartCoverOpen hex (a z)
  set W := a ⁻¹ᵁ V
  have hk : a.resLE V W le_rfl ≫ V.ι = W.ι ≫ a := Scheme.Hom.resLE_comp_ι a le_rfl
  refine pullback_map_eq_of_pullbackRestrictAlong_eq W.ι ?_
  refine (pullbackRestrictAlong_pullback_map _ W.ι rfl).trans ?_
  refine (pullbackRestrictAlong_pullback_map _ (a.resLE V W le_rfl) hk).symm.trans ?_
  refine (congrArg (pullbackRestrictAlong (a.resLE V W le_rfl) hk)
    (pullback_map_glueOfCover (chartCoverOpen hex) (fun t => ⟨t, mem_chartCoverOpen hex t⟩)
      (chartCoverHom ℳ hd hex) (chartCoverHom_compatible hex hπ) (a z))).trans ?_
  exact
    (pullbackRestrictAlong_localHom (ℳ := ℳ) (hd := hd) hπ _ _ _ hk (chartDatumAlong D W.ι)).trans
      (pullbackRestrictAlong_localHom (ℳ := ℳ) (hd := hd) hπ _ _ _ rfl (chartDatumAlong D W.ι)).symm

/-- **The chart formula**: for a morphism `a : Z ⟶ T` carrying a chart datum `D`, the pullback of
the comparison along `a` is `a^*ℳ̃_T ≅ ℳ̃_Z`, then the comparison of `D`, then
`(a ≫ h)^*ℳ̃ ≅ a^*h^*ℳ̃`. -/
theorem tildeComparison_chart (hπ : h ≫ relativeProjToBase s = f) {Z : Scheme.{u}} (a : Z ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    (Scheme.Modules.pullback a).map (tildeComparison ℳ hd hex hπ).hom =
      (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).hom ≫
        (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp a h).inv.app (moduleSheaf ℳ) :=
  (pullback_map_tildeComparison_hom hex hπ a D).trans (localHom_eq ℳ hd a D)

/-- The chart formula, solved for the comparison of the chart datum. -/
theorem tildeComparison_chart' (hπ : h ≫ relativeProjToBase s = f) {Z : Scheme.{u}} (a : Z ⟶ T)
    (D : ChartDatum (a ≫ f) (ψ.pullback a) (a ≫ h)) :
    (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L a ψ).inv ≫
        (Scheme.Modules.pullback a).map (tildeComparison ℳ hd hex hπ).hom ≫
          (Scheme.Modules.pullbackComp a h).hom.app (moduleSheaf ℳ) =
      (D.iso ℳ hd).hom :=
  conj_of_eq (C := Z.Modules) _ _ ((Scheme.Modules.pullbackComp a h).app (moduleSheaf ℳ)) _
    (tildeComparison_chart hex hπ a D)

/-- **Uniqueness**: an isomorphism `ℳ̃_T ≅ h^*ℳ̃` satisfying the chart formula on every open of
`T` carrying a chart datum is the comparison. -/
theorem eq_tildeComparison (hπ : h ≫ relativeProjToBase s = f)
    (Φ : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (hΦ : ∀ (V : T.Opens) (D : ChartDatum (V.ι ≫ f) (ψ.pullback V.ι) (V.ι ≫ h)),
      (Scheme.Modules.pullback V.ι).map Φ.hom =
        (associatedSheafPullbackIso (ℳ.toGradedModule s.mul_comm) (d : ℤ) L V.ι ψ).hom ≫
          (D.iso ℳ hd).hom ≫ (Scheme.Modules.pullbackComp V.ι h).inv.app (moduleSheaf ℳ)) :
    Φ = tildeComparison ℳ hd hex hπ :=
  Iso.ext (hom_ext_of_pullbackCover (chartCoverOpen hex)
    (fun t => ⟨t, mem_chartCoverOpen hex t⟩) fun t =>
      (hΦ _ (chartCoverDatum hex t)).trans
        (tildeComparison_chart hex hπ _ (chartCoverDatum hex t)).symm)

/-- **Uniqueness**, with the chart formula stated through the local comparisons. -/
theorem eq_tildeComparison_of_localHom (hπ : h ≫ relativeProjToBase s = f)
    (Φ : src ℳ f ψ ≅ (Scheme.Modules.pullback h).obj (moduleSheaf ℳ))
    (hΦ : ∀ (V : T.Opens) (D : ChartDatum (V.ι ≫ f) (ψ.pullback V.ι) (V.ι ≫ h)),
      (Scheme.Modules.pullback V.ι).map Φ.hom = localHom ℳ hd V.ι D) :
    Φ = tildeComparison ℳ hd hex hπ :=
  Iso.ext (hom_ext_of_pullbackCover (chartCoverOpen hex)
    (fun t => ⟨t, mem_chartCoverOpen hex t⟩) fun t =>
      (hΦ _ (chartCoverDatum hex t)).trans
        (pullback_map_tildeComparison_hom hex hπ _ (chartCoverDatum hex t)).symm)

end General

section Quadruple

variable {s : Stacks.RelativeProj.Situation.{u}}
  (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)
  [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] {d : ℕ} (hd : 0 < d)
  {T : Scheme.{u}} {f : T ⟶ s.base} (P : Quadruple f s.algebra (d : ℤ))

/-- **The comparison `ℳ̃_T ≅ h^*ℳ̃` of a quadruple** `P = (f : T → S, d, L, ψ)`, `h` the morphism
`T ⟶ Proj_S(𝒜)` it classifies: glued from the comparisons of the chart data of `(f, ψ, h)`, which
exist around every point of `T`. -/
def Quadruple.tildeComparison :
    letI := P.isInvertible
    Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) P.twisting ≅
      (Scheme.Modules.pullback (classifyingHom s (by exact_mod_cast hd) P)).obj (moduleSheaf ℳ) :=
  letI := P.isInvertible
  RelativeProjQuadrupleTilde.tildeComparison ℳ hd (exists_chartDatum s hd f P)
    (classifyingHom_comp_toBase s (by exact_mod_cast hd) P)

/-- **The chart formula for the comparison of a quadruple**: along any morphism `a : Z ⟶ T`
carrying a chart datum `D` of `(a ≫ f, a^*ψ, a ≫ h)`, the pullback of the comparison is the local
comparison of `D`: `a^*ℳ̃_T ≅ ℳ̃_Z`, then the comparison of `D`, then `(a ≫ h)^*ℳ̃ ≅ a^*h^*ℳ̃`
(`Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde.localHom_eq`). -/
theorem Quadruple.tildeComparison_chart {Z : Scheme.{u}} (a : Z ⟶ T) :
    letI := P.isInvertible
    ∀ D : ChartDatum (a ≫ f) (P.twisting.pullback a)
      (a ≫ classifyingHom s (by exact_mod_cast hd) P),
    (Scheme.Modules.pullback a).map (Quadruple.tildeComparison ℳ hd P).hom = localHom ℳ hd a D :=
  let _ := P.isInvertible
  fun D => RelativeProjQuadrupleTilde.pullback_map_tildeComparison_hom (ℳ := ℳ) (hd := hd)
    (exists_chartDatum s hd f P) (classifyingHom_comp_toBase s (by exact_mod_cast hd) P) a D

/-- **Uniqueness of the comparison of a quadruple**: an isomorphism `ℳ̃_T ≅ h^*ℳ̃` satisfying the
chart formula on every open of `T` carrying a chart datum is the comparison. -/
theorem Quadruple.eq_tildeComparison :
    letI := P.isInvertible
    ∀ (Φ : Twisting.associatedSheaf (ℳ.toGradedModule s.mul_comm) P.twisting ≅
      (Scheme.Modules.pullback (classifyingHom s (by exact_mod_cast hd) P)).obj (moduleSheaf ℳ)),
    (∀ (V : T.Opens) (D : ChartDatum (V.ι ≫ f) (P.twisting.pullback V.ι)
        (V.ι ≫ classifyingHom s (by exact_mod_cast hd) P)),
      (Scheme.Modules.pullback V.ι).map Φ.hom = localHom ℳ hd V.ι D) →
    Φ = Quadruple.tildeComparison ℳ hd P :=
  let _ := P.isInvertible
  fun Φ hΦ => RelativeProjQuadrupleTilde.eq_tildeComparison_of_localHom (ℳ := ℳ) (hd := hd)
    (exists_chartDatum s hd f P) (classifyingHom_comp_toBase s (by exact_mod_cast hd) P) Φ hΦ

end Quadruple

end Stacks.AlgebraicGeometry.RelativeProjQuadrupleTilde

end
