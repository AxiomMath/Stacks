module

public import StacksFrontier.Algebra.Polynomial.LaurentRingHomExt
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.MultiplicativeTorsorPointTrivialization
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Points of the multiplicative torsor with prescribed trivialization

In Situation 0EDT let `X/B` be good, let `ℒ` be an invertible `𝒪_X`-module and let
`q : T ⟶ X` be its multiplicative torsor, with its trivialization `α` of `q^*ℒ`. A point `t` of
`T` with values in a scheme `U` gives the trivialization `t^*α` of `x^*ℒ` along `x = q ∘ t`. This
file shows that `t` is determined by `t^*α`, and that over a chart of `U` whose chart of `X` is
affine and trivializes `ℒ` every trivialization of `x^*ℒ` is induced by a point of `T`.

## Main results

* `AlgebraicGeometry.Space.torsorHom_eq_of_trivialization`: two points of `T` over the same `x`
  inducing the same trivialization of `x^*ℒ` are equal.
* `AlgebraicGeometry.Space.localTorsorHom_trivialization`: over the source chart of a chart
  diagram whose chart of `X` is affine and trivializes `ℒ`, the point `localTorsorHom` of `T`
  induces the restriction of a given trivialization `β` of `x^*ℒ`.

## References

* [Stacks Project, Tag 0EQG](https://stacks.math.columbia.edu/tag/0EQG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (p : X ⟶ D.space) (hp : D.IsGood p)
    (L : Modules.{u, u} D.site D.base D.base_mem X hp.1)
    (hL : IsInvertibleSheaf D p hp L)

/-! ### Morphisms out of the inverse image of a module with a free generator -/

section Generator

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {A A' : AlgebraicSpaces B S hS} (f : A ⟶ A') (M : Modules.{u, u} B S hS A'.1 A'.2)
    (hM : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS A')
      (structureRingSheaf B S hS A').property M)
    (d : ChartDiagram B S hS A.1 A'.1 f.hom)
    (e : (W : SmallEtale B S hS A'.1) → (W ⟶ d.V) → M.val.obj (op W))
    (hcompat : ∀ (W W' : SmallEtale B S hS A'.1) (k : W ⟶ d.V) (g : W' ⟶ W),
      (M.val.map g.op).hom (e W k) = e W' (g ≫ k))
    (hbij : ∀ (W : SmallEtale B S hS A'.1) (k : W ⟶ d.V),
      Function.Bijective fun r : chartRing B S hS A'.1 A'.2 W ↦ r • e W k)

include hM hcompat hbij in
/-- **Two morphisms out of `f^*M` agreeing on the inverse image of a free generator agree over
every chart over the source chart.** -/
theorem modulePullback_val_app_eq_of_generator {N : Modules.{u, u} B S hS A.1 A.2}
    (φ ψ : (modulePullback B S hS f).obj M ⟶ N)
    (h : φ.val.app (op d.U) (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U)) =
      ψ.val.app (op d.U) (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U)))
    (W : SmallEtale B S hS A.1) (k : W ⟶ d.U)
    (x : ((modulePullback B S hS f).obj M).val.obj (op W)) :
    φ.val.app (op W) x = ψ.val.app (op W) x := by
  obtain ⟨r, rfl⟩ := (bijective_smul_modulePullbackChartGenerator B S hS f M hM d e hcompat hbij
    W k).2 x
  have hG : modulePullbackChartGenerator B S hS f M d e W k =
      ((modulePullback B S hS f).obj M).val.map k.op
        (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U)) := by
    rw [modulePullbackChartGenerator_compat, Category.comp_id]
  have hnat : ∀ χ : (modulePullback B S hS f).obj M ⟶ N,
      χ.val.app (op W) (r • modulePullbackChartGenerator B S hS f M d e W k) =
        r • (show N.val.obj (op W) from N.val.map k.op (χ.val.app (op d.U)
          (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U)))) := by
    intro χ
    refine ((χ.val.app (op W)).hom.map_smul r _).trans ?_
    congr 1
    rw [hG]
    exact congrArg (fun φ' => (ConcreteCategory.hom φ' : _ → _)
      (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U))) (χ.val.naturality k.op)
  rw [hnat φ, hnat ψ, h]

/-- The forward map of an isomorphism of sheaves of modules undoes the backward map. -/
private theorem iso_hom_app_inv_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (ε : M ≅ N) (Y : Cᵒᵖ) (x : N.val.obj Y) :
    ε.hom.val.app Y (ε.inv.val.app Y x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app Y) ε.inv_hom_id) x

/-- The backward map of an isomorphism of sheaves of modules undoes the forward map. -/
private theorem iso_inv_app_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (ε : M ≅ N) (Y : Cᵒᵖ) (x : M.val.obj Y) :
    ε.inv.val.app Y (ε.hom.val.app Y x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => φ.val.app Y) ε.hom_inv_id) x

/-- The sections of an isomorphism of sheaves of modules form a bijection. -/
private theorem bijective_iso_inv_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat} {M N : SheafOfModules R} (ε : M ≅ N) (Y : Cᵒᵖ) :
    Function.Bijective (ε.inv.val.app Y) :=
  Function.bijective_iff_has_inverse.2
    ⟨ε.hom.val.app Y, iso_hom_app_inv_app_apply ε Y, iso_inv_app_hom_app_apply ε Y⟩

/-- A morphism `f^*M ⟶ N` read on the chart diagram `d` at the free generator `e` is its value on
the inverse image of that generator. -/
private theorem modulePullbackHomFMap_app_generator {N : Modules.{u, u} B S hS A.1 A.2}
    (χ : (modulePullback B S hS f).obj M ⟶ N) :
    (modulePullbackHomFMap B S hS f M N χ).app d (e d.V (𝟙 d.V)) =
      χ.val.app (op d.U) (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U)) :=
  (modulePullbackHomFMap_app B S hS f M N χ d _).trans
    (congrArg (fun z => χ.val.app (op d.U) z)
      ((modulePullbackChartGenerator_id B S hS f M d e).trans
        (modulePullbackChartFMap_app_eq_unitSection B S hS f M d _)).symm)

include hM hcompat hbij in
/-- **An isomorphism `f^*M ≅ 𝒪` sends the inverse image of a free generator to a unit.** -/
theorem isUnit_iso_hom_modulePullbackChartGenerator
    (β : (modulePullback B S hS f).obj M ≅ SheafOfModules.unit (structureRingSheaf B S hS A)) :
    IsUnit (show chartRing B S hS A.1 A.2 d.U from β.hom.val.app (op d.U)
      (modulePullbackChartGenerator B S hS f M d e d.U (𝟙 d.U))) := by
  obtain ⟨r, hr⟩ := (bijective_smul_modulePullbackChartGenerator B S hS f M hM d e hcompat hbij
    d.U (𝟙 d.U)).2 (β.inv.val.app (op d.U) (1 : chartRing B S hS A.1 A.2 d.U))
  refine isUnit_iff_exists_inv.2 ⟨r, ?_⟩
  rw [mul_comm]
  have h1 := congrArg (β.hom.val.app (op d.U)) hr
  have h2 : β.hom.val.app (op d.U) (β.inv.val.app (op d.U) (1 : chartRing B S hS A.1 A.2 d.U)) =
      (1 : chartRing B S hS A.1 A.2 d.U) := iso_hom_app_inv_app_apply β _ _
  rwa [h2, (β.hom.val.app (op d.U)).hom.map_smul] at h1

/-- **A point of a relative spectrum over an affine chart is determined by its chart reading.** -/
theorem relativeSpecPoint_eq_of_chartEval {Xs : AlgebraicSpaces B S hS}
    {Al : AlgebraSheaf.{u, u} B S hS Xs.1 Xs.2} (hAq : Al.IsQuasicoherent)
    (V : SmallEtale B S hS Xs.1) [IsAffine (chartScheme V)] {T : BigFppfOver B S hS}
    (v : T ⟶ V.obj.left) (P P' : RelativeSpecPoint B S hS Al T) (hpt : P.pt = P'.pt)
    (h : yonedaEquiv.symm P.pt = yoneda.map v ≫ V.obj.hom)
    (h' : yonedaEquiv.symm P'.pt = yoneda.map v ≫ V.obj.hom)
    (he : P.chartEval B S hS V v h = P'.chartEval B S hS V v h') : P = P' := by
  obtain ⟨pt, a⟩ := P
  obtain ⟨pt', a'⟩ := P'
  dsimp only at hpt
  subst hpt
  congr 1
  exact injective_chartEval_of_isAffine B S hS Al hAq V v pt h he

/-- The chart reading of a point is compatible with the structure maps, as morphisms. -/
theorem chartAlgebraMap_comp_chartEval {Xs : AlgebraicSpaces B S hS}
    (Al : AlgebraSheaf.{u, u} B S hS Xs.1 Xs.2) (V : SmallEtale B S hS Xs.1)
    {T : BigFppfOver B S hS} (v : T ⟶ V.obj.left) (P : RelativeSpecPoint B S hS Al T)
    (h : yonedaEquiv.symm P.pt = yoneda.map v ≫ V.obj.hom) :
    chartAlgebraMap B S hS Al V ≫ P.chartEval B S hS V v h =
      ((BigFppfOver.toScheme B S hS).map v).appTop := by
  ext r
  exact chartEval_algebraMap B S hS (A := Al) V v P.pt h P.hom r

/-- The value of a morphism `f^*M ⟶ 𝒪` on the inverse image of the free generator `e` over the
chart diagram `d`, as a function on the source chart. -/
def modulePullbackGeneratorValue
    (u : (modulePullback B S hS f).obj M ⟶ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O)) :
    (structureRingSheaf B S hS A).obj.obj (op d.U) :=
  (modulePullbackHomFMap B S hS f M _ u).app d (e d.V (𝟙 d.V))

include hM hcompat hbij in
/-- **An isomorphism `f^*M ≅ 𝒪` takes the free generator to a unit.** -/
theorem isUnit_modulePullbackGeneratorValue
    (β : (modulePullback B S hS f).obj M ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS A.1 A.2).O)) :
    IsUnit (modulePullbackGeneratorValue B S hS f M d e β.hom) := by
  have h := isUnit_iso_hom_modulePullbackChartGenerator B S hS f M hM d e hcompat hbij β
  rwa [modulePullbackGeneratorValue, modulePullbackHomFMap_app_generator]

include hM hcompat hbij in
/-- **A morphism out of `f^*M` is determined by its value on the free generator** when every
chart of the source maps to the source chart of `d`. -/
theorem modulePullback_hom_ext_of_generator {N : Modules.{u, u} B S hS A.1 A.2}
    (φ ψ : (modulePullback B S hS f).obj M ⟶ N)
    (h : (modulePullbackHomFMap B S hS f M N φ).app d (e d.V (𝟙 d.V)) =
      (modulePullbackHomFMap B S hS f M N ψ).app d (e d.V (𝟙 d.V)))
    (hU : ∀ W : SmallEtale B S hS A.1, Nonempty (W ⟶ d.U)) : φ = ψ := by
  have hgen := (modulePullbackHomFMap_app_generator B S hS f M d e φ).symm.trans
    (h.trans (modulePullbackHomFMap_app_generator B S hS f M d e ψ))
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext (LinearMap.ext fun y =>
    modulePullback_val_app_eq_of_generator B S hS f M hM d e hcompat hbij φ ψ hgen W.unop
      (hU W.unop).some y)

/-- **The restriction of a trivialization `β : x^*M ≅ 𝒪` along `g`**, as a trivialization of
`(g ≫ x)^*M`. -/
def modulePullbackRestrictIso {Z Z' X₀ : AlgebraicSpaces B S hS} (g : Z' ⟶ Z) (x : Z ⟶ X₀)
    (M₀ : Modules.{u, u} B S hS X₀.1 X₀.2)
    (β : (modulePullback B S hS x).obj M₀ ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) :
    (modulePullback B S hS (g ≫ x)).obj M₀ ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z'.1 Z'.2).O) :=
  ((modulePullbackCompIso B S hS g x).app M₀).symm ≪≫ (modulePullback B S hS g).mapIso β ≪≫
    modulePullbackUnitIso B S hS g

/-- The forward map of `modulePullbackRestrictIso` is the inverse of the composition isomorphism,
followed by `g^*β` and the identification `g^*𝒪 ≅ 𝒪`. -/
theorem modulePullbackRestrictIso_hom {Z Z' X₀ : AlgebraicSpaces B S hS} (g : Z' ⟶ Z)
    (x : Z ⟶ X₀) (M₀ : Modules.{u, u} B S hS X₀.1 X₀.2)
    (β : (modulePullback B S hS x).obj M₀ ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)) :
    (modulePullbackRestrictIso B S hS g x M₀ β).hom =
      (modulePullbackCompIso B S hS g x).inv.app M₀ ≫
        ((modulePullback B S hS g).map β.hom ≫ (modulePullbackUnitIso B S hS g).hom) :=
  rfl

end Generator

/-! ### Covering by charts over which `ℒ` is trivial -/

include hL in
/-- **Through every point of an étale chart of `Z` there is a chart diagram over `f : Z ⟶ X`
whose chart of `X` is affine and trivializes `ℒ`.** -/
theorem exists_trivial_affine_chartDiagram_at_point {Z : AlgebraicSpaces D.site D.base D.base_mem}
    (f : Z ⟶ (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (U₀ : SmallEtale D.site D.base D.base_mem Z.1) (z : chartScheme U₀) :
    ∃ (d : ChartDiagram D.site D.base D.base_mem Z.1 X f.hom) (k : d.U ⟶ U₀),
      IsAffine (chartScheme d.V) ∧
      Nonempty (L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V)) ∧
        z ∈ Set.range ((BigFppfOver.toScheme D.site D.base D.base_mem).map
          ((SmallEtale.toOver D.site D.base D.base_mem _).map k)) := by
  obtain ⟨d₀, k₀, z₀, -, hV₀, hz₀⟩ := exists_affine_chartDiagram_at_chartPoint D.site D.base
    D.base_mem f U₀ z
  have hL' : IsInvertibleModule (B := D.site) ⟨X, hp.1⟩ L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  obtain ⟨g, hvg, e, hcompat, hbij⟩ := exists_basicOpen_freeGenerator D.site D.base D.base_mem
    ⟨X, hp.1⟩ L hL' d₀.V hV₀ ((BigFppfOver.toScheme D.site D.base D.base_mem).map d₀.g z₀)
  let O := (BigFppfOver.toScheme D.site D.base D.base_mem).map d₀.g ⁻¹ᵁ
    (chartScheme d₀.V).basicOpen g
  refine ⟨d₀.restrictOpens O ((chartScheme d₀.V).basicOpen g) le_rfl,
    openChartInclusion D.site D.base D.base_mem _ d₀.U O ≫ k₀,
    isAffine_chartScheme_openChart_basicOpen D.site D.base D.base_mem X d₀.V hV₀ g,
    nonempty_iso_unit_of_freeFamily D p hp L _ e hcompat hbij, ⟨⟨z₀, hvg⟩, ?_⟩⟩
  show ((BigFppfOver.toScheme D.site D.base D.base_mem).map
      ((SmallEtale.toOver D.site D.base D.base_mem _).map (openChartInclusion D.site D.base
        D.base_mem _ d₀.U O)) ≫ (BigFppfOver.toScheme D.site D.base D.base_mem).map
      ((SmallEtale.toOver D.site D.base D.base_mem _).map k₀)) ⟨z₀, hvg⟩ = z
  rw [toScheme_map_toOver_map_openChartInclusion, ← hz₀]
  rfl

/-! ### Points over a trivializing affine chart -/

section Local

variable {V : SmallEtale D.site D.base D.base_mem X}
    (e : L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V))
    (hV : (SmallEtale.topology D.site D.base D.base_mem X).IsQuasiCompactObject V)
    [IsAffine (chartScheme V)]

/-- The free generating family of `ℒ^{⊗ 1}` over the charts over `V` given by a trivialization of
`ℒ` over `V`. -/
def laurentPieceOneGeneratorFamily (W : SmallEtale D.site D.base D.base_mem X) (k : W ⟶ V) :
    (laurentPieceOne D p hp L hL).val.obj (op W) :=
  (laurentPieceOne D p hp L hL).val.map k.op (laurentChartGenerator D p hp L hL e 1)

omit [IsAffine (chartScheme V)] in
/-- Each member of `laurentPieceOneGeneratorFamily` freely generates `ℒ^{⊗ 1}` over its chart:
`r ↦ r • e` is bijective. -/
theorem bijective_smul_laurentPieceOneGeneratorFamily (W : SmallEtale D.site D.base D.base_mem X)
    (k : W ⟶ V) :
    Function.Bijective fun r : chartRing D.site D.base D.base_mem X hp.1 W ↦
      r • laurentPieceOneGeneratorFamily D p hp L hL e W k := by
  have hinv := Stacks.SheafOfModules.iso_inv_app_eq_smul (tensorStructureRingPresheaf D p hp)
    (isSheaf_tensorStructureRingPresheaf D p hp) ((laurentGradedAlgebra D p hp L hL).piece 1)
    (laurentPieceTrivialization D p hp L hL e 1) k
  have hb := bijective_iso_inv_app (laurentPieceTrivialization D p hp L hL e 1) (op (Over.mk k))
  refine ⟨fun a b hab => hb.1 ((hinv a).trans (hab.trans (hinv b).symm)), fun y => ?_⟩
  obtain ⟨r, hr⟩ := hb.2 y
  exact ⟨r, (hinv r).symm.trans hr⟩

/-- The free generating family of `ℒ` over the charts over `V` given by a trivialization of
`ℒ` over `V`. -/
def laurentGeneratorFamily (W : SmallEtale D.site D.base D.base_mem X) (k : W ⟶ V) :
    L.val.obj (op W) :=
  (laurentPieceOneIso D p hp L hL).inv.val.app (op W)
    (laurentPieceOneGeneratorFamily D p hp L hL e W k)

omit [IsAffine (chartScheme V)] in
/-- The family `laurentGeneratorFamily` is compatible with restriction along morphisms of
charts. -/
theorem laurentGeneratorFamily_compat (W W' : SmallEtale D.site D.base D.base_mem X)
    (k : W ⟶ V) (g : W' ⟶ W) :
    (L.val.map g.op).hom (laurentGeneratorFamily D p hp L hL e W k) =
      laurentGeneratorFamily D p hp L hL e W' (g ≫ k) := by
  have hpiece : ((laurentPieceOne D p hp L hL).val.map g.op).hom
      (laurentPieceOneGeneratorFamily D p hp L hL e W k) =
      laurentPieceOneGeneratorFamily D p hp L hL e W' (g ≫ k) := by
    unfold laurentPieceOneGeneratorFamily
    rw [op_comp]
    exact (PresheafOfModules.map_comp_apply _ _ _ _).symm
  unfold laurentGeneratorFamily
  have h1 := congrArg (fun φ => (ConcreteCategory.hom φ : _ → _)
    (laurentPieceOneGeneratorFamily D p hp L hL e W k))
    ((laurentPieceOneIso D p hp L hL).inv.val.naturality g.op)
  exact h1.symm.trans (congrArg (fun z => (laurentPieceOneIso D p hp L hL).inv.val.app (op W') z)
    hpiece)

omit [IsAffine (chartScheme V)] in
/-- Each member of `laurentGeneratorFamily` freely generates `ℒ` over its chart: `r ↦ r • e` is
bijective. -/
theorem bijective_smul_laurentGeneratorFamily (W : SmallEtale D.site D.base D.base_mem X)
    (k : W ⟶ V) :
    Function.Bijective fun r : chartRing D.site D.base D.base_mem X hp.1 W ↦
      r • laurentGeneratorFamily D p hp L hL e W k := by
  have hτ := bijective_iso_inv_app (laurentPieceOneIso D p hp L hL) (op W)
  have hb := bijective_smul_laurentPieceOneGeneratorFamily D p hp L hL e W k
  have hcomp : (fun r : chartRing D.site D.base D.base_mem X hp.1 W ↦
      r • laurentGeneratorFamily D p hp L hL e W k) =
      (laurentPieceOneIso D p hp L hL).inv.val.app (op W) ∘
        (fun r : chartRing D.site D.base D.base_mem X hp.1 W ↦
          r • laurentPieceOneGeneratorFamily D p hp L hL e W k) := funext fun r =>
    (((laurentPieceOneIso D p hp L hL).inv.val.app (op W)).hom.map_smul r _).symm
  rw [hcomp]
  exact hτ.comp hb

omit [IsAffine (chartScheme V)] in
/-- Over `V` itself, `laurentPieceOneIso` sends the generator of `ℒ` to the degree-one generator
`laurentChartGenerator`. -/
theorem laurentPieceOneIso_hom_laurentGeneratorFamily :
    (laurentPieceOneIso D p hp L hL).hom.val.app (op V)
        (laurentGeneratorFamily D p hp L hL e V (𝟙 V)) =
      laurentChartGenerator D p hp L hL e 1 := by
  unfold laurentGeneratorFamily
  refine (iso_hom_app_inv_app_apply (laurentPieceOneIso D p hp L hL) (op V) _).trans ?_
  unfold laurentPieceOneGeneratorFamily
  exact congrArg (fun φ => (ConcreteCategory.hom φ : _ → _) (laurentChartGenerator D p hp L hL e 1))
    ((laurentPieceOne D p hp L hL).val.map_id (op V))

omit [IsAffine (chartScheme V)] in
/-- The Laurent coordinate is the degree-one generator. -/
theorem laurentChartRingEquiv_T :
    laurentChartRingEquiv D p hp L hL e hV (LaurentPolynomial.T 1) =
      laurentPieceOneIncl D p hp L hL V (laurentChartGenerator D p hp L hL e 1) := by
  show ((laurentCommUnit D p hp L hL).app (op V)).hom
      (LaurentPolynomial.eval₂ (laurentChartStructureMap D p hp L hL (V := V))
        (laurentChartUnit D p hp L hL e) (LaurentPolynomial.T 1)) = _
  rw [LaurentPolynomial.eval₂_T, zpow_one]
  rfl

variable {U : BigFppfOver D.site D.base D.base_mem} (v : U ⟶ V.obj.left)

/-- The ring map `𝒜(V) ≅ 𝒪(V)[T, T⁻¹] ⟶ Γ(U)` sending `T` to a unit `w`. -/
def localTorsorRingMap (w : (Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U, ⊤))ˣ) :
    (laurentAlgebraSheaf D p hp L hL).right.obj.obj (op V) ⟶
      Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U, ⊤) :=
  CommRingCat.ofHom ((LaurentPolynomial.eval₂
    ((BigFppfOver.toScheme D.site D.base D.base_mem).map v).appTop.hom w).comp
      (laurentChartRingEquiv D p hp L hL e hV).symm.toRingHom)

omit [IsAffine (chartScheme V)] in
/-- The ring map `localTorsorRingMap` restricts along the structure map `𝒪(V) ⟶ 𝒜(V)` to the
ring map `𝒪(V) ⟶ Γ(U)` induced by `v`. -/
theorem localTorsorRingMap_comm
    (w : (Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U, ⊤))ˣ) :
    chartAlgebraMap D.site D.base D.base_mem (X := ⟨X, hp.1⟩) (laurentAlgebraSheaf D p hp L hL) V ≫
      localTorsorRingMap D p hp L hL e hV v w =
        ((BigFppfOver.toScheme D.site D.base D.base_mem).map v).appTop := by
  ext r
  show LaurentPolynomial.eval₂ _ w ((laurentChartRingEquiv D p hp L hL e hV).symm
    ((laurentAlgebraSheaf D p hp L hL).algebraMap (op V) r)) = _
  have h1 : (laurentChartRingEquiv D p hp L hL e hV).symm
      ((laurentAlgebraSheaf D p hp L hL).algebraMap (op V) r) = LaurentPolynomial.C r :=
    (RingEquiv.symm_apply_eq _).2 (laurentChartRingEquiv_C D p hp L hL e hV r).symm
  exact (congrArg (LaurentPolynomial.eval₂ _ w) h1).trans (LaurentPolynomial.eval₂_C _ _ _)

omit [IsAffine (chartScheme V)] in
/-- The ring map `localTorsorRingMap` sends the degree-one generator to `w`. -/
theorem localTorsorRingMap_generator
    (w : (Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj U, ⊤))ˣ) :
    localTorsorRingMap D p hp L hL e hV v w
        (laurentPieceOneIncl D p hp L hL V (laurentChartGenerator D p hp L hL e 1)) = w := by
  show LaurentPolynomial.eval₂ _ w ((laurentChartRingEquiv D p hp L hL e hV).symm
    (laurentPieceOneIncl D p hp L hL V (laurentChartGenerator D p hp L hL e 1))) = _
  have h1 : (laurentChartRingEquiv D p hp L hL e hV).symm
      (laurentPieceOneIncl D p hp L hL V (laurentChartGenerator D p hp L hL e 1)) =
        LaurentPolynomial.T 1 :=
    (RingEquiv.symm_apply_eq _).2 (laurentChartRingEquiv_T D p hp L hL e hV).symm
  refine (congrArg (LaurentPolynomial.eval₂ _ w) h1).trans ?_
  exact (LaurentPolynomial.eval₂_T _ _ 1).trans (congrArg Units.val (zpow_one w))

end Local

/-! ### Uniqueness -/

section Uniqueness

variable {U : BigFppfOver D.site D.base D.base_mem}

/-- **The chart reading of a point of `T` over a chart trivializing `ℒ` is determined by the
value of the degree-one generator.** -/
theorem chartEval_eq_of_generator {V : SmallEtale D.site D.base D.base_mem X}
    [IsAffine (chartScheme V)]
    (e : L.over V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over V))
    {W : BigFppfOver D.site D.base D.base_mem} (v : W ⟶ V.obj.left)
    (P P' : RelativeSpecPoint D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
      (laurentAlgebraSheaf D p hp L hL) W)
    (h : yonedaEquiv.symm P.pt = yoneda.map v ≫ V.obj.hom)
    (h' : yonedaEquiv.symm P'.pt = yoneda.map v ≫ V.obj.hom)
    (hgen : P.chartEval D.site D.base D.base_mem V v h
        (laurentPieceOneIncl D p hp L hL V (laurentChartGenerator D p hp L hL e 1)) =
      P'.chartEval D.site D.base D.base_mem V v h'
        (laurentPieceOneIncl D p hp L hL V (laurentChartGenerator D p hp L hL e 1))) :
    P.chartEval D.site D.base D.base_mem V v h = P'.chartEval D.site D.base D.base_mem V v h' := by
  have hqc := isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X V
    (inferInstance : IsAffine (chartScheme V))
  set φ := (P.chartEval D.site D.base D.base_mem V v h).hom
  set ψ := (P'.chartEval D.site D.base D.base_mem V v h').hom
  set ε := laurentChartRingEquiv D p hp L hL e hqc
  have hφ := chartAlgebraMap_comp_chartEval D.site D.base D.base_mem _ V v P h
  have hψ := chartAlgebraMap_comp_chartEval D.site D.base D.base_mem _ V v P' h'
  rw [chartAlgebraMap_laurentAlgebraSheaf D p hp L hL e hqc] at hφ hψ
  have hC : (φ.comp ε.toRingHom).comp LaurentPolynomial.C =
      (ψ.comp ε.toRingHom).comp LaurentPolynomial.C :=
    congrArg CommRingCat.Hom.hom (hφ.trans hψ.symm)
  have key : φ.comp ε.toRingHom = ψ.comp ε.toRingHom := by
    refine LaurentPolynomial.ringHom_ext_of_T (fun r => RingHom.congr_fun hC r) ?_
    · show φ (ε (LaurentPolynomial.T 1)) = ψ (ε (LaurentPolynomial.T 1))
      rw [laurentChartRingEquiv_T D p hp L hL e hqc]
      exact hgen
  apply CommRingCat.hom_ext
  refine RingHom.ext fun a => ?_
  have := congrArg (fun χ : LaurentPolynomial _ →+* _ => χ (ε.symm a)) key
  simpa using this

/-- **A point of `T` over a chart trivializing `ℒ` is determined by the value of the degree-one
generator.** -/
theorem torsorPointAt_eq_of_generator {Z : AlgebraicSpaces D.site D.base D.base_mem}
    (t t' : Z ⟶ torsorOfInvertibleSpace D p hp L hL)
    (hq : t ≫ torsorOfInvertibleProjection D p hp L hL =
      t' ≫ torsorOfInvertibleProjection D p hp L hL)
    (d : ChartDiagram D.site D.base D.base_mem Z.1 X
      (t ≫ torsorOfInvertibleProjection D p hp L hL).hom) [IsAffine (chartScheme d.V)]
    (e : L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V))
    (h : (torsorPointAt D p hp L hL t d.U).chartEval D.site D.base D.base_mem d.V d.g
        (torsorPointAt_pt D p hp L hL t d)
        (laurentPieceOneIncl D p hp L hL d.V (laurentChartGenerator D p hp L hL e 1)) =
      (torsorPointAt D p hp L hL t' d.U).chartEval D.site D.base D.base_mem d.V d.g
        (torsorPointAt_pt_of_eq D p hp L hL t' hq.symm d)
        (laurentPieceOneIncl D p hp L hL d.V (laurentChartGenerator D p hp L hL e 1))) :
    torsorPointAt D p hp L hL t d.U = torsorPointAt D p hp L hL t' d.U :=
  relativeSpecPoint_eq_of_chartEval D.site D.base D.base_mem (Xs := ⟨X, hp.1⟩)
    (Al := laurentAlgebraSheaf D p hp L hL)
    (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) d.V d.g (torsorPointAt D p hp L hL t d.U)
    (torsorPointAt D p hp L hL t' d.U)
    (yonedaEquiv.symm.injective ((torsorPointAt_pt D p hp L hL t d).trans
      (torsorPointAt_pt_of_eq D p hp L hL t' hq.symm d).symm))
    (torsorPointAt_pt D p hp L hL t d) (torsorPointAt_pt_of_eq D p hp L hL t' hq.symm d)
    (chartEval_eq_of_generator D p hp L hL e d.g (torsorPointAt D p hp L hL t d.U)
      (torsorPointAt D p hp L hL t' d.U) (torsorPointAt_pt D p hp L hL t d)
      (torsorPointAt_pt_of_eq D p hp L hL t' hq.symm d) h)

/-- **A point of `T` with values in a scheme is determined by its chart readings at the degree-one
generators of the charts over which `ℒ` is trivial.** -/
theorem torsorHom_eq_of_chartEval (t t' : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      torsorOfInvertibleSpace D p hp L hL)
    (hq : t ≫ torsorOfInvertibleProjection D p hp L hL =
      t' ≫ torsorOfInvertibleProjection D p hp L hL)
    (h : ∀ (d : ChartDiagram D.site D.base D.base_mem (yoneda.obj U) X
        (t ≫ torsorOfInvertibleProjection D p hp L hL).hom), IsAffine (chartScheme d.V) →
      ∀ s : (laurentPieceOne D p hp L hL).val.obj (op d.V),
        (torsorPointAt D p hp L hL t d.U).chartEval D.site D.base D.base_mem d.V d.g
          (torsorPointAt_pt D p hp L hL t d) (laurentPieceOneIncl D p hp L hL d.V s) =
        (torsorPointAt D p hp L hL t' d.U).chartEval D.site D.base D.base_mem d.V d.g
          (torsorPointAt_pt_of_eq D p hp L hL t' hq.symm d)
          (laurentPieceOneIncl D p hp L hL d.V s)) :
    t = t' := by
  choose d k haff he hz using fun z => exists_trivial_affine_chartDiagram_at_point D p hp L hL
    (t ≫ torsorOfInvertibleProjection D p hp L hL) (selfChart D.site D.base D.base_mem U) z
  have hP : ∀ z, torsorPointAt D p hp L hL t (d z).U = torsorPointAt D p hp L hL t' (d z).U := by
    intro z
    have := haff z
    exact torsorPointAt_eq_of_generator D p hp L hL t t' hq (d z) (he z).some
      (h (d z) (haff z) _)
  let f : ∀ z, (d z).U.obj.left ⟶ U := fun z =>
    (SmallEtale.toOver D.site D.base D.base_mem _).map (k z)
  have hf : ∀ (z) (s : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      torsorOfInvertibleSpace D p hp L hL),
      (torsorOfInvertibleSpace D p hp L hL).obj.map (f z).op (yonedaEquiv s.hom) =
        yonedaEquiv ((d z).U.obj.hom ≫ s.hom) := by
    intro z s
    have hw : yoneda.map (f z) ≫ (selfChart D.site D.base D.base_mem U).obj.hom = (d z).U.obj.hom :=
      ((SmallEtale.inclusion D.site D.base D.base_mem _).map (k z)).w
    have hw' : yoneda.map (f z) ≫ s.hom = (d z).U.obj.hom ≫ s.hom := by
      rw [← hw]
      rfl
    exact (yonedaEquiv_naturality s.hom (f z)).trans (congrArg yonedaEquiv hw')
  have hcov : Sieve.generate (Presieve.ofArrows (fun z => (d z).U.obj.left) f) ∈
      BigFppfOver.topology D.site D.base D.base_mem U :=
    BigFppfOver.sieve_generate_ofArrows_mem_topology _ f
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat ⊓ @LocallyOfFinitePresentation)).mpr
        ⟨fun x => ⟨x, hz x⟩, fun z => by
          have : Etale ((BigFppfOver.toScheme D.site D.base D.base_mem).map (f z)) :=
            etale_toScheme_toOver_map D.site D.base D.base_mem _ (k z)
          exact ⟨inferInstance, inferInstance⟩⟩)
  have hsep := ((isSheaf_iff_isSheaf_of_type _ _).1
    (torsorOfInvertibleSpace D p hp L hL).property.isSheaf _ hcov).isSeparatedFor
  have hpt : yonedaEquiv t.hom = yonedaEquiv t'.hom := by
    refine hsep.ext ?_
    rintro Y g ⟨Z', p', q', ⟨z⟩, rfl⟩
    rw [op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hf z t, hf z t']
    congr 1
    have := hP z
    unfold torsorPointAt at this
    exact (relativeSpecPointsEquiv D.site D.base D.base_mem _ _).injective this
  exact ObjectProperty.hom_ext _ (yonedaEquiv.injective hpt)

/-- **Uniqueness in the universal property of `(T, α)`**: two points of `T` with values in a
scheme `U`, over the same point `x` of `X`, inducing the same trivialization of `x^*ℒ`, are
equal. -/
theorem torsorHom_eq_of_trivialization
    (t t' : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      torsorOfInvertibleSpace D p hp L hL)
    {x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem)}
    (h : t ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (h' : t' ≫ torsorOfInvertibleProjection D p hp L hL = x)
    (hβ : (modulePullbackTriangle D.site D.base D.base_mem h).hom.app L ≫
        (((modulePullback D.site D.base D.base_mem t).map
            (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
          (modulePullbackUnitIso D.site D.base D.base_mem t).hom) =
      (modulePullbackTriangle D.site D.base D.base_mem h').hom.app L ≫
        (((modulePullback D.site D.base D.base_mem t').map
            (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
          (modulePullbackUnitIso D.site D.base D.base_mem t').hom)) :
    t = t' := by
  subst h
  refine torsorHom_eq_of_chartEval D p hp L hL t t' h'.symm (fun d _ s => ?_)
  have e := congrArg (fun φ => (modulePullbackHomFMap D.site D.base D.base_mem
    (t ≫ torsorOfInvertibleProjection D p hp L hL) L _ φ).app d
      ((laurentPieceOneIso D p hp L hL).inv.val.app (op d.V) s)) hβ
  have hs := iso_hom_app_inv_app_apply (laurentPieceOneIso D p hp L hL) (op d.V) s
  have e1 := torsorTrivialization_fmap_of_eq D p hp L hL t rfl d
    ((laurentPieceOneIso D p hp L hL).inv.val.app (op d.V) s)
  have e2 := torsorTrivialization_fmap_of_eq D p hp L hL t' h' d
    ((laurentPieceOneIso D p hp L hL).inv.val.app (op d.V) s)
  rw [hs] at e1 e2
  exact e1.symm.trans (e.trans e2)

end Uniqueness

/-! ### Existence over a trivializing chart -/

section ExistenceLocal

variable {U : BigFppfOver D.site D.base D.base_mem}
    (x : representedAlgebraicSpace D.site D.base D.base_mem U ⟶
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem))
    (β : (modulePullback D.site D.base D.base_mem x).obj L ≅
      SheafOfModules.unit (structureRingSheaf D.site D.base D.base_mem
        (representedAlgebraicSpace D.site D.base D.base_mem U)))
    (d : ChartDiagram D.site D.base D.base_mem
      (representedAlgebraicSpace D.site D.base D.base_mem U).1 X x.hom)

/-- The inclusion of the source chart of a chart diagram over `x`, as a morphism of represented
algebraic spaces. -/
def chartDiagramSourceInclusion :
    representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left ⟶
      representedAlgebraicSpace D.site D.base D.base_mem U :=
  ObjectProperty.homMk d.U.obj.hom

/-- The inclusion `chartDiagramSourceInclusion` of the source chart is étale. -/
theorem isEtale_chartDiagramSourceInclusion :
    IsEtale D.site D.base D.base_mem (chartDiagramSourceInclusion D p hp x d).hom :=
  (isEtale_iff_presheaf_of_yoneda D.site D.base D.base_mem _).2 d.U.property

/-- The chart diagram over `ι ≫ x` on the identity chart of the source of `d`. -/
def chartDiagramSelf :
    ChartDiagram D.site D.base D.base_mem
      (representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left).1
      (⟨X, hp.1⟩ : AlgebraicSpaces D.site D.base D.base_mem).1
      (chartDiagramSourceInclusion D p hp x d ≫ x).hom where
  U := selfChart D.site D.base D.base_mem d.U.obj.left
  V := d.V
  g := d.g
  comm := (Category.id_comp _).trans d.comm

/-- The chart diagram over `x` obtained from `chartDiagramSelf` by reading its chart as a chart of
`U`. -/
abbrev chartDiagramSelfPostcomp : ChartDiagram D.site D.base D.base_mem
      (representedAlgebraicSpace D.site D.base D.base_mem U).1 X x.hom :=
  ChartDiagram.postcompSource D.site D.base D.base_mem (chartDiagramSourceInclusion D p hp x d) x
    (isEtale_chartDiagramSourceInclusion D p hp x d) _ rfl (chartDiagramSelf D p hp x d)

variable [IsAffine (chartScheme d.V)]
    (e : L.over d.V ≅ SheafOfModules.unit ((tensorStructureSheaf D p hp).over d.V))

/-- **The restriction of `β` to the source chart of `d`**: the trivialization of `(ι ≫ x)^*ℒ`
obtained by pulling `β` back along `ι`. -/
def restrictedTrivialization :
    (modulePullback D.site D.base D.base_mem (chartDiagramSourceInclusion D p hp x d ≫ x)).obj L ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite D.site
        D.base D.base_mem (representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left).1
          (representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left).2).O) :=
  modulePullbackRestrictIso D.site D.base D.base_mem (chartDiagramSourceInclusion D p hp x d) x L β

omit [IsAffine (chartScheme d.V)] in
/-- `restrictedTrivialization` is the restriction `modulePullbackRestrictIso` of `β` along the
inclusion of the source chart. -/
theorem restrictedTrivialization_eq :
    restrictedTrivialization D p hp L x β d =
      modulePullbackRestrictIso D.site D.base D.base_mem (chartDiagramSourceInclusion D p hp x d) x
        L β :=
  rfl

/-- **The value of the restriction of `β` on the generator.** -/
def trivializationValue :=
  modulePullbackGeneratorValue D.site D.base D.base_mem
    (chartDiagramSourceInclusion D p hp x d ≫ x) L
    (chartDiagramSelf D p hp x d) (laurentGeneratorFamily D p hp L hL e)
    (restrictedTrivialization D p hp L x β d).hom

include hL in
omit [IsAffine (chartScheme d.V)] in
/-- The value `trivializationValue` of the restriction of `β` on the generator is a unit. -/
theorem isUnit_trivializationValue : IsUnit (trivializationValue D p hp L hL x β d e) :=
  isUnit_modulePullbackGeneratorValue D.site D.base D.base_mem
    (chartDiagramSourceInclusion D p hp x d ≫ x) L hL (chartDiagramSelf D p hp x d)
    (laurentGeneratorFamily D p hp L hL e) (laurentGeneratorFamily_compat D p hp L hL e)
    (bijective_smul_laurentGeneratorFamily D p hp L hL e) (restrictedTrivialization D p hp L x β d)

/-- The value of `β` on the generator, as a unit of the functions on the source chart. -/
def trivializationUnit :
    (Γ((BigFppfOver.toScheme D.site D.base D.base_mem).obj d.U.obj.left, ⊤))ˣ :=
  (isUnit_trivializationValue D p hp L hL x β d e).unit

/-- The point of the relative spectrum over the source chart of `d` reading the Laurent coordinate
as the value of `β` on the generator. -/
def localTorsorRelativePoint : RelativeSpecPoint D.site D.base D.base_mem (X := ⟨X, hp.1⟩)
    (laurentAlgebraSheaf D p hp L hL) d.U.obj.left :=
  ⟨yonedaEquiv (yoneda.map d.g ≫ d.V.obj.hom),
    (exists_chartEval_eq D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) d.V d.g _ (Equiv.symm_apply_apply _ _)
      (localTorsorRingMap D p hp L hL e
        (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X d.V
          (inferInstance : IsAffine (chartScheme d.V))) d.g
        (trivializationUnit D p hp L hL x β d e))
      (localTorsorRingMap_comm D p hp L hL e _ d.g _)).choose⟩

/-- The chart reading of `localTorsorRelativePoint` is `localTorsorRingMap`, sending the Laurent
coordinate to `trivializationUnit`. -/
theorem localTorsorRelativePoint_chartEval :
    (localTorsorRelativePoint D p hp L hL x β d e).chartEval D.site D.base D.base_mem d.V d.g
        (Equiv.symm_apply_apply _ _) =
      localTorsorRingMap D p hp L hL e
        (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X d.V
          (inferInstance : IsAffine (chartScheme d.V))) d.g
        (trivializationUnit D p hp L hL x β d e) :=
  (exists_chartEval_eq D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _
      (isQuasicoherent_laurentAlgebraSheaf D p hp L hL) d.V d.g _ (Equiv.symm_apply_apply _ _)
      (localTorsorRingMap D p hp L hL e
        (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X d.V
          (inferInstance : IsAffine (chartScheme d.V))) d.g
        (trivializationUnit D p hp L hL x β d e))
      (localTorsorRingMap_comm D p hp L hL e _ d.g _)).choose_spec

/-- **The point of `T` over the source chart of `d` given by `β`.** -/
def localTorsorHom : representedAlgebraicSpace D.site D.base D.base_mem d.U.obj.left ⟶
    torsorOfInvertibleSpace D p hp L hL :=
  ObjectProperty.homMk (yonedaEquiv.symm ((relativeSpecPointsEquiv D.site D.base D.base_mem
    (X := ⟨X, hp.1⟩) _ d.U.obj.left).symm (localTorsorRelativePoint D p hp L hL x β d e)))

/-- The point of the relative spectrum given by `localTorsorHom` on the identity chart is
`localTorsorRelativePoint`. -/
theorem torsorPointAt_localTorsorHom :
    torsorPointAt D p hp L hL (localTorsorHom D p hp L hL x β d e)
        (selfChart D.site D.base D.base_mem d.U.obj.left) =
      localTorsorRelativePoint D p hp L hL x β d e := by
  show relativeSpecPointsEquiv D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _ d.U.obj.left
      (yonedaEquiv (yonedaEquiv.symm ((relativeSpecPointsEquiv D.site D.base D.base_mem
        (X := ⟨X, hp.1⟩) _ d.U.obj.left).symm (localTorsorRelativePoint D p hp L hL x β d e)))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The point `localTorsorHom` of `T` lies over `ι ≫ x`, where `ι` is the inclusion of the source
chart of `d`. -/
theorem localTorsorHom_comp :
    localTorsorHom D p hp L hL x β d e ≫ torsorOfInvertibleProjection D p hp L hL =
      chartDiagramSourceInclusion D p hp x d ≫ x := by
  refine ObjectProperty.hom_ext _ (yonedaEquiv.injective ?_)
  have e1 : yonedaEquiv ((localTorsorHom D p hp L hL x β d e).hom ≫
      (torsorOfInvertibleProjection D p hp L hL).hom) =
      (relativeSpecPointsEquiv D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _ d.U.obj.left
        ((relativeSpecPointsEquiv D.site D.base D.base_mem (X := ⟨X, hp.1⟩) _ d.U.obj.left).symm
          (localTorsorRelativePoint D p hp L hL x β d e))).pt :=
    (yonedaEquiv_comp _ _).trans (congrArg _ (Equiv.apply_symm_apply _ _))
  have e2 : yonedaEquiv (d.U.obj.hom ≫ x.hom) = yonedaEquiv (yoneda.map d.g ≫ d.V.obj.hom) :=
    congrArg yonedaEquiv d.comm
  refine e1.trans (Eq.trans ?_ e2.symm)
  rw [Equiv.apply_symm_apply]
  rfl

/-- The chart reading of `localTorsorHom` over `chartDiagramSelf` is `localTorsorRingMap`, sending
the Laurent coordinate to `trivializationUnit`. -/
theorem localTorsorHom_chartEval :
    (torsorPointAt D p hp L hL (localTorsorHom D p hp L hL x β d e)
      (chartDiagramSelf D p hp x d).U).chartEval D.site D.base D.base_mem d.V d.g
      (torsorPointAt_pt_of_eq D p hp L hL _ (localTorsorHom_comp D p hp L hL x β d e)
        (chartDiagramSelf D p hp x d)) =
      localTorsorRingMap D p hp L hL e
        (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X d.V
          (inferInstance : IsAffine (chartScheme d.V))) d.g
        (trivializationUnit D p hp L hL x β d e) :=
  (RelativeSpecPoint.chartEval_congr D.site D.base D.base_mem (X := ⟨X, hp.1⟩) d.V
    (rfl : d.g = d.g) (torsorPointAt_localTorsorHom D p hp L hL x β d e)
    (torsorPointAt_pt_of_eq D p hp L hL _ (localTorsorHom_comp D p hp L hL x β d e)
      (chartDiagramSelf D p hp x d)) (Equiv.symm_apply_apply _ _)).trans
    (localTorsorRelativePoint_chartEval D p hp L hL x β d e)

/-- The chart reading of `localTorsorHom` takes the degree-one generator to
`trivializationValue`. -/
theorem localTorsorHom_chartEval_generator :
    (torsorPointAt D p hp L hL (localTorsorHom D p hp L hL x β d e)
      (chartDiagramSelf D p hp x d).U).chartEval D.site D.base D.base_mem
      (chartDiagramSelf D p hp x d).V (chartDiagramSelf D p hp x d).g
      (torsorPointAt_pt_of_eq D p hp L hL _ (localTorsorHom_comp D p hp L hL x β d e)
        (chartDiagramSelf D p hp x d))
      (laurentPieceOneIncl D p hp L hL (chartDiagramSelf D p hp x d).V
        ((laurentPieceOneIso D p hp L hL).hom.val.app (op (chartDiagramSelf D p hp x d).V)
          (laurentGeneratorFamily D p hp L hL e d.V (𝟙 _)))) =
      trivializationValue D p hp L hL x β d e := by
  have e0 := laurentPieceOneIso_hom_laurentGeneratorFamily D p hp L hL e
  have e3 := localTorsorRingMap_generator D p hp L hL e
    (isQuasiCompactObject_of_isAffine D.site D.base D.base_mem X d.V
      (inferInstance : IsAffine (chartScheme d.V))) d.g (trivializationUnit D p hp L hL x β d e)
  have e1 := localTorsorHom_chartEval D p hp L hL x β d e
  show ((torsorPointAt D p hp L hL (localTorsorHom D p hp L hL x β d e)
      (chartDiagramSelf D p hp x d).U).chartEval D.site D.base D.base_mem d.V d.g
      (torsorPointAt_pt_of_eq D p hp L hL _ (localTorsorHom_comp D p hp L hL x β d e)
        (chartDiagramSelf D p hp x d))).hom
      (laurentPieceOneIncl D p hp L hL d.V
        ((laurentPieceOneIso D p hp L hL).hom.val.app (op d.V)
          (laurentGeneratorFamily D p hp L hL e d.V (𝟙 _)))) = _
  rwa [e0, e1]

/-- The trivialization along the local point takes the value of `β` on the generator. -/
theorem localTorsorHom_trivialization_generator :
    (modulePullbackHomFMap D.site D.base D.base_mem (chartDiagramSourceInclusion D p hp x d ≫ x) L _
      ((modulePullbackTriangle D.site D.base D.base_mem
        (localTorsorHom_comp D p hp L hL x β d e)).hom.app L ≫
      (((modulePullback D.site D.base D.base_mem (localTorsorHom D p hp L hL x β d e)).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem
          (localTorsorHom D p hp L hL x β d e)).hom))).app
        (chartDiagramSelf D p hp x d) (laurentGeneratorFamily D p hp L hL e
          (chartDiagramSelf D p hp x d).V (𝟙 (chartDiagramSelf D p hp x d).V)) =
      trivializationValue D p hp L hL x β d e :=
  (torsorTrivialization_fmap_of_eq D p hp L hL _ (localTorsorHom_comp D p hp L hL x β d e)
      (chartDiagramSelf D p hp x d) _).trans
    (localTorsorHom_chartEval_generator D p hp L hL x β d e)

include hL in
/-- **The local point realizes the restriction of `β`**: the trivialization of `(ι ≫ x)^*ℒ`
induced by the local point of `T` over the source chart of `d` is the restriction of `β`. -/
theorem localTorsorHom_trivialization :
    (modulePullbackTriangle D.site D.base D.base_mem
        (localTorsorHom_comp D p hp L hL x β d e)).hom.app L ≫
      (((modulePullback D.site D.base D.base_mem (localTorsorHom D p hp L hL x β d e)).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem (localTorsorHom D p hp L hL x β d e)).hom) =
      (restrictedTrivialization D p hp L x β d).hom := by
  have hgen := localTorsorHom_trivialization_generator D p hp L hL x β d e
  unfold trivializationValue modulePullbackGeneratorValue at hgen
  exact modulePullback_hom_ext_of_generator D.site D.base D.base_mem
    (chartDiagramSourceInclusion D p hp x d ≫ x) L hL (chartDiagramSelf D p hp x d)
    (laurentGeneratorFamily D p hp L hL e) (laurentGeneratorFamily_compat D p hp L hL e)
    (bijective_smul_laurentGeneratorFamily D p hp L hL e)
    ((modulePullbackTriangle D.site D.base D.base_mem
        (localTorsorHom_comp D p hp L hL x β d e)).hom.app L ≫
      (((modulePullback D.site D.base D.base_mem (localTorsorHom D p hp L hL x β d e)).map
          (torsorOfInvertibleTrivialization D p hp L hL).hom) ≫
        (modulePullbackUnitIso D.site D.base D.base_mem (localTorsorHom D p hp L hL x β d e)).hom))
    (restrictedTrivialization D p hp L x β d).hom
    (by convert hgen using 6; exact rfl)
    (fun W => ⟨show W ⟶ selfChart D.site D.base D.base_mem d.U.obj.left from
      ObjectProperty.homMk (CostructuredArrow.homMk (Yoneda.fullyFaithful.preimage W.obj.hom)
        (by simp [selfChart]))⟩)

end ExistenceLocal

end AlgebraicGeometry.Space

end
