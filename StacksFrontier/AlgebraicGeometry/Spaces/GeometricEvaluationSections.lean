module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.FiberChart
public import StacksFrontier.AlgebraicGeometry.Limits.ResidueFieldSpreading
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartLocalRingGermsOnOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointOfSpecHom

/-!
# Evaluating a germ at a geometric point given by a homomorphism of sections

A geometric point of the algebraic space represented by an object `U` of the big fppf site is a
morphism of schemes `σ : Spec Ω ⟶ U` (Stacks 0486), and such a morphism landing in an affine
open `U' ⊆ U` is the same thing as a ring homomorphism `ε : Γ(U, U') → Ω`, through
`AlgebraicGeometry.IsAffineOpen.fromSpec`. The *geometric evaluation* at that point,
`AlgebraicGeometry.Space.geometricEval`, the homomorphism from the étale local ring to `Ω`,
takes the germ of a regular function on `U'` to its value under `ε`.

## Main results

* `AlgebraicGeometry.ΓSpecIso_hom_appLE_fromSpec`: the value on `Γ(X, U)` of the morphism
  `Spec Ω ⟶ X` attached to `ε : Γ(X, U) → Ω` is `ε` itself.
* `AlgebraicGeometry.germ_stalkMap_appLE_apply`: the square of a morphism of schemes relating the
  germ at a point of the source, the germ at its image, the restriction map between two affine
  opens and the stalk map.
* `AlgebraicGeometry.Space.geometricPointMap_geometricPointOfSpecHom_of_eq`: the image in a
  second object of the site of a geometric point built from a morphism of schemes, with the
  composite morphism given by an equation rather than as a composite.
* `AlgebraicGeometry.Space.geometricEval_chartLocalRingToEtaleLocalRing_germ`: the geometric
  evaluation of the image under the canonical map of Stacks 05VP of the germ of a regular
  function on a Zariski open of the chart.

## References

* [Stacks Project, Tag 0486](https://stacks.math.columbia.edu/tag/0486)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing Opposite

universe u

namespace AlgebraicGeometry

/-- `Scheme.Hom.appLE` at the top open of the target and the top open of the source is the
action of `AlgebraicGeometry.Scheme.Γ`. -/
theorem appLE_top_top {Z Z' : Scheme.{u}} (f : Z ⟶ Z') (e : (⊤ : Z.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = Scheme.Γ.map f.op := by
  simp only [Scheme.Hom.appLE, Scheme.Γ_map_op, Scheme.Hom.appTop]
  exact (congrArg (f.app ⊤ ≫ ·) (Z.presheaf.map_id (op (f ⁻¹ᵁ (⊤ : Z'.Opens))))).trans
    (Category.comp_id _)

/-- The restriction maps of two equal morphisms of schemes between the same pair of opens
agree. -/
alias appLE_of_eq := Scheme.Hom.appLE_eq_of_eq

/-- A morphism of schemes factoring through `AlgebraicGeometry.IsAffineOpen.fromSpec` of an
affine open lands in that open. -/
theorem le_preimage_of_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {Z : Scheme.{u}} (g : Z ⟶ Spec Γ(X, U)) :
    (⊤ : Z.Opens) ≤ (g ≫ hU.fromSpec) ⁻¹ᵁ U :=
  fun z _ ↦ hU.range_fromSpec.le ⟨g.base z, rfl⟩

/-- For an affine open `U` of a scheme `X` and a ring homomorphism `ε : Γ(X, U) ⟶ Ω`, the
morphism of schemes `Spec Ω ⟶ X` attached to `ε` restricts sections over `U` to global sections
of `Spec Ω` by `ε` itself, read through `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem ΓSpecIso_hom_appLE_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {Ω : CommRingCat.{u}} (ε : Γ(X, U) ⟶ Ω) (a : Γ(X, U)) :
    (Scheme.ΓSpecIso Ω).hom.hom
        (((Spec.map ε ≫ hU.fromSpec).appLE U ⊤
          (le_preimage_of_comp_fromSpec hU (Spec.map ε))).hom a) = ε.hom a := by
  have e₂ : (⊤ : (Spec Ω).Opens) ≤ Spec.map ε ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) :=
    le_preimage_of_comp_fromSpec hU (Spec.map ε)
  have e₃ : (⊤ : (Spec Ω).Opens) ≤ Spec.map ε ⁻¹ᵁ (⊤ : (Spec Γ(X, U)).Opens) := le_top
  have key : (Spec.map ε ≫ hU.fromSpec).appLE U ⊤
        (le_preimage_of_comp_fromSpec hU (Spec.map ε)) ≫ (Scheme.ΓSpecIso Ω).hom = ε := by
    have s1 : hU.fromSpec.appLE U (hU.fromSpec ⁻¹ᵁ U) le_rfl ≫
          (Spec.map ε).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ e₂ =
        (Spec.map ε ≫ hU.fromSpec).appLE U ⊤
          (le_preimage_of_comp_fromSpec hU (Spec.map ε)) :=
      Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have s2 : (Spec Γ(X, U)).presheaf.map (eqToHom hU.fromSpec_preimage_self).op ≫
          (Spec.map ε).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ e₂ =
        (Spec.map ε).appLE ⊤ ⊤ e₃ :=
      Scheme.Hom.map_appLE' (Spec.map ε) e₃ hU.fromSpec_preimage_self
    rw [← s1, Scheme.Hom.appLE_eq_app, hU.fromSpec_app_self]
    simp only [Category.assoc]
    rw [reassoc_of% s2, appLE_top_top, Scheme.Γ_map_op, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom key) a

/-- For `U' ⊆ f ⁻¹ᵁ W'` and a point `u ∈ U'`, the stalk map of `f` at `u` carries the germ at
`f u` of a section over `W'` to the germ at `u` of its restriction to `U'`. -/
theorem germ_stalkMap_appLE_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {W' : Y.Opens} {U' : X.Opens}
    (hUW : U' ≤ f ⁻¹ᵁ W') {u : X} (hu : u ∈ U') (r : Γ(Y, W')) :
    (f.stalkMap u).hom ((Y.presheaf.germ W' (f.base u) (hUW hu)).hom r) =
      (X.presheaf.germ U' u hu).hom ((f.appLE W' U' hUW).hom r) :=
  CategoryTheory.congr_fun (germ_stalkMap_appLE f W' U' hUW u hu) r

/-- The transport of a stalk along an equality of points carries the germ of a section over an
open containing both to the germ of the same section. -/
theorem eqToHom_stalk_germ {X : Scheme.{u}} {x y : X} (hxy : x = y) {U : X.Opens}
    (hx : x ∈ U) (hy : y ∈ U) (a : Γ(X, U)) :
    (eqToHom (congrArg (fun z => X.presheaf.stalk z) hxy)).hom
        (X.presheaf.germ U x hx a) = X.presheaf.germ U y hy a := by
  subst hxy; simp

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- If the composite of `σ : Spec Ω ⟶ U` with `g : U ⟶ W` is a given morphism `σW`, then the
image under `yoneda.map g` of the geometric point of `σ` is the geometric point of `σW`, over the
same structure morphism to the base. -/
theorem geometricPointMap_geometricPointOfSpecHom_of_eq {U W : BigFppfOver B S hS} (g : U ⟶ W)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (hΩ : B.Contains (Spec (.of Ω)))
    (tb : Spec (.of Ω) ⟶ S)
    (σ : Spec (.of Ω) ⟶ (BigFppfOver.toScheme B S hS).obj U)
    (hσ : σ ≫ B.inclusion.map U.hom = tb)
    (σW : Spec (.of Ω) ⟶ (BigFppfOver.toScheme B S hS).obj W)
    (hσW : σ ≫ (BigFppfOver.toScheme B S hS).map g = σW)
    (h : σW ≫ B.inclusion.map W.hom = tb) :
    geometricPointMap (yoneda.map g) (geometricPointOfSpecHom B S hS U hΩ tb σ hσ) =
      geometricPointOfSpecHom B S hS W hΩ tb σW h := by
  subst hσW; rfl

/-- The geometric evaluation is compatible with an equality of geometric points: two equal
geometric points of a presheaf have equal étale local rings and equal fields, and the
evaluations agree under the transport. -/
theorem geometricEval_eqToHom_cast {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z₁ z₂ : GeometricPoint B S hS F} (h : z₁ = z₂)
    (t : ↥(etaleLocalRing B S hS F z₁)) (Ω : Type u)
    (c₁ : z₁.val.carrier = Ω) (c₂ : z₂.val.carrier = Ω) :
    cast c₂ (geometricEval B S hS F z₂
        ((eqToHom (congrArg (etaleLocalRing B S hS F) h)).hom t)) =
      cast c₁ (geometricEval B S hS F z₁ t) := by
  subst h; simp

/-- Let `x̄` be a geometric point of an algebraic space `X`, let `V` be a small étale
neighbourhood of `x̄` and let `W` be a Zariski open of its chart containing the point `u` under
`x̄`. Then evaluating at `x̄` the image under the canonical map `𝒪_{U, u} → 𝒪_{X, x̄}` of
Stacks 05VP of the germ at `u` of a regular function on `W` is restricting that function along
the chosen lift of `x̄`. -/
theorem geometricEval_chartLocalRingToEtaleLocalRing_germ
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {x : GeometricPoint B S hS X} (V : SmallEtaleNeighborhood x)
    (W : (chartScheme V.chart).Opens) (hw : chartPoint B S hS X V ∈ W)
    (hle : (⊤ : ((BigFppfOver.toScheme B S hS).obj x.val.siteObject).Opens) ≤
      (BigFppfOver.toScheme B S hS).map V.point ⁻¹ᵁ W)
    (a : Γ(chartScheme V.chart, W)) :
    geometricEval B S hS X x
        (chartLocalRingToEtaleLocalRing B S hS X hX V
          ((chartScheme V.chart).presheaf.germ W (chartPoint B S hS X V) hw a)) =
      (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).hom.hom
        ((((BigFppfOver.toScheme B S hS).map V.point).appLE W ⊤ hle).hom a) := by
  refine (congrArg (geometricEval B S hS X x)
    (chartLocalRingToEtaleLocalRing_germ_open B S hS hX V W hw a)).trans ?_
  refine (geometricEval_etaleLocalRingGerm B S hS X x
    (chartOpenNeighborhood B S hS V W hw)
    (show (structurePresheaf B S hS X).obj
      (op (chartOpenNeighborhood B S hS V W hw).chart) from W.topIso.inv a)).trans ?_
  change (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).hom.hom
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (chartOpenNeighborhood B S hS V W hw).point).op).hom (W.topIso.inv a)) = _
  refine congrArg (Scheme.ΓSpecIso (CommRingCat.of x.val.carrier)).hom.hom ?_
  have hτ : (BigFppfOver.toScheme B S hS).map
        (chartOpenNeighborhood B S hS V W hw).point ≫ W.ι =
      (BigFppfOver.toScheme B S hS).map V.point :=
    chartOpenLift_comp B S hS V W hw
  have hiota : (W.topIso.inv : Γ(chartScheme V.chart, W) ⟶ Γ(W.toScheme, ⊤)) =
      W.ι.appLE W ⊤ W.ι_preimage_self.ge := by
    simp only [Scheme.Opens.ι_appLE]
    rfl
  have hetop : (⊤ : ((BigFppfOver.toScheme B S hS).obj x.val.siteObject).Opens) =
      (BigFppfOver.toScheme B S hS).map
        (chartOpenNeighborhood B S hS V W hw).point ⁻¹ᵁ ⊤ := by
    simp
  have hcomp := Scheme.Hom.appLE_comp_appLE
    ((BigFppfOver.toScheme B S hS).map (chartOpenNeighborhood B S hS V W hw).point) W.ι
    W ⊤ ⊤ W.ι_preimage_self.ge hetop.le
  have hcomp' := hcomp.trans (appLE_of_eq hτ _ hle)
  have hval := congrArg (fun k : Γ(chartScheme V.chart, W) ⟶ _ => k.hom a) hcomp'
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at hval
  rw [appLE_top_top] at hval
  exact Eq.trans (congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (chartOpenNeighborhood B S hS V W hw).point).op).hom
    (congrArg (fun k : Γ(chartScheme V.chart, W) ⟶ Γ(W.toScheme, ⊤) => k.hom a) hiota)) hval

end Space

end AlgebraicGeometry

end
