module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentZariskiChartH1
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartComparisonGeometric
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageChartRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedEpsilonNaiveCotangentMap
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.RepresentableLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartToBase

/-!
# The bottom edge of the square of Stacks 0D0X on sections over a chart

Step M3 of the proof of Stacks 0D0X: the bottom edge `f_0^{-1}𝒪_{Y₀} ⟶ ε_*f⁻¹𝒪_Y` of the square of
`AlgebraicGeometry.Space.representedEpsilonNaiveCotangentPushforwardMap`, read on sections over
Zariski opens `Z ⊆ f_0^{-1}W`, against the unit of `f⁻¹ ⊣ f_*` on the chart diagram of
`Z ⊆ f_0^{-1}W`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_homEquiv_mate_inv`: units across a square of
  adjunctions and the mate of the square.
* `AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct_unit`: on underlying sheaves of sets,
  the Zariski unit followed by the bottom edge, read through the square of Stacks 08GH, is the
  structure map of `ε_Y` followed by the étale unit.
* `AlgebraicGeometry.Space.chartComparison_fMapEquivPushforwardHom_ringUniverse`: the chart
  correspondence read through the chart comparison at the base-changed chart.
* `AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct_app_inverseImageSections`: step M3,
  the canonical map `𝒪_{Y₀}(W) ⟶ (f_0^{-1}𝒪_{Y₀})(Z)` followed by the bottom edge over `Z` is the
  unit of `f⁻¹ ⊣ f_*` on the chart diagram of `Z ⊆ f_0^{-1}W` after the structure map of `ε_Y`.
* `AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct_app_inverseImageSections_eq_map` and
  `AlgebraicGeometry.Space.representedEpsilonSiteSquare_inv_baseRingAdjunct_unit_app`: the Zariski
  and étale halves of the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒴₀ : Type u₁} [Category.{v₁} 𝒴₀] {𝒳₀ : Type u₂} [Category.{v₂} 𝒳₀]
  {𝒳 : Type u₃} [Category.{v₃} 𝒳] {𝒴 : Type u₄} [Category.{v₄} 𝒴]

/-- **A unit across a square of adjunctions.**  Let `L₀ ⊣ R₀`, `Lx ⊣ Rx`, `Ly ⊣ Ry` and
`Lf ⊣ Rf` be adjunctions forming a square `Rx ⋙ R₀ ≅ Rf ⋙ Ry` of right adjoints, and let `m` be
the mate `Ly ⋙ Lf ≅ L₀ ⋙ Lx`.  For `σ : Ly O₀ ⟶ O`, the unit of `L₀ ⊣ R₀` followed by `R₀` of
the adjunct under `Lx ⊣ Rx` of `m⁻¹ ≫ Lf σ`, read through the square, is the adjunct of `σ`
under `Ly ⊣ Ry` followed by `Ry` of the unit of `Lf ⊣ Rf`. -/
theorem unit_comp_map_homEquiv_mate_inv {L₀ : 𝒴₀ ⥤ 𝒳₀} {R₀ : 𝒳₀ ⥤ 𝒴₀} {Lx : 𝒳₀ ⥤ 𝒳}
    {Rx : 𝒳 ⥤ 𝒳₀} {Ly : 𝒴₀ ⥤ 𝒴} {Ry : 𝒴 ⥤ 𝒴₀} {Lf : 𝒴 ⥤ 𝒳} {Rf : 𝒳 ⥤ 𝒴}
    (a₀ : L₀ ⊣ R₀) (ax : Lx ⊣ Rx) (ay : Ly ⊣ Ry) (af : Lf ⊣ Rf) (e : Rx ⋙ R₀ ≅ Rf ⋙ Ry)
    (O₀ : 𝒴₀) (O : 𝒴) (σ : Ly.obj O₀ ⟶ O) :
    a₀.unit.app O₀ ≫ R₀.map (ax.homEquiv _ _
        ((leftAdjointUniq ((ay.comp af).ofNatIsoRight e.symm) (a₀.comp ax)).inv.app O₀ ≫
          Lf.map σ)) ≫ e.hom.app (Lf.obj O) =
      ay.homEquiv _ _ σ ≫ Ry.map (af.unit.app O) := by
  have hm := homEquiv_leftAdjointUniq_hom_app ((ay.comp af).ofNatIsoRight e.symm)
    (a₀.comp ax) O₀
  set m := leftAdjointUniq ((ay.comp af).ofNatIsoRight e.symm) (a₀.comp ax)
  have h1 : a₀.unit.app O₀ ≫ R₀.map (ax.homEquiv _ _ (m.inv.app O₀ ≫ Lf.map σ)) =
      (a₀.comp ax).homEquiv _ _ (m.inv.app O₀ ≫ Lf.map σ) := by
    rw [comp_homEquiv, Equiv.trans_apply, a₀.homEquiv_unit]
  have h2 : (a₀.comp ax).homEquiv _ _ (m.inv.app O₀ ≫ Lf.map σ) =
      ((ay.comp af).ofNatIsoRight e.symm).homEquiv _ _ (Lf.map σ) := by
    rw [(a₀.comp ax).homEquiv_unit, ← hm,
      ← Adjunction.homEquiv_naturality_right, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, h1, h2, homEquiv_ofNatIsoRight_apply, Category.assoc, Iso.symm_hom,
    Iso.inv_hom_id_app, Category.comp_id, comp_homEquiv, Equiv.trans_apply,
    af.homEquiv_unit]
  exact (congrArg (ay.homEquiv _ _) (af.unit_naturality σ)).trans
    (ay.homEquiv_naturality_right _ _)

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

universe u₀

section ChartCorrespondence

variable (B : BigFppfSite.{u₀}) (S : Scheme.{u₀}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The chart correspondence read through the chart comparison.**  For a representable
`f : X ⟶ Y`, an `f`-map `ξ` and an étale scheme chart `V` of `Y`, the section over `V` of the
homomorphism into the direct image attached to `ξ` by Stacks 03G8, read over the base-changed
chart `X ×_Y V` through `AlgebraicGeometry.Space.chartComparison`, is the component of `ξ` at the
chart diagram of the base-changed chart. -/
theorem chartComparison_fMapEquivPushforwardHom_ringUniverse (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom)
    (P : Sheaf (SmallEtale.topology B S hS X.1) (Type u₀))
    (Q : Sheaf (SmallEtale.topology B S hS Y.1) (Type u₀))
    (ξ : FMap B S hS X.1 Y.1 f.hom P.obj Q.obj) (V : SmallEtale B S hS Y.1)
    (s : Q.obj.obj (op V)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((chartComparison B S hS f hf).hom.app P).hom.app (op V)
        ((fMapEquivPushforwardHom_ringUniverse B S hS f P Q ξ).hom.app (op V) s) =
      ξ.app (chartDiagramOfIndex B S hS f V (smallBaseChangeIndex B S hS f hf V)) s := by
  let := isContinuous_smallBaseChange B S hS f hf
  let H := (smallEtaleComparisonRestriction B S hS X).objPreimage P
  let i : P ≅ (smallEtaleComparisonRestriction B S hS X).obj H :=
    ((smallEtaleComparisonRestriction B S hS X).objObjPreimageIso P).symm
  let d := chartDiagramOfIndex B S hS f V (smallBaseChangeIndex B S hS f hf V)
  have hlift : (smallBaseChangeComparisonIso B S hS f hf V).hom = chartLift B S hS f d :=
    chartLift_unique B S hS f d _
      (yoneda_map_chartBaseChangeMap B S hS f V (smallBaseChangeIndex B S hS f hf V)).symm
  have hc := fMapEquivPushforwardHom_ringUniverse_chart B S hS f P Q H i ξ d
    (chartLift B S hS f d) (heq_of_eq (congrArg (fun q ↦ q.hom) (chartLift_projection B S hS f d)))
    s
  have hp := congrArg (fun m ↦ m.hom.app (op V)
      ((fMapEquivPushforwardHom_ringUniverse B S hS f P Q ξ).hom.app (op V) s))
    (chartComparison_hom_app_of_presentation B S hS f hf P H i)
  have hinj : Function.Injective (i.hom.hom.app (op d.U)) := fun a b hab ↦
    (congrFun (congrArg (fun m ↦ m.hom.app (op d.U)) i.hom_inv_id) a).symm.trans
      ((congrArg (i.inv.hom.app (op d.U)) hab).trans
        (congrFun (congrArg (fun m ↦ m.hom.app (op d.U)) i.hom_inv_id) b))
  refine hinj ?_
  refine hp.trans (Eq.trans ?_ hc.symm)
  exact congrArg (fun h ↦ H.obj.map h.op _) hlift

/-- The chart correspondence carries the unit on charts to the unit of `f⁻¹ ⊣ f_*` on the
underlying sheaf of sets of `𝒪_Y`. -/
theorem fMapEquivPushforwardHom_ringUniverse_inverseImageUnitFMap (f : X ⟶ Y) :
    fMapEquivPushforwardHom_ringUniverse B S hS f
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
        (inverseImageUnitFMap B S hS f) =
      (smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app
        ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O) :=
  (Equiv.apply_symm_apply _ _).trans
    (Stacks.Sheaves.ToposPushforward.forgetRing_map_commRingImageAdjunction_unit_app
      (smallEtaleRingedTopos B S hS Y)
      (smallEtaleRingedToposHom B S hS f).toToposHom)

/-- **The unit of `f⁻¹ ⊣ f_*` read through the chart comparison is the unit on charts** at the
chart diagram of the base-changed chart, for a representable `f`. -/
theorem chartComparison_inverseImageUnit (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (s : ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op V)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((chartComparison B S hS f hf).hom.app
        ((smallEtaleRingedTopos B S hS X).forgetRing.obj
          (inverseImageStructureSheaf B S hS f))).hom.app (op V)
        (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O)).hom.app (op V) s) =
      (inverseImageUnitFMap B S hS f).app
        (chartDiagramOfIndex B S hS f V (smallBaseChangeIndex B S hS f hf V)) s := by
  let := isContinuous_smallBaseChange B S hS f hf
  have hE := fMapEquivPushforwardHom_ringUniverse_inverseImageUnitFMap B S hS f
  have hL := chartComparison_fMapEquivPushforwardHom_ringUniverse B S hS f hf
    ((smallEtaleRingedTopos B S hS X).forgetRing.obj (inverseImageStructureSheaf B S hS f))
    ((smallEtaleRingedTopos B S hS Y).forgetRing.obj (smallEtaleRingedTopos B S hS Y).O)
    (inverseImageUnitFMap B S hS f) V s
  rw [hE] at hL
  exact hL

/-- The unit on charts as a ring homomorphism acts as the unit on charts. -/
theorem inverseImageChartUnitRingHom_apply (f : X ⟶ Y)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom)
    (s : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    inverseImageChartUnitRingHom B S hS f d s = (inverseImageUnitFMap B S hS f).app d s :=
  rfl

/-- `AlgebraicGeometry.Space.chartComparison_inverseImageUnit` with the sheaf of sets underlying
`f⁻¹𝒪_Y` written as the inverse image of the sheaf of sets underlying `𝒪_Y`. -/
theorem chartComparison_inverseImage_unit (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS Y.1)
    (s : ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
      (smallEtaleRingedTopos B S hS Y).O).obj.obj (op V)) :
    letI := isContinuous_smallBaseChange B S hS f hf
    ((chartComparison B S hS f hf).hom.app
        ((smallEtaleRingedToposHom B S hS f).toToposHom.inverseImage.obj
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O))).hom.app (op V)
        (((smallEtaleRingedToposHom B S hS f).toToposHom.adj.unit.app
          ((smallEtaleRingedTopos B S hS Y).forgetRing.obj
            (smallEtaleRingedTopos B S hS Y).O)).hom.app (op V) s) =
      (inverseImageUnitFMap B S hS f).app
        (chartDiagramOfIndex B S hS f V (smallBaseChangeIndex B S hS f hf V)) s :=
  chartComparison_inverseImageUnit B S hS f hf V s

variable {f : X ⟶ Y}

/-- An `f`-map at a precomposed chart diagram is restriction of its value at the diagram. -/
theorem FMap.app_precomp {P : (SmallEtale B S hS X.1)ᵒᵖ ⥤ Type*}
    {Q : (SmallEtale B S hS Y.1)ᵒᵖ ⥤ Type*} (ξ : FMap B S hS X.1 Y.1 f.hom P Q)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) {U' : SmallEtale B S hS X.1} (k : U' ⟶ d.U)
    (s : Q.obj (op d.V)) :
    ξ.app (d.precomp B S hS k) s = P.map k.op (ξ.app d s) :=
  (congrArg (ξ.app (d.precomp B S hS k)) (Q.map_id_apply _ s).symm).trans
    (ξ.naturality d (d.precomp B S hS k) k (𝟙 d.V) (Category.comp_id _).symm s)

end ChartCorrespondence

/-- The restriction maps of the restriction of a sheaf of commutative rings along a continuous
functor, on elements, are those of the sheaf of sets underlying the sheaf. -/
theorem _root_.CategoryTheory.Functor.sheafPushforwardContinuous_obj_map_apply
    {C D : Type*} [Category C] [Category D] {J : GrothendieckTopology C}
    {K : GrothendieckTopology D} (G : C ⥤ D) [G.IsContinuous J K]
    [K.HasSheafCompose (forget CommRingCat.{u₀})] (F : Sheaf K CommRingCat.{u₀}) {A A' : Cᵒᵖ}
    (g : A ⟶ A') (x : ToType (F.obj.obj (G.op.obj A))) :
    ConcreteCategory.hom (((G.sheafPushforwardContinuous CommRingCat.{u₀} J K).obj F).obj.map g)
        x = ((sheafCompose K (forget CommRingCat.{u₀})).obj F).obj.map (G.op.map g) x :=
  rfl

/-- The action of a natural isomorphism on pushforward functors of sheaves of sets, on
sections. -/
theorem _root_.CategoryTheory.Functor.sheafPushforwardContinuousIso_hom_app_hom_app_apply
    {C D : Type*} [Category C] [Category D] {F F' : C ⥤ D} (e : F ≅ F')
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [F.IsContinuous J K]
    [F'.IsContinuous J K] (G : Sheaf K (Type u₀)) (A : Cᵒᵖ) (z : G.obj.obj (F.op.obj A)) :
    ((Functor.sheafPushforwardContinuousIso e (Type u₀) J K).hom.app G).hom.app A z =
      G.obj.map (e.inv.app A.unop).op z :=
  rfl

/-- Restricting along `h ≫ e.hom` a section restricted along `e.inv` is restricting along `h`. -/
theorem map_op_comp_hom_map_inv_op {C : Type*} [Category C] (P : Cᵒᵖ ⥤ Type*) {A B Z' : C}
    (e : A ≅ B) (h : Z' ⟶ A) (x : P.obj (op A)) :
    P.map (h ≫ e.hom).op (P.map e.inv.op x) = P.map h.op x := by
  rw [← Functor.map_comp_apply, ← op_comp, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- `map_op_comp_hom_map_inv_op` for the components of a natural isomorphism. -/
theorem map_op_comp_hom_app_map_inv_app_op {C D : Type*} [Category C] [Category D]
    (P : Dᵒᵖ ⥤ Type*) {F G : C ⥤ D} (e : F ≅ G) (W : C) {Z' : D} (h : Z' ⟶ F.obj W)
    (x : P.obj (op (F.obj W))) :
    P.map (h ≫ e.hom.app W).op (P.map (e.inv.app W).op x) = P.map h.op x :=
  map_op_comp_hom_map_inv_op P (e.app W) h x

/-- The canonical map `𝒪_Y(V) ⟶ (f⁻¹𝒪_Y)(U)` of an inclusion `U ⊆ f⁻¹V` of Zariski opens is the
unit of `f⁻¹ ⊣ f_*` on underlying sheaves of sets over `V`, followed by restriction. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.inverseImageSections_hom_apply {X' Y' : Scheme.{u₀}}
    (f : X' ⟶ Y') {U' : X'.Opens} {V' : Y'.Opens} (e : U' ≤ f ⁻¹ᵁ V') (t : Γ(Y', V')) :
    (Scheme.Hom.inverseImageSections f e).hom t =
      (Scheme.Hom.zariskiInverseImageStructureSheaf f).obj.map (homOfLE e).op
        ((f.zariskiRingedToposHom.toToposHom.adj.unit.app
          (Y'.zariskiRingedTopos.forgetRing.obj Y'.zariskiRingedTopos.O)).hom.app (op V') t) :=
  congrArg (fun y ↦ (Scheme.Hom.zariskiInverseImageStructureSheaf f).obj.map (homOfLE e).op y)
    (congrArg (fun m ↦ m.hom.app (op V') t)
      (Stacks.Sheaves.ToposPushforward.forgetRing_map_commRingImageAdjunction_unit_app
        Y'.zariskiRingedTopos f.zariskiRingedToposHom.toToposHom))

open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe u v₁' u₁' v₂' u₂' v₃' u₃' v₄' u₄' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U V : BigFppfOver B S hS}
  (φ : U ⟶ V)

section General

variable {A' : RingedTopos.{v₁', u₁', w'}} {B' : RingedTopos.{v₂', u₂', w'}}
  {C' : RingedTopos.{v₃', u₃', w'}} {D' : RingedTopos.{v₄', u₄', w'}}
  [A'.J.HasSheafCompose (forget RingCat.{w'})] [B'.J.HasSheafCompose (forget RingCat.{w'})]
  [C'.J.HasSheafCompose (forget RingCat.{w'})] [D'.J.HasSheafCompose (forget RingCat.{w'})]
  [A'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [B'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [C'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [D'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- On underlying sheaves of sets the inverse of the ring-level mate is the inverse of the
mate. -/
theorem _root_.AlgebraicGeometry.RingedToposHom.forgetRing_map_inverseImageCommRingMate_inv
    (f g : AlgebraicGeometry.RingedToposHom A' B')
    (e : f.toToposHom.pushforward ≅ g.toToposHom.pushforward) :
    A'.forgetRing.map ((AlgebraicGeometry.RingedToposHom.inverseImageCommRingMate f g e).inv.app
        B'.O) =
      (AlgebraicGeometry.RingedToposHom.inverseImageMate f g e).inv.app (B'.forgetRing.obj B'.O) :=
  rfl

/-- **An identification of inverse images across a square, on underlying sheaves of sets.**  For
a square `f₀ ∘ εX`, `εY ∘ f` of morphisms of ringed topoi and an isomorphism `e` of the direct
images of the two composites, the composite of the comparison of iterated inverse images, the
inverse of the ring-level mate of `e`, the inverse comparison and `f⁻¹σ` is, after forgetting the
ring operations, the inverse of the mate of `e` followed by `f⁻¹` of `σ`. -/
theorem _root_.AlgebraicGeometry.RingedToposHom.forgetRing_map_inverseImageCommRingComp_mate_comp
    (F₀ : AlgebraicGeometry.RingedToposHom B' C') (εX : AlgebraicGeometry.RingedToposHom A' B')
    (εY : AlgebraicGeometry.RingedToposHom D' C') (f : AlgebraicGeometry.RingedToposHom A' D')
    (e : (F₀.comp εX).toToposHom.pushforward ≅ (εY.comp f).toToposHom.pushforward)
    (σ : (inverseImageCommRingFunctor εY.toToposHom).obj C'.O ⟶ D'.O) :
    A'.forgetRing.map ((inverseImageCommRingComp F₀.toToposHom εX.toToposHom).hom.app C'.O ≫
        (AlgebraicGeometry.RingedToposHom.inverseImageCommRingMate (F₀.comp εX) (εY.comp f)
          e).inv.app C'.O ≫
        (inverseImageCommRingComp εY.toToposHom f.toToposHom).inv.app C'.O ≫
        (inverseImageCommRingFunctor f.toToposHom).map σ) =
      (AlgebraicGeometry.RingedToposHom.inverseImageMate (F₀.comp εX) (εY.comp f) e).inv.app
          (C'.forgetRing.obj C'.O) ≫
        f.toToposHom.inverseImage.map (D'.forgetRing.map σ) := by
  have h1 := forget_map_inverseImageCommRingComp_hom F₀.toToposHom εX.toToposHom C'.O
  have h2 := forget_map_inverseImageCommRingComp_inv εY.toToposHom f.toToposHom C'.O
  have h3 := inverseImageCommRingFunctor_map_forget f.toToposHom σ
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, h3]
  rw [h1, h2, AlgebraicGeometry.RingedToposHom.forgetRing_map_inverseImageCommRingMate_inv]
  exact (Category.id_comp _).trans (congrArg (fun k => _ ≫ k) (Category.id_comp _))

end General

/-- **The bottom edge before transposition, on underlying sheaves of sets**: forgetting the ring
operations, `AlgebraicGeometry.Space.representedEpsilonBaseRingMap` is the inverse of the mate of
the square of Stacks 08GH followed by `f⁻¹` of the structure map of `ε_Y`. -/
theorem forgetRing_map_representedEpsilonBaseRingMap :
    (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.map
        (representedEpsilonBaseRingMap B S hS φ) =
      (AlgebraicGeometry.RingedToposHom.inverseImageMate
            (representedZariskiEpsilonCompLeft B S hS φ)
            (representedZariskiEpsilonCompRight B S hS φ)
            (representedEpsilonPushforwardIso B S hS φ)).inv.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O) ≫
        (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS φ)).toToposHom.inverseImage.map
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.map
            (representedZariskiStructureSharpInverseImage B S hS V)) :=
  (congrArg (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.map
    (representedEpsilonBaseRingMap_eq B S hS φ)).trans
    (AlgebraicGeometry.RingedToposHom.forgetRing_map_inverseImageCommRingComp_mate_comp
      (representedZariskiSchemeHom B S hS φ) (representedToSchemeZariskiRingedToposHom B S hS U)
      (representedToSchemeZariskiRingedToposHom B S hS V)
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ))
      (representedEpsilonPushforwardIso B S hS φ)
      (representedZariskiStructureSharpInverseImage B S hS V))

/-- **The bottom edge on underlying sheaves of sets.**  Forgetting the ring operations,
`AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct` is the adjunct under `ε_X⁻¹ ⊣ ε_{X,*}`
of the inverse mate of the square of Stacks 08GH followed by `f⁻¹` of the structure map of
`ε_Y` in inverse-image form: the comparisons of iterated inverse images and the comparison of
the inverse image with restriction are identities on underlying sheaves of sets. -/
theorem forgetRing_map_representedEpsilonBaseRingAdjunct :
    ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
        (representedEpsilonBaseRingAdjunct B S hS φ) =
      (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom.adj.homEquiv _ _
        ((AlgebraicGeometry.RingedToposHom.inverseImageMate
            (representedZariskiEpsilonCompLeft B S hS φ)
            (representedZariskiEpsilonCompRight B S hS φ)
            (representedEpsilonPushforwardIso B S hS φ)).inv.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O) ≫
        (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS φ)).toToposHom.inverseImage.map
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.map
            (representedZariskiStructureSharpInverseImage B S hS V))) := by
  have h1 := forget_map_commRingImageAdjunction_homEquiv
      (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom _ _
      (representedEpsilonBaseRingMap B S hS φ)
  have h2 := ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map_comp
    ((commRingImageAdjunction
        (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom).homEquiv
      _ _ (representedEpsilonBaseRingMap B S hS φ))
    (@restrictionCommRingIso _ _ _ _ ((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.J
      (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J _ _
      (representedEpsilonFunctor B S hS U) (isContinuous_representedEpsilonFunctor B S hS U)
      ((inverseImageCommRingFunctor
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom).obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).hom
  refine h2.trans ?_
  refine (congrArg (fun k => k ≫ _) h1).trans ?_
  refine (Category.comp_id _).trans ?_
  refine congrArg
    ((representedToSchemeZariskiRingedToposHom B S hS U).toToposHom.adj.homEquiv _ _) ?_
  exact forgetRing_map_representedEpsilonBaseRingMap B S hS φ

/-- **The bottom edge after the Zariski unit is the étale unit, through the square of
Stacks 08GH.**  On underlying sheaves of sets on the Zariski site of `Y₀`, the unit
`𝒪_{Y₀} ⟶ f_{0,*}f_0^{-1}𝒪_{Y₀}` followed by `f_{0,*}` of the bottom edge
`AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct` and the identification
`f_{0,*}ε_{X,*} ≅ ε_{Y,*}f_*` of direct images is the structure map of `ε_Y` followed by
`ε_{Y,*}` of the unit `𝒪_Y ⟶ f_*f⁻¹𝒪_Y`. -/
theorem representedEpsilonBaseRingAdjunct_unit :
    (representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
        (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O) ≫
      (representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ)) ≫
      (representedEpsilonPushforwardIso B S hS φ).hom.app
        ((smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)) =
      AlgebraicGeometry.RingedToposHom.forgetFSharp
        (representedToSchemeZariskiRingedToposHom B S hS V) ≫
        (representedToSchemeZariskiRingedToposHom B S hS V).toToposHom.pushforward.map
          ((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS φ)).toToposHom.adj.unit.app
            ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
              (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)) :=
  (congrArg (fun k ↦ (representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
        (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O) ≫
      (representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map k ≫
      (representedEpsilonPushforwardIso B S hS φ).hom.app
        ((smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)))
    (forgetRing_map_representedEpsilonBaseRingAdjunct B S hS φ)).trans
  ((CategoryTheory.Adjunction.unit_comp_map_homEquiv_mate_inv
      (representedZariskiSchemeHom B S hS φ).toToposHom.adj
      (representedToSchemeZariskiRingedToposHom B S hS U).toToposHom.adj
      (representedToSchemeZariskiRingedToposHom B S hS V).toToposHom.adj
      (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS φ)).toToposHom.adj
      (representedEpsilonPushforwardIso B S hS φ)
      (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.map
        (representedZariskiStructureSharpInverseImage B S hS V))).trans
    (congrArg (fun k ↦ k ≫
        (representedToSchemeZariskiRingedToposHom B S hS V).toToposHom.pushforward.map
          ((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS φ)).toToposHom.adj.unit.app
            ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
              (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)))
      (AlgebraicGeometry.RingedToposHom.forgetFSharp_eq_homEquiv
        (representedToSchemeZariskiRingedToposHom B S hS V)).symm))

/-- `AlgebraicGeometry.Space.representedEpsilonBaseRingAdjunct_unit` on sections over a Zariski
open `W` of `Y₀`. -/
theorem representedEpsilonBaseRingAdjunct_unit_app
    (W : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (t : ToType ((((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj W)) :
    ((representedEpsilonPushforwardIso B S hS φ).hom.app
        ((smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
          ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
            (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O))).hom.app W
      (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app W
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app W t)) =
      ((representedToSchemeZariskiRingedToposHom B S hS V).toToposHom.pushforward.map
          ((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS φ)).toToposHom.adj.unit.app
            ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
              (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O))).hom.app W
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app W t) :=
  congrArg (fun m ↦ m.hom.app W t) (representedEpsilonBaseRingAdjunct_unit B S hS φ)

/-- The direct-image comparison of the square of Stacks 08GH at any sheaf: the comparison of the
square of sites followed by the right-hand comparison backwards. -/
theorem representedEpsilonPushforwardIso_hom_app_eq
    (P : Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J (Type u)) :
    (representedEpsilonPushforwardIso B S hS φ).hom.app P =
      (Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J).hom.app P ≫
        (representedZariskiEpsilonCompRightIso B S hS φ).inv.app P := by
  have h1 := congrArg (fun m ↦ NatTrans.app m P)
    (Iso.trans_hom (representedZariskiEpsilonCompLeftIso B S hS φ)
      (Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J ≪≫
        (representedZariskiEpsilonCompRightIso B S hS φ).symm))
  have h2 := congrArg (fun m ↦ NatTrans.app m P)
    (Iso.trans_hom
      (Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
          ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J)
        (representedZariskiEpsilonCompRightIso B S hS φ).symm)
  exact h1.trans ((Category.id_comp _).trans h2)

/-- The direct-image comparison of the square of Stacks 08GH followed by the right-hand
comparison is the comparison of the square of sites. -/
theorem representedEpsilonPushforwardIso_hom_app_comp_compRightIso_hom_app
    (P : Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J (Type u)) :
    (representedEpsilonPushforwardIso B S hS φ).hom.app P ≫
        (representedZariskiEpsilonCompRightIso B S hS φ).hom.app P =
      (Functor.sheafPushforwardContinuousIso (representedEpsilonSiteSquare B S hS φ) (Type u)
        ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.J
        (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J).hom.app P := by
  refine (congrArg (· ≫ (representedZariskiEpsilonCompRightIso B S hS φ).hom.app P)
    (representedEpsilonPushforwardIso_hom_app_eq B S hS φ P)).trans ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    ((representedZariskiEpsilonCompRightIso B S hS φ).inv_hom_id_app P)).trans
      (Category.comp_id _))

/-- The right-hand comparison of the square of Stacks 08GH on sections over a Zariski open `W`
of `Y₀` is the chart comparison over the étale chart of `Y` cut out by `W`, for every sheaf. -/
theorem representedZariskiEpsilonCompRightIso_hom_app_app
    (P : Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J (Type u))
    (Oop : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (x : ((representedZariskiEpsilonCompRight B S hS φ).toToposHom.pushforward.obj P).obj.obj
      Oop) :
    (((representedZariskiEpsilonCompRightIso B S hS φ).hom.app P).hom.app Oop) x =
      (((chartComparison B S hS (representedSpaceMap B S hS φ)
          (relativelyRepresentable_yoneda_map B S hS φ)).hom.app P).hom.app
        (op ((representedEpsilonFunctor B S hS V).obj Oop.unop))) x :=
  rfl

/-- The direct-image comparison of the square of Stacks 08GH followed by the right-hand
comparison, on sections over a Zariski open `W` of `Y₀`: restriction along the square of sites. -/
theorem representedZariskiEpsilonCompRightIso_hom_app_pushforwardIso_hom_app_apply
    (P : Sheaf (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).J (Type u))
    (W : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (x : ((representedZariskiEpsilonCompLeft B S hS φ).toToposHom.pushforward.obj P).obj.obj W) :
    ((representedZariskiEpsilonCompRightIso B S hS φ).hom.app P).hom.app W
        (((representedEpsilonPushforwardIso B S hS φ).hom.app P).hom.app W x) =
      P.obj.map ((representedEpsilonSiteSquare B S hS φ).inv.app W.unop).op x :=
  congrArg (fun m ↦ m.hom.app W x)
    (representedEpsilonPushforwardIso_hom_app_comp_compRightIso_hom_app B S hS φ P)

/-- **The bottom edge after the Zariski unit, over the base-changed chart.**  On sections over a
Zariski open `W` of `Y₀`, the section `f_{0,*}ψ(u₀(t))` read over the base-changed chart through
the square of sites is the chart comparison of the étale unit of `ε_Y^♯(t)`. -/
theorem representedEpsilonSiteSquare_baseRingAdjunct_unit
    (W : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (t : ToType ((((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj W)) :
    ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map
        ((representedEpsilonSiteSquare B S hS φ).inv.app W.unop).op
      (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app W
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app W t)) =
      ((chartComparison B S hS (representedSpaceMap B S hS φ)
          (relativelyRepresentable_yoneda_map B S hS φ)).hom.app ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O))).hom.app
        (op ((representedEpsilonFunctor B S hS V).obj W.unop))
        (((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS φ)).toToposHom.adj.unit.app
            ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
              (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).hom.app
          (op ((representedEpsilonFunctor B S hS V).obj W.unop))
          ((AlgebraicGeometry.RingedToposHom.forgetFSharp
            (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app W t)) := by
  have h3 := representedEpsilonBaseRingAdjunct_unit_app B S hS φ W t
  have h4 := congrArg (((representedZariskiEpsilonCompRightIso B S hS φ).hom.app
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O))).hom.app W) h3
  have h5 := representedZariskiEpsilonCompRightIso_hom_app_pushforwardIso_hom_app_apply B S hS φ
    ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)) W
      (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app W
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app W t))
  exact h5.symm.trans h4

variable {Z : ((BigFppfOver.toScheme B S hS).obj U).Opens}
  {W : ((BigFppfOver.toScheme B S hS).obj V).Opens}

/-- **The chart diagram of a Zariski square.**  For Zariski opens `Z` of `X₀` and `W` of `Y₀`
with `Z ⊆ f_0^{-1}W`, the diagram of étale scheme charts over `h_φ` with upper chart `Z` and
lower chart `W`: the inclusion `Z ⊆ f_0^{-1}W`, read through the square of sites of
Stacks 08GH as a morphism into the base-changed chart `W ×_Y X`, followed by its projection to
`W`. -/
noncomputable abbrev representedEpsilonChartDiagram
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :
    ChartDiagram B S hS (representedAlgebraicSpace B S hS U).1
      (representedAlgebraicSpace B S hS V).1 (representedSpaceMap B S hS φ).hom :=
  (chartDiagramOfIndex B S hS (representedSpaceMap B S hS φ)
      ((representedEpsilonFunctor B S hS V).obj W)
      (smallBaseChangeIndex B S hS (representedSpaceMap B S hS φ)
        (relativelyRepresentable_yoneda_map B S hS φ)
        ((representedEpsilonFunctor B S hS V).obj W))).precomp B S hS
    ((representedEpsilonFunctor B S hS U).map (homOfLE hZW) ≫
      (representedEpsilonSiteSquare B S hS φ).hom.app W)

/-- `AlgebraicGeometry.Space.representedEpsilonChartDiagram` unfolded. -/
theorem representedEpsilonChartDiagram_eq
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W) :
    representedEpsilonChartDiagram B S hS φ hZW =
      (chartDiagramOfIndex B S hS (representedSpaceMap B S hS φ)
        ((representedEpsilonFunctor B S hS V).obj W)
        (smallBaseChangeIndex B S hS (representedSpaceMap B S hS φ)
          (relativelyRepresentable_yoneda_map B S hS φ)
          ((representedEpsilonFunctor B S hS V).obj W))).precomp B S hS
        ((representedEpsilonFunctor B S hS U).map (homOfLE hZW) ≫
          (representedEpsilonSiteSquare B S hS φ).hom.app W) :=
  rfl

/-- The Zariski half of step M3: the canonical map of `Z ⊆ f_0^{-1}W` followed by the bottom edge
over `Z` is the restriction to `Z` of the bottom edge over `f_0^{-1}W` after the Zariski unit. -/
theorem representedEpsilonBaseRingAdjunct_app_inverseImageSections_eq_map
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (t : Γ((BigFppfOver.toScheme B S hS).obj V, W)) :
    ((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom
        ((Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom t) =
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
          (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ))).obj.map
        ((representedEpsilonFunctor B S hS U).map (homOfLE hZW)).op
        (((representedEpsilonBaseRingAdjunct B S hS φ).hom.app
            (op ((BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W))).hom
            (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
              (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
                ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app
              (op W) t)) := by
  have s1 :=
        congrArg ((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom
          (Scheme.Hom.inverseImageSections_hom_apply _ hZW t)
  have s2 :=
        (NatTrans.naturality_apply (representedEpsilonBaseRingAdjunct B S hS φ).hom
          (homOfLE hZW).op
          (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
              (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
                ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app (op W) t))
  exact s1.trans s2

/-- `AlgebraicGeometry.Space.chartComparison_inverseImage_unit` for the represented morphism at
the étale chart of `Y` cut out by a Zariski open of `Y₀`, at the structure map of `ε_Y`. -/
theorem representedChartComparison_inverseImage_unit
    (W : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (t : ToType ((((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj W)) :
    ((chartComparison B S hS (representedSpaceMap B S hS φ)
          (relativelyRepresentable_yoneda_map B S hS φ)).hom.app ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O))).hom.app
        (op ((representedEpsilonFunctor B S hS V).obj W.unop))
        (((smallEtaleRingedToposHom B S hS
              (representedSpaceMap B S hS φ)).toToposHom.adj.unit.app
            ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
              (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).hom.app
          (op ((representedEpsilonFunctor B S hS V).obj W.unop))
          ((AlgebraicGeometry.RingedToposHom.forgetFSharp
            (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app W t)) =
      (inverseImageUnitFMap B S hS (representedSpaceMap B S hS φ)).app
        (chartDiagramOfIndex B S hS (representedSpaceMap B S hS φ)
          ((representedEpsilonFunctor B S hS V).obj W.unop)
          (smallBaseChangeIndex B S hS (representedSpaceMap B S hS φ)
            (relativelyRepresentable_yoneda_map B S hS φ)
            ((representedEpsilonFunctor B S hS V).obj W.unop)))
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
            (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app W t) :=
  chartComparison_inverseImage_unit B S hS (representedSpaceMap B S hS φ)
    (relativelyRepresentable_yoneda_map B S hS φ) _ _

/-- The étale half of step M3 over a Zariski open of `Y₀` given as an object of the Zariski
site. -/
theorem representedEpsilonSiteSquare_inv_baseRingAdjunct_unit_app
    (W' : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    (t : ToType ((((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj W')) :
    ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map
        ((representedEpsilonSiteSquare B S hS φ).inv.app W'.unop).op
        (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app W'
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
              (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
                ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app W' t)) =
      (inverseImageUnitFMap B S hS (representedSpaceMap B S hS φ)).app
        (chartDiagramOfIndex B S hS (representedSpaceMap B S hS φ)
          ((representedEpsilonFunctor B S hS V).obj W'.unop)
          (smallBaseChangeIndex B S hS (representedSpaceMap B S hS φ)
            (relativelyRepresentable_yoneda_map B S hS φ)
            ((representedEpsilonFunctor B S hS V).obj W'.unop)))
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
            (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app W' t) :=
  (representedEpsilonSiteSquare_baseRingAdjunct_unit B S hS φ W' t).trans
    (representedChartComparison_inverseImage_unit B S hS φ W' t)

/-- The section `f_{0,*}ψ(u₀(t))` of the sheaf of sets underlying `f⁻¹𝒪_Y`, restricted to a chart,
is the restricted section of the sheaf of rings `f⁻¹𝒪_Y`. -/
theorem representedEpsilonBaseRingAdjunct_unit_map_eq {A : SmallEtale B S hS (yoneda.obj U)}
    (g : A ⟶ (representedEpsilonFunctor B S hS U).obj
      ((BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W))
    (t : Γ((BigFppfOver.toScheme B S hS).obj V, W)) :
    ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map g.op
        (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app (op W)
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
              (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
                ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app (op W) t)) =
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
          (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ))).obj.map g.op
        (((representedEpsilonBaseRingAdjunct B S hS φ).hom.app
            (op ((BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W))).hom
            (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
              (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
                ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app (op W) t)) :=
  rfl

/-- The restriction maps of the inverse image of the sheaf of sets underlying `𝒪_Y` are those of
the sheaf of sets underlying `f⁻¹𝒪_Y`. -/
theorem representedInverseImage_map_eq {A A' : SmallEtale B S hS (yoneda.obj U)}
    (k : A ⟶ A')
    (y : ToType ((inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ)).obj.obj
      (op A'))) :
    ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map k.op y =
      ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS U)).forgetRing.obj
          (inverseImageStructureSheaf B S hS (representedSpaceMap B S hS φ))).obj.map k.op y :=
  rfl

/-- The Zariski half of step M3 read on the sheaf of sets `f⁻¹(𝒪_Y)`. -/
theorem representedEpsilonBaseRingAdjunct_app_inverseImageSections_eq_map'
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (t : Γ((BigFppfOver.toScheme B S hS).obj V, W)) :
    ((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom
        ((Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom t) =
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map
        ((representedEpsilonFunctor B S hS U).map (homOfLE hZW)).op
        (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app (op W)
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app (op W) t)) :=
  (representedEpsilonBaseRingAdjunct_app_inverseImageSections_eq_map B S hS φ hZW t).trans
    (representedEpsilonBaseRingAdjunct_unit_map_eq B S hS φ
      ((representedEpsilonFunctor B S hS U).map (homOfLE hZW)) t).symm

/-- The étale half of step M3, restricted along a morphism of étale charts into the chart of
`f_0^{-1}W'`. -/
theorem representedEpsilonBaseRingAdjunct_unit_map_eq_fMap
    (W' : ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.Cᵒᵖ)
    {A : SmallEtale B S hS (yoneda.obj U)}
    (g : A ⟶ (representedEpsilonCharts B S hS φ).obj W'.unop)
    (t : ToType ((((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
      ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O).obj.obj W')) :
    ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map g.op
        (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app W'
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app W' t)) =
      ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map
        (g ≫ (representedEpsilonSiteSquare B S hS φ).hom.app W'.unop).op
        ((inverseImageUnitFMap B S hS (representedSpaceMap B S hS φ)).app
          (chartDiagramOfIndex B S hS (representedSpaceMap B S hS φ)
          ((representedEpsilonFunctor B S hS V).obj W'.unop)
          (smallBaseChangeIndex B S hS (representedSpaceMap B S hS φ)
            (relativelyRepresentable_yoneda_map B S hS φ)
            ((representedEpsilonFunctor B S hS V).obj W'.unop)))
          ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app W' t)) :=
  (map_op_comp_hom_app_map_inv_app_op ((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj
    (representedEpsilonSiteSquare B S hS φ) W'.unop g
    (((representedZariskiSchemeHom B S hS φ).toToposHom.pushforward.map
        (((BigFppfOver.toScheme B S hS).obj U).zariskiRingedTopos.forgetRing.map
          (representedEpsilonBaseRingAdjunct B S hS φ))).hom.app W'
        (((representedZariskiSchemeHom B S hS φ).toToposHom.adj.unit.app
          (((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.forgetRing.obj
            ((BigFppfOver.toScheme B S hS).obj V).zariskiRingedTopos.O)).hom.app W' t))).symm.trans
    (congrArg (((smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS φ)).toToposHom.inverseImage.obj
        ((smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).forgetRing.obj
          (smallEtaleRingedTopos B S hS (representedAlgebraicSpace B S hS V)).O)).obj.map
        (g ≫ (representedEpsilonSiteSquare B S hS φ).hom.app W'.unop).op)
      (representedEpsilonSiteSquare_inv_baseRingAdjunct_unit_app B S hS φ W' t))

/-- **Step M3 of Stacks 0D0X: the bottom edge on a chart is the unit on charts.**  For Zariski
opens `Z ⊆ f_0^{-1}W`, the canonical map `𝒪_{Y₀}(W) ⟶ (f_0^{-1}𝒪_{Y₀})(Z)` followed by the bottom
edge `f_0^{-1}𝒪_{Y₀} ⟶ ε_*f⁻¹𝒪_Y` over `Z` is the structure map `𝒪_{Y₀}(W) ⟶ 𝒪_Y(W)` of `ε_Y`
followed by the unit of `f⁻¹ ⊣ f_*` on the chart diagram
`AlgebraicGeometry.Space.representedEpsilonChartDiagram`. -/
theorem representedEpsilonBaseRingAdjunct_app_inverseImageSections
    (hZW : Z ≤ (BigFppfOver.toScheme B S hS).map φ ⁻¹ᵁ W)
    (t : Γ((BigFppfOver.toScheme B S hS).obj V, W)) :
    ((representedEpsilonBaseRingAdjunct B S hS φ).hom.app (op Z)).hom
        ((Scheme.Hom.inverseImageSections ((BigFppfOver.toScheme B S hS).map φ) hZW).hom t) =
      inverseImageChartUnitRingHom B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW)
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app (op W) t) := by
  refine (representedEpsilonBaseRingAdjunct_app_inverseImageSections_eq_map'
    B S hS φ hZW t).trans ?_
  refine (representedEpsilonBaseRingAdjunct_unit_map_eq_fMap B S hS φ (op W)
    ((representedEpsilonFunctor B S hS U).map (homOfLE hZW)) t).trans ?_
  refine (representedInverseImage_map_eq B S hS φ
    ((representedEpsilonFunctor B S hS U).map (homOfLE hZW) ≫
        (representedEpsilonSiteSquare B S hS φ).hom.app W) _).trans ?_
  refine (FMap.app_precomp B S hS (inverseImageUnitFMap B S hS (representedSpaceMap B S hS φ))
        (chartDiagramOfIndex B S hS (representedSpaceMap B S hS φ)
          ((representedEpsilonFunctor B S hS V).obj W)
          (smallBaseChangeIndex B S hS (representedSpaceMap B S hS φ)
            (relativelyRepresentable_yoneda_map B S hS φ)
            ((representedEpsilonFunctor B S hS V).obj W)))
        ((representedEpsilonFunctor B S hS U).map (homOfLE hZW) ≫
          (representedEpsilonSiteSquare B S hS φ).hom.app W)
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app (op W) t)).symm.trans ?_
  exact (inverseImageChartUnitRingHom_apply B S hS (representedSpaceMap B S hS φ)
        (representedEpsilonChartDiagram B S hS φ hZW)
        ((AlgebraicGeometry.RingedToposHom.forgetFSharp
          (representedToSchemeZariskiRingedToposHom B S hS V)).hom.app (op W) t)).symm

end AlgebraicGeometry.Space
