module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartH1
public import StacksFrontier.RingTheory.NaiveCotangent.FilteredColimitKaehler

/-!
# Kähler differentials of a chart diagram, spread over the localized small étale site

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a commutative
diagram of étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R`
of `Y`, so that `A` is an `R`-algebra through the vertical morphism of `d`.  Write
`Ω = Ω_{A/R}`.  For an étale chart `U` of `X` over `V`, the square

```
R ──▸ (f⁻¹𝒪_Y)(U)
│          │
▼          ▼
A ──▸   𝒪_X(U)
```

made of the unit of `f⁻¹ ⊣ f_*` on charts and of restriction gives a map
`Ω ⟶ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`, `d a ↦ d a|_U`, and its `𝒪_X(U)`-linear extension

`σ_U : 𝒪_X(U) ⊗_A Ω ⟶ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`.

This file proves that `σ` is *locally bijective* on the small étale site of `X` localized at `V`:
an element of the target is, on a covering, in the image of `σ`, and an element killed by `σ`
vanishes on a covering.  This is the degree `0` analogue of
`StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartH1`, and the proof is the same: both
properties are checked at the geometric points, where `σ` becomes the base change map of Kähler
differentials along a square of filtered colimits of étale algebras, which is bijective; the
passage from the points back to coverings uses that Kähler differentials and tensor products
commute with the filtered colimits defining the stalks.

## Main definitions

* `AlgebraicGeometry.Space.chartKaehlerMap`: the map `Ω ⟶ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`.
* `AlgebraicGeometry.Space.chartKaehlerTensor`: its linear extension `σ_U`.
* `AlgebraicGeometry.Space.chartSectionsKaehlerRestrict`: restriction of the differentials of
  the sections along a morphism of charts over `V`.

## Main results

* `AlgebraicGeometry.Space.chartKaehlerTensor_restrict`: `σ` commutes with restriction.
* `AlgebraicGeometry.Space.chartKaehlerTensorLiftSieve_mem`: local surjectivity.
* `AlgebraicGeometry.Space.chartKaehlerTensorVanishingSieve_mem`: local injectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite Algebra
  TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- `Ω_{A/R}` for the chart diagram. -/
abbrev chartKaehler : Type u :=
  @KaehlerDifferential (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) _ _
    (chartDiagramAlgebraInst B S hS f d)

/-- `Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}` for a chart `U` over `V`. -/
abbrev chartSectionsKaehler (U : Over d.U) : Type u :=
  @KaehlerDifferential (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) _ _
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))

/-- **The map `Ω ⟶ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`** over a chart `U` over `V`. -/
abbrev chartKaehlerMap (U : Over d.U) :
    chartKaehler B S hS f d →+ chartSectionsKaehler B S hS f d U :=
  @Stacks.NaiveCotangent.kaehlerMapOfSquare _ _ _ _ _ _ _ _ (chartDiagramAlgebraInst B S hS f d)
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))
    (chartDiagramRestrictBase B S hS f d U) (chartDiagramRestrictO B S hS f d U)
    (chartSquare_comm B S hS f d U)

/-- **`σ_U : 𝒪_X(U) ⊗_A Ω ⟶ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}`.** -/
def chartKaehlerTensor (U : Over d.U) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[ToType
        ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d →+
      chartSectionsKaehler B S hS f d U :=
  @Stacks.NaiveCotangent.kaehlerBaseChangeOfSquare _ _ _ _ _ _ _ _
    (chartDiagramAlgebraInst B S hS f d)
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))
    (chartDiagramRestrictBase B S hS f d U) (chartDiagramRestrictO B S hS f d U)
    (chartSquare_comm B S hS f d U)

/-- The value of `σ_U` on a pure tensor. -/
theorem chartKaehlerTensor_tmul (U : Over d.U)
    (s : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
    (ω : chartKaehler B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
    chartKaehlerTensor B S hS f d U (s ⊗ₜ ω) = s • chartKaehlerMap B S hS f d U ω :=
  rfl

/-! ### Restriction -/

/-- **Restriction of the differentials of the sections** along a morphism `g : U₂ ⟶ U₁` of
charts over `V`: the map `Ω_{𝒪_X(U₁)/(f⁻¹𝒪_Y)(U₁)} → Ω_{𝒪_X(U₂)/(f⁻¹𝒪_Y)(U₂)}` induced by the
square of restriction maps. -/
def chartSectionsKaehlerRestrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁) :
    chartSectionsKaehler B S hS f d U₁ →+ chartSectionsKaehler B S hS f d U₂ :=
  @Stacks.NaiveCotangent.kaehlerMapOfSquare _ _ _ _ _ _ _ _
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left))
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left))
    ((inverseImageStructureSheaf B S hS f).obj.map g.left.op).hom
    ((smallEtaleRingedTopos B S hS X).O.obj.map g.left.op).hom
    (Stacks.SheafOfModules.sectionsSquare_comm _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g.left.op)

/-- Restriction of the differentials of the sections on generators. -/
theorem chartSectionsKaehlerRestrict_D {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (b : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U₁.left))) :
    letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
    letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
    chartSectionsKaehlerRestrict B S hS f d g (KaehlerDifferential.D _ _ b) =
      KaehlerDifferential.D _ _ ((smallEtaleRingedTopos B S hS X).O.obj.map g.left.op b) :=
  @Stacks.NaiveCotangent.kaehlerMapOfSquare_D _ _ _ _ _ _ _ _
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left))
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left))
    _ _ _ b

/-- Restriction of the differentials of the sections is semilinear over restriction. -/
theorem chartSectionsKaehlerRestrict_smul {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (b : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U₁.left)))
    (z : chartSectionsKaehler B S hS f d U₁) :
    chartSectionsKaehlerRestrict B S hS f d g (b • z) =
      (smallEtaleRingedTopos B S hS X).O.obj.map g.left.op b •
        chartSectionsKaehlerRestrict B S hS f d g z :=
  @Stacks.NaiveCotangent.kaehlerMapOfSquare_smul _ _ _ _ _ _ _ _
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left))
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left))
    _ _ _ b z

/-- Pasting two squares on Kähler differentials gives the map of any square with the pasted
ring maps. -/
private theorem kaehlerMapOfSquare_comp_eq {R S R' S' R'' S'' : Type*} [CommRing R] [CommRing S]
    [CommRing R'] [CommRing S'] [CommRing R''] [CommRing S''] [Algebra R S] [Algebra R' S']
    [Algebra R'' S''] {fR : R →+* R'} {fS : S →+* S'} {gR : R' →+* R''} {gS : S' →+* S''}
    {hR : R →+* R''} {hS : S →+* S''}
    {h : ∀ r, fS (algebraMap R S r) = algebraMap R' S' (fR r)}
    {h' : ∀ r, gS (algebraMap R' S' r) = algebraMap R'' S'' (gR r)}
    {h'' : ∀ r, hS (algebraMap R S r) = algebraMap R'' S'' (hR r)}
    (eR : ∀ r, gR (fR r) = hR r) (eS : ∀ s, gS (fS s) = hS s) (x : Ω[S⁄R]) :
    Stacks.NaiveCotangent.kaehlerMapOfSquare gR gS h'
        (Stacks.NaiveCotangent.kaehlerMapOfSquare fR fS h x) =
      Stacks.NaiveCotangent.kaehlerMapOfSquare hR hS h'' x :=
  (Stacks.NaiveCotangent.kaehlerMapOfSquare_comp _ _ _ _ _ _ x).trans
    (Stacks.NaiveCotangent.kaehlerMapOfSquare_congr _ _ (RingHom.ext eR) (RingHom.ext eS) x)

/-- Restriction of the differentials of the sections along a composite is the composite of the
restrictions. -/
theorem chartSectionsKaehlerRestrict_comp {U₁ U₂ U₃ : Over d.U} (g : U₂ ⟶ U₁) (k : U₃ ⟶ U₂)
    (z : chartSectionsKaehler B S hS f d U₁) :
    chartSectionsKaehlerRestrict B S hS f d (k ≫ g) z =
      chartSectionsKaehlerRestrict B S hS f d k (chartSectionsKaehlerRestrict B S hS f d g z) := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₃.left)
  exact (kaehlerMapOfSquare_comp_eq
    (fun r => (ConcreteCategory.congr_hom
      ((inverseImageStructureSheaf B S hS f).obj.map_comp g.left.op k.left.op) r).symm)
    (fun r => (ConcreteCategory.congr_hom
      ((smallEtaleRingedTopos B S hS X).O.obj.map_comp g.left.op k.left.op) r).symm) z).symm

/-- Restriction of the differentials of the sections along an identity is the identity. -/
theorem chartSectionsKaehlerRestrict_id (U : Over d.U) (z : chartSectionsKaehler B S hS f d U) :
    chartSectionsKaehlerRestrict B S hS f d (𝟙 U) z = z := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
  refine Eq.trans ?_ (Stacks.NaiveCotangent.kaehlerMapOfSquare_id z)
  exact Stacks.NaiveCotangent.kaehlerMapOfSquare_congr _ _
    (RingHom.ext fun r => ConcreteCategory.congr_hom
      ((inverseImageStructureSheaf B S hS f).obj.map_id (op U.left)) r)
    (RingHom.ext fun r => ConcreteCategory.congr_hom
      ((smallEtaleRingedTopos B S hS X).O.obj.map_id (op U.left)) r) z

/-- **The map `Ω ⟶ Ω_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)}` commutes with restriction.** -/
theorem chartKaehlerMap_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁) (ω : chartKaehler B S hS f d) :
    chartSectionsKaehlerRestrict B S hS f d g (chartKaehlerMap B S hS f d U₁ ω) =
      chartKaehlerMap B S hS f d U₂ ω := by
  let := chartDiagramAlgebraInst B S hS f d
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
  exact kaehlerMapOfSquare_comp_eq (chartDiagramRestrictBase_naturality B S hS f d g)
    (chartDiagramRestrictO_naturality B S hS f d g) ω

/-- Restriction of `𝒪_X(U) ⊗_A Ω` along a morphism of charts over `V`. -/
abbrev chartRestrictKaehlerTensor {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁) :=
  Point.restrictTensor (chartStructurePresheaf B S hS f d) (chartDiagramRestrictO B S hS f d)
    (chartDiagramRestrictO_map B S hS f d) (chartKaehler B S hS f d) g

/-- **`σ` commutes with restriction.** -/
theorem chartKaehlerTensor_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U₁
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U₁.left))) ⊗[ToType
        ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d) :
    chartSectionsKaehlerRestrict B S hS f d g (chartKaehlerTensor B S hS f d U₁ t) =
      chartKaehlerTensor B S hS f d U₂ (chartRestrictKaehlerTensor B S hS f d g t) := by
  let := chartDiagramAlgebraInst B S hS f d
  let := chartDiagramRestrictAlgebra B S hS f d U₁
  let := chartDiagramRestrictAlgebra B S hS f d U₂
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s ω =>
    rw [Point.restrictTensor_tmul, chartKaehlerTensor_tmul, chartKaehlerTensor_tmul]
    refine (chartSectionsKaehlerRestrict_smul B S hS f d g s _).trans ?_
    exact congrArg (_ • ·) (chartKaehlerMap_restrict B S hS f d g ω)
  | add a b ha hb =>
    simp only [map_add, ha, hb]

/-! ### At a geometric point -/

section Stalk

variable {x : GeometricPoint B S hS X.1} (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U)

/-- **The map `Ω ⟶ Ω_{𝒪_{X,x}/(f⁻¹𝒪_Y)_x}` at the point.** -/
abbrev chartStalkKaehlerMap :
    chartKaehler B S hS f d →+
      @KaehlerDifferential (ToType (chartBaseStalk B S hS f d p))
        (ToType (chartStructureStalk B S hS f d p)) _ _
        (chartStalkAlgebra B S hS f d p) :=
  @Stacks.NaiveCotangent.kaehlerMapOfSquare _ _ _ _ _ _ _ _ (chartDiagramAlgebraInst B S hS f d)
    (chartStalkAlgebra B S hS f d p) (chartBaseStalkGerm B S hS f d p)
    (chartStalkGerm B S hS f d p) (chartStalkSquare_comm B S hS f d p)

/-- The germ map on Kähler differentials at a lift of the point into a chart over `V`. -/
abbrev chartGermKaehler (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U) :
    chartSectionsKaehler B S hS f d U →+
      @KaehlerDifferential (ToType (chartBaseStalk B S hS f d p))
        (ToType (chartStructureStalk B S hS f d p)) _ _
        (chartStalkAlgebra B S hS f d p) :=
  @Stacks.NaiveCotangent.kaehlerMapOfSquare _ _ _ _ _ _ _ _
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))
    (chartStalkAlgebra B S hS f d p)
    ((chartStalkPoint B S hS f d p).toPresheafFiber U q (chartBasePresheaf B S hS f d)).hom
    ((chartStalkPoint B S hS f d p).toPresheafFiber U q (chartStructurePresheaf B S hS f d)).hom
    (fun a => (Point.toPresheafFiber_naturality_apply (chartStalkPoint B S hS f d p)
      (chartSharp B S hS f d) U q a).symm)

/-- The germ map on differentials after the map of a chart diagram is the map at the point. -/
theorem chartGermKaehler_chartKaehlerMap (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U) (ω : chartKaehler B S hS f d) :
    chartGermKaehler B S hS f d p U q (chartKaehlerMap B S hS f d U ω) =
      chartStalkKaehlerMap B S hS f d p ω := by
  let := chartDiagramAlgebraInst B S hS f d
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
  let := chartStalkAlgebra B S hS f d p
  refine kaehlerMapOfSquare_comp_eq ?_ ?_ ω
  · exact toPresheafFiber_chartDiagramRestrictBase B S hS f d p U q
  · exact toPresheafFiber_chartDiagramRestrictO B S hS f d p U q

/-- The germ map on `𝒪_X(U) ⊗_A Ω` at a lift of the point into a chart over `V`. -/
abbrev chartGermKaehlerTensor (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U) :=
  Point.germTensor (chartStalkPoint B S hS f d p) (chartStructurePresheaf B S hS f d)
    (chartDiagramRestrictO B S hS f d) (chartStalkGerm B S hS f d p)
    (toPresheafFiber_chartDiagramRestrictO B S hS f d p) (chartKaehler B S hS f d) U q

/-- **The base change map at the point**, `𝒪_{X,x} ⊗_A Ω ⟶ Ω_{𝒪_{X,x}/(f⁻¹𝒪_Y)_x}`. -/
abbrev chartStalkKaehlerBaseChange :
    letI := (chartStalkGerm B S hS f d p).toAlgebra
    (ToType (chartStructureStalk B S hS f d p)) ⊗[ToType
        ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d →+
      @KaehlerDifferential (ToType (chartBaseStalk B S hS f d p))
        (ToType (chartStructureStalk B S hS f d p)) _ _
        (chartStalkAlgebra B S hS f d p) :=
  @Stacks.NaiveCotangent.kaehlerBaseChangeOfSquare _ _ _ _ _ _ _ _
    (chartDiagramAlgebraInst B S hS f d) (chartStalkAlgebra B S hS f d p)
    (chartBaseStalkGerm B S hS f d p) (chartStalkGerm B S hS f d p)
    (chartStalkSquare_comm B S hS f d p)

/-- **`σ` at a point is the base change map of the point.** -/
theorem chartGermKaehler_chartKaehlerTensor (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[ToType
        ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d) :
    chartGermKaehler B S hS f d p U q (chartKaehlerTensor B S hS f d U t) =
      chartStalkKaehlerBaseChange B S hS f d p (chartGermKaehlerTensor B S hS f d p U q t) := by
  let := chartDiagramAlgebraInst B S hS f d
  let := chartDiagramRestrictAlgebra B S hS f d U
  let := (chartStalkGerm B S hS f d p).toAlgebra
  let := chartStalkAlgebra B S hS f d p
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s ω =>
    rw [chartKaehlerTensor_tmul, Point.germTensor_tmul,
      Stacks.NaiveCotangent.kaehlerBaseChangeOfSquare_tmul]
    refine (Stacks.NaiveCotangent.kaehlerMapOfSquare_smul _ _ _ s _).trans ?_
    exact congrArg (_ • ·) (chartGermKaehler_chartKaehlerMap B S hS f d p U q ω)
  | add a b ha hb =>
    simp only [map_add, ha, hb]

/-- **At the point, the base change map of differentials is bijective.** -/
theorem chartStalkKaehlerBaseChange_bijective
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective (chartStalkKaehlerBaseChange B S hS f d p) :=
  @Stacks.NaiveCotangent.bijective_kaehlerMapOfSquare_liftBaseChange_of_ind_etale
    _ _ _ _ _ _ _ _ (chartDiagramAlgebraInst B S hS f d) (chartStalkAlgebra B S hS f d p)
    (chartBaseStalkGerm B S hS f d p) (chartStalkGerm B S hS f d p)
    (chartStalkSquare_comm B S hS f d p) (chartBaseStalk_ind_etale B S hS f d p hW)
    (chartStalk_ind_etale B S hS f d p hU)

/-- The germ map on differentials is compatible with restriction. -/
theorem chartGermKaehler_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U₂) (z : chartSectionsKaehler B S hS f d U₁) :
    chartGermKaehler B S hS f d p U₂ q (chartSectionsKaehlerRestrict B S hS f d g z) =
      chartGermKaehler B S hS f d p U₁ ((chartStalkPoint B S hS f d p).fiber.map g q) z := by
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
  let := chartStalkAlgebra B S hS f d p
  refine kaehlerMapOfSquare_comp_eq ?_ ?_ z
  · exact Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) g q
      (chartBasePresheaf B S hS f d)
  · exact Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) g q
      (chartStructurePresheaf B S hS f d)

/-- **A differential with vanishing germ vanishes on a smaller neighbourhood.** -/
theorem exists_chartSectionsKaehlerRestrict_eq_zero (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U) (z : chartSectionsKaehler B S hS f d U)
    (hz : chartGermKaehler B S hS f d p U q z = 0) :
    ∃ (U' : Over d.U) (g : U' ⟶ U) (q' : (chartStalkPoint B S hS f d p).fiber.obj U'),
      (chartStalkPoint B S hS f d p).fiber.map g q' = q ∧
        chartSectionsKaehlerRestrict B S hS f d g z = 0 := by
  obtain ⟨j, t, ht⟩ := Stacks.NaiveCotangent.exists_kaehlerMapOfSquare_eq_zero_of_isColimit
    (Functor.whiskerLeft (CategoryOfElements.π (chartStalkPoint B S hS f d p).fiber).op
      (chartSharp B S hS f d))
    (colimit.isColimit _) (colimit.isColimit _)
    (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).map
      (chartSharp B S hS f d))
    (fun i => colimit.ι_desc _ _) (op ⟨U, q⟩) z hz
  exact ⟨j.unop.1, t.unop.1, j.unop.2, t.unop.2, ht⟩

end Stalk

/-! ### Local bijectivity of `σ` -/

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
  (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))

/-- The arrows along which an element of `𝒪_X(U) ⊗_A Ω` restricts to zero. -/
def chartKaehlerTensorVanishingSieve (U : Over d.U)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[ToType
        ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d) :
    Sieve U where
  arrows _ g := chartRestrictKaehlerTensor B S hS f d g t = 0
  downward_closed := by
    intro U₁ U₂ g hg k
    rw [Point.restrictTensor_comp]
    exact (congrArg _ hg).trans (map_zero _)

include hU hW in
/-- **Local injectivity of `σ`.** -/
theorem chartKaehlerTensorVanishingSieve_mem (U : Over d.U)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[ToType
        ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartKaehler B S hS f d)
    (ht : chartKaehlerTensor B S hS f d U t = 0) :
    chartKaehlerTensorVanishingSieve B S hS f d U t ∈
      (SmallEtale.topology B S hS X.1).over d.U U := by
  refine mem_over_of_forall_geometricFiber B S hS f d U _ fun x p => ?_
  let p₀ := (etaleSitePoint B S hS X.1 x X.2).fiber.map U.hom p
  have h0 : chartGermKaehlerTensor B S hS f d p₀ U (chartFiberLift B S hS f d U p) t = 0 :=
    (chartStalkKaehlerBaseChange_bijective B S hS f d p₀ hU hW).injective <| by
      rw [map_zero, ← chartGermKaehler_chartKaehlerTensor, ht, map_zero]
  obtain ⟨U', g, q, hq, hg⟩ := Point.exists_restrictTensor_eq_zero (chartStalkPoint B S hS f d p₀)
    (chartStructurePresheaf B S hS f d) (chartDiagramRestrictO B S hS f d)
    (chartDiagramRestrictO_map B S hS f d) (chartStalkGerm B S hS f d p₀)
    (toPresheafFiber_chartDiagramRestrictO B S hS f d p₀) (chartKaehler B S hS f d)
    (chartFiberLift B S hS f d U p) t h0
  exact ⟨U', g, hg, q.1, congrArg Subtype.val hq⟩

/-- The arrows along which a differential of the sections restricts into the image of `σ`. -/
def chartKaehlerTensorLiftSieve (U : Over d.U) (z : chartSectionsKaehler B S hS f d U) :
    Sieve U where
  arrows U' g := ∃ t, chartKaehlerTensor B S hS f d U' t =
    chartSectionsKaehlerRestrict B S hS f d g z
  downward_closed := by
    rintro U₁ U₂ g ⟨t, ht⟩ k
    refine ⟨chartRestrictKaehlerTensor B S hS f d k t, ?_⟩
    rw [← chartKaehlerTensor_restrict, ht, ← chartSectionsKaehlerRestrict_comp]

include hU hW in
/-- **Local surjectivity of `σ`.** -/
theorem chartKaehlerTensorLiftSieve_mem (U : Over d.U) (z : chartSectionsKaehler B S hS f d U) :
    chartKaehlerTensorLiftSieve B S hS f d U z ∈ (SmallEtale.topology B S hS X.1).over d.U U := by
  refine mem_over_of_forall_geometricFiber B S hS f d U _ fun x p => ?_
  let p₀ := (etaleSitePoint B S hS X.1 x X.2).fiber.map U.hom p
  let q := chartFiberLift B S hS f d U p
  obtain ⟨ξ, hξ⟩ := (chartStalkKaehlerBaseChange_bijective B S hS f d p₀ hU hW).surjective
    (chartGermKaehler B S hS f d p₀ U q z)
  obtain ⟨U₁, g₁, q₁, hq₁, t₁, ht₁⟩ := Point.exists_germTensor_eq (chartStalkPoint B S hS f d p₀)
    (chartStructurePresheaf B S hS f d) (chartDiagramRestrictO B S hS f d)
    (chartStalkGerm B S hS f d p₀) (toPresheafFiber_chartDiagramRestrictO B S hS f d p₀)
    (chartKaehler B S hS f d) q ξ
  let z₁ := chartKaehlerTensor B S hS f d U₁ t₁ - chartSectionsKaehlerRestrict B S hS f d g₁ z
  have hz₁ : chartGermKaehler B S hS f d p₀ U₁ q₁ z₁ = 0 := by
    rw [map_sub, chartGermKaehler_chartKaehlerTensor, ht₁, hξ, chartGermKaehler_restrict, hq₁,
      sub_self]
  obtain ⟨U₂, g₂, q₂, hq₂, hg₂⟩ :=
    exists_chartSectionsKaehlerRestrict_eq_zero B S hS f d p₀ U₁ q₁ z₁ hz₁
  refine ⟨U₂, g₂ ≫ g₁, ⟨chartRestrictKaehlerTensor B S hS f d g₂ t₁, ?_⟩, q₂.1, ?_⟩
  · rw [map_sub, sub_eq_zero] at hg₂
    rw [← chartKaehlerTensor_restrict, hg₂, ← chartSectionsKaehlerRestrict_comp]
  · have := congrArg Subtype.val
      ((congrArg ((chartStalkPoint B S hS f d p₀).fiber.map g₁) hq₂).trans hq₁)
    rwa [Over.comp_left, FunctorToTypes.map_comp_apply]

end AlgebraicGeometry.Space

end
