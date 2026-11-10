module

public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentChartStalk
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSectionsH1
public import StacksFrontier.CategoryTheory.Sites.Point.TensorGerms
public import StacksFrontier.RingTheory.NaiveCotangent.FilteredColimitH1

/-!
# `H₁` of a chart diagram, spread over the localized small étale site

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, and let `d` be a commutative
diagram of étale scheme charts over `f` with affine charts `V = Spec A` of `X` and `W = Spec R`
of `Y`, so that `A` is an `R`-algebra through the vertical morphism of `d`.  Write
`H = H₁(L_{A/R})`.  For an étale chart `U` of `X` over `V`, the square

```
R ──▸ (f⁻¹𝒪_Y)(U)
│          │
▼          ▼
A ──▸   𝒪_X(U)
```

made of the unit of `f⁻¹ ⊣ f_*` on charts and of restriction gives a map
`H ⟶ H₁(L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)})`, and its `𝒪_X(U)`-linear extension

`τ_U : 𝒪_X(U) ⊗_A H ⟶ H₁(L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)})`.

This file proves that `τ` is *locally bijective* on the small étale site of `X` localized at `V`:
an element of the target is, on a covering, in the image of `τ`, and an element killed by `τ`
vanishes on a covering.  Both are checked at the geometric points, where `τ` becomes the base
change map of Stacks 0D08 between filtered colimits of étale algebras, which is bijective; the
passage from the points back to coverings uses that the first homology of the naive cotangent
complex and tensor products commute with the filtered colimits defining the stalks.

## Main definitions

* `AlgebraicGeometry.Space.chartH1Map`: the map `H ⟶ H₁(L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)})`.
* `AlgebraicGeometry.Space.chartH1Tensor`: its linear extension `τ_U`.

## Main results

* `AlgebraicGeometry.Space.chartH1Tensor_restrict`: `τ` commutes with restriction.
* `AlgebraicGeometry.Space.chartTensorLiftSieve_mem`: local surjectivity.
* `AlgebraicGeometry.Space.chartTensorVanishingSieve_mem`: local injectivity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite Algebra
  TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (d : ChartDiagram B S hS X.1 Y.1 f.hom)

/-- The algebra structure `R → A` of a diagram of charts. -/
abbrev chartDiagramAlgebraInst :
    Algebra (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :=
  (chartDiagramRingHom B S hS f d).toAlgebra

/-- `H₁(L_{A/R})` for the chart diagram. -/
abbrev chartH1 : Type u :=
  @H1Cotangent (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) _ _
    (chartDiagramAlgebraInst B S hS f d)

/-- Restriction of regular functions from `V` to a chart over `V`. -/
abbrev chartDiagramRestrictO (U : Over d.U) :
    ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)) →+*
      ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)) :=
  ((smallEtaleRingedTopos B S hS X).O.obj.map U.hom.op).hom

/-- The unit on charts, restricted from `V` to a chart over `V`. -/
abbrev chartDiagramRestrictBase (U : Over d.U) :
    ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)) →+*
      ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)) :=
  ((inverseImageStructureSheaf B S hS f).obj.map U.hom.op).hom.comp
    (inverseImageChartUnitRingHom B S hS f d)

/-- The square of rings over a chart `U` over `V` commutes. -/
theorem chartSquare_comm (U : Over d.U)
    (r : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    chartDiagramRestrictO B S hS f d U
        (@algebraMap _ _ _ _ (chartDiagramAlgebraInst B S hS f d) r) =
      @algebraMap _ _ _ _ (Stacks.SheafOfModules.algebraSections _
        (inverseImageStructureSheaf B S hS f) (smallEtaleRingedTopos B S hS X).O
        (structureSharpInverseImage B S hS f) (op U.left))
        (chartDiagramRestrictBase B S hS f d U r) := by
  change chartDiagramRestrictO B S hS f d U (chartDiagramRingHom B S hS f d r) =
    (structureSharpInverseImage B S hS f).hom.app (op U.left)
      ((inverseImageStructureSheaf B S hS f).obj.map U.hom.op
        (inverseImageChartUnitRingHom B S hS f d r))
  refine (congrArg (chartDiagramRestrictO B S hS f d U)
    (structureSharpInverseImage_inverseImageChartUnit B S hS f d r).symm).trans ?_
  exact (NatTrans.naturality_apply (structureSharpInverseImage B S hS f).hom U.hom.op _).symm

/-- **The map `H ⟶ H₁(L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)})`** over a chart `U` over `V`. -/
abbrev chartH1Map (U : Over d.U) :
    chartH1 B S hS f d →+
      @H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) _ _
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)) :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (chartDiagramAlgebraInst B S hS f d)
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))
    (chartDiagramRestrictBase B S hS f d U) (chartDiagramRestrictO B S hS f d U)
    (chartSquare_comm B S hS f d U)

/-- The `A`-algebra structure on the regular functions on a chart over `V`. -/
abbrev chartDiagramRestrictAlgebra (U : Over d.U) :
    Algebra (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) :=
  (chartDiagramRestrictO B S hS f d U).toAlgebra

/-- **`τ_U : 𝒪_X(U) ⊗_A H ⟶ H₁(L_{𝒪_X(U)/(f⁻¹𝒪_Y)(U)})`.** -/
def chartH1Tensor (U : Over d.U) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) ⊗[
        ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d →+
      H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := chartDiagramRestrictAlgebra B S hS f d U
  letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun h => s • chartH1Map B S hS f d U h
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun h₁ h₂ => by rw [map_add, smul_add] }
      map_zero' := AddMonoidHom.ext fun h =>
        zero_smul (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
          (chartH1Map B S hS f d U h)
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun h => add_smul s₁ s₂ _ }
    (fun a s h => by
      change (chartDiagramRestrictO B S hS f d U a * s) • chartH1Map B S hS f d U h =
        s • chartH1Map B S hS f d U (a • h)
      rw [Stacks.NaiveCotangent.h1CotangentMapOfSquare_smul, smul_smul, mul_comm])

/-- `chartH1Tensor` sends `s ⊗ₜ h` to `s • chartH1Map h`. -/
theorem chartH1Tensor_tmul (U : Over d.U)
    (s : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
    (h : chartH1 B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := chartDiagramRestrictAlgebra B S hS f d U
    letI := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
    chartH1Tensor B S hS f d U (s ⊗ₜ h) = s • chartH1Map B S hS f d U h :=
  rfl

/-! ### Restriction -/

/-- The structure ring maps `A → 𝒪_X(U)` are compatible with restriction. -/
theorem chartDiagramRestrictO_naturality {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :
    (smallEtaleRingedTopos B S hS X).O.obj.map g.left.op (chartDiagramRestrictO B S hS f d U₁ a) =
      chartDiagramRestrictO B S hS f d U₂ a := by
  change ((smallEtaleRingedTopos B S hS X).O.obj.map U₁.hom.op ≫
    (smallEtaleRingedTopos B S hS X).O.obj.map g.left.op) a = _
  rw [← Functor.map_comp, ← op_comp, Over.w g]

/-- The base ring maps `R → (f⁻¹𝒪_Y)(U)` are compatible with restriction. -/
theorem chartDiagramRestrictBase_naturality {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (r : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    (inverseImageStructureSheaf B S hS f).obj.map g.left.op
        (chartDiagramRestrictBase B S hS f d U₁ r) =
      chartDiagramRestrictBase B S hS f d U₂ r := by
  change ((inverseImageStructureSheaf B S hS f).obj.map U₁.hom.op ≫
    (inverseImageStructureSheaf B S hS f).obj.map g.left.op) _ = _
  rw [← Functor.map_comp, ← op_comp, Over.w g]
  rfl

/-- Pasting two squares of rings, whose composite ring maps agree with `fR'` and `fS'`. -/
private theorem h1CotangentMapOfSquare_comp_eq {R₁ S₁ R₂ S₂ R₃ S₃ : Type*} [CommRing R₁]
    [CommRing S₁] [CommRing R₂] [CommRing S₂] [CommRing R₃] [CommRing S₃] {_ : Algebra R₁ S₁}
    {_ : Algebra R₂ S₂} {_ : Algebra R₃ S₃} {fR : R₁ →+* R₂} {fS : S₁ →+* S₂}
    {h : ∀ r, fS (algebraMap R₁ S₁ r) = algebraMap R₂ S₂ (fR r)} {gR : R₂ →+* R₃}
    {gS : S₂ →+* S₃} {h' : ∀ r, gS (algebraMap R₂ S₂ r) = algebraMap R₃ S₃ (gR r)}
    {fR' : R₁ →+* R₃} {fS' : S₁ →+* S₃}
    {h'' : ∀ r, fS' (algebraMap R₁ S₁ r) = algebraMap R₃ S₃ (fR' r)}
    (eR : ∀ r, gR (fR r) = fR' r) (eS : ∀ s, gS (fS s) = fS' s) (x : H1Cotangent R₁ S₁) :
    Stacks.NaiveCotangent.h1CotangentMapOfSquare gR gS h'
        (Stacks.NaiveCotangent.h1CotangentMapOfSquare fR fS h x) =
      Stacks.NaiveCotangent.h1CotangentMapOfSquare fR' fS' h'' x :=
  (Stacks.NaiveCotangent.h1CotangentMapOfSquare_comp _ _ _ _ _ _ x).trans
    (Stacks.NaiveCotangent.h1CotangentMapOfSquare_congr _ _ (RingHom.ext eR) (RingHom.ext eS) x)

/-- **The map `H ⟶ H₁` commutes with restriction.** -/
theorem chartH1Map_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁) (h : chartH1 B S hS f d) :
    Stacks.SheafOfModules.sectionsH1Restrict _ (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g.left.op
        (chartH1Map B S hS f d U₁ h) =
      chartH1Map B S hS f d U₂ h := by
  exact h1CotangentMapOfSquare_comp_eq (chartDiagramRestrictBase_naturality B S hS f d g)
    (chartDiagramRestrictO_naturality B S hS f d g) h

/-- The ring maps `A → 𝒪_X(U)`, in the form the germ calculus on the localized site consumes. -/
theorem chartDiagramRestrictO_map {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :
    (chartStructurePresheaf B S hS f d).map g.op (chartDiagramRestrictO B S hS f d U₁ a) =
      chartDiagramRestrictO B S hS f d U₂ a :=
  chartDiagramRestrictO_naturality B S hS f d g a

/-- Restriction of `𝒪_X(U) ⊗_A H` along a morphism of charts over `V`. -/
abbrev chartRestrictTensor {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁) :=
  Point.restrictTensor (chartStructurePresheaf B S hS f d) (chartDiagramRestrictO B S hS f d)
    (chartDiagramRestrictO_map B S hS f d) (chartH1 B S hS f d) g

/-- **`τ` commutes with restriction.** -/
theorem chartH1Tensor_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U₁
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U₁.left)))
        ⊗[ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d) :
    Stacks.SheafOfModules.sectionsH1Restrict _ (inverseImageStructureSheaf B S hS f)
        (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g.left.op
        (chartH1Tensor B S hS f d U₁ t) =
      chartH1Tensor B S hS f d U₂ (chartRestrictTensor B S hS f d g t) := by
  let := chartDiagramAlgebraInst B S hS f d
  let := chartDiagramRestrictAlgebra B S hS f d U₁
  let := chartDiagramRestrictAlgebra B S hS f d U₂
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left)
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₂.left)
  induction t using TensorProduct.inductionOn with
  | tmul s h =>
    rw [Point.restrictTensor_tmul, chartH1Tensor_tmul, chartH1Tensor_tmul]
    refine (Stacks.NaiveCotangent.h1CotangentMapOfSquare_smul _ _ _ s _).trans ?_
    exact congrArg (_ • ·) (chartH1Map_restrict B S hS f d g h)
  | add a b ha hb =>
    simp only [map_add, ha, hb]

/-! ### At a geometric point -/

section Stalk

variable {x : GeometricPoint B S hS X.1} (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj d.U)

/-- The structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`, restricted to the localized site. -/
abbrev chartSharp : chartBasePresheaf B S hS f d ⟶ chartStructurePresheaf B S hS f d :=
  Functor.whiskerLeft (Over.forget d.U).op (structureSharpInverseImage B S hS f).hom

/-- The stalk of `f⁻¹𝒪_Y`. -/
abbrev chartBaseStalk : CommRingCat.{u} :=
  ((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
    (chartBasePresheaf B S hS f d)

/-- The stalk of `𝒪_X`. -/
abbrev chartStructureStalk : CommRingCat.{u} :=
  ((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).obj
    (chartStructurePresheaf B S hS f d)

/-- The stalk of the structure map. -/
abbrev chartStalkAlgebra :
    Algebra (ToType (chartBaseStalk B S hS f d p)) (ToType (chartStructureStalk B S hS f d p)) :=
  (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).map
    (chartSharp B S hS f d)).hom.toAlgebra

/-- The square of stalks commutes. -/
theorem chartStalkSquare_comm
    (r : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    chartStalkGerm B S hS f d p (@algebraMap _ _ _ _ (chartDiagramAlgebraInst B S hS f d) r) =
      @algebraMap _ _ _ _ (chartStalkAlgebra B S hS f d p) (chartBaseStalkGerm B S hS f d p r) := by
  change _ = ((chartStalkPoint B S hS f d p).presheafFiber.map (chartSharp B S hS f d))
    ((chartStalkPoint B S hS f d p).toPresheafFiber _ (chartStalkPointTop B S hS f d p)
      (chartBasePresheaf B S hS f d) (inverseImageChartUnitRingHom B S hS f d r))
  rw [Point.toPresheafFiber_naturality_apply]
  exact congrArg (chartStalkGerm B S hS f d p)
    (structureSharpInverseImage_inverseImageChartUnit B S hS f d r).symm

/-- **The map `H ⟶ H₁(L_{𝒪_{X,x}/(f⁻¹𝒪_Y)_x})` at the point.** -/
abbrev chartStalkH1Map :
    chartH1 B S hS f d →+
      @H1Cotangent (ToType (chartBaseStalk B S hS f d p))
        (ToType (chartStructureStalk B S hS f d p)) _ _
        (chartStalkAlgebra B S hS f d p) :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _ (chartDiagramAlgebraInst B S hS f d)
    (chartStalkAlgebra B S hS f d p) (chartBaseStalkGerm B S hS f d p)
    (chartStalkGerm B S hS f d p) (chartStalkSquare_comm B S hS f d p)

/-- The morphism from a chart over `V` to the terminal object of the localized site. -/
abbrev chartToTop (U : Over d.U) : U ⟶ Over.mk (𝟙 d.U) :=
  Over.homMk U.hom

/-- Every lift of the point into a chart over `V` lies over the chosen lift into `V`. -/
theorem chartStalkPoint_map_toTop (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U) :
    (chartStalkPoint B S hS f d p).fiber.map (chartToTop B S hS f d U) q =
      chartStalkPointTop B S hS f d p :=
  Subtype.ext ((FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).1 q.2)

/-- The germ of a restriction from `V` is the germ at `V`. -/
theorem toPresheafFiber_chartDiagramRestrictO (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U)
    (a : ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))) :
    (chartStalkPoint B S hS f d p).toPresheafFiber U q (chartStructurePresheaf B S hS f d)
        (chartDiagramRestrictO B S hS f d U a) = chartStalkGerm B S hS f d p a := by
  refine (Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) (chartToTop B S hS f d U) q
    (chartStructurePresheaf B S hS f d) a).trans ?_
  rw [chartStalkPoint_map_toTop]

/-- The germ of the unit on charts restricted from `V` is the germ at `V`. -/
theorem toPresheafFiber_chartDiagramRestrictBase (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U)
    (r : ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V))) :
    (chartStalkPoint B S hS f d p).toPresheafFiber U q (chartBasePresheaf B S hS f d)
        (chartDiagramRestrictBase B S hS f d U r) = chartBaseStalkGerm B S hS f d p r := by
  refine (Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) (chartToTop B S hS f d U) q
    (chartBasePresheaf B S hS f d) _).trans ?_
  rw [chartStalkPoint_map_toTop]
  rfl

/-- The germ map on `H₁` at a lift of the point into a chart over `V`. -/
abbrev chartGermH1 (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U) :
    @H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) _ _
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)) →+
      @H1Cotangent (ToType (chartBaseStalk B S hS f d p))
        (ToType (chartStructureStalk B S hS f d p)) _ _
        (chartStalkAlgebra B S hS f d p) :=
  @Stacks.NaiveCotangent.h1CotangentMapOfSquare _ _ _ _ _ _ _ _
    (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))
    (chartStalkAlgebra B S hS f d p)
    ((chartStalkPoint B S hS f d p).toPresheafFiber U q (chartBasePresheaf B S hS f d)).hom
    ((chartStalkPoint B S hS f d p).toPresheafFiber U q (chartStructurePresheaf B S hS f d)).hom
    (fun a => (Point.toPresheafFiber_naturality_apply (chartStalkPoint B S hS f d p)
      (chartSharp B S hS f d) U q a).symm)

/-- The germ map on `H₁` after the map of a chart diagram is the map at the point. -/
theorem chartGermH1_chartH1Map (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U)
    (h : chartH1 B S hS f d) :
    chartGermH1 B S hS f d p U q (chartH1Map B S hS f d U h) = chartStalkH1Map B S hS f d p h := by
  exact h1CotangentMapOfSquare_comp_eq
    (fun r => toPresheafFiber_chartDiagramRestrictBase B S hS f d p U q r)
    (fun a => toPresheafFiber_chartDiagramRestrictO B S hS f d p U q a) h

/-- The germ map on tensor products at a lift of the point into a chart over `V`. -/
abbrev chartGermTensor (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U) :=
  Point.germTensor (chartStalkPoint B S hS f d p) (chartStructurePresheaf B S hS f d)
    (chartDiagramRestrictO B S hS f d) (chartStalkGerm B S hS f d p)
    (toPresheafFiber_chartDiagramRestrictO B S hS f d p) (chartH1 B S hS f d) U q

/-- **The base change map at the point**, `𝒪_{X,x} ⊗_A H ⟶ H₁(L_{𝒪_{X,x}/(f⁻¹𝒪_Y)_x})`. -/
def chartStalkH1BaseChange :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := (chartStalkGerm B S hS f d p).toAlgebra
    letI := chartStalkAlgebra B S hS f d p
    (ToType (chartStructureStalk B S hS f d p)) ⊗[
        ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d →+
      H1Cotangent (ToType (chartBaseStalk B S hS f d p))
        (ToType (chartStructureStalk B S hS f d p)) :=
  letI := chartDiagramAlgebraInst B S hS f d
  letI := (chartStalkGerm B S hS f d p).toAlgebra
  letI := chartStalkAlgebra B S hS f d p
  TensorProduct.liftAddHom
    { toFun := fun s =>
        { toFun := fun h => s • chartStalkH1Map B S hS f d p h
          map_zero' := by rw [map_zero, smul_zero]
          map_add' := fun h₁ h₂ => by rw [map_add, smul_add] }
      map_zero' := AddMonoidHom.ext fun h =>
        zero_smul (ToType (chartStructureStalk B S hS f d p)) (chartStalkH1Map B S hS f d p h)
      map_add' := fun s₁ s₂ => AddMonoidHom.ext fun h => add_smul s₁ s₂ _ }
    (fun a s h => by
      change (chartStalkGerm B S hS f d p a * s) • chartStalkH1Map B S hS f d p h =
        s • chartStalkH1Map B S hS f d p (a • h)
      rw [Stacks.NaiveCotangent.h1CotangentMapOfSquare_smul, smul_smul, mul_comm])

/-- `chartStalkH1BaseChange` sends `s ⊗ₜ h` to `s • chartStalkH1Map h`. -/
theorem chartStalkH1BaseChange_tmul (s : ToType (chartStructureStalk B S hS f d p))
    (h : chartH1 B S hS f d) :
    letI := chartDiagramAlgebraInst B S hS f d
    letI := (chartStalkGerm B S hS f d p).toAlgebra
    letI := chartStalkAlgebra B S hS f d p
    chartStalkH1BaseChange B S hS f d p (s ⊗ₜ h) = s • chartStalkH1Map B S hS f d p h :=
  rfl

/-- **`τ` at a point is the base change map of the point.** -/
theorem chartGermH1_chartH1Tensor (U : Over d.U) (q : (chartStalkPoint B S hS f d p).fiber.obj U)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
        ⊗[ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d) :
    chartGermH1 B S hS f d p U q (chartH1Tensor B S hS f d U t) =
      chartStalkH1BaseChange B S hS f d p (chartGermTensor B S hS f d p U q t) := by
  let := chartDiagramAlgebraInst B S hS f d
  let := chartDiagramRestrictAlgebra B S hS f d U
  let := (chartStalkGerm B S hS f d p).toAlgebra
  let := chartStalkAlgebra B S hS f d p
  let := Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
    (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)
  induction t using TensorProduct.inductionOn with
  | tmul s h =>
    rw [chartH1Tensor_tmul, Point.germTensor_tmul, chartStalkH1BaseChange_tmul]
    refine (Stacks.NaiveCotangent.h1CotangentMapOfSquare_smul _ _ _ s _).trans ?_
    exact congrArg (_ • ·) (chartGermH1_chartH1Map B S hS f d p U q h)
  | add a b ha hb =>
    simp only [map_add, ha, hb]

/-- **Stacks 0D08 at the point: the base change map is bijective.** -/
theorem chartStalkH1BaseChange_bijective
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
    (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V)) :
    Function.Bijective (chartStalkH1BaseChange B S hS f d p) := by
  let := chartDiagramAlgebraInst B S hS f d
  let := (chartStalkGerm B S hS f d p).toAlgebra
  let := chartStalkAlgebra B S hS f d p
  let := (chartBaseStalkGerm B S hS f d p).toAlgebra
  let : Algebra (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
      (ToType (chartStructureStalk B S hS f d p)) :=
    ((chartStalkGerm B S hS f d p).comp (chartDiagramRingHom B S hS f d)).toAlgebra
  have : IsScalarTower (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
      (ToType (chartStructureStalk B S hS f d p)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
      (ToType (chartBaseStalk B S hS f d p)) (ToType (chartStructureStalk B S hS f d p)) :=
    IsScalarTower.of_algebraMap_eq fun r => chartStalkSquare_comm B S hS f d p r
  have hbij := Algebra.bijective_h1Cotangent_map_liftBaseChange_of_ind_etale
    (ToType ((smallEtaleRingedTopos B S hS Y).O.obj.obj (op d.V)))
    (ToType (chartBaseStalk B S hS f d p))
    (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U)))
    (ToType (chartStructureStalk B S hS f d p))
    (chartBaseStalk_ind_etale B S hS f d p hW) (chartStalk_ind_etale B S hS f d p hU)
  convert hbij using 1
  funext t
  induction t using TensorProduct.inductionOn with
  | tmul s h =>
    rw [chartStalkH1BaseChange_tmul, LinearMap.liftBaseChange_tmul,
      Stacks.NaiveCotangent.h1Cotangent_map_eq_h1CotangentMapOfSquare]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The germ map on `H₁` is compatible with restriction. -/
theorem chartGermH1_restrict {U₁ U₂ : Over d.U} (g : U₂ ⟶ U₁)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U₂)
    (z : @H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U₁.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U₁.left))) _ _
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U₁.left))) :
    chartGermH1 B S hS f d p U₂ q
        (Stacks.SheafOfModules.sectionsH1Restrict _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g.left.op z) =
      chartGermH1 B S hS f d p U₁ ((chartStalkPoint B S hS f d p).fiber.map g q) z := by
  exact h1CotangentMapOfSquare_comp_eq
    (fun r => Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) g q
      (chartBasePresheaf B S hS f d) r)
    (fun r => Point.toPresheafFiber_w_apply (chartStalkPoint B S hS f d p) g q
      (chartStructurePresheaf B S hS f d) r) z

/-- **A class of `H₁` with vanishing germ vanishes on a smaller neighbourhood.** -/
theorem exists_sectionsH1Restrict_eq_zero (U : Over d.U)
    (q : (chartStalkPoint B S hS f d p).fiber.obj U)
    (z : @H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) _ _
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left)))
    (hz : chartGermH1 B S hS f d p U q z = 0) :
    ∃ (U' : Over d.U) (g : U' ⟶ U) (q' : (chartStalkPoint B S hS f d p).fiber.obj U'),
      (chartStalkPoint B S hS f d p).fiber.map g q' = q ∧
        Stacks.SheafOfModules.sectionsH1Restrict _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g.left.op z =
          0 := by
  obtain ⟨j, t, ht⟩ := Stacks.NaiveCotangent.exists_h1CotangentMapOfSquare_eq_zero_of_isColimit
    (Functor.whiskerLeft (Functor.Elements.π (chartStalkPoint B S hS f d p).fiber).op
      (chartSharp B S hS f d))
    (colimit.isColimit _) (colimit.isColimit _)
    (((chartStalkPoint B S hS f d p).presheafFiber (A := CommRingCat.{u})).map
      (chartSharp B S hS f d))
    (fun i => colimit.ι_desc _ _) (op ((chartStalkPoint B S hS f d p).fiber.elementsMk U q)) z hz
  exact ⟨j.unop.obj, t.unop.hom, j.unop.val, t.unop.map_val, ht⟩

end Stalk

/-! ### Local bijectivity of `τ` -/

/-- **Coverings of the localized site are detected at geometric points.**  A sieve of a chart
`U` over `V` through which every lift of every geometric point into `U` factors is a covering
sieve of the small étale site localized at `V`. -/
theorem mem_over_of_forall_geometricFiber (U : Over d.U) (T : Sieve U)
    (hT : ∀ (x : GeometricPoint B S hS X.1)
      (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj U.left),
      ∃ (U' : Over d.U) (g : U' ⟶ U), T g ∧
        ∃ q : (etaleSitePoint B S hS X.1 x X.2).fiber.obj U'.left,
          (etaleSitePoint B S hS X.1 x X.2).fiber.map g.left q = p) :
    T ∈ (SmallEtale.topology B S hS X.1).over d.U U := by
  rw [GrothendieckTopology.mem_over_iff]
  refine mem_topology_of_forall_geometricFiber B S hS X U.left _ fun x p => ?_
  obtain ⟨U', g, hg, q, hq⟩ := hT x p
  refine ⟨U'.left, g.left, ?_, q, hq⟩
  rw [Sieve.overEquiv_iff]
  have e : (Over.homMk g.left : Over.mk (g.left ≫ U.hom) ⟶ U) =
      (Over.homMk (𝟙 _) (by simp [Over.w g]) : Over.mk (g.left ≫ U.hom) ⟶ U') ≫ g := by
    ext
    simp
  rw [e]
  exact T.downward_closed hg _

/-- The lift of a geometric point into a chart over `V`, as a lift for the localized point. -/
def chartFiberLift (U : Over d.U) {x : GeometricPoint B S hS X.1}
    (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj U.left) :
    (chartStalkPoint B S hS f d
      ((etaleSitePoint B S hS X.1 x X.2).fiber.map U.hom p)).fiber.obj U :=
  ⟨p, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).2 rfl⟩

variable (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj d.U))
  (hW : IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj d.V))

/-- The arrows along which an element of `𝒪_X(U) ⊗_A H` restricts to zero. -/
def chartTensorVanishingSieve (U : Over d.U)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
        ⊗[ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d) :
    Sieve U where
  arrows _ g := chartRestrictTensor B S hS f d g t = 0
  downward_closed := by
    intro U₁ U₂ g hg k
    rw [Point.restrictTensor_comp]
    exact (congrArg _ hg).trans (map_zero _)

include hU hW in
/-- **Local injectivity of `τ`.** -/
theorem chartTensorVanishingSieve_mem (U : Over d.U)
    (t : letI := chartDiagramAlgebraInst B S hS f d
      letI := chartDiagramRestrictAlgebra B S hS f d U
      (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left)))
        ⊗[ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op d.U))] chartH1 B S hS f d)
    (ht : chartH1Tensor B S hS f d U t = 0) :
    chartTensorVanishingSieve B S hS f d U t ∈ (SmallEtale.topology B S hS X.1).over d.U U := by
  refine mem_over_of_forall_geometricFiber B S hS f d U _ fun x p => ?_
  let p₀ := (etaleSitePoint B S hS X.1 x X.2).fiber.map U.hom p
  have h0 : chartStalkH1BaseChange B S hS f d p₀
      (chartGermTensor B S hS f d p₀ U (chartFiberLift B S hS f d U p) t) = 0 := by
    rw [← chartGermH1_chartH1Tensor, ht, map_zero]
  have h1 : chartGermTensor B S hS f d p₀ U (chartFiberLift B S hS f d U p) t = 0 :=
    (chartStalkH1BaseChange_bijective B S hS f d p₀ hU hW).injective (h0.trans (map_zero _).symm)
  obtain ⟨U', g, q, hq, hg⟩ := Point.exists_restrictTensor_eq_zero (chartStalkPoint B S hS f d p₀)
    (chartStructurePresheaf B S hS f d) (chartDiagramRestrictO B S hS f d)
    (chartDiagramRestrictO_map B S hS f d) (chartStalkGerm B S hS f d p₀)
    (toPresheafFiber_chartDiagramRestrictO B S hS f d p₀) (chartH1 B S hS f d)
    (chartFiberLift B S hS f d U p) t h1
  exact ⟨U', g, hg, q.1, congrArg Subtype.val hq⟩

/-- The arrows along which an element of `H₁` restricts into the image of `τ`. -/
def chartTensorLiftSieve (U : Over d.U)
    (z : @H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) _ _
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))) :
    Sieve U where
  arrows U' g := ∃ t, chartH1Tensor B S hS f d U' t =
    Stacks.SheafOfModules.sectionsH1Restrict _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g.left.op z
  downward_closed := by
    rintro U₁ U₂ g ⟨t, ht⟩ k
    refine ⟨chartRestrictTensor B S hS f d k t, ?_⟩
    rw [← chartH1Tensor_restrict, ht, ← Stacks.SheafOfModules.sectionsH1Restrict_comp]
    rfl

include hU hW in
/-- **Local surjectivity of `τ`.** -/
theorem chartTensorLiftSieve_mem (U : Over d.U)
    (z : @H1Cotangent (ToType ((inverseImageStructureSheaf B S hS f).obj.obj (op U.left)))
        (ToType ((smallEtaleRingedTopos B S hS X).O.obj.obj (op U.left))) _ _
        (Stacks.SheafOfModules.algebraSections _ (inverseImageStructureSheaf B S hS f)
          (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) (op U.left))) :
    chartTensorLiftSieve B S hS f d U z ∈ (SmallEtale.topology B S hS X.1).over d.U U := by
  refine mem_over_of_forall_geometricFiber B S hS f d U _ fun x p => ?_
  let p₀ := (etaleSitePoint B S hS X.1 x X.2).fiber.map U.hom p
  let q := chartFiberLift B S hS f d U p
  obtain ⟨ξ, hξ⟩ := (chartStalkH1BaseChange_bijective B S hS f d p₀ hU hW).surjective
    (chartGermH1 B S hS f d p₀ U q z)
  obtain ⟨U₁, g₁, q₁, hq₁, t₁, ht₁⟩ := Point.exists_germTensor_eq (chartStalkPoint B S hS f d p₀)
    (chartStructurePresheaf B S hS f d) (chartDiagramRestrictO B S hS f d)
    (chartStalkGerm B S hS f d p₀) (toPresheafFiber_chartDiagramRestrictO B S hS f d p₀)
    (chartH1 B S hS f d) q ξ
  let z₁ := chartH1Tensor B S hS f d U₁ t₁ -
    Stacks.SheafOfModules.sectionsH1Restrict _ (inverseImageStructureSheaf B S hS f)
      (smallEtaleRingedTopos B S hS X).O (structureSharpInverseImage B S hS f) g₁.left.op z
  have hz₁ : chartGermH1 B S hS f d p₀ U₁ q₁ z₁ = 0 := by
    rw [map_sub, chartGermH1_chartH1Tensor, ht₁, hξ, chartGermH1_restrict, hq₁, sub_self]
  obtain ⟨U₂, g₂, q₂, hq₂, hg₂⟩ :=
    exists_sectionsH1Restrict_eq_zero B S hS f d p₀ U₁ q₁ z₁ hz₁
  refine ⟨U₂, g₂ ≫ g₁, ⟨chartRestrictTensor B S hS f d g₂ t₁, ?_⟩, q₂.1, ?_⟩
  · rw [map_sub, sub_eq_zero] at hg₂
    rw [← chartH1Tensor_restrict, hg₂, ← Stacks.SheafOfModules.sectionsH1Restrict_comp]
    rfl
  · rw [Over.comp_left, Functor.map_comp_apply]
    exact congrArg Subtype.val
      ((congrArg ((chartStalkPoint B S hS f d p₀).fiber.map g₁) hq₂).trans hq₁)

end AlgebraicGeometry.Space

end
