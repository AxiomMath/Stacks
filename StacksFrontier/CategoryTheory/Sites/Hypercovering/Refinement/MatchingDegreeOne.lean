module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement.DegreewiseProducts
import all StacksFrontier.CategoryTheory.Sites.Hypercovering.Refinement.DegreewiseProducts

/-!
# Refining a hypercovering: the degree-one matching map

The covering morphisms are stable under base change as a `MorphismProperty`; the matching
category of `⦋1⦌` for the `0`-coskeleton is discrete, so the degree-one matching map of a constant
power is computed by hand: `constPowerMap_matching_prop_zero`.
-/

public section

universe w v u
universe w'
universe a b c d
universe w₂ u₁ v₁

open CategoryTheory CategoryTheory.Limits Simplicial SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

/- The two local attribute changes of `Refinement.DegreewiseProducts`, for the reasons given
there. -/
attribute [local implicit_reducible] CategoryTheory.SimplicialObject.power
attribute [-instance] CategoryTheory.Limits.FormalCoproduct.instHasProductsOfShape

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- **Stacks Project, Tag 01G4, part (2)** read through `MorphismProperty`: the covering
morphisms are stable under base change. -/
instance (J : Pretopology C) [Precoverage.IsStableUnderComposition J.toPrecoverage] (X : C) :
    (coveringOverProperty J X : MorphismProperty
      (FormalCoproduct.{w} (Over X))).IsStableUnderBaseChange where
  of_isPullback sq hg := IsCoveringOver.of_isPullback J sq hg

/-- The degreewise product of a finite family of covering morphisms is covering: `prop_piMap` at
the covering property. -/
private theorem isCoveringOver_piMap (J : Pretopology C)
    [Precoverage.IsStableUnderComposition J.toPrecoverage]
    {X : C}
    {α : Type w} [Finite α]
    (A B : α → FormalCoproduct.{w} (Over X)) (f : ∀ a, A a ⟶ B a)
    [HasProduct A] [HasProduct B]
    (hf : ∀ a, IsCoveringOver J (f a)) :
    IsCoveringOver J (CategoryTheory.Limits.Pi.map f) :=
  (coveringOverProperty_iff J _).1
    (prop_piMap (coveringOverProperty J X) A B f fun a =>
      (coveringOverProperty_iff J (f a)).2 (hf a))

/-- Over a singleton index the degreewise product of a morphism is that morphism, read through
`Limits.productUniqueIso`. -/
private theorem piMap_comp_productUniqueIso_hom {D : Type u} [Category.{v} D] {ι : Type w}
    [Unique ι] {Y Z : D} (u : Z ⟶ Y) [HasProduct fun _ : ι => Y] [HasProduct fun _ : ι => Z] :
    CategoryTheory.Limits.Pi.map (fun _ : ι => u) ≫
        (CategoryTheory.Limits.productUniqueIso (fun _ : ι => Y)).hom =
      (CategoryTheory.Limits.productUniqueIso (fun _ : ι => Z)).hom ≫ u := by
  rw [CategoryTheory.Limits.productUniqueIso_hom, CategoryTheory.Limits.productUniqueIso_hom,
    CategoryTheory.Limits.Pi.map_π]
/-- The object `⦋1⦌`, read in `SimplexCategoryᵒᵖ`: the degree in which the matching object of a
`0`-coskeleton is computed. -/
private abbrev degOne : SimplexCategoryᵒᵖ := Opposite.op (SimplexCategory.mk 1)

/-- The opposite of the inclusion of the `0`-truncated simplex category. -/
private abbrev trunc0Incl : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ SimplexCategoryᵒᵖ :=
  (SimplexCategory.Truncated.inclusion 0).op

/-- The matching category of `⦋1⦌` for the `0`-coskeleton: the category of vertices of `⦋1⦌`. -/
private abbrev VertexOverOne := StructuredArrow degOne trunc0Incl

attribute [instance] isDiscrete_verticesOverOne

/-- The `0`-truncated simplex category has exactly one object. -/
@[instance_reducible]
private def uniqueTrunc0 : Unique (SimplexCategory.Truncated 0) where
  default := ⟨SimplexCategory.mk 0, by simp⟩
  uniq x := simplexTrunc0ObjEq x

/-- There are finitely many maps from `⦋1⦌` to an object of the `0`-truncated simplex
category. -/
@[instance_reducible]
private noncomputable def fintypeDegOneHom (j : (SimplexCategory.Truncated 0)ᵒᵖ) :
    Fintype (degOne ⟶ trunc0Incl.obj j) := by
  let h := congrArg trunc0Incl.obj (simplexTrunc0OpObjEq j)
  letI : Fintype (degOne ⟶ Opposite.op (SimplexCategory.mk 0)) := by
    let e : (Opposite.op (SimplexCategory.mk 1) ⟶
        Opposite.op (SimplexCategory.mk 0)) ≃
        (SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1) := {
      toFun f := f.unop
      invFun f := f.op
      left_inv := by intro f; rfl
      right_inv := by intro f; rfl
    }
    letI : Fintype (SimplexCategory.mk 0 ⟶ SimplexCategory.mk 1) :=
      Fintype.ofFinite _
    exact Fintype.ofEquiv _ e.symm
  let e : (degOne ⟶ trunc0Incl.obj j) ≃
      (degOne ⟶ Opposite.op (SimplexCategory.mk 0)) := {
    toFun f := f ≫ eqToHom h
    invFun f := f ≫ eqToHom h.symm
    left_inv := by intro f; simp [Category.assoc]
    right_inv := by intro f; simp [Category.assoc]
  }
  exact Fintype.ofEquiv _ e.symm

/-- The matching category of `⦋1⦌` for the `0`-coskeleton is finite. -/
@[instance_reducible]
private noncomputable def fintypeVertexOverOne : Fintype VertexOverOne := by
  letI := uniqueTrunc0
  letI : Fintype (SimplexCategory.Truncated 0) := Fintype.ofFinite _
  letI : Fintype (SimplexCategory.Truncated 0)ᵒᵖ := Fintype.ofFinite _
  letI := fintypeDegOneHom
  let eJ : VertexOverOne ≃ (Σ a : Discrete PUnit, Σ j : (SimplexCategory.Truncated 0)ᵒᵖ,
      (degOne ⟶ trunc0Incl.obj j)) := {
    toFun j := ⟨j.left, j.right, j.hom⟩
    invFun x := ⟨x.1, x.2.1, x.2.2⟩
    left_inv := by rintro ⟨a, j, f⟩; rfl
    right_inv := by rintro ⟨a, j, f⟩; rfl
  }
  exact Fintype.ofEquiv _ eJ.symm

/-- The unique point of the cosimplicial set `C[k]` in degree zero. -/
private noncomputable def degZeroPoint (k : ℕ) :
    (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 0) := by
  letI : Unique ((simplexPowerIndex.{w} k).obj (SimplexCategory.mk 0)) := by
    change Unique (ULift (SimplexCategory.mk k ⟶ SimplexCategory.mk 0))
    infer_instance
  exact default

/-- The vertex of `⦋1⦌` named by an object of the matching category. -/
private noncomputable def vertexCoord (k : ℕ) (j : VertexOverOne) :
    (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) :=
  (simplexPowerIndex.{w} k).map
    ((j.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq j.right))).unop) (degZeroPoint.{w} k)

private theorem vertexCoord_injective (k : ℕ) :
    Function.Injective (vertexCoord.{w} k) := by
  intro j l h
  have h' : ((default : SimplexCategory.mk k ⟶ SimplexCategory.mk 0) ≫
      (j.hom ≫ eqToHom (congrArg trunc0Incl.obj (simplexTrunc0OpObjEq j.right))).unop) =
      ((default : SimplexCategory.mk k ⟶ SimplexCategory.mk 0) ≫
      (l.hom ≫ eqToHom (congrArg trunc0Incl.obj (simplexTrunc0OpObjEq l.right))).unop) := by
    change ULift.up _ = ULift.up _ at h
    exact congrArg ULift.down h
  have hval : (j.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq j.right))).unop.toOrderHom 0 =
      (l.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq l.right))).unop.toOrderHom 0 := by
    have hh := congrArg
      (fun f : SimplexCategory.mk k ⟶ SimplexCategory.mk 1 => f.toOrderHom 0) h'
    simpa only [SimplexCategory.eq_const_to_zero, SimplexCategory.const_comp,
      SimplexCategory.const_apply] using hh
  have hφ : (j.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq j.right))).unop =
      (l.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq l.right))).unop :=
    SimplexCategory.Hom.ext_zero_left _ _ hval
  have hjl : j.right = l.right :=
    (simplexTrunc0OpObjEq j.right).trans (simplexTrunc0OpObjEq l.right).symm
  apply StructuredArrow.obj_ext j l hjl
  have hL : trunc0Incl.obj j.right = trunc0Incl.obj l.right := congrArg trunc0Incl.obj hjl
  have ht : j.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq j.right)) =
      l.hom ≫ eqToHom (congrArg trunc0Incl.obj
      (simplexTrunc0OpObjEq l.right)) := by
    simpa using congrArg Quiver.Hom.op hφ
  have htransport : trunc0Incl.map (eqToHom hjl) = eqToHom hL :=
    CategoryTheory.eqToHom_map trunc0Incl hjl
  rw [htransport]
  apply (cancel_mono (eqToHom (congrArg trunc0Incl.obj
    (simplexTrunc0OpObjEq l.right)))).mp
  calc
    j.hom ≫ eqToHom hL ≫ eqToHom (congrArg trunc0Incl.obj
        (simplexTrunc0OpObjEq l.right)) =
        j.hom ≫ eqToHom (congrArg trunc0Incl.obj
          (simplexTrunc0OpObjEq j.right)) := by
      have hp : hL.trans (congrArg trunc0Incl.obj (simplexTrunc0OpObjEq l.right)) =
          congrArg trunc0Incl.obj (simplexTrunc0OpObjEq j.right) := Subsingleton.elim _ _
      simp
    _ = l.hom ≫ eqToHom (congrArg trunc0Incl.obj
        (simplexTrunc0OpObjEq l.right)) := ht

/-- The vertices of `⦋1⦌` that are named by the matching category. -/
private noncomputable def coveredIdx (k : ℕ) :
    Set ((simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1)) :=
  Set.range (vertexCoord.{w} k)

/-- The matching category indexes the covered vertices of `⦋1⦌`. -/
private noncomputable def vertexEquivCovered (k : ℕ) :
    VertexOverOne ≃ coveredIdx.{w} k :=
  Equiv.ofInjective _ (vertexCoord_injective.{w} k)

/-- The vertices of `⦋1⦌` split into the covered ones and the rest. -/
private noncomputable def coveredSumEquiv (k : ℕ) :
    (coveredIdx.{w} k) ⊕
        {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
          a ∉ coveredIdx.{w} k} ≃
      (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) :=
  @Equiv.sumCompl _ (fun a => a ∈ coveredIdx.{w} k)
    (fun _ => Classical.propDecidable _)

/-- The splitting equivalence is the inclusion on the covered vertices. -/
private theorem coveredSumEquiv_inl (k : ℕ) (q : coveredIdx.{w} k) :
    coveredSumEquiv.{w} k (Sum.inl q) = (q : (simplexPowerIndex.{w} k).obj
      (SimplexCategory.mk 1)) := rfl

/-- Over a discrete index category a limit is the product of the values. -/
private noncomputable def discreteLimitIso {J : Type a} [Category.{b} J] [IsDiscrete J]
    {D : Type c} [Category.{d} D] (G : J ⥤ D) [HasLimit G] [HasProduct G.obj] :
    limit G ≅ ∏ᶜ G.obj where
  hom := Pi.lift fun j => limit.π G j
  inv := limit.lift G (discreteLimitCone G)
  hom_inv_id := by
    apply limit.hom_ext
    intro j
    simp [discreteLimitCone]
  inv_hom_id := by
    apply Pi.hom_ext
    intro j
    simp [Category.assoc, discreteLimitCone]

/-- The `0`-truncation of the power `Hom(C[k], T)` of a constant simplicial object. -/
private noncomputable abbrev constPowerTrunc (k : ℕ) {D : Type u} [Category.{v} D] (T : D)
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj n.unop =>
      ((SimplicialObject.const D).obj T).obj n] :
    SimplicialObject.Truncated D 0 :=
  (SimplicialObject.truncation 0).obj
    (((SimplicialObject.const D).obj T).power (simplexPowerIndex.{w} k))

/-- In degree one every matching component of `Hom(C[k], T)` is a copy of `T`. -/
private noncomputable def vertexCompIso (k : ℕ) {D : Type u} [Category.{v} D] (T : D)
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj n.unop =>
      ((SimplicialObject.const D).obj T).obj n]
    (j : VertexOverOne) :
    (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k T).obj j ≅ T := by
  letI : Unique ((simplexPowerIndex.{w} k).obj (trunc0Incl.obj j.right).unop) :=
    uniqueUliftCoyonedaTrunc0 k j.right
  change (∏ᶜ fun _ : (simplexPowerIndex.{w} k).obj
    (trunc0Incl.obj j.right).unop => T) ≅ T
  exact CategoryTheory.Limits.productUniqueIso _

/-- The matching isomorphism of `Hom(C[k], T)` in degree one: the matching object is the product
of the copies of `T` indexed by the covered vertices of `⦋1⦌`. -/
private noncomputable def matchIso (k : ℕ) {D : Type u} [Category.{v} D] (T : D)
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj n.unop =>
      ((SimplicialObject.const D).obj T).obj n]
    [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ D, trunc0Incl.HasRightKanExtension F]
    [Functor.HasPointwiseRightKanExtension trunc0Incl (constPowerTrunc.{w} k T)]
    [HasLimit (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k T)]
    [HasProduct (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k T).obj]
    [HasProduct fun _ : VertexOverOne => T]
    [HasProduct fun _ : coveredIdx.{w} k => T] :
    (trunc0Incl.ran.obj (constPowerTrunc.{w} k T)).obj degOne ≅
      ∏ᶜ fun _ : coveredIdx.{w} k => T :=
  (((Functor.ranObjObjIsoLimit trunc0Incl (constPowerTrunc.{w} k T) degOne).trans
        (discreteLimitIso
          (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k T))).trans
      (piIsoOfComponents _ (fun _ : VertexOverOne => T) (vertexCompIso.{w} k T))).trans
    (piReindexIso (vertexEquivCovered.{w} k).symm (fun _ : VertexOverOne => T))

/-- The degree-one component of the matching isomorphism reads off a single coordinate of the
limit over the matching category. -/
private theorem matchIso_hom_π (k : ℕ) {D : Type u} [Category.{v} D] (Y : D)
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj n.unop =>
      ((SimplicialObject.const D).obj Y).obj n]
    [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ D, trunc0Incl.HasRightKanExtension F]
    [Functor.HasPointwiseRightKanExtension trunc0Incl (constPowerTrunc.{w} k Y)]
    [HasLimit (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y)]
    [HasProduct (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y).obj]
    [HasProduct fun _ : VertexOverOne => Y]
    [HasProduct fun _ : coveredIdx.{w} k => Y]
    [HasProduct fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) => Y]
    [HasProduct fun _ : {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
      a ∉ coveredIdx.{w} k} => Y]
    [HasProduct fun _ : (coveredIdx.{w} k) ⊕
      {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
        a ∉ coveredIdx.{w} k} => Y]
    [HasBinaryProduct (∏ᶜ fun _ : coveredIdx.{w} k => Y)
      (∏ᶜ fun _ : {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
        a ∉ coveredIdx.{w} k} => Y)]
    (j : VertexOverOne) :
    (matchIso.{w} k Y).hom ≫ Pi.π (fun _ : coveredIdx.{w} k => Y)
        (vertexEquivCovered.{w} k j) =
      (trunc0Incl.ranObjObjIsoLimit (constPowerTrunc.{w} k Y) degOne).hom ≫
        limit.π (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y) j ≫
          (vertexCompIso.{w} k Y j).hom := by
  have hlift := CategoryTheory.Limits.Pi.lift_π
    (f := (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y).obj)
    (p := fun i : VertexOverOne =>
      limit.π (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y) i) j
  have hreindex := CategoryTheory.Limits.Pi.lift_π
    (f := fun _ : coveredIdx.{w} k => Y)
    (p := fun b : coveredIdx.{w} k =>
      Pi.π (fun _ : VertexOverOne => Y) ((vertexEquivCovered.{w} k).symm b))
    (vertexEquivCovered.{w} k j)
  have hmap := CategoryTheory.Limits.Pi.map'_comp_π
    (f := (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y).obj)
    (g := fun _ : VertexOverOne => Y) (fun a : VertexOverOne => a)
    (fun a : VertexOverOne => (vertexCompIso.{w} k Y a).hom) j
  dsimp [matchIso, discreteLimitIso]
  simp only [Category.assoc, piReindexIso, piIsoOfComponents]
  rw [hreindex, Equiv.symm_apply_apply, hmap,
    ← Category.assoc (f := Pi.lift fun i : VertexOverOne =>
        limit.π (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y) i)
      (g := Pi.π (StructuredArrow.proj degOne trunc0Incl ⋙
        constPowerTrunc.{w} k Y).obj j)
      (h := (vertexCompIso.{w} k Y j).hom), hlift]

/-- In degree one the unit of the `0`-coskeleton adjunction at `Hom(C[k], Y)`, read through the
matching isomorphism, is the projection onto the covered vertices of `⦋1⦌`.

This is shared by the `Y` and the `Z` halves of
`constPowerMap_matching_prop_zero`; it is a declaration of its own both because the two
halves are the same argument and because the elaboration budget is per declaration. -/
private theorem unit_comp_matchIso (k : ℕ) {D : Type u} [Category.{v} D] (Y : D)
    [∀ n : SimplexCategoryᵒᵖ, HasProduct fun _ : (simplexPowerIndex.{w} k).obj n.unop =>
      ((SimplicialObject.const D).obj Y).obj n]
    [∀ F : (SimplexCategory.Truncated 0)ᵒᵖ ⥤ D, trunc0Incl.HasRightKanExtension F]
    [Functor.HasPointwiseRightKanExtension trunc0Incl (constPowerTrunc.{w} k Y)]
    [HasLimit (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y)]
    [HasProduct (StructuredArrow.proj degOne trunc0Incl ⋙ constPowerTrunc.{w} k Y).obj]
    [HasProduct fun _ : VertexOverOne => Y]
    [HasProduct fun _ : coveredIdx.{w} k => Y]
    [HasProduct fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) => Y]
    [HasProduct fun _ : {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
      a ∉ coveredIdx.{w} k} => Y]
    [HasProduct fun _ : (coveredIdx.{w} k) ⊕
      {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
        a ∉ coveredIdx.{w} k} => Y]
    [HasBinaryProduct (∏ᶜ fun _ : coveredIdx.{w} k => Y)
      (∏ᶜ fun _ : {a : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) //
        a ∉ coveredIdx.{w} k} => Y)] :
    (((SimplicialObject.coskAdj 0).unit.app
          (((SimplicialObject.const D).obj Y).power (simplexPowerIndex.{w} k))).app
        degOne) ≫ (matchIso.{w} k Y).hom =
      eqToHom (SimplicialObject.power_obj ((SimplicialObject.const D).obj Y)
          (simplexPowerIndex.{w} k) degOne) ≫
        (piSplitIso (coveredSumEquiv.{w} k)
            (fun _ : (simplexPowerIndex.{w} k).obj (SimplexCategory.mk 1) => Y)).hom ≫
          prod.fst := by
  classical
  let U : CosimplicialObject (Type w) := simplexPowerIndex.{w} k
  let PY : SimplicialObject D := ((SimplicialObject.const D).obj Y).power U
  let d1 := degOne
  let L0 := trunc0Incl
  let J0 := VertexOverOne
  let : Unique (SimplexCategory.Truncated 0) := uniqueTrunc0
  let : IsDiscrete J0 := isDiscrete_verticesOverOne
  let : Fintype (SimplexCategory.Truncated 0) := Fintype.ofFinite _
  let : Fintype (SimplexCategory.Truncated 0)ᵒᵖ := Fintype.ofFinite _
  let : ∀ j : (SimplexCategory.Truncated 0)ᵒᵖ, Fintype (d1 ⟶ L0.obj j) := fintypeDegOneHom
  let : Fintype J0 := fintypeVertexOverOne
  let FY := (SimplicialObject.truncation 0).obj PY
  let GY := StructuredArrow.proj d1 L0 ⋙ FY
  let e0 := degZeroPoint.{w} k
  let coord := vertexCoord.{w} k
  let β := coveredIdx.{w} k
  let : Fintype β := Fintype.ofEquiv J0 (vertexEquivCovered.{w} k)
  let eSum := coveredSumEquiv.{w} k
  let splitY := piSplitIso eSum (fun _ : U.obj (SimplexCategory.mk 1) => Y)
  let compY := vertexCompIso.{w} k Y
  let matchY := matchIso.{w} k Y
  show (((SimplicialObject.coskAdj 0).unit.app PY).app d1) ≫ matchY.hom =
      eqToHom (SimplicialObject.power_obj
        ((SimplicialObject.const D).obj (Y)) U d1) ≫
        splitY.hom ≫ prod.fst
  have hcoordY (j : J0) :
        (((SimplicialObject.coskAdj 0).unit.app PY).app d1) ≫ matchY.hom ≫
        Pi.π (fun _ : β => Y) ((vertexEquivCovered.{w} k) j) =
          eqToHom (SimplicialObject.power_obj
            ((SimplicialObject.const D).obj (Y)) U d1) ≫
            Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) (coord j) := by
    have htri :
        ((SimplicialObject.coskAdj 0).unit.app PY).app (L0.obj j.right) ≫
          (L0.ranCounit.app FY).app j.right = 𝟙 (FY.obj j.right) := by
      have h := congrArg (fun t : FY ⟶ FY => t.app j.right)
        ((SimplicialObject.coskAdj 0).left_triangle_components PY)
      dsimp only [NatTrans.comp_app, NatTrans.id_app] at h
      dsimp [SimplicialObject.truncation] at h
      simp only [SimplicialObject.coskAdj] at h
      convert h using 1;
        simp [L0, FY, SimplicialObject.truncation, SimplicialObject.coskAdj,
          Functor.ranCounit]
    have hnat :
        (((SimplicialObject.coskAdj 0).unit.app PY).app d1) ≫
            (L0.ran.obj FY).map j.hom =
          PY.map j.hom ≫
            ((SimplicialObject.coskAdj 0).unit.app PY).app (L0.obj j.right) := by
      have hnat' := ((SimplicialObject.coskAdj 0).unit.app PY).naturality j.hom
      change PY.map j.hom ≫
          ((SimplicialObject.coskAdj 0).unit.app PY).app (L0.obj j.right) =
        ((SimplicialObject.coskAdj 0).unit.app PY).app d1 ≫
          ((SimplicialObject.Truncated.cosk 0).obj FY).map j.hom at hnat'
      have hmap : (L0.ran.obj FY).map j.hom =
          ((SimplicialObject.Truncated.cosk 0).obj FY).map j.hom := by
        rfl
      rw [hmap] at hnat'
      exact hnat'.symm
    let : Unique (U.obj (L0.obj j.right).unop) :=
      uniqueUliftCoyonedaTrunc0 k j.right
    have hindex : (U.map (eqToHom (congrArg L0.obj
        (simplexTrunc0OpObjEq j.right))).unop) e0 =
          (default : U.obj (L0.obj j.right).unop) :=
      Subsingleton.elim _ _
    have hcoordIndex :
        (U.map j.hom.unop) (default : U.obj (L0.obj j.right).unop) =
          coord j := by
      dsimp [coord, vertexCoord]
      rw [Functor.map_comp]
      exact congrArg (U.map j.hom.unop) hindex.symm
    have hcore : PY.map j.hom ≫ (compY j).hom =
          eqToHom (SimplicialObject.power_obj
            ((SimplicialObject.const D).obj (Y)) U d1) ≫
            Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) (coord j) := by
      let : Unique (U.obj (L0.obj j.right).unop) :=
        uniqueUliftCoyonedaTrunc0 k j.right
      show (((SimplicialObject.const D).obj (Y)).power U).map j.hom ≫
          (CategoryTheory.Limits.productUniqueIso
            (fun _ : U.obj (L0.obj j.right).unop => Y)).hom =
        eqToHom (SimplicialObject.power_obj
          ((SimplicialObject.const D).obj (Y)) U d1) ≫
          Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) (coord j)
      have hp := power_map_productUniqueIso
        ((SimplicialObject.const D).obj (Y)) U j.hom
      simpa only [CategoryTheory.Limits.productUniqueIso_hom, hcoordIndex,
        Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
        Category.assoc] using hp
    have hmπ : matchY.hom ≫ Pi.π (fun _ : β => Y)
        ((vertexEquivCovered.{w} k) j) =
        (L0.ranObjObjIsoLimit FY d1).hom ≫ limit.π GY j ≫ (compY j).hom :=
      matchIso_hom_π k Y j
    rw [hmπ]
    rw [← Category.assoc (f := (L0.ranObjObjIsoLimit FY d1).hom)
      (g := limit.π GY j) (h := (compY j).hom)]
    rw [Functor.ranObjObjIsoLimit_hom_π]
    simp only [← Category.assoc]
    rw [hnat]
    simp only [Category.assoc, reassoc_of% htri]
    exact (PY.map j.hom ≫= Category.id_comp (compY j).hom).trans hcore
  apply Pi.hom_ext
  intro q
  calc
    _ = eqToHom (SimplicialObject.power_obj
          ((SimplicialObject.const D).obj (Y)) U d1) ≫
          Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y)
            (coord ((vertexEquivCovered.{w} k).symm q)) := by
          simpa using hcoordY ((vertexEquivCovered.{w} k).symm q)
    _ = eqToHom (SimplicialObject.power_obj
          ((SimplicialObject.const D).obj (Y)) U d1) ≫
          Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) q.1 :=
          congrArg (fun a => eqToHom (SimplicialObject.power_obj
            ((SimplicialObject.const D).obj (Y)) U d1) ≫
              Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) a)
            (congrArg Subtype.val (Equiv.apply_symm_apply (vertexEquivCovered.{w} k) q))
    _ = (eqToHom (SimplicialObject.power_obj
          ((SimplicialObject.const D).obj (Y)) U d1) ≫
            splitY.hom ≫ prod.fst) ≫ Pi.π (fun _ : β => Y) q := by
          have hp := piSplitIso_fst_π eSum
            (fun _ : U.obj (SimplexCategory.mk 1) => Y) q
          have hp' : splitY.hom ≫ prod.fst ≫ Pi.π
              (fun _ : β => Y) q =
              Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) q.1 := by
            have he : eSum (Sum.inl q) = q.1 := coveredSumEquiv_inl k q
            rw [he] at hp
            calc
              _ = Pi.π (fun _ : U.obj (SimplexCategory.mk 1) => Y) q.1 := by
                simpa [splitY] using hp
              _ = _ := rfl
          simpa [Category.assoc] using (congrArg (fun f => eqToHom (SimplicialObject.power_obj
            ((SimplicialObject.const D).obj (Y)) U d1) ≫ f) hp').symm

/-- The degree-one matching map of `Hom(C[k], -)` at a covering morphism is covering.

This is the `n = 0` half of the matching hypothesis of Tag 01GH for `Hom(C[k], u)`; in degree one
the matching category is discrete, so the matching object is computed by hand. It is a declaration
of its own, rather than a branch of the tagged theorem, because the elaboration budget is per
declaration. -/
private theorem constPowerMap_matching_prop_zero
    {E : Type u₁} [Category.{v₁} E] [HasFiniteLimits E]
    [∀ (m : ℕ) (F : SimplicialObject.Truncated E m),
      (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F]
    (P : MorphismProperty E) [P.ContainsIdentities] [P.IsStableUnderComposition]
    [P.IsStableUnderBaseChange]
    (k : ℕ) {Y Z : E} (u : Z ⟶ Y) (hu : P u)
    [∀ r : SimplexCategoryᵒᵖ, Finite ((simplexPowerIndex.{w} k).obj r.unop)] :
    P
      (pullback.lift
        (f := (((SimplicialObject.coskAdj 0).unit.app
          (((SimplicialObject.const (E)).obj Y).power
            (simplexPowerIndex.{w} k))).app
            (Opposite.op (SimplexCategory.mk (1)))))
        (g := (((SimplicialObject.Truncated.cosk 0).map
          ((SimplicialObject.truncation 0).map (constPowerMap u (simplexPowerIndex.{w} k)))).app
            (Opposite.op (SimplexCategory.mk (1)))))
        ((constPowerMap u (simplexPowerIndex.{w} k)).app (Opposite.op (SimplexCategory.mk (1))))
        (((SimplicialObject.coskAdj 0).unit.app
          (((SimplicialObject.const (E)).obj Z).power
            (simplexPowerIndex.{w} k))).app
            (Opposite.op (SimplexCategory.mk (1))))
        (NatTrans.congr_app ((SimplicialObject.coskAdj 0).unit.naturality
          (constPowerMap u (simplexPowerIndex.{w} k)))
          (Opposite.op (SimplexCategory.mk (1))))) := by
  classical
  let : ∀ r : SimplexCategoryᵒᵖ,
      Fintype ((simplexPowerIndex.{w} k).obj r.unop) := fun _ => Fintype.ofFinite _
  let D := E
  let U : CosimplicialObject (Type w) := simplexPowerIndex.{w} k
  let PZ : SimplicialObject D := ((SimplicialObject.const D).obj Z).power U
  let PY : SimplicialObject D := ((SimplicialObject.const D).obj Y).power U
  let b : PZ ⟶ PY := constPowerMap u U
  show P
      (pullback.lift
        (f := (((SimplicialObject.coskAdj 0).unit.app PY).app
          (Opposite.op (SimplexCategory.mk (1)))))
        (g := (((SimplicialObject.Truncated.cosk 0).map
          ((SimplicialObject.truncation 0).map b)).app
            (Opposite.op (SimplexCategory.mk (1)))))
        (b.app (Opposite.op (SimplexCategory.mk (1))))
        (((SimplicialObject.coskAdj 0).unit.app PZ).app
          (Opposite.op (SimplexCategory.mk (1))))
        (NatTrans.congr_app ((SimplicialObject.coskAdj 0).unit.naturality b)
          (Opposite.op (SimplexCategory.mk (1)))))
  let d1 := degOne
  let L0 := trunc0Incl
  let J0 := VertexOverOne
  let : Unique (SimplexCategory.Truncated 0) := uniqueTrunc0
  let : IsDiscrete J0 := isDiscrete_verticesOverOne
  let : Fintype (SimplexCategory.Truncated 0) := Fintype.ofFinite _
  let : Fintype (SimplexCategory.Truncated 0)ᵒᵖ := Fintype.ofFinite _
  let : ∀ j : (SimplexCategory.Truncated 0)ᵒᵖ, Fintype (d1 ⟶ L0.obj j) := fintypeDegOneHom
  let : Fintype J0 := fintypeVertexOverOne
  let FY := (SimplicialObject.truncation 0).obj PY
  let FZ := (SimplicialObject.truncation 0).obj PZ
  let GY := StructuredArrow.proj d1 L0 ⋙ FY
  let GZ := StructuredArrow.proj d1 L0 ⋙ FZ
  let β := coveredIdx.{w} k
  let γ := {a : U.obj (SimplexCategory.mk 1) // a ∉ β}
  let eRange := vertexEquivCovered.{w} k
  let : Fintype β := Fintype.ofEquiv J0 eRange
  let : Fintype γ := Fintype.ofFinite _
  let : Unique (U.obj (SimplexCategory.mk 0)) := by
    show Unique (ULift (SimplexCategory.mk k ⟶ SimplexCategory.mk 0))
    infer_instance
  let eSum := coveredSumEquiv.{w} k
  let compY := vertexCompIso.{w} k Y
  let compZ := vertexCompIso.{w} k Z
  let matchY := matchIso.{w} k Y
  let matchZ := matchIso.{w} k Z
  let b0 := (SimplicialObject.truncation 0).map b
  let α : GZ ⟶ GY := Functor.whiskerLeft (StructuredArrow.proj d1 L0) b0
  let gOld := (((SimplicialObject.Truncated.cosk 0).map b0).app d1)
  have hRan : gOld ≫ (L0.ranObjObjIsoLimit FY d1).hom =
      (L0.ranObjObjIsoLimit FZ d1).hom ≫
        (limit.isLimit GY).map (limit.cone GZ) α := by
    apply limit.hom_ext
    intro j
    dsimp [gOld, α, b0]
    simp only [Category.assoc, L0.ranObjObjIsoLimit_hom_π]
    have hcosk :
        ((SimplicialObject.Truncated.cosk 0).map b0).app d1 =
          (L0.ran.map b0).app d1 := rfl
    rw [hcosk]
    have hmap := (L0.ran.map b0).naturality j.hom
    have hmap' : (L0.ran.obj FZ).map j.hom ≫ (L0.ran.map b0).app (L0.obj j.right) =
        (L0.ran.map b0).app d1 ≫ (L0.ran.obj FY).map j.hom := by
      simp [FY, FZ]
    have hε := congr_app (L0.ranCounit.naturality b0) j.right
    dsimp at hε
    have hlimitπ := IsLimit.map_π (limit.cone GZ) (limit.isLimit GY) α j
    dsimp [α] at hlimitπ
    have hisoπ : (L0.ranObjObjIsoLimit FZ d1).hom ≫ limit.π GZ j =
        (L0.ran.obj FZ).map j.hom ≫ (L0.ranCounit.app FZ).app j.right := by
      simp [GZ]
    rw [hlimitπ]
    rw [← Category.assoc (f := (L0.ranObjObjIsoLimit FZ d1).hom)
      (g := limit.π GZ j) (h := b0.app j.right), hisoπ]
    simp only [Category.assoc]
    calc
      _ = ((L0.ran.obj FZ).map j.hom ≫
          (L0.ran.map b0).app (L0.obj j.right)) ≫
          (L0.ranCounit.app FY).app j.right := by
              rw [← Category.assoc, ← hmap']
      _ = ((L0.ran.obj FZ).map j.hom ≫
          (L0.ranCounit.app FZ).app j.right) ≫ b0.app j.right := by
              calc
                _ = (L0.ran.obj FZ).map j.hom ≫
                    ((L0.ran.map b0).app (L0.obj j.right) ≫
                      (L0.ranCounit.app FY).app j.right) :=
                        Category.assoc _ _ _
                _ = (L0.ran.obj FZ).map j.hom ≫
                    ((L0.ranCounit.app FZ).app j.right ≫ b0.app j.right) := by
                      have hε' :
                          (L0.ran.map b0).app (L0.obj j.right) ≫
                              (L0.ranCounit.app FY).app j.right =
                            (L0.ranCounit.app FZ).app j.right ≫ b0.app j.right := by
                        simpa [FY, FZ] using hε
                      exact congrArg (fun q => (L0.ran.obj FZ).map j.hom ≫ q) hε'
                _ = ((L0.ran.obj FZ).map j.hom ≫
                      (L0.ranCounit.app FZ).app j.right) ≫ b0.app j.right :=
                        (Category.assoc _ _ _).symm
      _ = _ := Category.assoc _ _ _
  let ι := U.obj (SimplexCategory.mk 1)
  let γ := {a : ι // a ∉ β}
  let mβ : (∏ᶜ fun _ : β => Z) ⟶ ∏ᶜ fun _ : β => Y :=
    CategoryTheory.Limits.Pi.map fun _ : β => u
  let mγ : (∏ᶜ fun _ : γ => Z) ⟶ ∏ᶜ fun _ : γ => Y :=
    CategoryTheory.Limits.Pi.map fun _ : γ => u
  have hmatchYπ (j : J0) :
      matchY.hom ≫ Pi.π (fun _ : β => Y) (eRange j) =
        (L0.ranObjObjIsoLimit FY d1).hom ≫ limit.π GY j ≫ (compY j).hom :=
    matchIso_hom_π k Y j
  have hmatchZπ (j : J0) :
      matchZ.hom ≫ Pi.π (fun _ : β => Z) (eRange j) =
        (L0.ranObjObjIsoLimit FZ d1).hom ≫ limit.π GZ j ≫ (compZ j).hom :=
    matchIso_hom_π k Z j
  have hcompMap (j : J0) : b0.app j.right ≫ (compY j).hom =
      (compZ j).hom ≫ u := by
    rcases j with ⟨a, x, φ⟩
    let : Unique (U.obj (L0.obj x).unop) := uniqueUliftCoyonedaTrunc0 k x
    cases simplexTrunc0OpObjEq x
    show CategoryTheory.Limits.Pi.map
        (fun _ : U.obj (SimplexCategory.mk 0) => u) ≫
          (CategoryTheory.Limits.productUniqueIso
            (fun _ : U.obj (SimplexCategory.mk 0) => Y)).hom =
      (CategoryTheory.Limits.productUniqueIso
        (fun _ : U.obj (SimplexCategory.mk 0) => Z)).hom ≫ u
    exact piMap_comp_productUniqueIso_hom u
  have hmatchMap : gOld ≫ matchY.hom = matchZ.hom ≫ mβ := by
    apply Pi.hom_ext
    intro q
    let j := eRange.symm q
    have hj : eRange j = q := Equiv.apply_symm_apply eRange q
    have hlimitπ := IsLimit.map_π (limit.cone GZ) (limit.isLimit GY) α j
    dsimp [α] at hlimitπ
    calc
      _ = (gOld ≫ (L0.ranObjObjIsoLimit FY d1).hom ≫
            limit.π GY j) ≫ (compY j).hom := by
              rw [← hj]
              rw [Category.assoc, hmatchYπ j]
              simp [Category.assoc]
      _ = (((L0.ranObjObjIsoLimit FZ d1).hom ≫ limit.π GZ j) ≫
            b0.app j.right) ≫ (compY j).hom := by
              calc
                _ = ((gOld ≫ (L0.ranObjObjIsoLimit FY d1).hom) ≫
                      limit.π GY j) ≫ (compY j).hom := by simp [Category.assoc]
                _ = (((L0.ranObjObjIsoLimit FZ d1).hom ≫
                      (limit.isLimit GY).map (limit.cone GZ) α) ≫
                      limit.π GY j) ≫ (compY j).hom :=
                      congrArg (fun t => (t ≫ limit.π GY j) ≫ (compY j).hom) hRan
                _ = ((L0.ranObjObjIsoLimit FZ d1).hom ≫
                      ((limit.isLimit GY).map (limit.cone GZ) α ≫ limit.π GY j)) ≫
                      (compY j).hom := by simp [Category.assoc]
                _ = ((L0.ranObjObjIsoLimit FZ d1).hom ≫
                      (limit.π GZ j ≫ b0.app j.right)) ≫ (compY j).hom :=
                      congrArg (fun t =>
                        ((L0.ranObjObjIsoLimit FZ d1).hom ≫ t) ≫ (compY j).hom)
                        hlimitπ
                _ = (((L0.ranObjObjIsoLimit FZ d1).hom ≫ limit.π GZ j) ≫
                      b0.app j.right) ≫ (compY j).hom := by simp [Category.assoc]
      _ = ((L0.ranObjObjIsoLimit FZ d1).hom ≫ limit.π GZ j) ≫
            ((compZ j).hom ≫ u) := by
              simpa only [Category.assoc] using congrArg (fun t =>
                ((L0.ranObjObjIsoLimit FZ d1).hom ≫ limit.π GZ j) ≫ t)
                (hcompMap j)
      _ = (matchZ.hom ≫ Pi.π (fun _ : β => Z) (eRange j)) ≫ u := by
              rw [hmatchZπ]
              simp [Category.assoc]
      _ = matchZ.hom ≫ (Pi.π (fun _ : β => Z) q ≫ u) := by
              rw [hj]
              exact Category.assoc (f := matchZ.hom)
                (g := Pi.π (fun _ : β => Z) q) (h := u)
      _ = matchZ.hom ≫ (mβ ≫ Pi.π (fun _ : β => Y) q) := by
              congr 1
              simp [mβ]
      _ = (matchZ.hom ≫ mβ) ≫ Pi.π (fun _ : β => Y) q :=
              Category.assoc' (f := Pi.π (fun _ : β => Y) q)
                (g := mβ) (h := matchZ.hom)
  have hobjY : PY.obj d1 = ∏ᶜ fun _ : ι => Y := by rfl
  have hobjZ : PZ.obj d1 = ∏ᶜ fun _ : ι => Z := by rfl
  let toPY : PY.obj d1 ⟶ ∏ᶜ fun _ : ι => Y := eqToHom hobjY
  let toPZ : PZ.obj d1 ⟶ ∏ᶜ fun _ : ι => Z := eqToHom hobjZ
  have htoPY : toPY = 𝟙 _ := by cases hobjY; rfl
  have htoPZ : toPZ = 𝟙 _ := by cases hobjZ; rfl
  let splitY := piSplitIso eSum (fun _ : ι => Y)
  let splitZ := piSplitIso eSum (fun _ : ι => Z)
  let eFullY : PY.obj d1 ≅ (∏ᶜ fun _ : β => Y) ⨯
      (∏ᶜ fun _ : γ => Y) := (asIso toPY).trans splitY
  let eFullZ : PZ.obj d1 ≅ (∏ᶜ fun _ : β => Z) ⨯
      (∏ᶜ fun _ : γ => Z) := (asIso toPZ).trans splitZ
  have hunitY :
      (((SimplicialObject.coskAdj 0).unit.app PY).app d1) ≫ matchY.hom =
        eqToHom (SimplicialObject.power_obj
          ((SimplicialObject.const D).obj (Y)) U d1) ≫
          splitY.hom ≫ prod.fst := unit_comp_matchIso k Y
  have hunitZ :
      (((SimplicialObject.coskAdj 0).unit.app PZ).app d1) ≫ matchZ.hom =
        eqToHom (SimplicialObject.power_obj
          ((SimplicialObject.const D).obj (Z)) U d1) ≫
          splitZ.hom ≫ prod.fst := unit_comp_matchIso k Z
  have hunitY' :
      (((SimplicialObject.coskAdj 0).unit.app PY).app d1) ≫ matchY.hom =
        eFullY.hom ≫ prod.fst := by
    have h : eFullY.hom ≫ prod.fst = toPY ≫ splitY.hom ≫ prod.fst := by
      simp [eFullY, Category.assoc]; rfl
    rw [h]
    exact hunitY
  have hunitZ' :
      (((SimplicialObject.coskAdj 0).unit.app PZ).app d1) ≫ matchZ.hom =
        eFullZ.hom ≫ prod.fst := by
    have h : eFullZ.hom ≫ prod.fst = toPZ ≫ splitZ.hom ≫ prod.fst := by
      simp [eFullZ, Category.assoc]; rfl
    rw [h]
    exact hunitZ
  have hcoord (a : ι) :
      b.app d1 ≫ toPY ≫ Pi.π (fun _ : ι => Y) a =
        toPZ ≫ Pi.π (fun _ : ι => Z) a ≫ u := by
    rw [htoPY, htoPZ]
    dsimp [b, constPowerMap, PZ, PY, SimplicialObject.power]
    simpa only [Category.assoc, Category.comp_id, Category.id_comp] using
      (CategoryTheory.Limits.Pi.map_π (fun _ : ι => u) a)
  have hsplitMap : b.app d1 ≫ eFullY.hom =
      eFullZ.hom ≫ prod.map mβ mγ := by
    apply prod.hom_ext
    · apply Pi.hom_ext
      intro s
      calc
        _ = b.app d1 ≫ toPY ≫ splitY.hom ≫ prod.fst ≫
              Pi.π (fun _ : β => Y) s := by
                simp [eFullY, Category.assoc]; rfl
        _ = b.app d1 ≫ toPY ≫ Pi.π (fun _ : ι => Y) (eSum (Sum.inl s)) :=
              congrArg (fun q => b.app d1 ≫ toPY ≫ q)
                (piSplitIso_fst_π eSum (fun _ : ι => Y) s)
        _ = toPZ ≫ Pi.π (fun _ : ι => Z) (eSum (Sum.inl s)) ≫ u :=
              hcoord (eSum (Sum.inl s))
        _ = ((eFullZ.hom ≫ prod.map mβ mγ) ≫ prod.fst) ≫
              Pi.π (fun _ : β => Y) s := by
              calc
                _ = toPZ ≫ splitZ.hom ≫ prod.fst ≫
                      Pi.π (fun _ : β => Z) s ≫ u := by
                    simpa only [Category.assoc] using
                      congrArg (fun q => toPZ ≫ q ≫ u)
                        (piSplitIso_fst_π eSum (fun _ : ι => Z) s).symm
                _ = ((eFullZ.hom ≫ prod.map mβ mγ) ≫ prod.fst) ≫
                      Pi.π (fun _ : β => Y) s := by
                    simp [eFullZ, mβ, mγ, Category.assoc]; rfl
    · apply Pi.hom_ext
      intro s
      calc
        _ = b.app d1 ≫ toPY ≫ splitY.hom ≫ prod.snd ≫
              Pi.π (fun _ : γ => Y) s := by
                simp [eFullY, Category.assoc]; rfl
        _ = b.app d1 ≫ toPY ≫ Pi.π (fun _ : ι => Y) (eSum (Sum.inr s)) :=
              congrArg (fun q => b.app d1 ≫ toPY ≫ q)
                (piSplitIso_snd_π eSum (fun _ : ι => Y) s)
        _ = toPZ ≫ Pi.π (fun _ : ι => Z) (eSum (Sum.inr s)) ≫ u :=
              hcoord (eSum (Sum.inr s))
        _ = ((eFullZ.hom ≫ prod.map mβ mγ) ≫ prod.snd) ≫
              Pi.π (fun _ : γ => Y) s := by
              calc
                _ = toPZ ≫ splitZ.hom ≫ prod.snd ≫
                      Pi.π (fun _ : γ => Z) s ≫ u := by
                    simpa only [Category.assoc] using
                      congrArg (fun q => toPZ ≫ q ≫ u)
                        (piSplitIso_snd_π eSum (fun _ : ι => Z) s).symm
                _ = ((eFullZ.hom ≫ prod.map mβ mγ) ≫ prod.snd) ≫
                      Pi.π (fun _ : γ => Y) s := by
                    simp [eFullZ, mβ, mγ, Category.assoc]; rfl
  let fOld := (((SimplicialObject.coskAdj 0).unit.app PY).app d1)
  let pNew := pullback.map fOld gOld prod.fst mβ eFullY.hom matchZ.hom matchY.hom
    (by simpa [eFullY] using hunitY') hmatchMap
  let : IsIso eFullY.hom := inferInstance
  let : IsIso matchZ.hom := inferInstance
  let : IsIso matchY.hom := inferInstance
  let ePB : pullback fOld gOld ≅ pullback prod.fst mβ := asIso pNew
  let eTarget := ePB.trans (pullbackProdFstIso mβ)
  let mOld := pullback.lift (b.app d1)
    (((SimplicialObject.coskAdj 0).unit.app PZ).app d1)
    (NatTrans.congr_app ((SimplicialObject.coskAdj 0).unit.naturality b) d1)
  have hmOldFst : mOld ≫ pullback.fst fOld gOld = b.app d1 :=
    pullback.lift_fst (f := fOld) (g := gOld) (b.app d1)
      (((SimplicialObject.coskAdj 0).unit.app PZ).app d1)
      (NatTrans.congr_app ((SimplicialObject.coskAdj 0).unit.naturality b) d1)
  have hmOldSnd : mOld ≫ pullback.snd fOld gOld =
      ((SimplicialObject.coskAdj 0).unit.app PZ).app d1 :=
    pullback.lift_snd (f := fOld) (g := gOld) (b.app d1)
      (((SimplicialObject.coskAdj 0).unit.app PZ).app d1)
      (NatTrans.congr_app ((SimplicialObject.coskAdj 0).unit.naturality b) d1)
  have hmOld : mOld ≫ eTarget.hom = eFullZ.hom ≫ prod.map (𝟙 _) mγ := by
    have hpNew : pNew ≫ pullback.snd prod.fst mβ =
        pullback.snd fOld gOld ≫ matchZ.hom := by
      dsimp [pNew, pullback.map]
      simp only [pullback.lift_snd]
    have hpNewFst : pNew ≫ pullback.fst prod.fst mβ =
        pullback.fst fOld gOld ≫ eFullY.hom := by
      dsimp [pNew, pullback.map]
      simp only [pullback.lift_fst]
    apply prod.hom_ext
    · calc
        _ = (mOld ≫ pNew) ≫ (pullbackProdFstIso mβ).hom ≫ prod.fst := by
              simp [eTarget, ePB, Category.assoc]
        _ = (mOld ≫ pNew) ≫ pullback.snd prod.fst mβ := by
              simp [pullbackProdFstIso, Category.assoc]
        _ = mOld ≫ (pullback.snd fOld gOld ≫ matchZ.hom) := by
              rw [Category.assoc, hpNew]
        _ = (((SimplicialObject.coskAdj 0).unit.app PZ).app d1) ≫ matchZ.hom := by
              simpa only [Category.assoc] using congrArg (fun q => q ≫ matchZ.hom) hmOldSnd
        _ = eFullZ.hom ≫ prod.fst := hunitZ'
        _ = (eFullZ.hom ≫ prod.map (𝟙 _) mγ) ≫ prod.fst := by simp [Category.assoc]
    · calc
        _ = (mOld ≫ pNew) ≫ (pullbackProdFstIso mβ).hom ≫ prod.snd := by
              simp [eTarget, ePB, Category.assoc]
        _ = (mOld ≫ pNew) ≫ pullback.fst prod.fst mβ ≫ prod.snd := by
              simp [pullbackProdFstIso, Category.assoc]
        _ = mOld ≫ (pullback.fst fOld gOld ≫ eFullY.hom) ≫ prod.snd := by
              simpa only [Category.assoc] using congrArg (fun q => (mOld ≫ q) ≫ prod.snd) hpNewFst
        _ = (b.app d1 ≫ eFullY.hom) ≫ prod.snd := by
              simpa only [Category.assoc] using
                congrArg (fun q => (q ≫ eFullY.hom) ≫ prod.snd) hmOldFst
        _ = (eFullZ.hom ≫ prod.map mβ mγ) ≫ prod.snd :=
              congrArg (fun q => q ≫ prod.snd) hsplitMap
        _ = (eFullZ.hom ≫ prod.map (𝟙 _) mγ) ≫ prod.snd := by simp [mβ, Category.assoc]
  have hmCover : P (mOld ≫ eTarget.hom) := by
    rw [hmOld]
    have hpi (κ : Type w) [Finite κ] : P (CategoryTheory.Limits.Pi.map fun _ : κ => u) :=
      prop_piMap (P := P) (A := fun _ : κ => Z) (B := fun _ : κ => Y) (f := fun _ => u)
        (hf := fun _ => hu)
    have hid : P (𝟙 (∏ᶜ fun _ : β => Z)) :=
      prop_of_isIso P (𝟙 _)
    have hprod := CategoryTheory.MorphismProperty.prod_map P _ _ hid (hpi γ)
    exact (P.cancel_left_of_respectsIso eFullZ.hom _).2 hprod
  exact (P.cancel_right_of_respectsIso mOld eTarget.hom).1 hmCover

end Stacks.CategoryTheory.Hypercovering
