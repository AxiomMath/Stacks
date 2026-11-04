module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftRefine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq

/-!
# The chart projections of the base-change comparison of a commutative square

Let `p : W ⟶ Z` be a commutative square over `g : Y ⟶ X` of algebraic spaces over a scheme `S`,
with `W` over `Y` and `Z` over `X`.  This file reads the comparison
`AlgebraicGeometry.Space.pushforwardSquareMap` `Z_* 𝒪_Z ⟶ g_* (W_* 𝒪_W)` at an étale chart `V`
of `X` and then at a chart above the base change of a chart diagram `U ⟶ V`:
`AlgebraicGeometry.Space.directImageChartProjection_pushforwardSquareMap_aux` identifies the
result with pullback of the reading at a chart of `Z`.

## Implementation notes

The comparison is declared with the direct-image algebras
`AlgebraicGeometry.Space.pushforwardAlgebra` as source and target, while its factors are stated
with `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor` of the structure sheaf.  The
chart computation is carried out entirely in the second spelling, the comparison being supplied as
a morphism `Φ` equal to its factors; the two spellings are compared, as sheaves, by
`AlgebraicGeometry.Space.squareChartMap_heq_aux` of
`StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChartSquare`.

**The imports of this file are chosen so that the instances agree.**  The declarations of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism` are elaborated in an
environment where the sheaf condition along `forget₂ CommRingCat RingCat` on a small étale site is
found by `CategoryTheory.hasSheafComposeEssentiallySmallSite`.  This file imports nothing that
provides another instance of that class (such as
`Stacks.instHasSheafComposeForget₂CommRingCatRingCat` of
`StacksFrontier.CategoryTheory.Sites.Sheaf.HasSheafComposeForgetRing`), so that the terms it builds
agree with those declarations; with a different instance the kernel check of
`AlgebraicGeometry.Space.directImageChartProjection_pushforwardSquareMap_aux` does not finish in
the default budget.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-! ### Chart projections at the index of a chart diagram -/

section General

variable {A C : AlgebraicSpaces B S hS}

/-- Chart projections at equal indices agree. -/
theorem directImageChartProjection_congr (q : A ⟶ C) (V : SmallEtale B S hS C.1)
    {j j' : StructuredArrow (op (chartBaseChange B S hS q V)) (comparisonFunctor B S hS A).op}
    (h : j = j') (F : Sheaf (SmallEtale.topology B S hS A.1) (Type u))
    (a : (smallEtaleDirectImage B S hS q ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS C.1) (op V)).obj F) :
    HEq ((directImageChartProjection B S hS q V j).app F a)
      ((directImageChartProjection B S hS q V j').app F a) := by
  subst h
  rfl

/-- Reading at the index of the chart diagram of an index is reading at that index. -/
private theorem directImageChartProjection_index_chartDiagramOfIndex (q : A ⟶ C)
    (V : SmallEtale B S hS C.1)
    (j : StructuredArrow (op (chartBaseChange B S hS q V)) (comparisonFunctor B S hS A).op)
    (F : Sheaf (SmallEtale.topology B S hS A.1) (Type u))
    (a : (smallEtaleDirectImage B S hS q ⋙
      Sheaf.sectionsFunctor (SmallEtale.topology B S hS C.1) (op V)).obj F) :
    HEq ((directImageChartProjection B S hS q V
      (indexOfChartDiagram B S hS q (chartDiagramOfIndex B S hS q V j))).app F a)
      ((directImageChartProjection B S hS q V j).app F a) :=
  directImageChartProjection_congr B S hS q V
    (indexOfChartDiagram_chartDiagramOfIndex B S hS q V j) F a

/-- **Transport along an equality of morphisms.**  Reading a section of `q₁_* 𝒪` over `V`, moved
to `q₂_* 𝒪` along `q₁ = q₂`, at the index of a chart diagram over `q₂` is reading it at the index
of the same chart diagram over `q₁`. -/
theorem directImageChartProjection_eqToHom {q₁ q₂ : A ⟶ C} (h : q₁ = q₂)
    (V : SmallEtale B S hS C.1) (U : SmallEtale B S hS A.1)
    (m₁ m₂ : (SmallEtale.toOver B S hS A.1).obj U ⟶ (SmallEtale.toOver B S hS C.1).obj V)
    (hm : m₁ = m₂)
    (hc₁ : U.1.hom ≫ q₁.hom = yoneda.map m₁ ≫ V.1.hom)
    (hc₂ : U.1.hom ≫ q₂.hom = yoneda.map m₂ ≫ V.1.hom)
    (x : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q₁).toToposHom).obj
      (smallEtaleRingedTopos B S hS A).O).obj.obj (op V)) :
    (directImageChartProjection B S hS q₂ V
          (indexOfChartDiagram B S hS q₂ ⟨U, V, m₂, hc₂⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A).O)
        ((eqToHom (congrArg (fun q : A ⟶ C ↦ (pushforwardCommRingFunctor
          (smallEtaleRingedToposHom B S hS q).toToposHom).obj
            (smallEtaleRingedTopos B S hS A).O) h)).hom.app (op V) x) =
      (directImageChartProjection B S hS q₁ V
          (indexOfChartDiagram B S hS q₁ ⟨U, V, m₁, hc₁⟩)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A).O) x := by
  subst h hm
  rfl

/-- Regrouping the first three factors of a composite as a named morphism.  Stated at
variables so that no composite of sheaves is reassociated in place. -/
theorem comp₃_comp_eq_of_eq {C : Type*} [Category C] {a b c d e : C} (f₁ : a ⟶ b) (f₂ : b ⟶ c)
    (f₃ : c ⟶ d) (r : d ⟶ e) {k : a ⟶ d} (hk : k = f₁ ≫ f₂ ≫ f₃) :
    f₁ ≫ f₂ ≫ f₃ ≫ r = k ≫ r := by
  subst hk
  simp only [Category.assoc]

/-- The underlying morphism of sheaves of sets of a morphism of sheaves of commutative rings,
on sections. -/
theorem sheafCompose_forget_map_hom_app_apply {C : Type*} [Category C]
    {J : GrothendieckTopology C} [J.HasSheafCompose (forget CommRingCat.{u})]
    {P Q : Sheaf J CommRingCat.{u}} (Φ : P ⟶ Q) (U : Cᵒᵖ) (t : P.obj.obj U) :
    ((sheafCompose J (forget CommRingCat.{u})).map Φ).hom.app U t = Φ.hom.app U t :=
  rfl

/-- A four-fold composite of morphisms of sheaves of commutative rings, on sections.  Stated at
variables so that it is checked once. -/
theorem sheaf_comp₄_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P₀ P₁ P₂ P₃ P₄ : Sheaf J CommRingCat.{u}} (f₁ : P₀ ⟶ P₁) (f₂ : P₁ ⟶ P₂)
    (f₃ : P₂ ⟶ P₃) (f₄ : P₃ ⟶ P₄) (U : Cᵒᵖ) (t : P₀.obj.obj U) :
    (f₁ ≫ f₂ ≫ f₃ ≫ f₄).hom.app U t =
      f₄.hom.app U (f₃.hom.app U (f₂.hom.app U (f₁.hom.app U t))) :=
  rfl

/-- An isomorphism of sheaves of commutative rings whose underlying morphism of sheaves of sets
is `θ` is inverted by `θ` on sections. -/
theorem forget_hom_inv_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {P Q : Sheaf J CommRingCat.{u}} (e : P ≅ Q)
    {θ : (sheafCompose J (forget CommRingCat.{u})).obj P ⟶
      (sheafCompose J (forget CommRingCat.{u})).obj Q}
    (h : (sheafCompose J (forget CommRingCat.{u})).map e.hom = θ) (W : Cᵒᵖ)
    (y : Q.obj.obj W) : θ.hom.app W (e.inv.hom.app W y) = y := by
  subst h
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun m ↦ m.hom) e.inv_hom_id) W) y

/-- **The chart projections of the direct-image map of a morphism, over its target's structure
morphism.**  For `p : A₁ ⟶ A₂` and `z : A₂ ⟶ X`, reading the direct-image map
`AlgebraicGeometry.Space.pushforwardAlgMap p z` of a section `s` of `z_* 𝒪_{A₂}` over a chart
`V` at the index composed from a chart `j'` of `A₂` above `A₂ ×_X V` and a chart `k` of `A₁`
above `A₁ ×_{A₂} j'` is pulling back the reading of `s` at `j'` along the chartwise morphism of
`k`. -/
theorem directImageChartProjection_pushforwardAlgMap {A₁ A₂ X : AlgebraicSpaces B S hS}
    (p : A₁ ⟶ A₂) (z : A₂ ⟶ X) (V : SmallEtale B S hS X.1)
    (j' : StructuredArrow (op (chartBaseChange B S hS z V)) (comparisonFunctor B S hS A₂).op)
    (k : StructuredArrow (op (chartBaseChange B S hS p j'.right.unop))
      (comparisonFunctor B S hS A₁).op)
    (s : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS z).toToposHom).obj
      (smallEtaleRingedTopos B S hS A₂).O).obj.obj (op V)) :
    (directImageChartProjection B S hS (p ≫ z) V
          (StructuredArrow.mk ((chartBaseChangeComp B S hS p z V j').op ≫ k.hom))).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₁).O)
        ((pushforwardAlgMap B S hS p z).hom.app (op V) s) =
      chartPullback B S hS p j'.right.unop k
        ((directImageChartProjection B S hS z V j').app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₂).O) s) :=
              by
  have h1 := Sheaf.hom_congr_app_apply (forgetRing_pushforwardAlgMap B S hS p z) (op V) s
  refine (congrArg _ h1).trans ?_
  refine (directImageChartProjection_smallToposMorphismTypeU_comp B S hS p z V j' k
    (structureSetSheaf B S hS A₁) _).trans ?_
  refine (congrArg _ (directImageChartProjection_map B S hS z V j'
    (structureSharpSet B S hS p) s)).trans ?_
  exact directImageChartProjection_structureSharpSet B S hS p j'.right.unop k _

/-- **The chart projections of a section moved back across the comparison of iterated direct
images.**  For `a : A₁ ⟶ A₂`, `g : A₂ ⟶ X` and a section `y` of `(a ≫ g)_* 𝒪_{A₁}` over `V`,
moving `y` to `g_*(a_* 𝒪_{A₁})` by the inverses of the two composition comparisons and reading
it at a chart `j` of `A₂` and then at a chart `k` of `A₁` is reading `y` at the composed
index. -/
theorem directImageChartProjection_compIso_inv {A₁ A₂ X : AlgebraicSpaces B S hS}
    (a : A₁ ⟶ A₂) (g : A₂ ⟶ X) (V : SmallEtale B S hS X.1)
    (j : StructuredArrow (op (chartBaseChange B S hS g V)) (comparisonFunctor B S hS A₂).op)
    (k : StructuredArrow (op (chartBaseChange B S hS a j.right.unop))
      (comparisonFunctor B S hS A₁).op)
    (y : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS (a ≫ g)).toToposHom).obj
      (smallEtaleRingedTopos B S hS A₁).O).obj.obj (op V)) :
    (directImageChartProjection B S hS a j.right.unop k).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₁).O)
        ((directImageChartProjection B S hS g V j).app
          ((smallEtaleDirectImage B S hS a).obj
            ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₁).O))
          ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
              (smallEtaleRingedToposHom B S hS g).toToposHom
              (smallEtaleRingedTopos B S hS A₁).O).inv.hom.app (op V)
            (((smallEtaleRingedToposHom_compRingIso B S hS a g).inv.app
              (smallEtaleRingedTopos B S hS A₁).O).hom.app (op V) y))) =
      (directImageChartProjection B S hS (a ≫ g) V
          (StructuredArrow.mk ((chartBaseChangeComp B S hS a g V j).op ≫ k.hom))).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₁).O) y := by
  have key : ((smallToposMorphismTypeU_comp B S hS a g).hom.app
      ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₁).O)).hom.app
        (op V)
      ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
          (smallEtaleRingedToposHom B S hS g).toToposHom
          (smallEtaleRingedTopos B S hS A₁).O).inv.hom.app (op V)
        (((smallEtaleRingedToposHom_compRingIso B S hS a g).inv.app
          (smallEtaleRingedTopos B S hS A₁).O).hom.app (op V) y)) = y := by
    have h1 := forget_hom_inv_app_apply
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom (smallEtaleRingedTopos B S hS A₁).O)
      (pushforwardCommRingCompIso_hom_forget (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom (smallEtaleRingedTopos B S hS A₁).O)
      (op V) (((smallEtaleRingedToposHom_compRingIso B S hS a g).inv.app
          (smallEtaleRingedTopos B S hS A₁).O).hom.app (op V) y)
    have h2 := forget_hom_inv_app_apply
      ((smallEtaleRingedToposHom_compRingIso B S hS a g).app (smallEtaleRingedTopos B S hS A₁).O)
      (underlyingRingSheaf_map_pullbackCommRingSheafFunctorIsoOfNatIso_hom
        (SmallEtale.topology B S hS X.1) (smallEtaleRingedTopos B S hS A₁).O
        (smallToposMorphismTypeU_comp B S hS a g)) (op V) y
    exact (congrArg _ h1).trans h2
  exact (directImageChartProjection_smallToposMorphismTypeU_comp B S hS a g V j k
    ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS A₁).O)
    _).symm.trans (congrArg _ key)

end General

/-! ### The chart projections of the base-change comparison of a square -/

section Square

/-- `AlgebraicGeometry.Space.pushforwardAlgMap`, unfolded. -/
theorem pushforwardAlgMap_eq_comp {A₁ A₂ X : AlgebraicSpaces B S hS} (a : A₁ ⟶ A₂)
    (y : A₂ ⟶ X) :
    pushforwardAlgMap B S hS a y =
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS y).toToposHom).map
          (smallEtaleRingedToposHom B S hS a).fSharp ≫
        (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS a).toToposHom
          (smallEtaleRingedToposHom B S hS y).toToposHom (smallEtaleRingedTopos B S hS A₁).O).hom ≫
        (smallEtaleRingedToposHom_compRingIso B S hS a y).hom.app
          (smallEtaleRingedTopos B S hS A₁).O :=
  rfl

/-- `AlgebraicGeometry.Space.pushforwardSquareMap`, unfolded. -/
theorem pushforwardSquareMap_eq_comp (g : Y ⟶ X) (Zo : Over X) (Wo : Over Y)
    (p : Wo.left ⟶ Zo.left) (hw : p ≫ Zo.hom = Wo.hom ≫ g) :
    pushforwardSquareMap B S hS g Zo Wo p hw = ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS Zo.hom).toToposHom).map (smallEtaleRingedToposHom B S hS
        p).fSharp) ≫ ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS p).toToposHom
        (smallEtaleRingedToposHom B S hS Zo.hom).toToposHom (smallEtaleRingedTopos B S hS
        Wo.left).O).hom) ≫ ((smallEtaleRingedToposHom_compRingIso B S hS p Zo.hom).hom.app
        (smallEtaleRingedTopos B S hS Wo.left).O) ≫ (eqToHom (congrArg (fun q : Wo.left ⟶ X =>
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS q).toToposHom).obj
        (smallEtaleRingedTopos B S hS Wo.left).O) hw)) ≫ ((smallEtaleRingedToposHom_compRingIso B S
        hS Wo.hom g).inv.app (smallEtaleRingedTopos B S hS Wo.left).O) ≫
        ((pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom (smallEtaleRingedTopos B S hS
        Wo.left).O).inv) := rfl

/-- **The base-change comparison of a commutative square, read at two charts.**  Let
`p : W ⟶ Z` cover `g : Y ⟶ X`, with `W` over `Y` and `Z` over `X`, let `d` be a chart diagram
`U ⟶ V` over `g`, `j₀` a chart of `Z` above `Z ×_X V` and `T` a chart of `W` carrying an index
`φ₀` above `W ×_Y U` and an index `φ₂` above `W ×_Z j₀` whose chartwise morphisms are compatible
over `V`.  Then reading the comparison `AlgebraicGeometry.Space.pushforwardSquareMap` (given as a
morphism `Φ` equal to its four factors, so that it is never unfolded in place) of a section `s`
of `Z_* 𝒪_Z` over `V` at the index of `d` and then at `φ₀` is pulling back the reading of `s` at
`j₀` along the chartwise morphism of `φ₂`. -/
theorem directImageChartProjection_pushforwardSquareMap_aux (g : Y ⟶ X) (Zo : Over X)
    (Wo : Over Y) (p : Wo.left ⟶ Zo.left) (hw : p ≫ Zo.hom = Wo.hom ≫ g)
    (Φ : (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Zo.hom).toToposHom).obj
        (smallEtaleRingedTopos B S hS Zo.left).O ⟶
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom).obj
          (smallEtaleRingedTopos B S hS Wo.left).O))
    (hΦ : Φ = pushforwardAlgMap B S hS p Zo.hom ≫ (eqToHom (congrArg (fun q : Wo.left ⟶ X ↦
        (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS q).toToposHom).obj (smallEtaleRingedTopos B S hS
            Wo.left).O) hw)) ≫
      (smallEtaleRingedToposHom_compRingIso B S hS Wo.hom g).inv.app (smallEtaleRingedTopos B S hS
          Wo.left).O ≫
      (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom
        (smallEtaleRingedToposHom B S hS g).toToposHom (smallEtaleRingedTopos B S hS
            Wo.left).O).inv)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (j₀ : StructuredArrow (op (chartBaseChange B S hS Zo.hom d.V))
      (comparisonFunctor B S hS Zo.left).op)
    (T : SmallEtale B S hS Wo.left.1)
    (φ₀ : op (chartBaseChange B S hS Wo.hom d.U) ⟶
      (comparisonFunctor B S hS Wo.left).op.obj (op T))
    (φ₂ : op (chartBaseChange B S hS p j₀.right.unop) ⟶
      (comparisonFunctor B S hS Wo.left).op.obj (op T))
    (hm : chartBaseChangeMap B S hS p j₀.right.unop (StructuredArrow.mk φ₂) ≫
        chartBaseChangeMap B S hS Zo.hom d.V j₀ =
      chartBaseChangeMap B S hS Wo.hom d.U (StructuredArrow.mk φ₀) ≫ d.g)
    (s : ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Zo.hom).toToposHom).obj
        (smallEtaleRingedTopos B S hS Zo.left).O).obj.obj (op d.V)) :
    (directImageChartProjection B S hS Wo.hom d.U (StructuredArrow.mk φ₀)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Wo.left).O)
        ((directImageChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
          ((smallEtaleDirectImage B S hS Wo.hom).obj
            ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS
                Wo.left).O))
          (((sheafCompose _ (forget CommRingCat.{u})).map Φ).hom.app (op d.V) s)) =
      chartPullback B S hS p j₀.right.unop (StructuredArrow.mk φ₂)
        ((directImageChartProjection B S hS Zo.hom d.V j₀).app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Zo.left).O)
          s) := by
  rw [sheafCompose_forget_map_hom_app_apply]
  subst hΦ
  have hm' : chartBaseChangeMap B S hS (p ≫ Zo.hom) d.V
        (StructuredArrow.mk ((chartBaseChangeComp B S hS p Zo.hom d.V j₀).op ≫ φ₂)) =
      chartBaseChangeMap B S hS (Wo.hom ≫ g) d.V
        (StructuredArrow.mk ((chartBaseChangeComp B S hS Wo.hom g d.V
          (indexOfChartDiagram B S hS g d)).op ≫ φ₀)) := by
    refine (chartBaseChangeMap_comp_chart B S hS p Zo.hom d.V j₀
      (StructuredArrow.mk φ₂)).trans ?_
    refine Eq.trans ?_ (chartBaseChangeMap_comp_chart B S hS Wo.hom g d.V
      (indexOfChartDiagram B S hS g d) (StructuredArrow.mk φ₀)).symm
    refine hm.trans ?_
    exact congrArg (fun x ↦ chartBaseChangeMap B S hS Wo.hom d.U (StructuredArrow.mk φ₀) ≫ x)
      (chartBaseChangeMap_indexOfChartDiagram B S hS g d).symm
  have step0 := sheaf_comp₄_hom_app_apply (pushforwardAlgMap B S hS p Zo.hom) (eqToHom (congrArg
      (fun q : Wo.left ⟶ X ↦ (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS q).toToposHom).obj (smallEtaleRingedTopos B S hS
            Wo.left).O) hw))
    ((smallEtaleRingedToposHom_compRingIso B S hS Wo.hom g).inv.app (smallEtaleRingedTopos B S hS
        Wo.left).O)
    (pushforwardCommRingCompIso (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom
      (smallEtaleRingedToposHom B S hS g).toToposHom (smallEtaleRingedTopos B S hS Wo.left).O).inv
          (op d.V) s
  have step1 := directImageChartProjection_compIso_inv B S hS Wo.hom g d.V
    (indexOfChartDiagram B S hS g d) (StructuredArrow.mk φ₀)
    ((eqToHom (congrArg (fun q : Wo.left ⟶ X ↦ (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS q).toToposHom).obj (smallEtaleRingedTopos B S hS
            Wo.left).O) hw)).hom.app (op d.V) ((pushforwardAlgMap B S hS p Zo.hom).hom.app (op d.V)
            s))
  have step2 := directImageChartProjection_eqToHom B S hS hw d.V T _ _ hm'
    (chartDiagramOfIndex B S hS (p ≫ Zo.hom) d.V
      (StructuredArrow.mk ((chartBaseChangeComp B S hS p Zo.hom d.V j₀).op ≫ φ₂))).comm
    (chartDiagramOfIndex B S hS (Wo.hom ≫ g) d.V
      (StructuredArrow.mk ((chartBaseChangeComp B S hS Wo.hom g d.V
        (indexOfChartDiagram B S hS g d)).op ≫ φ₀))).comm
    ((pushforwardAlgMap B S hS p Zo.hom).hom.app (op d.V) s)
  have step3 := directImageChartProjection_pushforwardAlgMap B S hS p Zo.hom d.V j₀
    (StructuredArrow.mk φ₂) s
  rw [step0]
  refine step1.trans ?_
  refine (eq_of_heq
    (directImageChartProjection_index_chartDiagramOfIndex B S hS _ _ _ _ _)).symm.trans ?_
  refine step2.trans ?_
  refine (eq_of_heq
    (directImageChartProjection_index_chartDiagramOfIndex B S hS _ _ _ _ _)).trans ?_
  exact step3

end Square

end AlgebraicGeometry.Space

end
