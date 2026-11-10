module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentableComp
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartLiftRefine
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineTripleOverlap
public import StacksFrontier.CategoryTheory.Limits.IsPullbackOfEq

/-!
# The chart map of a commutative square of direct images

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `p : W ⟶ Z` be a commutative square over `g`, with `W` over `Y` and `Z` over `X`.
For a chart diagram `U ⟶ V` over `g`, the comparison `AlgebraicGeometry.Space.pushforwardSquareMap`
read at `V` and then at the chart `U` above `Y ×_X V` gives the *chart map*
`(Z_* 𝒪_Z)(V) ⟶ (W_* 𝒪_W)(U)`.  This file defines it and computes it on the base-changed charts;
`StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeChartTensor` uses it for the affine base
change.

## Main definitions

* `AlgebraicGeometry.Space.squareChartMap`: the chart map of a commutative square `W ⟶ Z` over
  `g`, and `AlgebraicGeometry.Space.squareChartSchemeMap` the morphism of base-changed charts
  `W ×_Y U ⟶ Z ×_X V`.

## Main results

* `AlgebraicGeometry.Space.directImageChartProjection_squareChartMap`: read at the base-changed
  charts, the chart map is pullback of regular functions along `W ×_Y U ⟶ Z ×_X V`.
* `AlgebraicGeometry.Space.isPullback_squareChartSchemeMap`: for the base-change square the
  square of base-changed charts is cartesian.

## Implementation notes

The comparison `pushforwardSquareMap` is declared with the direct-image algebras
`AlgebraicGeometry.Space.pushforwardAlgebra` as source and target, while its factors are stated
with `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor` of the structure sheaf.  The
chart computation is carried out in the second spelling, as
`AlgebraicGeometry.Space.directImageChartProjection_pushforwardSquareMap_aux` of
`StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionSquare`, and the spellings are
compared only as sheaves, with the sheaf of `W` a variable
(`AlgebraicGeometry.Space.squareChartMap_heq_aux`).

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

/-! ### Base change from a pushout square of rings -/

/-- **The `S`-linear extension of an `R`-linear map is bijective over a pushout square.**  If
`R ⟶ S`, `R ⟶ M`, `S ⟶ N`, `M ⟶ N` is a pushout square of commutative rings, then the
`S`-linear extension `S ⊗_R M ⟶ N` of `M ⟶ N` is bijective. -/
theorem _root_.LinearMap.bijective_liftBaseChange_of_isPushout {R S M N : Type u} [CommRing R]
    [CommRing S] [CommRing M] [CommRing N] [Algebra R S] [Algebra R M] [Algebra S N]
    [Algebra M N] [Algebra R N] [IsScalarTower R S N] [IsScalarTower R M N]
    (h : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R M))
      (CommRingCat.ofHom (algebraMap S N)) (CommRingCat.ofHom (algebraMap M N)))
    (τ : M →ₗ[R] N) (hτ : ∀ m, τ m = algebraMap M N m) :
    Function.Bijective (τ.liftBaseChange S) := by
  have : Algebra.IsPushout R S M N := CommRingCat.isPushout_iff_isPushout.mp h
  have : Algebra.IsPushout R M S N := Algebra.IsPushout.symm inferInstance
  have hb := (Algebra.IsPushout.out (R := R) (R' := M) (S := S) (S' := N))
  have heq : (τ.liftBaseChange S : TensorProduct R S M → N) = hb.equiv := by
    funext x
    induction x using TensorProduct.inductionOn with
    | tmul a m =>
      rw [LinearMap.liftBaseChange_tmul, IsBaseChange.equiv_tmul, hτ]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [heq]
  exact hb.equiv.bijective

/-- `LinearMap.bijective_liftBaseChange_of_isPushout` with the module structures given as
arbitrary instances agreeing with the ring maps of the square, so that it applies to module
structures not syntactically the algebra ones. -/
theorem _root_.LinearMap.bijective_liftBaseChange_of_isPushout' {R S M N : Type u} [CommRing R]
    [CommRing S] [CommRing M] [CommRing N] [Algebra R S] [instM : Module R M]
    [instN : Module S N] [instRN : Module R N] [IsScalarTower R S N]
    (a : R →+* M) (b : S →+* N) (t : M →+* N)
    (ha : ∀ (r : R) (m : M), r • m = a r * m) (hb : ∀ (x : S) (n : N), x • n = b x * n)
    (hRN : ∀ (r : R) (n : N), r • n = b (algebraMap R S r) * n)
    (h : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom a)
      (CommRingCat.ofHom b) (CommRingCat.ofHom t))
    (τ : M →ₗ[R] N) (hτ : ∀ m, τ m = t m) :
    Function.Bijective (τ.liftBaseChange S) := by
  let : Algebra R M := a.toAlgebra
  let : Algebra S N := b.toAlgebra
  let : Algebra R N := (b.comp (algebraMap R S)).toAlgebra
  let : Algebra M N := t.toAlgebra
  have eM : instM = Algebra.toModule := Module.ext (funext fun r ↦ funext fun m ↦ ha r m)
  have eN : instN = Algebra.toModule := Module.ext (funext fun x ↦ funext fun n ↦ hb x n)
  have eRN : instRN = Algebra.toModule := Module.ext (funext fun r ↦ funext fun n ↦ hRN r n)
  subst eM eN eRN
  have : IsScalarTower R M N := IsScalarTower.of_algebraMap_eq fun r ↦ by
    have hw := ConcreteCategory.congr_hom h.w r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hw
    exact hw.symm.symm
  exact LinearMap.bijective_liftBaseChange_of_isPushout h τ hτ

/-- `LinearMap.bijective_liftBaseChange_of_isPushout'` for a pushout square of commutative rings
given up to ring isomorphisms at its four corners. -/
theorem _root_.LinearMap.bijective_liftBaseChange_of_isPushout_of_ringEquiv {R S M N : Type u}
    [CommRing R] [CommRing S] [CommRing M] [CommRing N] [instRS : Algebra R S]
    [instM : Module R M] [instN : Module S N] [instRN : Module R N] [instT : IsScalarTower R S N]
    {P₀ P₁ P₂ P₃ : CommRingCat.{u}} {f : P₀ ⟶ P₁} {g : P₀ ⟶ P₂} {inl : P₁ ⟶ P₃} {inr : P₂ ⟶ P₃}
    (h : IsPushout f g inl inr)
    (eR : R ≃+* P₀) (eS : S ≃+* P₂) (eM : M ≃+* P₁) (eN : N ≃+* P₃)
    (a : R →+* M) (b : S →+* N) (t : M →+* N)
    (ha : ∀ (r : R) (m : M), r • m = a r * m) (hb : ∀ (x : S) (n : N), x • n = b x * n)
    (hRN : ∀ (r : R) (n : N), r • n = b (algebraMap R S r) * n)
    (c₁ : ∀ r, f.hom (eR r) = eM (a r)) (c₂ : ∀ r, g.hom (eR r) = eS (algebraMap R S r))
    (c₃ : ∀ m, inl.hom (eM m) = eN (t m)) (c₄ : ∀ x, inr.hom (eS x) = eN (b x))
    (τ : M →ₗ[R] N) (hτ : ∀ m, τ m = t m) :
    Function.Bijective (τ.liftBaseChange S) := by
  refine LinearMap.bijective_liftBaseChange_of_isPushout' a b t ha hb hRN ?_ τ hτ
  refine h.flip.of_iso eR.symm.toCommRingCatIso eS.symm.toCommRingCatIso
    eM.symm.toCommRingCatIso eN.symm.toCommRingCatIso ?_ ?_ ?_ ?_
  all_goals
    ext y
    first
    | obtain ⟨r, rfl⟩ := eR.surjective y
    | obtain ⟨x, rfl⟩ := eS.surjective y
    | obtain ⟨m, rfl⟩ := eM.surjective y
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom,
      RingHom.coe_coe, RingEquiv.symm_apply_apply, c₁, c₂, c₃, c₄]

/-- The chart map of a square does not depend on the spelling of the direct image of the
structure sheaf of `W`: an auxiliary statement with that sheaf a variable, so that the two
spellings are only ever compared as sheaves. -/
theorem squareChartMap_heq_aux (g : Y ⟶ X) (Zo : Over X) (Wo : Over Y)
    (d : ChartDiagram B S hS Y.1 X.1 g.hom)
    (R : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}) (hR : R =
        (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom).obj
        (smallEtaleRingedTopos B S hS Wo.left).O)
    (Φ : (pushforwardAlgebra B S hS Zo).right ⟶
      (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj R)
    (Ψ : (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Zo.hom).toToposHom).obj
        (smallEtaleRingedTopos B S hS Zo.left).O ⟶ (pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS g).toToposHom).obj ((pushforwardCommRingFunctor
        (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom).obj (smallEtaleRingedTopos B S hS
        Wo.left).O)) (hΦ : HEq Φ Ψ)
    (s : (pushforwardAlgebra B S hS Zo).right.obj.obj (op d.V)) :
    HEq ((moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj R)
        (((sheafCompose _ (forget CommRingCat.{u})).map Φ).hom.app (op d.V) s))
      ((directImageChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
          ((smallEtaleDirectImage B S hS Wo.hom).obj
            ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS
                Wo.left).O))
          (((sheafCompose _ (forget CommRingCat.{u})).map Ψ).hom.app (op d.V) s)) := by
  subst hR
  obtain rfl := eq_of_heq hΦ
  rfl

/-! ### The base-changed chart reads the sections of a representable direct image -/

section Representable

variable {X : AlgebraicSpaces B S hS}

/-- **The chart projection at the base-changed chart is the identification of Stacks 03G8.**
For `Yo` over `X` with representable structure morphism and a chart `V` of `X`, reading a
section of `Yo_* 𝒪` over `V` at the chart `Yo ×_X V` is
`AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`. -/
theorem directImageChartProjection_chartBaseChangeArrow_apply (Yo : Over X)
    (hY : yoneda.relativelyRepresentable Yo.hom.hom) (V : SmallEtale B S hS X.1)
    (t : (pushforwardAlgebra B S hS Yo).right.obj.obj (op V)) :
    (directImageChartProjection B S hS Yo.hom V (chartBaseChangeArrow B S hS Yo.hom hY V)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Yo.left).O) t =
      (pushforwardAlgebraSectionsIso B S hS Yo hY V).hom.hom t := by
  let := isContinuous_smallBaseChange B S hS Yo.hom hY
  exact (directImageChartProjection_smallEtaleRingedToposHom_representable B S hS Yo.hom hY
    ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Yo.left).O) V
      t).symm.trans
    (Sheaf.hom_congr_app_apply (smallEtaleRingedToposHom_representableRing_forget B S hS Yo.hom hY
      (smallEtaleRingedTopos B S hS Yo.left).O) (op V) t).symm

end Representable

/-! ### The chart map of a commutative square over `g` -/

section Chart

variable (g : Y ⟶ X) (Zo : Over X) (Wo : Over Y) (p : Wo.left ⟶ Zo.left)
  (hw : p ≫ Zo.hom = Wo.hom ≫ g) (hZ : yoneda.relativelyRepresentable Zo.hom.hom)
  (hW : yoneda.relativelyRepresentable Wo.hom.hom) (d : ChartDiagram B S hS Y.1 X.1 g.hom)

include hw in
/-- The compatibility defining `AlgebraicGeometry.Space.squareChartSchemeMap`. -/
theorem squareChartSchemeMap_cond :
    (hW.fst d.U.1.hom ≫ p.hom) ≫ Zo.hom.hom = yoneda.map (hW.snd d.U.1.hom ≫ d.g) ≫ d.V.1.hom := by
  have hw' : p.hom ≫ Zo.hom.hom = Wo.hom.hom ≫ g.hom := congrArg (fun r ↦ r.hom) hw
  rw [Category.assoc, hw', ← Category.assoc, hW.w d.U.1.hom, Category.assoc, d.comm,
    Functor.map_comp, Category.assoc]

/-- **The morphism of base-changed charts** `W ×_Y U ⟶ Z ×_X V` attached to a chart diagram
`U ⟶ V` over `g` and a square `p : W ⟶ Z` over `g`: the morphism covering `p` and the vertical
morphism `U ⟶ V` of the diagram. -/
def squareChartSchemeMap : hW.pullback d.U.1.hom ⟶ hZ.pullback d.V.1.hom :=
  hZ.lift _ _ (squareChartSchemeMap_cond B S hS g Zo Wo p hw hW d)

/-- The first projection of `AlgebraicGeometry.Space.squareChartSchemeMap` to `Z` is the first
projection of `W ×_Y U` followed by `p`. -/
theorem squareChartSchemeMap_fst :
    yoneda.map (squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d) ≫ hZ.fst d.V.1.hom =
      hW.fst d.U.1.hom ≫ p.hom :=
  hZ.lift_fst _ _ _

/-- The second projection of `AlgebraicGeometry.Space.squareChartSchemeMap` to `V` is the second
projection of `W ×_Y U` followed by the morphism `U ⟶ V` of the chart diagram. -/
theorem squareChartSchemeMap_snd :
    squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d ≫ hZ.snd d.V.1.hom =
      hW.snd d.U.1.hom ≫ d.g :=
  hZ.lift_snd _ _ _

/-- The chart diagram over `p` formed by the two base-changed charts and
`AlgebraicGeometry.Space.squareChartSchemeMap`. -/
def squareChartDiagram : ChartDiagram B S hS Wo.left.1 Zo.left.1 p.hom where
  U := (smallBaseChange B S hS Wo.hom hW).obj d.U
  V := (smallBaseChange B S hS Zo.hom hZ).obj d.V
  g := squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d
  comm := (squareChartSchemeMap_fst B S hS g Zo Wo p hw hZ hW d).symm

/-- **The chart map** `(Z_* 𝒪_Z)(V) ⟶ (W_* 𝒪_W)(U)` of a commutative square `p : W ⟶ Z` over
`g : Y ⟶ X` at a chart diagram `U ⟶ V` over `g`: the comparison
`AlgebraicGeometry.Space.pushforwardSquareMap` at `V`, read at the chart `U` of `Y` above
`Y ×_X V` named by the diagram. -/
def squareChartMap (s : (pushforwardAlgebra B S hS Zo).right.obj.obj (op d.V)) :
    (pushforwardAlgebra B S hS Wo).right.obj.obj (op d.U) :=
  (moduleChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
    ((sheafCompose _ (forget CommRingCat.{u})).obj (pushforwardAlgebra B S hS Wo).right)
    (((sheafCompose _ (forget CommRingCat.{u})).map
      (pushforwardSquareMap B S hS g Zo Wo p hw)).hom.app (op d.V) s)

/-- `AlgebraicGeometry.Space.squareChartMap` in the spelling of the factors of the
comparison. -/
theorem squareChartMap_eq (s : (pushforwardAlgebra B S hS Zo).right.obj.obj (op d.V)) :
    squareChartMap B S hS g Zo Wo p hw d s =
      (directImageChartProjection B S hS g d.V (indexOfChartDiagram B S hS g d)).app
          ((smallEtaleDirectImage B S hS Wo.hom).obj
            ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS
                Wo.left).O))
          (((sheafCompose _ (forget CommRingCat.{u})).map (show (pushforwardCommRingFunctor
              (smallEtaleRingedToposHom B S hS Zo.hom).toToposHom).obj
      (smallEtaleRingedTopos B S hS Zo.left).O ⟶
            (pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS g).toToposHom).obj
      ((pushforwardCommRingFunctor (smallEtaleRingedToposHom B S hS Wo.hom).toToposHom).obj
        (smallEtaleRingedTopos B S hS Wo.left).O) from pushforwardSquareMap B S hS g Zo Wo p
            hw)).hom.app (op d.V) s) :=
  eq_of_heq (squareChartMap_heq_aux B S hS g Zo Wo d _ rfl _ _ HEq.rfl s)

/-- **The chart map, read at the base-changed charts, is pullback of regular functions along
`AlgebraicGeometry.Space.squareChartSchemeMap`.** -/
theorem directImageChartProjection_squareChartMap
    (s : (pushforwardAlgebra B S hS Zo).right.obj.obj (op d.V)) :
    (directImageChartProjection B S hS Wo.hom d.U
        (StructuredArrow.mk (smallBaseChangeComparisonIso B S hS Wo.hom hW d.U).hom.op)).app
        ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Wo.left).O)
        (squareChartMap B S hS g Zo Wo p hw d s) =
      ((BigFppfOver.toScheme B S hS).map
          (squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d)).appTop.hom
        ((directImageChartProjection B S hS Zo.hom d.V (chartBaseChangeArrow B S hS _ hZ d.V)).app
          ((sheafCompose _ (forget CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS Zo.left).O)
              s) := by
  have hsq := (pushforwardSquareMap_eq_comp B S hS g Zo Wo p hw).trans
    (comp₃_comp_eq_of_eq _ _ _ _ (pushforwardAlgMap_eq_comp B S hS p Zo.hom))
  have hm : chartBaseChangeMap B S hS p ((smallBaseChange B S hS Zo.hom hZ).obj d.V)
        (indexOfChartDiagram B S hS p (squareChartDiagram B S hS g Zo Wo p hw hZ hW d)) ≫
      chartBaseChangeMap B S hS Zo.hom d.V (chartBaseChangeArrow B S hS Zo.hom hZ d.V) =
      chartBaseChangeMap B S hS Wo.hom d.U (chartBaseChangeArrow B S hS Wo.hom hW d.U) ≫ d.g := by
    refine (congrArg₂ (fun x y ↦ x ≫ y)
      (chartBaseChangeMap_indexOfChartDiagram B S hS p
        (squareChartDiagram B S hS g Zo Wo p hw hZ hW d))
      (chartBaseChangeMap_chartBaseChangeArrow B S hS Zo.hom hZ d.V)).trans ?_
    refine Eq.trans ?_ (congrArg (fun x ↦ x ≫ d.g)
      (chartBaseChangeMap_chartBaseChangeArrow B S hS Wo.hom hW d.U)).symm
    exact squareChartSchemeMap_snd B S hS g Zo Wo p hw hZ hW d
  have hpull : chartPullback B S hS p ((smallBaseChange B S hS Zo.hom hZ).obj d.V)
      (indexOfChartDiagram B S hS p (squareChartDiagram B S hS g Zo Wo p hw hZ hW d)) =
      (forget CommRingCat.{u}).map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
        (squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d)).op) := by
    unfold chartPullback
    exact congrArg (fun m ↦ (forget CommRingCat.{u}).map
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op))
      (chartBaseChangeMap_indexOfChartDiagram B S hS p
        (squareChartDiagram B S hS g Zo Wo p hw hZ hW d))
  rw [squareChartMap_eq]
  exact (directImageChartProjection_pushforwardSquareMap_aux B S hS g Zo Wo p hw _ hsq d
    (chartBaseChangeArrow B S hS Zo.hom hZ d.V) ((smallBaseChange B S hS Wo.hom hW).obj d.U)
    (smallBaseChangeComparisonIso B S hS Wo.hom hW d.U).hom.op
    (chartLift B S hS p (squareChartDiagram B S hS g Zo Wo p hw hZ hW d)).op hm s).trans
    (ConcreteCategory.congr_hom hpull _)

include hw in
/-- **The square of base-changed charts is cartesian.**  If `p : W ⟶ Z` is the base change of
`Z ⟶ X` along `g : Y ⟶ X`, then for a chart diagram `U ⟶ V` over `g` the square formed by
`W ×_Y U ⟶ Z ×_X V`, the two projections and `U ⟶ V` is a fibre square, in the big fppf
category: `W ×_Y U = (Z ×_X Y) ×_Y U = Z ×_X U = (Z ×_X V) ×_V U`. -/
theorem isPullback_squareChartSchemeMap (hsq : IsPullback p Wo.hom Zo.hom g) :
    IsPullback (squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d) (hW.snd d.U.1.hom)
      (hZ.snd d.V.1.hom) d.g := by
  have outer := (hW.isPullback d.U.1.hom).paste_horiz (AlgebraicSpaces.isPullback_hom B S hS hsq)
  have outer' : IsPullback (yoneda.map (squareChartSchemeMap B S hS g Zo Wo p hw hZ hW d) ≫
      hZ.fst d.V.1.hom) (yoneda.map (hW.snd d.U.1.hom)) Zo.hom.hom
      (yoneda.map d.g ≫ d.V.1.hom) :=
    outer.of_eq (squareChartSchemeMap_fst B S hS g Zo Wo p hw hZ hW d).symm rfl rfl d.comm
  have hy := outer'.of_right (by
      rw [← Functor.map_comp, ← Functor.map_comp, squareChartSchemeMap_snd])
    (hZ.isPullback d.V.1.hom)
  exact IsPullback.of_map_of_faithful yoneda
    (hy.of_eq rfl rfl rfl rfl)

end Chart

end AlgebraicGeometry.Space

end
