module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingIdealPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralClosureQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence

/-!
# The sections of an algebra pullback over a diagram of étale charts

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `A` be a sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`, and
let `d` be a diagram of étale scheme charts over `f`: a chart `d.U` of `Y`, a chart `d.V` of
`X`, and a morphism `d.g : d.U ⟶ d.V` of schemes over `f`.

This file constructs the canonical comparison
`𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)` as a homomorphism of `𝒪_Y(d.U)`-algebras, and
proves it natural in `A`.  Bijectivity is *not* proved here and is not needed for either:
multiplicativity and naturality are independent of it.

## Main definitions

* `AlgebraicGeometry.Space.ringChartProjection`: the chart projection of the direct image of a
  sheaf of commutative rings, as a ring homomorphism.
* `AlgebraicGeometry.Space.ringChartSection`: the canonical ring homomorphism
  `R(d.V) ⟶ (f⁻¹R)(d.U)` on the sections of a sheaf of commutative rings over a chart diagram.
* `AlgebraicGeometry.Space.algebraPullbackChartSection`: the canonical ring homomorphism
  `A(d.V) ⟶ (f^*A)(d.U)`.
* `AlgebraicGeometry.Space.algebraPullbackChartComparison`: the canonical homomorphism of
  `𝒪_Y(d.U)`-algebras `𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)`.

## Main results

* `AlgebraicGeometry.Space.ringChartSection_structurePullbackMap`: the chart section of the
  structure sheaf, followed by the inverse-image form `f♯ : f⁻¹𝒪_X ⟶ 𝒪_Y` of the structure map,
  is pullback of regular functions along the vertical morphism of the diagram.
* `AlgebraicGeometry.Space.algebraPullbackChartComparison_naturality`: the comparison is natural
  in the algebra sheaf.
* `AlgebraicGeometry.Space.algebraPullbackChartComparison_one_tmul`: the comparison takes
  `1 ⊗ₜ a` to the chart section of `a`.

## Implementation notes

The pullback `f^*A` is a *pushout of sheaves of commutative rings*, `𝒪_Y ⊗_{f⁻¹𝒪_X} f⁻¹A`, and
that is where the multiplicativity of the comparison comes from.  The comparison is assembled
from three maps, each of them multiplicative for its own reason:

* the unit `A ⟶ f_*f⁻¹A` of Stacks 00YV for commutative rings,
  `CategoryTheory.MorphismOfTopoi.ringAdjunction`, which is a morphism of sheaves of
  commutative rings and so multiplicative on sections;
* the chart projection `(f_*P)(d.V) ⟶ P(d.U)`, which is *not* a morphism of sheaves but is the
  component of a natural transformation of finite-product-preserving functors of sheaves of
  sets, `AlgebraicGeometry.Space.moduleChartProjection`, and therefore respects the transported
  ring operations by `CategoryTheory.Sheaf.ringAddObj_naturality` and its siblings — exactly as
  the module side uses `CategoryTheory.Sheaf.moduleAddObj_naturality` in
  `AlgebraicGeometry.Space.modulePushforwardCounitApp_add`.  The ring structure on the sections
  of a direct image of sheaves of commutative rings *is* the transported one, by construction of
  `Stacks.Sheaves.RingedToposModules.inverseImageCommRingPresheaf`, so no comparison of ring
  structures is crossed on that side;
* the leg `pushout.inl` of the pushout, `AlgebraicGeometry.Space.algebraPullbackMap`, which is a
  morphism of sheaves of commutative rings.

That the comparison is a homomorphism of `𝒪_X(d.V)`-algebras — which is what lets
`Algebra.TensorProduct.lift` assemble it — is `pushout.condition` read on sections over `d.U`,
together with `ringChartSection_structurePullbackMap` for the structure sheaf; and naturality in
`A` is naturality of the three factors.

No `eqToHom` and no comparison of functors enters: the three bridges of spelling the
construction crosses — `AlgebraicGeometry.Space.smallEtaleRingedToposHom_pushforward_eq`,
`CategoryTheory.MorphismOfTopoi.pushforwardRing_forget` and `…inverseImageRing_forget` — are
each `rfl`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 00YV](https://stacks.math.columbia.edu/tag/00YV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor commRingImageAdjunction)

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The direct image of sheaves of commutative rings -/

/-- The direct image `f_*` of sheaves of commutative rings along the morphism of small étale
topoi of a morphism `f : Y ⟶ X` of algebraic spaces.  This is the right adjoint of
`AlgebraicGeometry.Space.ringSheafPullback`. -/
def ringSheafPushforward (f : Y ⟶ X) :
    Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u} ⥤
      Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS f).toToposHom

/-- **Stacks 00YV for commutative rings**, on the small étale topoi of a morphism of algebraic
spaces: the inverse image of sheaves of commutative rings is left adjoint to the direct
image. -/
def ringSheafPullbackAdjunction (f : Y ⟶ X) :
    ringSheafPullback B S hS f ⊣ ringSheafPushforward B S hS f :=
  commRingImageAdjunction.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS f).toToposHom

/-- The sheaf of sets underlying a sheaf of commutative rings on the small étale site of an
algebraic space. -/
abbrev commRingSetSheaf (Z : AlgebraicSpaces B S hS)
    (R : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}) :
    Sheaf (SmallEtale.topology B S hS Z.1) (Type u) :=
  (sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u})).obj R

/-- The morphism of underlying sheaves of sets of a morphism of sheaves of commutative rings. -/
abbrev commRingSetSheafMap (Z : AlgebraicSpaces B S hS)
    {R R' : Sheaf (SmallEtale.topology B S hS Z.1) CommRingCat.{u}} (ψ : R ⟶ R') :
    commRingSetSheaf B S hS Z R ⟶ commRingSetSheaf B S hS Z R' :=
  (sheafCompose (SmallEtale.topology B S hS Z.1) (forget CommRingCat.{u})).map ψ

/-! ### The chart projection of a direct image of sheaves of commutative rings -/

/-- **The chart projection of the direct image of a sheaf of commutative rings is a ring
homomorphism.**  The sections of `f_*R` over an étale chart `d.V` of `X` carry the ring
operations transported along the direct image of sheaves of sets, and
`AlgebraicGeometry.Space.moduleChartProjection` is a natural transformation of
finite-product-preserving functors of sheaves of sets, so it respects them. -/
def ringChartProjection (f : Y ⟶ X)
    (R : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u})
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    ((ringSheafPushforward B S hS f).obj R).obj.obj (op d.V) →+* R.obj.obj (op d.U) :=
  let RR := Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
    (J := SmallEtale.topology B S hS Y.1) R
  let θ := moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)
  { toFun := θ.app (commRingSetSheaf B S hS Y R)
    map_add' := fun x y =>
      (Sheaf.ringAddObj_naturality RR θ x y).trans
        (Sheaf.sectionsFunctor_map_ringAddHom RR (op d.U) _ _)
    map_mul' := fun x y =>
      (Sheaf.ringMulObj_naturality RR θ x y).trans
        (Sheaf.sectionsFunctor_map_ringMulHom RR (op d.U) _ _)
    map_zero' :=
      (Sheaf.ringZeroObj_naturality RR θ).trans
        (Sheaf.sectionsFunctor_map_ringZeroHom RR (op d.U) default)
    map_one' :=
      (Sheaf.ringOneObj_naturality RR θ).trans
        (Sheaf.sectionsFunctor_map_ringOneHom RR (op d.U) default) }

/-- The chart projection of a direct image is the component of
`AlgebraicGeometry.Space.moduleChartProjection` at the underlying sheaf of sets. -/
theorem ringChartProjection_apply (f : Y ⟶ X)
    (R : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u})
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (z : ((ringSheafPushforward B S hS f).obj R).obj.obj (op d.V)) :
    ringChartProjection B S hS f R d z =
      (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d)).app
        (commRingSetSheaf B S hS Y R) z :=
  rfl

/-- The chart projection of a direct image is natural in the sheaf of commutative rings. -/
theorem ringChartProjection_naturality (f : Y ⟶ X)
    {R R' : Sheaf (SmallEtale.topology B S hS Y.1) CommRingCat.{u}} (ψ : R ⟶ R')
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (z : ((ringSheafPushforward B S hS f).obj R).obj.obj (op d.V)) :
    ringChartProjection B S hS f R' d
        ((((ringSheafPushforward B S hS f).map ψ).hom.app (op d.V)).hom z) =
      (ψ.hom.app (op d.U)).hom (ringChartProjection B S hS f R d z) := by
  have hm : (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
        ((ringSheafPushforward B S hS f).map ψ) =
      (smallEtaleDirectImage B S hS f).map (commRingSetSheafMap B S hS Y ψ) :=
    Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap
      (SmallEtale.topology B S hS X.1)
      (smallEtaleRingedToposHom B S hS f).toToposHom.pushforward ψ
  refine Eq.trans (congrArg (ringChartProjection B S hS f R' d)
    (congrArg (fun m : commRingSetSheaf B S hS X ((ringSheafPushforward B S hS f).obj R) ⟶
        commRingSetSheaf B S hS X ((ringSheafPushforward B S hS f).obj R') =>
      m.hom.app (op d.V) z) hm)) ?_
  exact Functor.natTrans_app_map_apply
    (moduleChartProjection B S hS f d.V (indexOfChartDiagram B S hS f d))
    (commRingSetSheafMap B S hS Y ψ) z

/-! ### The chart section of an inverse image of sheaves of commutative rings -/

/-- Equal morphisms of sheaves of commutative rings agree on every section. -/
private theorem sheaf_hom_app_apply_congr {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R R' : Sheaf J CommRingCat.{u}} {m m' : R ⟶ R'}
    (h : m = m') (c : Cᵒᵖ) (x : R.obj.obj c) : (m.hom.app c).hom x = (m'.hom.app c).hom x :=
  h ▸ rfl

/-- **The canonical ring homomorphism `R(d.V) ⟶ (f⁻¹R)(d.U)` attached to a diagram of étale
scheme charts over `f`.**  It is the unit of Stacks 00YV for commutative rings over the chart
`d.V` of `X`, followed by the chart projection of the direct image at the chart `d.U` of `Y`
which the diagram names. -/
def ringChartSection (f : Y ⟶ X)
    (R : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u})
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    R.obj.obj (op d.V) →+* ((ringSheafPullback B S hS f).obj R).obj.obj (op d.U) :=
  (ringChartProjection B S hS f ((ringSheafPullback B S hS f).obj R) d).comp
    (((ringSheafPullbackAdjunction B S hS f).unit.app R).hom.app (op d.V)).hom

/-- The chart section of an inverse image is natural in the sheaf of commutative rings. -/
theorem ringChartSection_naturality (f : Y ⟶ X)
    {R R' : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}} (ψ : R ⟶ R')
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) (x : R.obj.obj (op d.V)) :
    ringChartSection B S hS f R' d ((ψ.hom.app (op d.V)).hom x) =
      (((ringSheafPullback B S hS f).map ψ).hom.app (op d.U)).hom
        (ringChartSection B S hS f R d x) := by
  have hu := (ringSheafPullbackAdjunction B S hS f).unit.naturality ψ
  have hx : (((ringSheafPullbackAdjunction B S hS f).unit.app R').hom.app (op d.V)).hom
        ((ψ.hom.app (op d.V)).hom x) =
      ((((ringSheafPullback B S hS f ⋙ ringSheafPushforward B S hS f).map ψ).hom.app
        (op d.V)).hom)
          ((((ringSheafPullbackAdjunction B S hS f).unit.app R).hom.app (op d.V)).hom x) :=
    sheaf_hom_app_apply_congr hu _ x
  refine Eq.trans (congrArg
    (ringChartProjection B S hS f ((ringSheafPullback B S hS f).obj R') d) hx) ?_
  exact ringChartProjection_naturality B S hS f ((ringSheafPullback B S hS f).map ψ) d _

/-- **The chart section of the structure sheaf is pullback of regular functions.**  The unit
`𝒪_X ⟶ f_*f⁻¹𝒪_X`, the chart projection, and the inverse-image form `f♯ : f⁻¹𝒪_X ⟶ 𝒪_Y` of the
structure map of Stacks 03G8 compose to pullback of regular functions along the vertical
morphism of schemes of the diagram.

The unit and the inverse-image form of the structure map compose to its direct-image form, which
is the triangle identity of Stacks 00YV; and the chart projection of the direct-image form is
pullback of functions, which is
`AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp`. -/
theorem ringChartSection_structurePullbackMap (f : Y ⟶ X)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (r : chartRing B S hS X.1 X.2 d.V) :
    ((structurePullbackMap B S hS f).hom.app (op d.U)).hom
        (ringChartSection B S hS f (structureSheaf B S hS X.1 X.2) d r) =
      chartDiagramRestrict B S hS f d r := by
  have htri : (ringSheafPullbackAdjunction B S hS f).unit.app
          (structureSheaf B S hS X.1 X.2) ≫
        (ringSheafPushforward B S hS f).map (structurePullbackMap B S hS f) =
      (smallEtaleRingedToposHom B S hS f).fSharp :=
    (Adjunction.homEquiv_unit (ringSheafPullbackAdjunction B S hS f) _ _
          (structurePullbackMap B S hS f)).symm.trans
      (Equiv.apply_symm_apply
        ((ringSheafPullbackAdjunction B S hS f).homEquiv
          (structureSheaf B S hS X.1 X.2) (structureSheaf B S hS Y.1 Y.2))
        (smallEtaleRingedToposHom B S hS f).fSharp)
  have hsharp : (((ringSheafPushforward B S hS f).map
          (structurePullbackMap B S hS f)).hom.app (op d.V)).hom
        (((ringSheafPullbackAdjunction B S hS f).unit.app
          (structureSheaf B S hS X.1 X.2)).hom.app (op d.V) r) =
      (((structureSharp B S hS f).hom.app (op d.V)).hom r) := by
    refine (sheaf_hom_app_apply_congr htri _ r).trans ?_
    exact congrArg (fun m : structureRingSheaf B S hS X ⟶
        structureRingSheafDirectImage B S hS f => (m.hom.app (op d.V)).hom r)
      (forgetCommRingSheaf_map_fSharp B S hS f)
  refine Eq.trans (ringChartProjection_naturality B S hS f
    (structurePullbackMap B S hS f) d _).symm ?_
  refine Eq.trans (congrArg
    (ringChartProjection B S hS f (structureSheaf B S hS Y.1 Y.2) d) hsharp) ?_
  refine Eq.trans (moduleChartProjection_app_structureSharp B S hS f d.V
    (indexOfChartDiagram B S hS f d) r) ?_
  exact chartPullback_indexOfChartDiagram B S hS f d r

/-! ### The chart section of an algebra pullback -/

/-- **The canonical ring homomorphism `A(d.V) ⟶ (f^*A)(d.U)` attached to a diagram of étale
scheme charts over `f`.**  It is the chart section of the inverse image followed by the leg
`pushout.inl` of the pushout `𝒪_Y ⊗_{f⁻¹𝒪_X} f⁻¹A` which defines the pullback. -/
def algebraPullbackChartSection (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    A.right.obj.obj (op d.V) →+* ((algebraPullback B S hS f).obj A).right.obj.obj (op d.U) :=
  ((((algebraPullbackMap B S hS f).app A).hom.app (op d.U)).hom).comp
    (ringChartSection B S hS f A.right d)

/-- **The chart section of an algebra pullback is natural in the algebra sheaf.**  This is the
compatibility with a morphism `A ⟶ C` of algebra sheaves: all three factors of the chart section
are natural, `AlgebraicGeometry.Space.algebraPullbackMap` being a natural transformation. -/
theorem algebraPullbackChartSection_naturality (f : Y ⟶ X)
    {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A ⟶ C)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) (a : A.right.obj.obj (op d.V)) :
    algebraPullbackChartSection B S hS f C d ((φ.right.hom.app (op d.V)).hom a) =
      ((((algebraPullback B S hS f).map φ).right.hom.app (op d.U)).hom)
        (algebraPullbackChartSection B S hS f A d a) := by
  have hnat := (algebraPullbackMap B S hS f).naturality φ
  refine Eq.trans (congrArg (fun z => ((((algebraPullbackMap B S hS f).app C).hom.app
    (op d.U)).hom) z) (ringChartSection_naturality B S hS f φ.right d a)) ?_
  exact sheaf_hom_app_apply_congr hnat _ _

/-- **The chart section of an algebra pullback is a homomorphism of `𝒪_X(d.V)`-algebras.**  On
the image of the structure map of `A` it is the structure map of `f^*A` composed with pullback of
regular functions: that is `pushout.condition`, read on the sections over `d.U`, together with
`AlgebraicGeometry.Space.ringChartSection_structurePullbackMap`. -/
theorem algebraPullbackChartSection_algebraMap (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (r : chartRing B S hS X.1 X.2 d.V) :
    algebraPullbackChartSection B S hS f A d (A.algebraMap (op d.V) r) =
      ((algebraPullback B S hS f).obj A).algebraMap (op d.U)
        (chartDiagramRestrict B S hS f d r) := by
  have hcond : (ringSheafPullback B S hS f).map A.hom ≫
        pushout.inl ((ringSheafPullback B S hS f).map A.hom)
          (structurePullbackMap B S hS f) =
      structurePullbackMap B S hS f ≫
        pushout.inr ((ringSheafPullback B S hS f).map A.hom)
          (structurePullbackMap B S hS f) :=
    pushout.condition
  refine Eq.trans (congrArg (fun z => ((((algebraPullbackMap B S hS f).app A).hom.app
    (op d.U)).hom) z) (ringChartSection_naturality B S hS f A.hom d r)) ?_
  refine Eq.trans (sheaf_hom_app_apply_congr hcond _ _) ?_
  exact congrArg (((algebraPullback B S hS f).obj A).algebraMap (op d.U))
    (ringChartSection_structurePullbackMap B S hS f d r)

/-! ### The algebra of sections over a chart diagram -/

/-- The `𝒪_X(d.V)`-algebra structure that a diagram of étale scheme charts over `f : Y ⟶ X`
puts on the sections over `d.U` of an algebra sheaf on `Y`: the structure-algebra map of the
algebra sheaf, composed with pullback of regular functions along the vertical morphism of the
diagram.  Not an instance: it depends on the diagram. -/
@[instance_reducible]
def chartDiagramSectionsAlgebra (f : Y ⟶ X) (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    Algebra (chartRing B S hS X.1 X.2 d.V) (C.right.obj.obj (op d.U)) :=
  ((C.algebraMap (op d.U)).comp (chartDiagramRestrict B S hS f d)).toAlgebra

/-- The sections over `d.U` of an algebra sheaf on `Y` are an algebra over the chart ring of
`d.V` through the chart ring of `d.U`. -/
theorem isScalarTower_chartDiagramSectionsAlgebra (f : Y ⟶ X)
    (C : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra C d.U
    letI := chartDiagramSectionsAlgebra B S hS f C d
    IsScalarTower (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
      (C.right.obj.obj (op d.U)) :=
  let := chartDiagramAlgebra B S hS f d
  let := chartSectionsAlgebra C d.U
  let := chartDiagramSectionsAlgebra B S hS f C d
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The chart section of an algebra pullback, as a homomorphism of `𝒪_X(d.V)`-algebras. -/
def algebraPullbackChartSectionAlgHom (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    letI := chartSectionsAlgebra A d.V
    letI := chartDiagramSectionsAlgebra B S hS f ((algebraPullback B S hS f).obj A) d
    A.right.obj.obj (op d.V) →ₐ[chartRing B S hS X.1 X.2 d.V]
      ((algebraPullback B S hS f).obj A).right.obj.obj (op d.U) :=
  letI := chartSectionsAlgebra A d.V
  letI := chartDiagramSectionsAlgebra B S hS f ((algebraPullback B S hS f).obj A) d
  { __ := algebraPullbackChartSection B S hS f A d
    commutes' := algebraPullbackChartSection_algebraMap B S hS f A d }

/-! ### The comparison out of the tensor product -/

/-- **The canonical comparison `𝒪_Y(d.U) ⊗_{𝒪_X(d.V)} A(d.V) ⟶ (f^*A)(d.U)`**, as a homomorphism
of `𝒪_Y(d.U)`-algebras.  Its two factors are the structure map of `f^*A` over the chart `d.U` of
`Y` and the chart section `AlgebraicGeometry.Space.algebraPullbackChartSection`; they commute
because the target is commutative.

This is the map whose bijectivity is the sections half of Stacks 03GA for algebra sheaves.  That
it is an algebra homomorphism, and natural in `A`, is independent of its bijectivity and is
proved here. -/
def algebraPullbackChartComparison (f : Y ⟶ X) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra A d.V
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    TensorProduct (chartRing B S hS X.1 X.2 d.V) (chartRing B S hS Y.1 Y.2 d.U)
        (A.right.obj.obj (op d.V)) →ₐ[chartRing B S hS Y.1 Y.2 d.U]
      ((algebraPullback B S hS f).obj A).right.obj.obj (op d.U) :=
  letI := chartDiagramAlgebra B S hS f d
  letI := chartSectionsAlgebra A d.V
  letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  letI := chartDiagramSectionsAlgebra B S hS f ((algebraPullback B S hS f).obj A) d
  haveI := isScalarTower_chartDiagramSectionsAlgebra B S hS f
    ((algebraPullback B S hS f).obj A) d
  Algebra.TensorProduct.lift (Algebra.ofId _ _)
    (algebraPullbackChartSectionAlgHom B S hS f A d) fun _ _ => Commute.all _ _

/-- The comparison takes `1 ⊗ₜ a` to the chart section of `a`. -/
theorem algebraPullbackChartComparison_one_tmul (f : Y ⟶ X)
    (A : AlgebraSheaf.{u, u} B S hS X.1 X.2) (d : ChartDiagram B S hS Y.1 X.1 f.hom)
    (a : A.right.obj.obj (op d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra A d.V
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    algebraPullbackChartComparison B S hS f A d (1 ⊗ₜ a) =
      algebraPullbackChartSection B S hS f A d a := by
  let := chartDiagramAlgebra B S hS f d
  let := chartSectionsAlgebra A d.V
  let := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  let := chartDiagramSectionsAlgebra B S hS f ((algebraPullback B S hS f).obj A) d
  have := isScalarTower_chartDiagramSectionsAlgebra B S hS f
    ((algebraPullback B S hS f).obj A) d
  refine Eq.trans (Algebra.TensorProduct.lift_tmul (Algebra.ofId _ _)
    (algebraPullbackChartSectionAlgHom B S hS f A d) (fun _ _ => Commute.all _ _) 1 a) ?_
  exact (congrArg (fun z => z * algebraPullbackChartSection B S hS f A d a)
    (map_one (Algebra.ofId (chartRing B S hS Y.1 Y.2 d.U)
      (((algebraPullback B S hS f).obj A).right.obj.obj (op d.U))))).trans
    (one_mul _)

/-- **The comparison is natural in the algebra sheaf.**  This is the compatibility clause that a
tensor presentation of an algebra pullback is asked for: on the element `1 ⊗ₜ a` the pullback of
a morphism `φ : A ⟶ C` of algebra sheaves carries the comparison for `A` to the comparison
for `C`. -/
theorem algebraPullbackChartComparison_naturality (f : Y ⟶ X)
    {A C : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : A ⟶ C)
    (d : ChartDiagram B S hS Y.1 X.1 f.hom) (a : A.right.obj.obj (op d.V)) :
    letI := chartDiagramAlgebra B S hS f d
    letI := chartSectionsAlgebra A d.V
    letI := chartSectionsAlgebra C d.V
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
    letI := chartSectionsAlgebra ((algebraPullback B S hS f).obj C) d.U
    ((((algebraPullback B S hS f).map φ).right.hom.app (op d.U)).hom)
        (algebraPullbackChartComparison B S hS f A d (1 ⊗ₜ a)) =
      algebraPullbackChartComparison B S hS f C d
        (1 ⊗ₜ ((φ.right.hom.app (op d.V)).hom a)) := by
  let := chartDiagramAlgebra B S hS f d
  let := chartSectionsAlgebra A d.V
  let := chartSectionsAlgebra C d.V
  let := chartSectionsAlgebra ((algebraPullback B S hS f).obj A) d.U
  let := chartSectionsAlgebra ((algebraPullback B S hS f).obj C) d.U
  refine Eq.trans (congrArg (fun z => ((((algebraPullback B S hS f).map φ).right.hom.app
    (op d.U)).hom) z) (algebraPullbackChartComparison_one_tmul B S hS f A d a)) ?_
  refine Eq.trans (algebraPullbackChartSection_naturality B S hS f φ d a).symm ?_
  exact (algebraPullbackChartComparison_one_tmul B S hS f C d _).symm

end AlgebraicGeometry.Space

end
