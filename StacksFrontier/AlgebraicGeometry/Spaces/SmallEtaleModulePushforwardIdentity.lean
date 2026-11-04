module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondenceComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# The direct and inverse image of modules along an identity, unconditionally

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces the adjoint pair `(f^*, f_*)`
on `𝒪`-modules.  For `f` an identity both members are identity functors, and this file proves it.

The direct image is characterized chartwise: `f_*` is the functor carrying a canonical linear map
of sections along `f` out of every module, universally.  Along `𝟙 X` a chart diagram is a pair of
étale charts of `X` with a morphism between them, a linear map of sections along `𝟙 X` out of a
module is the same thing as a morphism of modules into it, and the identity functor therefore
satisfies the characterization.  The direct image along `𝟙 X` is then the identity functor by
uniqueness of a functor with that property, and the inverse image along `𝟙 X` is the identity
functor by uniqueness of a left adjoint.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardIdPresentation`: the identity functor satisfies the
  chartwise universal property of the direct image along `𝟙 X`.
* `AlgebraicGeometry.Space.modulePushforwardIdentityIso`: **`(𝟙 X)_* ≅ 𝟭`**, the direct image of
  `𝒪_X`-modules along an identity is the identity functor.
* `AlgebraicGeometry.Space.modulePullbackIdentityIso`: **`(𝟙 X)^* ≅ 𝟭`**, the inverse image of
  `𝒪_X`-modules along an identity is the identity functor.

## Implementation notes

A `AlgebraicGeometry.Space.ChartDiagram` over `𝟙 X` carries two étale charts `U`, `V` of `X` and
a morphism `g` of the underlying objects of the site with `U.hom = yoneda.map g ≫ V.hom`; that is
exactly a morphism `U ⟶ V` of étale charts, which is
`AlgebraicGeometry.Space.chartMapOfIdChartDiagram` below.  Reading a morphism of modules on that
morphism of charts is the bijection with linear maps of sections, and the diagram at a single
chart `U`, with `g` the identity, is the inverse construction.

The identity functor is compared with `AlgebraicGeometry.Space.modulePushforward (𝟙 X)` through
`AlgebraicGeometry.Space.ModulePushforwardPresentation.natIso`, so the comparison is the one
matching the two counits and no choice is made.

`AlgebraicGeometry.Space.modulePullbackIdentityIso` is `(𝟙 X)_* ≅ 𝟭` read through uniqueness of a
left adjoint, `CategoryTheory.Adjunction.leftAdjointIdIso`, exactly as the conditional
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackIdIso` reads the corresponding
hypothesis; with the hypothesis now a theorem the two agree and this one takes no input.

No tag is placed: the identity law is part of Stacks 03LU, which is already carried by
`AlgebraicGeometry.Space.modulePushforward` and `AlgebraicGeometry.Space.modulePullback` and by
the chartwise universal property, and what is added here is the value of that law at an identity.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G3](https://stacks.math.columbia.edu/tag/03G3)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-! ### Chart diagrams over an identity -/

/-- The chart diagram over `𝟙 X` at a single étale chart of `X`, with the identity as its
vertical morphism. -/
def idChartDiagram (U : SmallEtale B S hS X.1) :
    ChartDiagram B S hS X.1 X.1 (𝟙 X.1) :=
  ⟨U, U, 𝟙 _, by simp⟩

/-- A chart diagram over `𝟙 X` is a morphism of étale charts of `X`: its vertical morphism
commutes with the two structure morphisms to `X`. -/
def chartMapOfIdChartDiagram (d : ChartDiagram B S hS X.1 X.1 (𝟙 X.1)) : d.U ⟶ d.V :=
  ObjectProperty.homMk (CostructuredArrow.homMk d.g (by simpa using d.comm.symm))

/-- The coefficient map of the chart diagram at a single chart is the identity: its vertical
morphism is the identity, and pullback of regular functions along it is the identity. -/
theorem chartDiagramPullback_idChartDiagram (U : SmallEtale B S hS X.1) :
    chartDiagramPullback B S hS (𝟙 X) (idChartDiagram B S hS X U) = 𝟙 _ := by
  have h : ((BigFppfOver.toScheme B S hS).map (idChartDiagram B S hS X U).g).op = 𝟙 _ := by
    simp [idChartDiagram]
  refine Eq.trans (congrArg
    (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map k)) h) ?_
  refine Eq.trans (congrArg (fun k => (forget₂ CommRingCat.{u} RingCat.{u}).map k)
    (Scheme.Γ.map_id _)) ?_
  exact (forget₂ CommRingCat.{u} RingCat.{u}).map_id _

/-- `AlgebraicGeometry.Space.chartDiagramPullback_idChartDiagram` on a section. -/
theorem chartDiagramPullback_idChartDiagram_apply (U : SmallEtale B S hS X.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj (op U)) :
    chartDiagramPullback B S hS (𝟙 X) (idChartDiagram B S hS X U) r = r := by
  rw [chartDiagramPullback_idChartDiagram]
  rfl

variable {X}

/-! ### Linear maps of sections along an identity -/

/-- The linear map of sections along `𝟙 X` attached to a morphism of `𝒪_X`-modules: on a chart
diagram, restrict along the morphism of charts the diagram is and apply the morphism. -/
def moduleFMapOfHomId {F G : Modules.{u, u} B S hS X.1 X.2} (a : G ⟶ F) :
    ModuleFMap B S hS (𝟙 X) F G where
  app d s := F.val.map (chartMapOfIdChartDiagram B S hS X d).op (a.val.app _ s)
  naturality d d' i j h s := by
    have hk : i ≫ chartMapOfIdChartDiagram B S hS X d =
        chartMapOfIdChartDiagram B S hS X d' ≫ j :=
      ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h)
    have e3 : j.op ≫ (chartMapOfIdChartDiagram B S hS X d').op =
        (chartMapOfIdChartDiagram B S hS X d).op ≫ i.op := by
      rw [← op_comp, ← op_comp, hk]
    refine Eq.trans (congrArg (fun x => F.val.map (chartMapOfIdChartDiagram B S hS X d').op x)
      (PresheafOfModules.naturality_apply a.val j.op s)) ?_
    refine Eq.trans (PresheafOfModules.map_comp_apply F.val j.op
      (chartMapOfIdChartDiagram B S hS X d').op (a.val.app (op d.V) s)).symm ?_
    refine Eq.trans (PresheafOfModules.congr_map_apply F.val e3 (a.val.app (op d.V) s)) ?_
    exact PresheafOfModules.map_comp_apply F.val (chartMapOfIdChartDiagram B S hS X d).op i.op
      (a.val.app (op d.V) s)
  map_add d s t :=
    Eq.trans (congrArg (fun x => F.val.map (chartMapOfIdChartDiagram B S hS X d).op x)
        ((a.val.app (op d.V)).hom.map_add s t))
      ((F.val.map (chartMapOfIdChartDiagram B S hS X d).op).hom.map_add _ _)
  map_smul d r s :=
    Eq.trans (congrArg (fun x => F.val.map (chartMapOfIdChartDiagram B S hS X d).op x)
        ((a.val.app (op d.V)).hom.map_smul r s))
      (PresheafOfModules.map_smul F.val (chartMapOfIdChartDiagram B S hS X d).op r _)

/-- `AlgebraicGeometry.Space.moduleFMapOfHomId` on a section: restrict the image of the section
along the morphism of charts of the diagram. -/
@[simp]
theorem moduleFMapOfHomId_app {F G : Modules.{u, u} B S hS X.1 X.2} (a : G ⟶ F)
    (d : ChartDiagram B S hS X.1 X.1 (𝟙 X.1)) (s : G.val.obj (op d.V)) :
    (moduleFMapOfHomId B S hS a).app d s =
      F.val.map (chartMapOfIdChartDiagram B S hS X d).op (a.val.app (op d.V) s) :=
  rfl

/-- The morphism of `𝒪_X`-modules attached to a linear map of sections along `𝟙 X`: evaluate it
on the chart diagram at each chart with the identity as its vertical morphism. -/
def moduleHomOfModuleFMapId {F G : Modules.{u, u} B S hS X.1 X.2}
    (a : ModuleFMap B S hS (𝟙 X) F G) : G ⟶ F where
  val :=
    { app U := ModuleCat.ofHom
        { toFun := a.app (idChartDiagram B S hS X U.unop)
          map_add' s t := a.map_add (idChartDiagram B S hS X U.unop) s t
          map_smul' r s :=
            (a.map_smul (idChartDiagram B S hS X U.unop) r s).trans
              (congrArg (fun t => t • a.app (idChartDiagram B S hS X U.unop) s)
                (chartDiagramPullback_idChartDiagram_apply B S hS X U.unop r)) }
      naturality {U V} i := by
        refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
        exact a.naturality (idChartDiagram B S hS X U.unop)
          (idChartDiagram B S hS X V.unop) i.unop i.unop (by simp [idChartDiagram]) s }

/-- `AlgebraicGeometry.Space.moduleHomOfModuleFMapId` on a section: the linear map evaluated on
the identity-vertical diagram at the chart. -/
@[simp]
theorem moduleHomOfModuleFMapId_app {F G : Modules.{u, u} B S hS X.1 X.2}
    (a : ModuleFMap B S hS (𝟙 X) F G) (U : (SmallEtale B S hS X.1)ᵒᵖ) (s : G.val.obj U) :
    (moduleHomOfModuleFMapId B S hS a).val.app U s = a.app (idChartDiagram B S hS X U.unop) s :=
  rfl

/-- **Morphisms of `𝒪_X`-modules into a module are the linear maps of sections along `𝟙 X` out
of it.**  This is the chartwise universal property of the direct image, for the identity functor
and the identity morphism. -/
def moduleFMapIdEquiv (F G : Modules.{u, u} B S hS X.1 X.2) :
    (G ⟶ F) ≃ ModuleFMap B S hS (𝟙 X) F G where
  toFun := moduleFMapOfHomId B S hS
  invFun := moduleHomOfModuleFMapId B S hS
  left_inv a := by
    ext U s
    refine Eq.trans (moduleHomOfModuleFMapId_app B S hS _ U s) ?_
    refine Eq.trans (moduleFMapOfHomId_app B S hS a (idChartDiagram B S hS X U.unop) s) ?_
    have h : (chartMapOfIdChartDiagram B S hS X (idChartDiagram B S hS X U.unop)).op =
        𝟙 U := rfl
    refine Eq.trans (PresheafOfModules.congr_map_apply F.val h (a.val.app U s)) ?_
    exact congrArg (fun k => (ConcreteCategory.hom k) (a.val.app U s)) (F.val.map_id U)
  right_inv a := by
    apply ModuleFMap.ext
    funext d s
    refine Eq.trans (moduleFMapOfHomId_app B S hS _ d s) ?_
    refine Eq.trans (congrArg (fun x => F.val.map (chartMapOfIdChartDiagram B S hS X d).op x)
      (moduleHomOfModuleFMapId_app B S hS a (op d.V) s)) ?_
    have h := a.naturality (idChartDiagram B S hS X d.V) d
      (chartMapOfIdChartDiagram B S hS X d) (𝟙 d.V)
      (by simp [idChartDiagram, chartMapOfIdChartDiagram]) s
    have hG : G.val.map (𝟙 (op d.V)) s = s :=
      congrArg (fun k => (ConcreteCategory.hom k) s) (G.val.map_id (op d.V))
    exact h.symm.trans (congrArg (a.app d) hG)

/-! ### The identity law -/

variable (X)

/-- **The identity functor satisfies the chartwise universal property of the direct image along
`𝟙 X`**, with the identity map of sections of
`AlgebraicGeometry.Space.moduleFMapOfHomId` as its counit. -/
def modulePushforwardIdPresentation :
    ModulePushforwardPresentation B S hS (𝟙 X)
      (𝟭 (Modules.{u, u} B S hS X.1 X.2)) where
  counit F := moduleFMapOfHomId B S hS (𝟙 F)
  homEquiv F G := moduleFMapIdEquiv B S hS F G
  homEquiv_apply _ _ _ _ _ := rfl
  naturality a d s :=
    (congrArg (fun k => k.hom s)
      (a.val.naturality (chartMapOfIdChartDiagram B S hS X d).op)).symm

/-- **The direct image of `𝒪_X`-modules along an identity is the identity functor**, which is
the identity law of Stacks 03LU for the direct image.

Both functors satisfy the chartwise universal property of the direct image along `𝟙 X`, so they
are isomorphic by the isomorphism matching the two counits. -/
def modulePushforwardIdentityIso :
    modulePushforward B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  ModulePushforwardPresentation.natIso B S hS (modulePushforwardPresentation B S hS (𝟙 X))
    (modulePushforwardIdPresentation B S hS X)

/-- **The inverse image of `𝒪_X`-modules along an identity is the identity functor**, which is
the identity law of Stacks 03LU for the inverse image.

It is the identity law for the direct image read through uniqueness of a left adjoint. -/
def modulePullbackIdentityIso :
    modulePullback B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS (𝟙 X))
    (modulePushforwardIdentityIso B S hS X)

end AlgebraicGeometry.Space

end

