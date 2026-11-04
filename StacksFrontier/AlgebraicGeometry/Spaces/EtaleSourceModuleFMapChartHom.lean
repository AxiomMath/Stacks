module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdentity

/-!
# Linear maps of sections along an étale morphism, as morphisms out of the étale restriction

Let `p_U : X' ⟶ X` be an **étale** morphism of algebraic spaces over a scheme `S` of a big fppf
site `B`.  For an `𝒪_X`-module `P` and an `𝒪_{X'}`-module `N` this file identifies

`P|_{X'} ⟶ N`   with   `AlgebraicGeometry.Space.ModuleFMap` along `p_U` from `N` to `P`,

the restriction on the left being `AlgebraicGeometry.Space.etaleModulePullback`.  This is the
chart form of the adjunction between étale restriction of modules and the direct image, and it is
**elementary**: no comparison of inverse images enters, and in particular neither the comparison
of Stacks 03LU nor the identification of Stacks 03LW appears.

The reason it is elementary is that a chart diagram over an étale `p_U` *is* a morphism of charts
of `X`.  Its vertical morphism commutes with the two structure morphisms to `X`, so it is a
morphism from the postcomposition of its chart of `X'` — which is a chart of `X` with the same
underlying scheme — to its chart of `X`
(`AlgebraicGeometry.Space.ChartDiagram.etaleSourceMap`).  Restricting along that morphism and
applying a morphism out of the étale restriction gives a linear map of sections; conversely the
value of a linear map of sections at a diagram is *forced*, by its own naturality for the
morphism of diagrams which is the identity on the chart of `X'` and that morphism of charts on
the chart of `X`, to be its value at the identity-vertical diagram
`AlgebraicGeometry.Space.ChartDiagram.etaleUnit` after that restriction.

## Main definitions

* `AlgebraicGeometry.Space.ChartDiagram.etaleSourceMap`: the morphism of charts of `X` which a
  chart diagram over the étale `p_U` is.
* `AlgebraicGeometry.Space.ChartDiagram.etaleSourceOfId`: a chart diagram over `𝟙 X'` is one
  over `p_U`, its chart of `X` being the postcomposition of its chart of `X'`.
* `AlgebraicGeometry.Space.moduleFMapOfEtaleRestrictHom`: the linear map of sections along `p_U`
  attached to a morphism out of the étale restriction.
* `AlgebraicGeometry.Space.moduleFMapIdOfEtaleSource` and
  `AlgebraicGeometry.Space.etaleRestrictHomOfModuleFMap`: the inverse assignment, factored
  through linear maps of sections along `𝟙 X'` and
  `AlgebraicGeometry.Space.moduleHomOfModuleFMapId`.
* `AlgebraicGeometry.Space.moduleFMapEtaleRestrictHomEquiv`: **the bijection.**

## Main results

* `AlgebraicGeometry.Space.chartDiagramPullback_etaleUnit`: pullback of regular functions along
  an identity-vertical diagram is the identity, which is what lets a linear map of sections be
  read as an honest morphism of modules over the structure sheaf of `X'`.
* `AlgebraicGeometry.Space.moduleFMapOfEtaleRestrictHom_app_etaleUnit`: at an identity-vertical
  diagram the linear map of sections of a morphism is that morphism on sections.  This is the
  value the consumers use.
* `AlgebraicGeometry.Space.etaleRestrictHom_moduleFMapOfEtaleRestrictHom` and
  `AlgebraicGeometry.Space.moduleFMapOfEtaleRestrictHom_etaleRestrictHom`: the two assignments
  are mutually inverse.

## Implementation notes

The inverse assignment is **not** built by writing a morphism of sheaves of modules out of the
étale restriction by hand.  Doing so asks for the module structure on the sections of
`AlgebraicGeometry.Space.etaleModulePullback` over a chart as a module over the ring of regular
functions of that chart of `X'`; the two are the same ring, but the sections are spelt through
`PresheafOfModules.pushforward₀` and instance search does not find the action at that spelling.
Instead the linear map of sections along `p_U` is turned into one along `𝟙 X'`
(`AlgebraicGeometry.Space.moduleFMapIdOfEtaleSource`, pure chart-diagram bookkeeping: the
vertical morphism is unchanged, so the coefficient map
`AlgebraicGeometry.Space.chartDiagramPullback` is literally the same) and
`AlgebraicGeometry.Space.moduleHomOfModuleFMapId` supplies the morphism.

Two elaboration constraints shape the proofs.  First, `ext` on an equality of morphisms of
sheaves of modules at these types exhausts the heartbeat budget; the explicit
`SheafOfModules.hom_ext (PresheafOfModules.hom_ext …)` followed by
`ModuleCat.hom_ext (LinearMap.ext …)` is instant.  Second, the two halves of the mutual
inverse are stated as named theorems rather than inlined as the `left_inv` and `right_inv`
fields: inlined, the fields are elaborated inside the structure instance and the whole
`CategoryTheory.Equiv` diverges without reporting which step did.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LP](https://stacks.math.columbia.edu/tag/03LP)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G4](https://stacks.math.columbia.edu/tag/03G4)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' : AlgebraicSpaces B S hS} (pU : X' ⟶ X) (hU : IsEtale B S hS pU.hom)

/-- **A chart diagram over an étale `p_U` is a morphism of charts of `X`** from the
postcomposition of its chart of `X'` to its chart of `X`: its vertical morphism commutes with
the two structure morphisms to `X`, which is exactly the commutation of the diagram. -/
def ChartDiagram.etaleSourceMap (d : ChartDiagram B S hS X'.1 X.1 pU.hom) :
    (smallEtalePostcomp B S hS pU hU).obj d.U ⟶ d.V :=
  ObjectProperty.homMk (CostructuredArrow.homMk d.g d.comm.symm)

/-- At an identity-vertical diagram the morphism of charts is the identity. -/
theorem ChartDiagram.etaleSourceMap_etaleUnit (W : SmallEtale B S hS X'.1) :
    ChartDiagram.etaleSourceMap B S hS pU hU (ChartDiagram.etaleUnit B S hS pU hU W) =
      𝟙 ((smallEtalePostcomp B S hS pU hU).obj W) :=
  rfl

/-- The morphisms of charts of two diagrams joined by a morphism of diagrams form a commuting
square. -/
theorem ChartDiagram.etaleSourceMap_naturality
    (d d' : ChartDiagram B S hS X'.1 X.1 pU.hom) (i : d'.U ⟶ d.U) (j : d'.V ⟶ d.V)
    (h : (SmallEtale.toOver B S hS X'.1).map i ≫ d.g =
      d'.g ≫ (SmallEtale.toOver B S hS X.1).map j) :
    (smallEtalePostcomp B S hS pU hU).map i ≫
        ChartDiagram.etaleSourceMap B S hS pU hU d =
      ChartDiagram.etaleSourceMap B S hS pU hU d' ≫ j :=
  ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h)

/-- Pullback of regular functions along an identity-vertical diagram is the identity. -/
theorem chartDiagramPullback_etaleUnit (W : SmallEtale B S hS X'.1) :
    chartDiagramPullback B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W) = 𝟙 _ := by
  have h : ((BigFppfOver.toScheme B S hS).map
      (ChartDiagram.etaleUnit B S hS pU hU W).g).op = 𝟙 _ :=
    (congrArg Quiver.Hom.op ((BigFppfOver.toScheme B S hS).map_id _)).trans op_id
  refine Eq.trans (congrArg
    (fun k ↦ (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map k)) h) ?_
  refine Eq.trans (congrArg (fun k ↦ (forget₂ CommRingCat.{u} RingCat.{u}).map k)
    (Scheme.Γ.map_id _)) ?_
  exact (forget₂ CommRingCat.{u} RingCat.{u}).map_id _

/-- `AlgebraicGeometry.Space.chartDiagramPullback_etaleUnit` on a section. -/
theorem chartDiagramPullback_etaleUnit_apply (W : SmallEtale B S hS X'.1)
    (r : ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).obj.obj
      (op ((smallEtalePostcomp B S hS pU hU).obj W))) :
    chartDiagramPullback B S hS pU (ChartDiagram.etaleUnit B S hS pU hU W) r = r := by
  rw [chartDiagramPullback_etaleUnit]
  rfl

/-! ### Linear maps of sections along an étale morphism -/

section Equiv

variable (N : Modules.{u, u} B S hS X'.1 X'.2) (P : Modules.{u, u} B S hS X.1 X.2)

/-- **The linear map of sections along the étale `p_U` attached to a morphism out of the étale
restriction**: at a chart diagram, restrict the section along the morphism of charts the diagram
is and apply the morphism.  The sections of `P|_{X'}` over the chart of `X'` are the sections of
`P` over its postcomposition, so no comparison of inverse images enters. -/
noncomputable def moduleFMapOfEtaleRestrictHom
    (u : (etaleModulePullback B S hS pU hU).obj P ⟶ N) :
    ModuleFMap B S hS pU N P where
  app d t := u.val.app (op d.U)
    (P.val.map (ChartDiagram.etaleSourceMap B S hS pU hU d).op t)
  naturality d d' i j h t := by
    have e3 : j.op ≫ (ChartDiagram.etaleSourceMap B S hS pU hU d').op =
        (ChartDiagram.etaleSourceMap B S hS pU hU d).op ≫
          ((smallEtalePostcomp B S hS pU hU).map i).op := by
      rw [← op_comp, ← op_comp,
        ChartDiagram.etaleSourceMap_naturality B S hS pU hU d d' i j h]
    refine Eq.trans (congrArg (fun x ↦ u.val.app (op d'.U) x)
      (PresheafOfModules.map_comp_apply P.val j.op
        (ChartDiagram.etaleSourceMap B S hS pU hU d').op t).symm) ?_
    refine Eq.trans (congrArg (fun x ↦ u.val.app (op d'.U) x)
      (PresheafOfModules.congr_map_apply P.val e3 t)) ?_
    refine Eq.trans (congrArg (fun x ↦ u.val.app (op d'.U) x)
      (PresheafOfModules.map_comp_apply P.val
        (ChartDiagram.etaleSourceMap B S hS pU hU d).op
        ((smallEtalePostcomp B S hS pU hU).map i).op t)) ?_
    refine Eq.trans (congrArg (fun x ↦ u.val.app (op d'.U) x)
      (QuasiCoherentDescent.etaleModulePullback_val_map_apply B S hS pU hU P i
        (P.val.map (ChartDiagram.etaleSourceMap B S hS pU hU d).op t)).symm) ?_
    exact PresheafOfModules.naturality_apply u.val i.op
      (P.val.map (ChartDiagram.etaleSourceMap B S hS pU hU d).op t)
  map_add d s t :=
    Eq.trans (congrArg (fun x ↦ u.val.app (op d.U) x)
        ((P.val.map (ChartDiagram.etaleSourceMap B S hS pU hU d).op).hom.map_add s t))
      ((u.val.app (op d.U)).hom.map_add _ _)
  map_smul d r s :=
    Eq.trans (congrArg (fun x ↦ u.val.app (op d.U) x)
        (PresheafOfModules.map_smul P.val
          (ChartDiagram.etaleSourceMap B S hS pU hU d).op r s))
      ((u.val.app (op d.U)).hom.map_smul _ _)

/-- The values of that linear map of sections.  This is the definition, stated so that it can be
rewritten with. -/
theorem moduleFMapOfEtaleRestrictHom_app
    (u : (etaleModulePullback B S hS pU hU).obj P ⟶ N)
    (d : ChartDiagram B S hS X'.1 X.1 pU.hom) (t : P.val.obj (op d.V)) :
    (moduleFMapOfEtaleRestrictHom B S hS pU hU N P u).app d t =
      u.val.app (op d.U)
        (P.val.map (ChartDiagram.etaleSourceMap B S hS pU hU d).op t) :=
  rfl

/-- At an identity-vertical diagram the linear map of sections of a morphism out of the étale
restriction is that morphism on sections. -/
theorem moduleFMapOfEtaleRestrictHom_app_etaleUnit
    (u : (etaleModulePullback B S hS pU hU).obj P ⟶ N) (W : SmallEtale B S hS X'.1)
    (t : P.val.obj (op ((smallEtalePostcomp B S hS pU hU).obj W))) :
    (moduleFMapOfEtaleRestrictHom B S hS pU hU N P u).app
        (ChartDiagram.etaleUnit B S hS pU hU W) t =
      u.val.app (op W) t := by
  refine Eq.trans (moduleFMapOfEtaleRestrictHom_app B S hS pU hU N P u
    (ChartDiagram.etaleUnit B S hS pU hU W) t) ?_
  refine congrArg (fun x ↦ u.val.app (op W) x) ?_
  have h : (ChartDiagram.etaleSourceMap B S hS pU hU
      (ChartDiagram.etaleUnit B S hS pU hU W)).op =
      𝟙 (op ((smallEtalePostcomp B S hS pU hU).obj W)) := rfl
  refine Eq.trans (PresheafOfModules.congr_map_apply P.val h t) ?_
  exact congrArg (fun k ↦ (ConcreteCategory.hom k) t)
    (P.val.map_id (op ((smallEtalePostcomp B S hS pU hU).obj W)))

include hU in
/-- **A chart diagram over the identity of `X'` is one over the étale `p_U`**, its chart of `X`
being the postcomposition of its chart of `X'`.  The vertical morphism is unchanged, so the
pullback of regular functions along it is literally the same map. -/
def ChartDiagram.etaleSourceOfId (d : ChartDiagram B S hS X'.1 X'.1 (𝟙 X'.1)) :
    ChartDiagram B S hS X'.1 X.1 pU.hom where
  U := d.U
  V := (smallEtalePostcomp B S hS pU hU).obj d.V
  g := d.g
  comm := by
    change d.U.1.hom ≫ pU.hom = yoneda.map d.g ≫ d.V.1.hom ≫ pU.hom
    rw [← Category.assoc, ← d.comm, Category.comp_id]

include hU in
/-- The identity-vertical diagram at a chart is the diagram over `p_U` of the identity-vertical
diagram over `𝟙 X'`. -/
theorem ChartDiagram.etaleSourceOfId_idChartDiagram (W : SmallEtale B S hS X'.1) :
    ChartDiagram.etaleSourceOfId B S hS pU hU (idChartDiagram B S hS X' W) =
      ChartDiagram.etaleUnit B S hS pU hU W :=
  rfl

/-- **A linear map of sections along the étale `p_U` is one along `𝟙 X'` into the étale
restriction.**  At a diagram over `𝟙 X'` it is the given map at the diagram over `p_U` whose
chart of `X` is the postcomposed chart of `X'`.

All four fields are the four fields of the given linear map of sections at those diagrams:
postcomposition leaves the underlying object of a chart, hence its sections, its ring of regular
functions and the pullback of regular functions along the vertical morphism, unchanged. -/
def moduleFMapIdOfEtaleSource (η : ModuleFMap B S hS pU N P) :
    ModuleFMap B S hS (𝟙 X') N ((etaleModulePullback B S hS pU hU).obj P) where
  app d := η.app (ChartDiagram.etaleSourceOfId B S hS pU hU d)
  naturality d d' i j h s := η.naturality
    (ChartDiagram.etaleSourceOfId B S hS pU hU d)
    (ChartDiagram.etaleSourceOfId B S hS pU hU d') i
    ((smallEtalePostcomp B S hS pU hU).map j) h s
  map_add d := η.map_add (ChartDiagram.etaleSourceOfId B S hS pU hU d)
  map_smul d := η.map_smul (ChartDiagram.etaleSourceOfId B S hS pU hU d)

/-- **The morphism out of the étale restriction attached to a linear map of sections along the
étale `p_U`**: evaluate it at the identity-vertical chart diagram of each chart. -/
noncomputable def etaleRestrictHomOfModuleFMap (η : ModuleFMap B S hS pU N P) :
    (etaleModulePullback B S hS pU hU).obj P ⟶ N :=
  moduleHomOfModuleFMapId B S hS (moduleFMapIdOfEtaleSource B S hS pU hU N P η)

/-- The values of that morphism on sections: it is the given linear map of sections at the
identity-vertical diagram. -/
theorem etaleRestrictHomOfModuleFMap_val_app (η : ModuleFMap B S hS pU N P)
    (W : (SmallEtale B S hS X'.1)ᵒᵖ)
    (t : ((etaleModulePullback B S hS pU hU).obj P).val.obj W) :
    (etaleRestrictHomOfModuleFMap B S hS pU hU N P η).val.app W t =
      η.app (ChartDiagram.etaleUnit B S hS pU hU W.unop) t :=
  moduleHomOfModuleFMapId_app B S hS (moduleFMapIdOfEtaleSource B S hS pU hU N P η) W t

/-- The morphism attached to the linear map of sections of a morphism is that morphism: at a
chart the identity-vertical diagram's morphism of charts is the identity. -/
theorem etaleRestrictHom_moduleFMapOfEtaleRestrictHom
    (u : (etaleModulePullback B S hS pU hU).obj P ⟶ N) :
    etaleRestrictHomOfModuleFMap B S hS pU hU N P
        (moduleFMapOfEtaleRestrictHom B S hS pU hU N P u) = u := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun t ↦ ?_)
  refine Eq.trans (etaleRestrictHomOfModuleFMap_val_app B S hS pU hU N P
    (moduleFMapOfEtaleRestrictHom B S hS pU hU N P u) W t) ?_
  exact moduleFMapOfEtaleRestrictHom_app_etaleUnit B S hS pU hU N P u W.unop t

/-- The linear map of sections of the morphism attached to a linear map of sections is that
linear map of sections: its value at a diagram is forced by its own naturality for the morphism
of diagrams which is the identity on the chart of `X'` and the diagram's own morphism of charts
on the chart of `X`. -/
theorem moduleFMapOfEtaleRestrictHom_etaleRestrictHom
    (η : ModuleFMap B S hS pU N P) :
    moduleFMapOfEtaleRestrictHom B S hS pU hU N P
        (etaleRestrictHomOfModuleFMap B S hS pU hU N P η) = η := by
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun t ↦ ?_)
  refine Eq.trans (moduleFMapOfEtaleRestrictHom_app B S hS pU hU N P
    (etaleRestrictHomOfModuleFMap B S hS pU hU N P η) d t) ?_
  refine Eq.trans (etaleRestrictHomOfModuleFMap_val_app B S hS pU hU N P η (op d.U)
    (P.val.map (ChartDiagram.etaleSourceMap B S hS pU hU d).op t)) ?_
  refine Eq.trans (η.naturality d (ChartDiagram.etaleUnit B S hS pU hU d.U) (𝟙 d.U)
    (ChartDiagram.etaleSourceMap B S hS pU hU d)
    ((Category.id_comp _).trans (Category.comp_id _).symm) t) ?_
  exact congrArg (fun k ↦ (ConcreteCategory.hom k) (η.app d t)) (N.val.map_id (op d.U))

/-- **Morphisms of `𝒪_{X'}`-modules out of the étale restriction of `P` are exactly the linear
maps of sections along the étale `p_U` from `N` to `P`.**

This is the chart form of the adjunction between étale restriction and the direct image, and it
is elementary: a chart diagram over `p_U` is a morphism of charts of `X` out of the
postcomposition of its chart of `X'`, and the value of a linear map of sections at the diagram
is forced, by its own naturality, to be its value at the identity-vertical diagram after
restriction along that morphism.  Neither the comparison of Stacks 03LU nor the identification
of Stacks 03LW appears. -/
noncomputable def moduleFMapEtaleRestrictHomEquiv :
    ((etaleModulePullback B S hS pU hU).obj P ⟶ N) ≃ ModuleFMap B S hS pU N P where
  toFun := moduleFMapOfEtaleRestrictHom B S hS pU hU N P
  invFun := etaleRestrictHomOfModuleFMap B S hS pU hU N P
  left_inv := etaleRestrictHom_moduleFMapOfEtaleRestrictHom B S hS pU hU N P
  right_inv := moduleFMapOfEtaleRestrictHom_etaleRestrictHom B S hS pU hU N P

end Equiv

end AlgebraicGeometry.Space

end
