module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangeChartUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections

/-!
# Sections of the direct image of the structure sheaf along a representable morphism

Let `g : P ⟶ Q` be a representable morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B` — for instance an affine one — and let `W` be an étale scheme chart of `Q`.
Base change of `W` along `g` is an étale scheme chart `W ×_Q P` of `P` (Stacks 03G2, part (4),
`AlgebraicGeometry.Space.smallBaseChange`), and its underlying scheme represents the fibre
product `P ×_Q W` (`AlgebraicGeometry.Space.smallBaseChange_isPullback`).  This file records that
the sections over `W` of the direct image `g_*𝒪_P` of Stacks 03LU are the global regular
functions on that scheme, as a module over `Γ(W)` through pullback of regular functions along
the cartesian projection `P ×_Q W ⟶ W`, compatibly with restriction along morphisms of charts.

The content is `AlgebraicGeometry.Space.modulePushforwardChartIso`, the identification of the
direct image of Stacks 03LU with restriction along base change of charts, evaluated at the
structure sheaf: the sections of the latter over `W` are, by definition, the sections of `𝒪_P`
over `W ×_Q P` with scalars restricted along the structure map
`AlgebraicGeometry.Space.smallBaseChangeSharp`.  On sections the comparison is the chart
projection, `AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app`.

## Main definitions

* `AlgebraicGeometry.Space.modulePushforwardUnitSectionsIso`: the sections of `g_*𝒪_P` over an
  étale chart `W` of `Q` are `Γ(P ×_Q W)`, with `Γ(W)` acting through the cartesian projection,
  as an isomorphism of `Γ(W)`-modules.
* `AlgebraicGeometry.Space.modulePushforwardUnitSectionsLinearEquiv`: the same as a linear
  equivalence.

## Main results

* `AlgebraicGeometry.Space.modulePushforwardUnitSectionsIso_naturality`: the identification
  commutes with restriction along a morphism of étale charts `W' ⟶ W` of `Q`, the restriction on
  the right being pullback of regular functions along the base-changed morphism of charts.
* `AlgebraicGeometry.Space.baseChangeChartSections_smul`: the `Γ(W)`-module structure on
  `Γ(P ×_Q W)` is multiplication after pullback along the cartesian projection.

## Implementation notes

No declaration carries a tag: the identification is used in the proof of Stacks 0AF4 (the
affine case of formal glueing of algebraic spaces), whose source statement does not isolate it.
Only representability of `g` is used; affineness of `g` or of `W` is not needed.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 0AF4](https://stacks.math.columbia.edu/tag/0AF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q : AlgebraicSpaces B S hS}

/-- The ring `Γ(P ×_Q W)` of global regular functions on the base change `W ×_Q P` of an étale
chart `W` of `Q` along a representable morphism `g : P ⟶ Q`, read as a `Γ(W)`-module by
pullback of regular functions along the cartesian projection `P ×_Q W ⟶ W`. -/
def baseChangeChartSections (g : P ⟶ Q) (hg : yoneda.relativelyRepresentable g.hom)
    (W : SmallEtale B S hS Q.1) : ModuleCat (chartRing B S hS Q.1 Q.2 W) :=
  (ModuleCat.restrictScalars ((smallBaseChangeSharp B S hS g hg).hom.app (op W)).hom).obj
    (ModuleCat.of ((structureRingSheaf B S hS P).obj.obj
        (op ((smallBaseChange B S hS g hg).obj W)))
      ((structureRingSheaf B S hS P).obj.obj (op ((smallBaseChange B S hS g hg).obj W))))

/-- The underlying type of `AlgebraicGeometry.Space.baseChangeChartSections` is the ring of
global regular functions on the scheme underlying the base-changed chart `W ×_Q P`. -/
theorem baseChangeChartSections_carrier (g : P ⟶ Q) (hg : yoneda.relativelyRepresentable g.hom)
    (W : SmallEtale B S hS Q.1) :
    (baseChangeChartSections B S hS g hg W : Type u) =
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS P.1).obj
        ((smallBaseChange B S hS g hg).obj W)), ⊤) :=
  rfl

/-- **The sections of `g_*𝒪_P` over an étale chart `W` of `Q` are `Γ(P ×_Q W)`.**  For a
representable morphism `g : P ⟶ Q` of algebraic spaces, the sections over `W` of the direct image
of the structure sheaf of Stacks 03LU are the global regular functions on the base-changed chart
`W ×_Q P`, whose scheme represents `P ×_Q W`, as a `Γ(W)`-module through pullback along the
cartesian projection.

It is `AlgebraicGeometry.Space.modulePushforwardChartIso` at the structure sheaf, evaluated at
`W`; on sections it is the chart projection, by
`AlgebraicGeometry.Space.modulePushforwardChartIso_hom_app_val_app`. -/
def modulePushforwardUnitSectionsIso (g : P ⟶ Q) (hg : yoneda.relativelyRepresentable g.hom)
    (W : SmallEtale B S hS Q.1) :
    ((modulePushforward B S hS g).obj
        (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op W) ≅
      baseChangeChartSections B S hS g hg W :=
  (SheafOfModules.evaluation (structureRingSheaf B S hS Q) (op W)).mapIso
    ((modulePushforwardChartIso B S hS g hg).app
      (SheafOfModules.unit (structureRingSheaf B S hS P)))

/-- The forward map of `AlgebraicGeometry.Space.modulePushforwardUnitSectionsIso` is the value
at `W` of the comparison `AlgebraicGeometry.Space.modulePushforwardChartIso`. -/
theorem modulePushforwardUnitSectionsIso_hom_apply (g : P ⟶ Q)
    (hg : yoneda.relativelyRepresentable g.hom) (W : SmallEtale B S hS Q.1)
    (x : ((modulePushforward B S hS g).obj
        (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op W)) :
    (modulePushforwardUnitSectionsIso B S hS g hg W).hom.hom x =
      (((modulePushforwardChartIso B S hS g hg).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS P))).val.app (op W)).hom x :=
  rfl

/-- **The sections of `g_*𝒪_P` over an étale chart `W` of `Q` are `Γ(P ×_Q W)`**, as a linear
equivalence over `Γ(W)`; see `AlgebraicGeometry.Space.modulePushforwardUnitSectionsIso`. -/
def modulePushforwardUnitSectionsLinearEquiv (g : P ⟶ Q)
    (hg : yoneda.relativelyRepresentable g.hom) (W : SmallEtale B S hS Q.1) :
    ((modulePushforward B S hS g).obj
        (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op W) ≃ₗ[
        chartRing B S hS Q.1 Q.2 W]
      baseChangeChartSections B S hS g hg W :=
  (modulePushforwardUnitSectionsIso B S hS g hg W).toLinearEquiv

/-- The `Γ(W)`-module structure of `Γ(P ×_Q W)` is multiplication after pullback of regular
functions along the cartesian projection `P ×_Q W ⟶ W`. -/
theorem baseChangeChartSections_smul (g : P ⟶ Q)
    (hg : yoneda.relativelyRepresentable g.hom) (W : SmallEtale B S hS Q.1)
    (r : chartRing B S hS Q.1 Q.2 W) (x : baseChangeChartSections B S hS g hg W) :
    r • x = (show (structureRingSheaf B S hS P).obj.obj
        (op ((smallBaseChange B S hS g hg).obj W)) from
      ((smallBaseChangeSharp B S hS g hg).hom.app (op W)).hom r) *
        (show (structureRingSheaf B S hS P).obj.obj
          (op ((smallBaseChange B S hS g hg).obj W)) from x) :=
  rfl

/-- **Naturality in the chart.**  For a morphism `k : W' ⟶ W` of étale charts of `Q`, the
identification `AlgebraicGeometry.Space.modulePushforwardUnitSectionsIso` carries restriction of
sections of `g_*𝒪_P` along `k` to pullback of regular functions along the base-changed morphism
`W' ×_Q P ⟶ W ×_Q P`. -/
theorem modulePushforwardUnitSectionsIso_naturality (g : P ⟶ Q)
    (hg : yoneda.relativelyRepresentable g.hom) {W' W : SmallEtale B S hS Q.1} (k : W' ⟶ W)
    (x : ((modulePushforward B S hS g).obj
        (SheafOfModules.unit (structureRingSheaf B S hS P))).val.obj (op W)) :
    (modulePushforwardUnitSectionsIso B S hS g hg W').hom.hom
        ((((modulePushforward B S hS g).obj
          (SheafOfModules.unit (structureRingSheaf B S hS P))).val.map k.op).hom x) =
      ((structureRingSheaf B S hS P).obj.map ((smallBaseChange B S hS g hg).map k).op).hom
        ((modulePushforwardUnitSectionsIso B S hS g hg W).hom.hom x) :=
  PresheafOfModules.naturality_apply
    ((modulePushforwardChartIso B S hS g hg).hom.app
      (SheafOfModules.unit (structureRingSheaf B S hS P))).val k.op x

end AlgebraicGeometry.Space
