module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFppfLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionsStableUnderBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Thickening

/-!
# Open charts, residue-field points and thickenings of represented algebraic stacks

Three constructions on the 2-Yoneda 1-morphisms of **Stacks 04SP**, used to localise a
represented algebraic stack at a point of its scheme.

* an open subscheme of a scheme of the site is again a scheme of the site, and its inclusion is
  a morphism of the site (this is `AlgebraicGeometry.Space.opensObject`, which the names used
  here delegate to);
* the spectrum of the residue field at a point of a scheme of the site is a scheme of the site
  (**Stacks 04VA**, through `AlgebraicGeometry.BigFppfSite.residueField_spec_contains`), and
  `AlgebraicGeometry.Scheme.fromSpecResidueField` is a morphism of the site;
* a morphism of the site which is an open, respectively closed, immersion of schemes induces an
  open, respectively closed, immersion of the represented algebraic stacks (**Stacks 04YL**), and
  one which is a closed immersion surjective on the underlying spaces induces a thickening
  (**Stacks 0BPP**, part (1)).

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.openChart` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.openChartHom`: an open of a scheme of the site as an
  object of the site, and its inclusion.
* `AlgebraicGeometry.Stack.AlgebraicStacks.residueChart` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.residueChartHom`: the spectrum of the residue field at
  a point of a scheme of the site as an object of the site, and its structural morphism.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isOpenImmersion_schemeStackMap`: the open immersion
  promotion.
* `AlgebraicGeometry.Stack.AlgebraicStacks.surjective_pointsMap_schemeStackMap`: a morphism of
  the site surjective on the underlying topological spaces induces a surjection on the points of
  **Stacks 04XG**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isThickening_schemeStackMap`: the thickening
  promotion.

## Implementation notes

The two immersion promotions are the pattern of
`AlgebraicGeometry.Stack.AlgebraicStacks.isImmersion_schemeStackMap`: the condition of
**Stacks 04XB** at a represented source and target is the relative property of **Stacks 03YK**,
which `AlgebraicGeometry.Stack.hasRelativeProperty_schemeFibredCategoryMap` supplies from the
corresponding property of the induced morphism of representable algebraic spaces, and that in
turn is the property of the morphism of schemes by
`AlgebraicGeometry.Space.presheaf_yoneda_map_iff`. The locality hypothesis is
**Stacks 041X** in its fppf form, `AlgebraicGeometry.Space.openImmersion_isLocalAtTarget_fppf`,
for open immersions; for closed immersions the library has **Stacks 0420** for the fpqc topology
only, so the fppf form is produced from it by
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage`, exactly as
`AlgebraicGeometry.Stack.AlgebraicStacks.isClosedImmersion_comp` does.

Surjectivity on points is read through
`AlgebraicGeometry.Stack.pointsHomeomorphScheme`, the identification of the points of a
represented algebraic stack with the points of its scheme, and its naturality.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 041X](https://stacks.math.columbia.edu/tag/041X)
* [Stacks Project, Tag 0420](https://stacks.math.columbia.edu/tag/0420)
* [Stacks Project, Tag 04VA](https://stacks.math.columbia.edu/tag/04VA)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

/-! ### The residue field at the point of a one-point scheme -/

/-- On a scheme with at most one point every singleton is the whole space, hence closed. -/
theorem isClosed_singleton_of_subsingleton {X : Scheme.{u}} [Subsingleton X] (x : X) :
    IsClosed ({x} : Set X) := by
  have hx : ({x} : Set X) = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim y x
  rw [hx]
  exact isClosed_univ

/-- **The morphism from the spectrum of the residue field at the point of a one-point scheme is
a closed immersion.** On a scheme with at most one point a singleton is closed, and
`AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion` turns that into the closed-immersion
property of `AlgebraicGeometry.Scheme.fromSpecResidueField`. -/
theorem isClosedImmersion_fromSpecResidueField_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    (x : X) : IsClosedImmersion (X.fromSpecResidueField x) :=
  isClosed_singleton_iff_isClosedImmersion.1 (isClosed_singleton_of_subsingleton x)

/-- **The morphism from the spectrum of the residue field at the point of a one-point scheme is
surjective.** Its range is the singleton `{x}` (**Stacks 01J6**), which is the whole space. -/
theorem surjective_fromSpecResidueField_of_subsingleton {X : Scheme.{u}} [Subsingleton X]
    (x : X) : Function.Surjective (X.fromSpecResidueField x).base := by
  rw [← Set.range_eq_univ, Scheme.range_fromSpecResidueField]
  exact Set.eq_univ_of_forall fun y => Subsingleton.elim y x

namespace Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Open charts of an object of the big fppf site over `S` -/

/-- An open of a scheme of the site, as an object of the site over that scheme. This is
`AlgebraicGeometry.Space.opensObject` under the name the constructions below use. -/
def openChart (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Space.opensObject B S hS U V

/-- The inclusion of an open of a scheme of the site, as a morphism of the site. -/
def openChartHom (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openChart B S hS U V ⟶ U :=
  Over.homMk ⟨V.ι⟩ (by rfl)

/-- The scheme underlying an open chart is the open subscheme. -/
theorem openChart_toScheme (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).obj (openChart B S hS U V) = V.toScheme := rfl

/-- The morphism of schemes underlying the inclusion of an open chart is the inclusion of that
open subscheme. -/
theorem openChartHom_toScheme (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map (openChartHom B S hS U V) = V.ι := rfl

/-- The inclusion of an open chart is an open immersion of schemes. -/
theorem isOpenImmersion_openChartHom (U : BigFppfOver B S hS)
    (V : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (openChartHom B S hS U V)) :=
  inferInstanceAs (AlgebraicGeometry.IsOpenImmersion V.ι)

/-! ### The residue field at a point of an object of the big fppf site over `S` -/

/-- The spectrum of the residue field at a point of a scheme of the site, as an object of the
site over that scheme. -/
noncomputable def residueChart (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) : BigFppfOver B S hS :=
  Over.mk (⟨((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x ≫
      B.inclusion.map U.hom⟩ :
    B.obj (B.residueField_spec_contains U.left.property x) ⟶ B.obj hS)

/-- The morphism from the spectrum of the residue field at a point, as a morphism of the
site. -/
noncomputable def residueChartHom (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) : residueChart B S hS U x ⟶ U :=
  Over.homMk ⟨((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x⟩ (by rfl)

/-- The morphism of schemes underlying `AlgebraicGeometry.Stack.AlgebraicStacks.residueChartHom`
is `AlgebraicGeometry.Scheme.fromSpecResidueField`. -/
theorem residueChartHom_toScheme (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    (BigFppfOver.toScheme B S hS).map (residueChartHom B S hS U x) =
      ((BigFppfOver.toScheme B S hS).obj U).fromSpecResidueField x := rfl

/-! ### Immersions and thickenings of represented algebraic stacks -/

/-- **An open immersion of the site induces an open immersion of the represented algebraic
stacks.** Being an open immersion is stable under base change for morphisms of algebraic spaces
and is fpqc, hence fppf, local on the target, so the relative property of Stacks 03YK at the
open-immersion property of Stacks 02YU holds for the induced 1-morphism as soon as it holds for
the morphism of representable algebraic spaces that the morphism of the site induces, which is
Stacks 03XP, part (1). -/
theorem isOpenImmersion_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map g)) :
    IsOpenImmersion B S hS (Stack.schemeStackMap.{u, w} B S hS g) := by
  let _ : (Space.openImmersionProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
    Space.openImmersion_isLocalAtTarget_fppf.{u, u + 1} B S hS
  refine ⟨Stack.isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g, ?_⟩
  exact Stack.hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
    (Space.openImmersionProperty B S hS) g
    ((Space.presheaf_yoneda_map_iff B S hS
      (P := @AlgebraicGeometry.IsOpenImmersion.{u}) inferInstance g).2 hg)

/-- **A morphism of the site surjective on points induces a surjection on the points of the
represented algebraic stacks.** The identification of the points of a represented algebraic
stack with the points of its scheme is natural, so the map on points of Stacks 04XG is conjugate
to the map on the underlying topological spaces. -/
theorem surjective_pointsMap_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base) :
    Function.Surjective (Stack.pointsMap B S hS
      (Stack.schemeFibredCategory B S hS U).val
      (Stack.schemeFibredCategory B S hS U).property
      (Stack.schemeFibredCategory B S hS V).property
      (Stack.schemeFibredCategoryMap B S hS g).hom) := by
  let := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS U)
  let := Stack.pointTopology B S hS (Stack.schemeFibredCategory B S hS V)
  intro t
  obtain ⟨x, hx⟩ := hg (Stack.pointsHomeomorphScheme B S hS V t)
  refine ⟨(Stack.pointsHomeomorphScheme B S hS U).symm x, ?_⟩
  refine (Stack.pointsHomeomorphScheme B S hS V).injective ?_
  rw [Stack.pointsHomeomorphScheme_naturality B S hS g, Homeomorph.apply_symm_apply]
  exact hx

/-- **A closed immersion of the site surjective on points induces a thickening of the
represented algebraic stacks.** The two clauses of **Stacks 0BPP**, part (1), are that the
induced 1-morphism is a closed immersion, which is **Stacks 0420** read through the relative
property of Stacks 03YK exactly as for open immersions, and
`AlgebraicGeometry.Stack.AlgebraicStacks.surjective_pointsMap_schemeStackMap`. -/
theorem isThickening_schemeStackMap {U V : BigFppfOver B S hS} (g : U ⟶ V)
    (hg : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map g).base) :
    Stack.IsThickening (Stack.schemeStackMap.{u, w} B S hS g) := by
  have hci : IsClosedImmersion B S hS (Stack.schemeStackMap.{u, w} B S hS g) := by
    have _hfpqc : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
        (Space.Topology.precoverage.{u, u + 1} .fpqc B S hS) :=
      Space.isClosedImmersion_isLocalAtTarget_fpqc.{u, u + 1} B S hS
    let _ : (Space.closedImmersionProperty B S hS).IsLocalAtTarget
        (Space.Topology.fppf.precoverage.{u, u + 1} B S hS) :=
      .of_le (Space.fppfPrecoverage_le_fpqcPrecoverage.{u, u + 1} B S hS)
    refine ⟨Stack.isRepresentableByAlgebraicSpaces_schemeFibredCategoryMap B S hS g, ?_⟩
    exact Stack.hasRelativeProperty_schemeFibredCategoryMap.{u, u + 1} B S hS
      (Space.closedImmersionProperty B S hS) g
      ((Space.presheaf_yoneda_map_iff B S hS
        (P := @AlgebraicGeometry.IsClosedImmersion.{u}) inferInstance g).2 hg)
  exact ⟨hci, surjective_pointsMap_schemeStackMap B S hS g hsurj⟩

end Stack.AlgebraicStacks

end AlgebraicGeometry

end
