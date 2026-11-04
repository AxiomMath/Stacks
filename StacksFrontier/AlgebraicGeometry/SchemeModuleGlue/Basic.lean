module

public import StacksFrontier.Topology.Sheaves.Glueing.OModule
public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluing
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Glueing sheaves of modules on a scheme from modules on charts

`StacksFrontier/Topology/Sheaves/Glueing/OModule.lean` glues sheaves of `𝒪`-modules on a
topological space from a datum `TopCat.Sheaf.OModuleGlueData` whose local pieces are
`TopCat.Sheaf.OModuleLocalPresheaf`s — modules over `𝒪(V)` indexed by the opens `V` of the
ambient space contained in a member of the covering family. That presentation is what makes an
overlap of two members a single open of the ambient space, with no transport along an order
isomorphism of lattices of opens; but it means the local pieces of a glueing datum are *not*
sheaves of modules on the open subschemes, and the local data one actually has — a sheaf of
`𝒪`-modules on each chart scheme — has to be put into that shape.

This file does that, and connects the construction to Mathlib's `AlgebraicGeometry.Scheme.Modules`
at both ends.

The transport is free, and the reason is `AlgebraicGeometry.Scheme.Modules.pushforward`: for any
morphism of schemes `f : Y ⟶ X` and any `M : Y.Modules`, the sections of `(pushforward f).obj M`
over an open `V` of `X` *are* the sections of `M` over `f ⁻¹ᵁ V`, by `rfl`, with the
`𝒪_X(V)`-module structure obtained by restriction of scalars along `f.app V` — which is exactly
the data an `OModuleLocalPresheaf` on `V ≤ U` records. So a module on a chart becomes chart-local
data on the ambient scheme by pushing forward and then forgetting the opens not contained in the
chart image, and no open immersion hypothesis is needed for either step.

## Main definitions

* `TopCat.Sheaf.OModuleLocalPresheaf.ofPresheafOfModules`: a presheaf of `𝒪`-modules on the whole
  space, read as chart-local data on the opens contained in a given open `U`.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartLocalPresheaf`: the chart-local data attached to
  a sheaf of modules on a chart.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.gluedModules`: **the glued sheaf of modules as an
  object of Mathlib's `AlgebraicGeometry.Scheme.Modules`.**

## Main results

* `TopCat.Sheaf.isSheaf_ofPresheafOfModules`: a sheaf of `𝒪`-modules, read as chart-local data,
  satisfies the local sheaf condition. Nothing is required of `U`.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.isSheaf_chartLocalPresheaf`: the chart-local data
  attached to a sheaf of modules on a chart satisfies it.
* `Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionsLinearEquiv`: over an open contained in
  the chart's own open, the sections of the glued module are the sections of the module on the
  chart, `𝒪_X(V)`-linearly. This is Stacks 00AL's `φ i` in the form the chart identifications of
  a relative Proj are stated at.

## Why no open immersion hypothesis appears

The glueing construction of `TopCat.Sheaf.OModuleGlueData` never uses one: its local pieces are
indexed by opens of the ambient space, and its comparison isomorphisms are given over arbitrary
opens contained in two members of the family. Consequently `chartLocalPresheaf` is defined for an
arbitrary morphism of schemes and an arbitrary open `U`, and `IsOpenImmersion` enters only when
the *user* of the construction has to produce the comparison isomorphisms and wants to know that
the result restricts on a chart to the module it was glued from. Keeping the hypothesis out of
these definitions is not generality for its own sake: the instance for the charts of a relative
Proj fires at one spelling of the chart and not at another
(`Stacks.AlgebraicGeometry.RelativeProjTwistGlue`'s implementation notes), so a definition that
demanded it would need a `letI` at every use site, exactly as
`Stacks.AlgebraicGeometry.RelativeProjTwists.ChartData` does.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`. That
costs nothing at the level of *terms* — the anonymous constructor builds an `X.Modules` from the
glued presheaf and its sheaf condition, and the projections `.val` and `.isSheaf` of an `X.Modules`
are available directly, with no re-ascription. What it does cost is `rw`, whose congruence motives
are elaborated at implicit transparency, which does not unfold a semireducible `def`; the few
proofs here that have to see through it are written in term mode, and
`StacksFrontier/AlgebraicGeometry/SchemeModuleGlue/Chart.lean` records where that bites.

The ring-valued presheaf these constructions run over is `X.ringCatSheaf.obj`, the composite of the
scheme's structure sheaf with the forgetful functor to `RingCat`. Mathlib's
`CategoryTheory.Sheaf` is an `ObjectProperty.FullSubcategory`, so its underlying presheaf is
`.obj`, not `.val`; `.val` on a `SheafOfModules` is its underlying presheaf of modules.

The local sheaf condition `TopCat.Sheaf.OModuleLocalPresheaf.IsSheaf` opens with a strict-implicit
index type and an implicit open, so its proof has to begin by introducing those explicitly: a
lambda that names only the explicit binders silently binds the implicit ones instead, and the
error it produces names the covering family rather than the binder that went wrong.

## References

* [Stacks Project, Tag 00AL](https://stacks.math.columbia.edu/tag/00AL)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- A presheaf of `𝒪`-modules on `X`, read as `TopCat.Sheaf.OModuleLocalPresheaf` data on the
opens of `X` contained in `U`: the module of sections over `V ≤ U` is the module of sections of
the presheaf over `V`, and the restriction maps are its own, bundled as semilinear maps by
`PresheafOfModules.resLE`. -/
@[ega "0 3.1.5"]
public def OModuleLocalPresheaf.ofPresheafOfModules (N : PresheafOfModules.{u} 𝒪)
    (U : Opens X) : OModuleLocalPresheaf 𝒪 U where
  obj V _ := N.obj (op V)
  map hWV := N.resLE hWV
  map_id s := by
    rw [PresheafOfModules.resLE_apply, show (homOfLE (le_refl _)).op = 𝟙 _ from
      Subsingleton.elim _ _]
    simp
  map_map hWV hZW s := N.resLE_resLE hWV hZW s

/-- **A sheaf of `𝒪`-modules, read as chart-local data on the opens contained in `U`, satisfies
the local sheaf condition.** No hypothesis on `U` is needed: the local sheaf condition quantifies
over the opens contained in `U` and their coverings by opens of `X`, and each instance of it is an
instance of the sheaf condition for the presheaf itself. -/
public theorem isSheaf_ofPresheafOfModules {N : PresheafOfModules.{u} 𝒪}
    (hN : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X) N.presheaf)
    (U : Opens X) : (OModuleLocalPresheaf.ofPresheafOfModules N U).IsSheaf := by
  intro _ι _V _hV W hWV hcov s hs
  exact existsUnique_gluing_of_isSheafPresheaf hN W hWV hcov s hs

end TopCat.Sheaf

namespace Stacks.AlgebraicGeometry.SchemeModuleGlue

variable {X Y : Scheme.{u}}

/-! ### Chart-local data from a module on a chart -/

/-- **The chart-local data attached to a sheaf of modules on a chart.** For a morphism of schemes
`f : Y ⟶ X`, an `M : Y.Modules` and an open `U` of `X`, the sections over `V ≤ U` are the sections
of `M` over `f ⁻¹ᵁ V`, an `𝒪_X(V)`-module by restriction of scalars along `f.app V`.

This is the pushforward of `M` along `f`, read as data on the opens contained in `U`; both steps
are definitional, so a section of this local datum over `V` *is* a section of `M` over
`f ⁻¹ᵁ V`. -/
public def chartLocalPresheaf (f : Y ⟶ X) (M : Y.Modules) (U : X.Opens) :
    TopCat.Sheaf.OModuleLocalPresheaf X.ringCatSheaf.obj U :=
  .ofPresheafOfModules ((Scheme.Modules.pushforward f).obj M).val U

/-- A section of the chart-local data over `V ≤ U` *is* a section of `M` over `f ⁻¹ᵁ V`: the two
modules differ only in their scalars, the former being the latter with scalars restricted along
`f.app V`, so their underlying types are the same. -/
public theorem chartLocalPresheaf_obj (f : Y ⟶ X) (M : Y.Modules) (U V : X.Opens) (hV : V ≤ U) :
    ((chartLocalPresheaf f M U).obj V hV : Type u) = (M.val.obj (op (f ⁻¹ᵁ V)) : Type u) :=
  rfl

/-- **The chart-local data attached to a sheaf of modules on a chart satisfies the local sheaf
condition**, because the pushforward of a sheaf of modules along a morphism of schemes is a sheaf
of modules. -/
public theorem isSheaf_chartLocalPresheaf (f : Y ⟶ X) (M : Y.Modules) (U : X.Opens) :
    (chartLocalPresheaf f M U).IsSheaf :=
  TopCat.Sheaf.isSheaf_ofPresheafOfModules
    (N := ((Scheme.Modules.pushforward f).obj M).val)
    ((Scheme.Modules.pushforward f).obj M).isSheaf U

/-! ### The glued module as an object of `Scheme.Modules` -/

variable {ι : Type u} {U : ι → X.Opens}

/-- **The glued sheaf of `𝒪_X`-modules, as an object of `AlgebraicGeometry.Scheme.Modules`.**

The glueing datum is one of sheaves of `𝒪`-modules on the underlying topological space of `X` for
the ring-valued presheaf `X.ringCatSheaf.obj`, so the glued presheaf of modules and the proof that
it is a sheaf are exactly the two fields of a `SheafOfModules X.ringCatSheaf`. -/
public def gluedModules (D : TopCat.Sheaf.OModuleGlueData (X := X.toTopCat)
    X.ringCatSheaf.obj U) : X.Modules :=
  ⟨D.gluedPresheafOfModules, D.isSheaf_gluedPresheafOfModules⟩

/-- The underlying presheaf of modules of the glued module is the glued presheaf of modules. -/
public theorem gluedModules_val (D : TopCat.Sheaf.OModuleGlueData (X := X.toTopCat)
    X.ringCatSheaf.obj U) : (gluedModules D).val = D.gluedPresheafOfModules :=
  rfl

/-- **Stacks 00AL's `φ i` for a glueing datum whose local pieces come from modules on charts.**
Over an open `V` of `X` contained in the chart's own open `U i`, the sections of the glued module
are the sections of the module on the `i`-th chart over the preimage of `V`, `𝒪_X(V)`-linearly.

This is the shape at which the chart identifications of the twists on a relative Proj are stated:
a section of the glued object over a sub-open of a chart image is a section of the local module
there, with no sheafification and no local-to-global step. -/
public def chartSectionsLinearEquiv
    (D : TopCat.Sheaf.OModuleGlueData (X := X.toTopCat) X.ringCatSheaf.obj U)
    (i : ι) {V : X.Opens} (hV : V ≤ U i) :
    (gluedModules D).val.obj (op V) ≃ₗ[X.ringCatSheaf.obj.obj (op V)] (D.sheaf i).obj V hV :=
  D.sectionsLinearEquiv i hV

end Stacks.AlgebraicGeometry.SchemeModuleGlue

end
