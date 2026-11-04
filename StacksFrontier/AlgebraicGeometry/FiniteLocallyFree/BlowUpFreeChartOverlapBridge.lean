module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.IsoDescentGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentTransport
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleRestrictChart
public import StacksFrontier.AlgebraicGeometry.Descent.ModuleGlueRestrictIso
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreeChartGlue

/-!
# The two spellings of "restrict a morphism of restrictions to a smaller open"

Two developments in this repository restrict a morphism of restrictions to a smaller open, and
**nothing relates them**:  no file mentions both.

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE` is defined sectionwise, from the action
  of the morphism on sections.  It is what the Zariski glueing of an isomorphism,
  `Stacks.AlgebraicGeometry.ModuleLimits.nonempty_iso_of_cover_of_inf`, states its compatibility
  hypothesis with.
* `AlgebraicGeometry.restrictLocal` is defined categorically, as the conjugate of the image under
  the restriction functor of the inclusion.  It is what the two-chart glueing
  `AlgebraicGeometry.TwoOpensGlue` and the chart calculus of
  `StacksFrontier/AlgebraicGeometry/Descent/ModuleRestrictChart.lean` are written in, and therefore
  what the agreement `AlgebraicGeometry.TwoOpensGlue.chartRestrictIso_false_eq_true` of the two
  trivialisations of a glued module over the overlap is expressed in.

A local-to-global argument that builds its local isomorphisms chart by chart and then glues them
has its hypothesis in the second spelling and needs it in the first.  This file supplies the
passage, and the two further identifications that make it usable.

## The three identifications

The first is that the comparison isomorphism `restrictHomOfLE` conjugates by and the one
`restrictLocal` conjugates by are the same morphism:
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` followed by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` at the level of functors, and
`AlgebraicGeometry.restrictCompIso` is the same two in the same order at a single module, so the
component of the inverse of the former *is* the latter -- by `rfl`.  The second is the passage
itself, which is then
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq` and nothing more.

The third is about the inclusion of the overlap.  `AlgebraicGeometry.TwoOpensGlue.mid` is the
factorisation `AlgebraicGeometry.openLift` of the inclusion of the overlap through the inclusion
of a member, obtained from the universal property of an open immersion, whereas `restrictLocal`
and `restrictHomOfLE` are stated at `AlgebraicGeometry.Scheme.homOfLE`.  The two agree, because an
open immersion is a monomorphism and `AlgebraicGeometry.eq_openLift` records that `openLift` is the
only morphism with its defining property -- but no lemma said so, and every chart comparison of the
two-chart glueing is stated at `mid`.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso_inv_app_eq_restrictCompIso_hom`: the two
  comparison isomorphisms agree.
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq_restrictLocal`: **the two spellings
  agree.**
* `AlgebraicGeometry.TwoOpensGlue.mid_eq_homOfLE`: **the inclusion of the overlap into a member of
  the two-element cover is the inclusion of opens.**
* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_chart_conj`: **a morphism of restrictions
  presented through trivialisations over the larger open restricts to the conjugate, by the two
  chart comparisons, of the morphism of the trivialisations.**  This is the form in which an
  equation between chart comparisons becomes an equation between the morphisms
  `nonempty_iso_of_cover_of_inf` consumes.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}}

/-- **The comparison isomorphism `restrictHomOfLE` conjugates by is the one `restrictLocal`
conjugates by.**  Both are `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` followed by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`, the former as a natural isomorphism of
functors and the latter at a single module, so the two sides are literally the same term. -/
theorem restrictLEIso_inv_app_eq_restrictCompIso_hom {M : X.Modules} {V W : X.Opens}
    (e : V ≤ W) :
    (restrictLEIso e).inv.app M =
      (restrictCompIso (X.homOfLE e) W.ι (Scheme.homOfLE_ι X e) M).hom :=
  rfl

/-- **The sectionwise and the categorical restriction of a morphism of restrictions to a smaller
open agree.**

`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq` rewrites the sectionwise one as the
conjugate by `restrictLEIso`, and
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso_inv_app_eq_restrictCompIso_hom` identifies
that conjugation with the one defining `AlgebraicGeometry.restrictLocal`. -/
theorem restrictHomOfLE_eq_restrictLocal {M N : X.Modules} {V W : X.Opens} (e : V ≤ W)
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι) :
    restrictHomOfLE e χ = restrictLocal χ e := by
  rw [restrictHomOfLE_eq]
  rfl

/-- **A morphism of restrictions presented through trivialisations over the larger open restricts
to the conjugate, by the two chart comparisons, of the morphism of the trivialisations.**

For `V ≤ W`, trivialisations `κ` of `M` and `lam` of `N` over `W` and a morphism `φ` of the
trivialised modules, the restriction to `V` of `κ.hom ≫ φ ≫ lam.inv` is the image of `φ` under the
restriction functor of the inclusion, conjugated by the two chart comparisons
`AlgebraicGeometry.restrictChartIso`.

This is the shape a local-to-global argument needs:  the agreement over an overlap of two chart
comparisons is an equation between `restrictChartIso`s, and the glueing
`Stacks.AlgebraicGeometry.ModuleLimits.nonempty_iso_of_cover_of_inf` asks for an equation between
`restrictHomOfLE`s. -/
theorem restrictHomOfLE_chart_conj {M N : X.Modules} {V W : X.Opens} (e : V ≤ W)
    {M' N' : W.toScheme.Modules} (κ : Scheme.Modules.restrict M W.ι ≅ M')
    (lam : Scheme.Modules.restrict N W.ι ≅ N') (φ : M' ⟶ N') :
    restrictHomOfLE e (κ.hom ≫ φ ≫ lam.inv) =
      (restrictChartIso W.ι κ (X.homOfLE e) (Scheme.homOfLE_ι X e)).hom ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE e)).map φ ≫
          (restrictChartIso W.ι lam (X.homOfLE e) (Scheme.homOfLE_ι X e)).inv := by
  rw [restrictHomOfLE_eq_restrictLocal, restrictLocal_eq]
  simp only [restrictChartIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, CategoryTheory.Functor.map_comp, Category.assoc]

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry

namespace TwoOpensGlue

/-- **The inclusion of the overlap into a member of the two-element cover is the inclusion of
opens.**  `AlgebraicGeometry.TwoOpensGlue.mid` is the factorisation of the inclusion of the
overlap through the inclusion of the member given by the universal property of an open immersion,
and `AlgebraicGeometry.Scheme.homOfLE` is the inclusion of opens; both composed with the inclusion
of the member are the inclusion of the overlap, and `AlgebraicGeometry.eq_openLift` says the
factorisation is the only morphism with that property. -/
theorem mid_eq_homOfLE {S : Scheme.{u}} (U₁ U₂ : S.Opens) (i : ULift.{u} Bool) :
    mid U₁ U₂ i = S.homOfLE (inf_le_opn U₁ U₂ i) :=
  (eq_openLift _ _ _ (Scheme.homOfLE_ι S _)).symm

end TwoOpensGlue

end AlgebraicGeometry

end
