module

public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinChartRestriction
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictLEPullback

/-!
# Restricting an equation chart to a smaller chart

[Stacks, Tag 0G86] compares the local Gysin maps of two equation charts over an open contained in
both.  Reducing that comparison to the one-chart statement
`Stacks.Gysin.chartCls_det` of [Stacks, Tag 0G7S] means restricting each chart to the smaller
open, and `Stacks.Gysin.chartTargetHom` — the identification of the target of the chart Gysin map
with the restriction to the chart of `Stacks.Gysin.gysinTarget` — is a four-factor composite,
each factor of which needs its own compatibility with that restriction.

This file supplies two of them, for two opens `W' ≤ W` of the ambient scheme.

* The identification `(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` of the coefficient module composes:
  `Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso_hom_comp`.
  The chart-to-chart leg is the open immersion `AlgebraicGeometry.Scheme.homOfLE`, so the nested
  chart stays an open of the *ambient* scheme and no open subscheme of an open subscheme appears.
* The chart's equations, read as global sections of the chart by
  `Stacks.Gysin.restrictEquations`, restrict to the equations of the smaller chart, and their
  common zero locus restricts to the common zero locus:
  `Stacks.Gysin.restrictEquations_homOfLE` and `Stacks.Gysin.equationsClosedSet_appTop`.

## Main definitions

* `Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictLEIso`: for
  `W' ≤ W` in `X`, the identification `(Ω^n_{W/S})|_{W'} ≅ Ω^n_{W'/S}` along
  `AlgebraicGeometry.Scheme.homOfLE`.

## Main results

* `Stacks.AlgebraicGeometry.DifferentialsRestrict.toRestrictForms_comp`: **the comparison
  `(Ω^n_{X/S})|_{X'} ⟶ Ω^n_{X'/S'}` composes** over two horizontally composable commuting
  squares whose left-hand arrows are open immersions, the composition isomorphism
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the restriction functors mediating.
* `Stacks.AlgebraicGeometry.DifferentialsRestrict.toRestrictForms_congr`: the same comparison
  along an equal open immersion.
* `Stacks.AlgebraicGeometry.DifferentialsRestrict.restrictFormsIso_comp`: the composition as an
  equality of isomorphisms.
* `Stacks.AlgebraicGeometry.DifferentialsRestrict.relativeDifferentialFormsRestrictIso_hom_comp`
  and `…_inv_comp`: **the nested-chart form**, for `W' ≤ W` in `X` and the structural morphisms
  of `W` and `W'` over the same base, with
  `Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` mediating.  The `inv` form is the one
  `Stacks.Gysin.chartTargetHom` composes with.
* `Stacks.Gysin.equationsClosedSet_appTop`: the common zero locus of the equations pulled back
  along a morphism of schemes is the preimage of the common zero locus.
* `Stacks.Gysin.restrictEquations_homOfLE`: **transitivity of
  `Stacks.Gysin.restrictEquations`** — the equations of a chart `W`, restricted to a smaller
  chart `W'` and read there as global sections, are the global sections of the chart `W` pulled
  back along `AlgebraicGeometry.Scheme.homOfLE`.
* `Stacks.Gysin.equationsClosedSet_restrictEquations_homOfLE`: consequently the zero locus of the
  smaller chart's equations is the preimage of the zero locus of the chart's equations.

## Implementation notes

**The composition coherence of `restrictFunctorIsoPullback` is not reproved here.**  It is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_app_comp` of
`StacksFrontier/AlgebraicGeometry/ModuleLimits/RestrictPullbackCoherence.lean`, which is public;
the remaining content of `toRestrictForms_comp` is
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp` and one naturality square of
`restrictFunctorIsoPullback`, the two copies of
`AlgebraicGeometry.Scheme.Modules.pullbackComp` cancelling in between.

**Why the nesting leg is `AlgebraicGeometry.Scheme.homOfLE` and not an open of `W.toScheme`.**
`Stacks.Gysin.chartTargetHom` takes its chart as an open of the *ambient* scheme, so a nested
chart must be one too.  Presenting the nesting as `W' ≤ W` in `X.Opens` with the leg
`X.homOfLE : W'.toScheme ⟶ W.toScheme` keeps both charts opens of `X`; presenting it as an open
`V` of `W.toScheme` would instead require identifying `V.toScheme` with an open subscheme of `X`,
which no declaration supplies.  The mediator for the leg is
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso`, already available.

## References

* [Stacks Project, Tag 0FLV](https://stacks.math.columbia.edu/tag/0FLV)
* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.DifferentialsRestrict

open AlgebraicGeometry.Scheme.Hom

variable {X'' X' X S'' S' S : Scheme.{u}}

/-! ### Composing the comparison of [Stacks, Tag 0FLV] -/

/-- **The comparison `(Ω^n_{X/S})|_{X'} ⟶ Ω^n_{X'/S'}` of two horizontally composable commuting
squares composes**, in every degree `n`: for `f : X' ⟶ X` and `f' : X'' ⟶ X'` open immersions,
the comparison of the outer square is the composition isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the restriction functors, followed by
the restriction along `f'` of the comparison of the right-hand square, followed by the
comparison of the left-hand square.

Both comparisons are `restrictFunctorIsoPullback` followed by
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap`; the composition coherence of the
first and `AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsMap_comp` of the second produce
two mutually inverse copies of `AlgebraicGeometry.Scheme.Modules.pullbackComp`, and what is left
is one naturality square of `restrictFunctorIsoPullback`. -/
theorem toRestrictForms_comp (f : X' ⟶ X) (f' : X'' ⟶ X') [IsOpenImmersion f]
    [IsOpenImmersion f'] (p : X ⟶ S) (p' : X' ⟶ S') (p'' : X'' ⟶ S'') (g : S' ⟶ S)
    (g' : S'' ⟶ S') (g'' : S'' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (hcomm' : f' ≫ p' = p'' ≫ g')
    (hcomm'' : (f' ≫ f) ≫ p = p'' ≫ g'') (n : ℤ) :
    toRestrictForms (f' ≫ f) p p'' g'' hcomm'' n =
      (Scheme.Modules.restrictFunctorComp f' f).hom.app (relativeDifferentialForms p n) ≫
        (Scheme.Modules.restrictFunctor f').map (toRestrictForms f p p' g hcomm n) ≫
          toRestrictForms f' p' p'' g' hcomm' n := by
  have hnat := (Scheme.Modules.restrictFunctorIsoPullback f').hom.naturality
    (relativeDifferentialFormsMap f p p' g hcomm n)
  rw [toRestrictForms, toRestrictForms, toRestrictForms,
    ModuleLimits.restrictFunctorIsoPullback_hom_app_comp f' f,
    relativeDifferentialFormsMap_comp f f' p p' p'' g g' g'' hcomm hcomm' hcomm'' n,
    Functor.map_comp]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_app_assoc, ← reassoc_of% hnat]

/-- **The comparison of [Stacks, Tag 0FLV] along an equal open immersion.**  The comparisons for
two equal open immersions `f = k` differ by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr`. -/
theorem toRestrictForms_congr {f k : X' ⟶ X} [IsOpenImmersion f] [IsOpenImmersion k]
    (hfk : f = k) (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g)
    (hcommk : k ≫ p = p' ≫ g) (n : ℤ) :
    toRestrictForms k p p' g hcommk n =
      (Scheme.Modules.restrictFunctorCongr hfk).inv.app (relativeDifferentialForms p n) ≫
        toRestrictForms f p p' g hcomm n := by
  subst hfk
  obtain rfl : hcommk = hcomm := rfl
  have hinv := (Scheme.Modules.restrictFunctorCongr (rfl : f = f)).inv_hom_id
  rw [ModuleLimits.restrictFunctorCongr_rfl f, Category.comp_id] at hinv
  rw [hinv, NatTrans.id_app, Category.id_comp]

/-- `toRestrictForms_comp` as an equality of **isomorphisms**, available because an open
immersion is étale and hence every comparison in sight is invertible by
`Stacks.AlgebraicGeometry.DifferentialsRestrict.isIso_toRestrictForms`. -/
theorem restrictFormsIso_comp (f : X' ⟶ X) (f' : X'' ⟶ X') [IsOpenImmersion f]
    [IsOpenImmersion f'] (p : X ⟶ S) (p' : X' ⟶ S') (p'' : X'' ⟶ S'') (g : S' ⟶ S)
    (g' : S'' ⟶ S') (g'' : S'' ⟶ S) [Etale g] [Etale g'] [Etale g'']
    (hcomm : f ≫ p = p' ≫ g) (hcomm' : f' ≫ p' = p'' ≫ g')
    (hcomm'' : (f' ≫ f) ≫ p = p'' ≫ g'') (n : ℤ) :
    restrictFormsIso (f' ≫ f) p p'' g'' hcomm'' n =
      (Scheme.Modules.restrictFunctorComp f' f).app (relativeDifferentialForms p n) ≪≫
        (Scheme.Modules.restrictFunctor f').mapIso (restrictFormsIso f p p' g hcomm n) ≪≫
          restrictFormsIso f' p' p'' g' hcomm' n :=
  Iso.ext (toRestrictForms_comp f f' p p' p'' g g' g'' hcomm hcomm' hcomm'' n)

/-! ### Two nested opens of the ambient scheme -/

variable (π : X ⟶ S)

/-- The square `X.homOfLE e ≫ (W.ι ≫ π) = (W'.ι ≫ π) ≫ 𝟙 S` of an open `W' ≤ W` of `X` read
inside `W`, with `𝟙 S` on the base. -/
theorem homOfLE_comp_ι_comp {W' W : X.Opens} (e : W' ≤ W) :
    X.homOfLE e ≫ (W.ι ≫ π) = (W'.ι ≫ π) ≫ 𝟙 S := by
  rw [← Category.assoc, X.homOfLE_ι, Category.comp_id]

/-- **`(Ω^n_{W/S})|_{W'} ≅ Ω^n_{W'/S}` for two opens `W' ≤ W` of `X`**, the restriction being
taken along `AlgebraicGeometry.Scheme.homOfLE`.  This is the chart-to-chart leg of the
identification of the coefficient module in `Stacks.Gysin.chartTargetHom`. -/
def relativeDifferentialFormsRestrictLEIso {W' W : X.Opens} (e : W' ≤ W) (n : ℤ) :
    Scheme.Modules.restrict (relativeDifferentialForms (W.ι ≫ π) n) (X.homOfLE e) ≅
      relativeDifferentialForms (W'.ι ≫ π) n :=
  restrictFormsIso (X.homOfLE e) (W.ι ≫ π) (W'.ι ≫ π) (𝟙 S) (homOfLE_comp_ι_comp π e) n

/-- **The identification `(Ω^n_{X/S})|_W ≅ Ω^n_{W/S}` of the coefficient module is compatible
with passing to a smaller chart.**  For `W' ≤ W` in `X`, the identification for `W'` is the
identification for `W`, restricted along `X.homOfLE e`, followed by the identification for
`W' ≤ W` inside `W`, with
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` mediating at the source.

**This is one of the four factors of `Stacks.Gysin.chartTargetHom` that the two-chart comparison
of [Stacks, Tag 0G86] needs.** -/
theorem relativeDifferentialFormsRestrictIso_hom_comp {W' W : X.Opens} (e : W' ≤ W) (n : ℤ) :
    (relativeDifferentialFormsRestrictIso π W' n).hom =
      (ModuleLimits.restrictLEIso e).inv.app (relativeDifferentialForms π n) ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
            (relativeDifferentialFormsRestrictIso π W n).hom ≫
          (relativeDifferentialFormsRestrictLEIso π e n).hom := by
  have hcongr := toRestrictForms_congr (X.homOfLE_ι e) π (W'.ι ≫ π) (𝟙 S) (by simp)
    (by simp) n
  rw [toRestrictForms_comp W.ι (X.homOfLE e) π (W.ι ≫ π) (W'.ι ≫ π) (𝟙 S) (𝟙 S) (𝟙 S)
    (by simp) (homOfLE_comp_ι_comp π e) (by simp)] at hcongr
  simp only [ModuleLimits.restrictLEIso, relativeDifferentialFormsRestrictIso,
    relativeDifferentialFormsRestrictIsoOfEq, relativeDifferentialFormsRestrictLEIso,
    restrictFormsIso_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, hcongr, Category.assoc]

/-- `relativeDifferentialFormsRestrictIso_hom_comp` read on the inverses, which is the direction
`Stacks.Gysin.chartTargetHom` composes with: it holds the inverse of the identification of the
coefficient module, not its forward map. -/
theorem relativeDifferentialFormsRestrictIso_inv_comp {W' W : X.Opens} (e : W' ≤ W) (n : ℤ) :
    (relativeDifferentialFormsRestrictIso π W' n).inv =
      (relativeDifferentialFormsRestrictLEIso π e n).inv ≫
        (Scheme.Modules.restrictFunctor (X.homOfLE e)).map
            (relativeDifferentialFormsRestrictIso π W n).inv ≫
          (ModuleLimits.restrictLEIso e).hom.app (relativeDifferentialForms π n) := by
  have h : relativeDifferentialFormsRestrictIso π W' n =
      ((ModuleLimits.restrictLEIso e).app (relativeDifferentialForms π n)).symm ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE e)).mapIso
            (relativeDifferentialFormsRestrictIso π W n) ≪≫
          relativeDifferentialFormsRestrictLEIso π e n :=
    Iso.ext (relativeDifferentialFormsRestrictIso_hom_comp π e n)
  rw [h]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Category.assoc]

end Stacks.AlgebraicGeometry.DifferentialsRestrict

namespace Stacks.Gysin

open Stacks.Perfect.CechDerivedSupport

variable {X X' Z : Scheme.{u}}

/-! ### The equations of a smaller chart -/

/-- **The common zero locus of the equations pulled back along a morphism of schemes is the
preimage of the common zero locus.**  Each principal open pulls back to a principal open, by
`AlgebraicGeometry.Scheme.preimage_basicOpen`, and taking preimages commutes with the supremum
and with the complement. -/
theorem equationsClosedSet_appTop (m : X' ⟶ X) {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    equationsClosedSet (fun j => m.appTop (f j)) = m ⁻¹' equationsClosedSet f := by
  have hsup : (⨆ j, X'.basicOpen (m.appTop (f j)) : X'.Opens) =
      m ⁻¹ᵁ (⨆ j, X.basicOpen (f j) : X.Opens) := by
    rw [Scheme.Hom.preimage_iSup]
    exact iSup_congr fun j => (Scheme.preimage_basicOpen m (f j)).symm
  change ((⨆ j, X'.basicOpen (m.appTop (f j)) : X'.Opens) : Set X')ᶜ =
    m ⁻¹' ((⨆ j, X.basicOpen (f j) : X.Opens) : Set X)ᶜ
  rw [hsup, Set.preimage_compl]
  rfl

/-- **Transitivity of `Stacks.Gysin.restrictEquations`.**  For `W' ≤ W` two opens of `X`, the
equations of the chart `W` restricted to `W'` — that is, the sections `f j ∈ Γ(X, W)` restricted
along `W' ≤ W` — read as global sections of `W'.toScheme`, are the global sections of
`W.toScheme` given by `Stacks.Gysin.restrictEquations W f`, pulled back along
`AlgebraicGeometry.Scheme.homOfLE`.

Both sides are one restriction map of `𝒪_X` applied to `f j`, between the same two opens of `X`,
and the morphisms of `X.Opens` between two opens form a subsingleton. -/
theorem restrictEquations_homOfLE {W' W : X.Opens} (e : W' ≤ W) {I : Type*}
    (f : I → Γ(X, W)) (j : I) :
    restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k)) j =
      (X.homOfLE e).appTop (restrictEquations W f j) := by
  rw [restrictEquations_apply, restrictEquations_apply, Scheme.homOfLE_appTop]
  refine Eq.trans (presheaf_map_comp_apply (homOfLE e).op (eqToHom W'.ι_image_top).op (f j)) ?_
  refine Eq.trans ?_ (presheaf_map_comp_apply (eqToHom W.ι_image_top).op
    (homOfLE (X.ι_image_homOfLE_le_ι_image e ⊤)).op (f j)).symm
  exact presheaf_map_congr _ _ (f j)

/-- **The zero locus of a smaller chart's equations is the preimage of the zero locus.** This is
`equationsClosedSet_appTop` at `restrictEquations_homOfLE`, and it is what identifies the
supporting closed subsets of the two charts' targets. -/
theorem equationsClosedSet_restrictEquations_homOfLE {W' W : X.Opens} (e : W' ≤ W) {c : ℕ}
    (f : Fin c → Γ(X, W)) :
    equationsClosedSet (restrictEquations W' (fun k => X.presheaf.map (homOfLE e).op (f k))) =
      X.homOfLE e ⁻¹' equationsClosedSet (restrictEquations W f) := by
  rw [← equationsClosedSet_appTop (X.homOfLE e) (restrictEquations W f)]
  exact congrArg equationsClosedSet (funext fun j => restrictEquations_homOfLE e f j)

end Stacks.Gysin

end
