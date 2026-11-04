module

public import StacksFrontier.AlgebraicGeometry.NestedCocycleReduction.Basic

/-!
# Tag 01NO's pushed-forward twist comparison on sections, unconditionally

`StacksFrontier/AlgebraicGeometry/NestedCocycleReduction/Basic.lean` computes the pushed-forward
twist comparison `Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNested` on sections
*conditionally on the action of its tail*, and records that the action of the tail was not
reachable from outside the file defining it. That hypothesis is now discharged, by
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail_hom_val_app`, so the comparison
on sections is available outright.

This file draws the two consequences. The comparison is computed on sections with no hypothesis,
and the nested cocycle
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` — the one statement the chart
data of a relative projective spectrum is conditional on — is **reduced to a statement in which
no construction on the relative projective spectrum occurs at all**.

## Main definitions

* `Stacks.AlgebraicGeometry.NestedCocycleTail.IsChartCocycle`: **the cocycle for Tag 01NO's
  chart-level comparison**, for a chain `W ⊆ W' ⊆ U` of affine opens of the base. It is a
  statement about the three isomorphisms
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` on the sections over opens
  of the three charts, with every inclusion of opens a free argument. The relative projective
  spectrum does not appear in it.

## Main results

* `Stacks.AlgebraicGeometry.NestedCocycleTail.pushNested_app_val`: **the comparison on sections,
  unconditionally.** A section `s` over an open `V` of the relative Proj is carried to the
  chart-level comparison applied to the restriction of `s` to the image, in the chart of `U`, of
  the preimage of `V` in the chart of `W`.
* `Stacks.AlgebraicGeometry.NestedCocycleTail.cmpNested_app_val`: the same read through
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested`, which is the form the cocycle is
  stated over.
* `Stacks.AlgebraicGeometry.NestedCocycleTail.isNestedCocycle_of_isChartCocycle`: **the
  reduction.** The nested cocycle follows from the chart cocycle, with no further input.

## What this changes, and what it does not

The nested cocycle was the single hypothesis of
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelData`, `gluedTwist`, `chartIso` and
`cmpGen`. After the reduction its content is entirely chart-level: three isomorphisms of sheaves
of modules on three projective spectra of graded rings, and the assertion that the comparison of
the outer pair is the composite of the two inner ones on sections. Neither the relative Proj, nor
its charts, nor the pushforward along them, nor the restriction adjunction occurs in
`IsChartCocycle`.

What remains genuinely open is that chart-level statement, and it is not formal. Tag 01NO's
comparison `Stacks.AlgebraicGeometry.ChartTransRelativeProj.restrictTwistIso` is
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` followed by
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, a sixfold composite of
components of the **pullback** pseudofunctoriality isomorphisms together with the functor image
of Tag 01MY's twist map. So `IsChartCocycle` is the functoriality of that twist map in the graded
ring map, transported across six pullback factors — which is what the owning file's "What is not
done" names, and nothing here supplies it.

No `stacks` attribute is attached to any declaration below. Nothing here is a covering set for
any label: every statement is either a computation of a comparison whose invertibility assertion
is already carried elsewhere, or a reduction conditional on an unproved hypothesis.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

namespace Stacks.AlgebraicGeometry.NestedCocycleTail

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u

/-! ### Named generic vocabulary for the chart-level legs -/

/-- **One leg of a chart-level twist comparison, read on sections, as a named generic function.**
Restrict a section over an open of the target along an inclusion of the image of an open of the
source, then apply the comparison there.

The single definitional step — that the sections of the restriction of `M` along `g` over `T` are
the sections of `M` over `g ''ᵁ T`, which is
`AlgebraicGeometry.Scheme.Modules.restrict_obj` and holds by `rfl` — is taken **once, here, at
the level of variables**. Every statement below mentions this named function instead of writing
the composite out, so that every match is between two instantiations of one head symbol. -/
public def chartLeg {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] {M : X.Modules}
    {N : Y.Modules} (e : (Scheme.Modules.restrictFunctor g).obj M ≅ N) {T : Y.Opens}
    {T₀ : X.Opens} (j : g ''ᵁ T ⟶ T₀) : M.val.obj (op T₀) → N.val.obj (op T) :=
  fun t => e.hom.val.app (op T) (M.val.map j.op t)

/-- **Three functions compose**, as a named generic predicate. Read
`IsEvalComposite G₂ G₁ G₃` as: following `G₂` by `G₁` is `G₃`.

Named for the reason recorded throughout this cluster: an equation written out at the concrete
instance cannot be matched against the same equation produced by instantiating a generic
statement, so both sides of every match are kept generic. -/
public def IsEvalComposite {α β γ : Type u} (G₂ : α → β) (G₁ : β → γ) (G₃ : α → γ) : Prop :=
  ∀ s, G₁ (G₂ s) = G₃ s

/-! ### A composition law from three computed actions -/

/-- **A composition law for three local isomorphisms, from a description of each one's action on
sections.** Given plain functions `G₂`, `G₁`, `G₃` computing the three isomorphisms over one
open, the composition law reduces to the corresponding equation between the functions.

Every ingredient is a variable, which is what makes it usable at the concrete instance below.
There, chaining the three computations and the function-level equation by hand with
`CategoryTheory.Eq.trans` and `congrArg` fails with a recursion limit, because the goal's
left-hand side is then a `congrArg` application that has to be matched against a generically
produced body. Instantiating this lemma performs no
match: `G₂`, `G₁` and `G₃` are determined by the three computations, and the function-level
equation is then compared against assigned metavariables. -/
public theorem isComposite_of_eval {X : TopCat.{u}} {𝒪 : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    {M N P : PresheafOfModules.{u} 𝒪} {W₀ W₁ : Opens X}
    (e₀ : TopCat.Sheaf.LocalModuleEquiv M N W₁) (e₁ : TopCat.Sheaf.LocalModuleEquiv N P W₀)
    (e₂ : TopCat.Sheaf.LocalModuleEquiv M P W₀) (V : Opens X) (hV₀ : V ≤ W₀) (hV₁ : V ≤ W₁)
    (G₂ : M.obj (op V) → N.obj (op V)) (G₁ : N.obj (op V) → P.obj (op V))
    (G₃ : M.obj (op V) → P.obj (op V))
    (h₀ : ∀ s, e₀.app V hV₁ s = G₂ s) (h₁ : ∀ z, e₁.app V hV₀ z = G₁ z)
    (h₂ : ∀ s, e₂.app V hV₀ s = G₃ s) (hcc : IsEvalComposite G₂ G₁ G₃) :
    IsComposite e₀ e₁ e₂ V hV₀ hV₁ :=
  fun s => ((h₁ (e₀.app V hV₁ s)).trans ((congrArg G₁ (h₀ s)).trans (hcc s))).trans (h₂ s).symm

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### The comparison on sections, unconditionally -/

section Nested

variable (W U : S.Opens) (h : W ≤ U) (hW : IsAffineOpen W) (hU : IsAffineOpen U) (n : ℤ)

/-- **Tag 01NO's pushed-forward twist comparison on sections.** The comparison carries a section
`s` over an open `V` of the relative projective spectrum to Tag 01NO's chart-level comparison,
read over the preimage of `V` in the chart of `W`, applied to the restriction of `s` to the image
in the chart of `U` of that preimage.

This is
`Stacks.AlgebraicGeometry.NestedCocycleReduction.pushNested_app_val_of` with its hypothesis
discharged by
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.pushNestedTail_hom_val_app`. The inclusion of
opens it is instantiated at is the transport of
`Stacks.AlgebraicGeometry.NestedCocycleReduction.chart_preimage_eq`; which inclusion is used does
not matter, since morphisms between opens are unique. -/
public theorem pushNested_app_val (V : (relativeProj A).scheme.Opens)
    (s : (twistingSheaf (A.grading U) n).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (pushNested A W U h hW hU n).val.app (op V) s =
      chartLeg (projInclusionMap A W U h hW hU) (restrictTwistIso A W U h hW hU n)
        (homOfLE (image_preimage_le_preimage A W U h hW hU V)) s :=
  pushNested_app_val_of A W U h hW hU n V (eqToHom (chart_preimage_eq A W U h hW hU V))
    (fun y => pushNestedTail_hom_val_app A W U h hW hU n V
      (eqToHom (chart_preimage_eq A W U h hW hU V)) y) s

/-- The same, read through
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpNested`. This is the form the nested cocycle
is stated over. -/
public theorem cmpNested_app_val (V : (relativeProj A).scheme.Opens)
    (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (s : (twistingSheaf (A.grading U) n).val.obj
      (op ((relativeProj A).chart U hU ⁻¹ᵁ V))) :
    (cmpNested A W U h hW hU n).app V hV s =
      chartLeg (projInclusionMap A W U h hW hU) (restrictTwistIso A W U h hW hU n)
        (homOfLE (image_preimage_le_preimage A W U h hW hU V)) s :=
  (cmpNested_app A W U h hW hU n V hV s).trans (pushNested_app_val A W U h hW hU n V s)

end Nested

/-! ### The chart-level cocycle, and the reduction -/

/-- **The cocycle for Tag 01NO's chart-level twist comparison.** For a chain `W ⊆ W' ⊆ U` of
affine opens of the base, an integer `n`, opens `T`, `T'` and `T₀` of the three charts and
inclusions between their images, the comparison of the charts of `U` and `W` agrees on sections
with the comparison of the charts of `U` and `W'` followed by that of the charts of `W'` and `W`.

Every inclusion of opens is a **free argument**: morphisms between opens are unique, so the three
containments never have to be exhibited in any particular form, and no transport of opens occurs
in the statement. For the same reason the three opens are unrelated parameters rather than being
tied to one another — the composition law `g₁ ≫ g₂ = g₃` for the transition morphisms is not
needed and is not assumed.

Nothing in this statement mentions the relative projective spectrum, its charts, the pushforward
along them, or the restriction adjunction. That is the content of
`Stacks.AlgebraicGeometry.NestedCocycleTail.isNestedCocycle_of_isChartCocycle`: those four layers
are exactly what the reduction strips. -/
public def IsChartCocycle : Prop :=
  ∀ (W W' U : S.Opens) (hWW' : W ≤ W') (hW'U : W' ≤ U) (hWU : W ≤ U)
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hU : IsAffineOpen U) (n : ℤ)
    (T : (AlgebraicGeometry.Proj (A.grading W)).Opens)
    (T' : (AlgebraicGeometry.Proj (A.grading W')).Opens)
    (T₀ : (AlgebraicGeometry.Proj (A.grading U)).Opens)
    (i₁ : projInclusionMap A W W' hWW' hW hW' ''ᵁ T ⟶ T')
    (j₂ : projInclusionMap A W' U hW'U hW' hU ''ᵁ T' ⟶ T₀)
    (j₃ : projInclusionMap A W U hWU hW hU ''ᵁ T ⟶ T₀),
    IsEvalComposite
      (chartLeg (projInclusionMap A W' U hW'U hW' hU)
        (restrictTwistIso A W' U hW'U hW' hU n) j₂)
      (chartLeg (projInclusionMap A W W' hWW' hW hW')
        (restrictTwistIso A W W' hWW' hW hW' n) i₁)
      (chartLeg (projInclusionMap A W U hWU hW hU) (restrictTwistIso A W U hWU hW hU n) j₃)

/-- **The nested cocycle follows from the chart cocycle.** The three comparisons appearing in
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` are computed on sections by
`Stacks.AlgebraicGeometry.NestedCocycleTail.cmpNested_app_val`, after which the statement is
an instance of `Stacks.AlgebraicGeometry.NestedCocycleTail.IsChartCocycle` at the three chart
preimages of the open, with the three inclusions supplied by
`Stacks.AlgebraicGeometry.NestedCocycleReduction.image_preimage_le_preimage`.

No further input is used: the free inclusion arguments of `IsChartCocycle` are what make the
three restriction maps the reduction produces acceptable without any identification. -/
public theorem isNestedCocycle_of_isChartCocycle (hc : IsChartCocycle A) (n : ℤ) :
    IsNestedCocycle A n := by
  intro W W' U hWW' hW'U hWU hW hW' hU V hV hV'
  refine isComposite_of_eval (cmpNested A W' U hW'U hW' hU n) (cmpNested A W W' hWW' hW hW' n)
      (cmpNested A W U hWU hW hU n) V hV hV' _ _ _
      (cmpNested_app_val A W' U hW'U hW' hU n V hV')
      (cmpNested_app_val A W W' hWW' hW hW' n V hV)
      (cmpNested_app_val A W U hWU hW hU n V hV) ?_
  exact (hc W W' U hWW' hW'U hWU hW hW' hU n
        ((relativeProj A).chart W hW ⁻¹ᵁ V) ((relativeProj A).chart W' hW' ⁻¹ᵁ V)
        ((relativeProj A).chart U hU ⁻¹ᵁ V)
        (homOfLE (image_preimage_le_preimage A W W' hWW' hW hW' V))
        (homOfLE (image_preimage_le_preimage A W' U hW'U hW' hU V))
        (homOfLE (image_preimage_le_preimage A W U hWU hW hU V)))

end Stacks.AlgebraicGeometry.NestedCocycleTail

end
