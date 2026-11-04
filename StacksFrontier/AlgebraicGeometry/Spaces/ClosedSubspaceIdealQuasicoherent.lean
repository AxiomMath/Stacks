module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CartesianRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian

/-!
# Stacks 03MB reduced to the surjectivity half of Descent 03DX(2) for sheaves of ideals

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Stacks 03MB
asserts that `Z ↦ 𝓘_Z` is an inclusion-reversing bijection between the closed subspaces of `X`
and the **quasi-coherent** sheaves of ideals `𝓘 ⊆ 𝒪_X` on the small étale site of `X`.
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` assembles that statement, together with
the kernel formula that pins the bijection down to the canonical rule, from two hypotheses:

* `hq`, that the defining ideal sheaf of a closed subspace is quasi-coherent;
* `hr`, that every quasi-coherent sheaf of ideals is a defining ideal sheaf.

**Both are discharged here, and what is left is a single implication.**  Each of `hq` and `hr`
was previously reached only through the two-way bridge

`∀ G, G.IsQuasicoherentOnSite ↔ IsCartesianOnAffineCharts G`

which this tree carries as the hypothesis `h03DX` of Descent, Proposition 03DX(2).  The
implication `←` of that bridge is now the unconditional
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`, and the chartwise
construction of the surjectivity half is the unconditional
`AlgebraicGeometry.Space.exists_idealSheafData_of_isCartesianOnAffineCharts`.  Combining them:

* `hq` becomes unconditional, because `𝓘_Z` is cartesian on affine charts unconditionally
  (`AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`) and `←` turns that
  into quasi-coherence;
* `hr` becomes unconditional **for a sheaf of ideals that is cartesian on affine charts**, by
  running the chartwise construction on an atlas supplied by `X` itself and feeding it to
  `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isInvariantSubscheme`.

So the only input Stacks 03MB still needs *in this file* is the *forward* implication of Descent
03DX(2): that a quasi-coherent `𝒪_X`-module is cartesian on affine charts, and only for sheaves
of ideals at that.  **For a sheaf of ideals that implication splits, and one of its two halves is
proved here.**  Being cartesian over a morphism of affine charts is injectivity *and*
surjectivity of the base change comparison, and for a sheaf submodule of `𝒪_X` injectivity is
unconditional:
`𝒪_X` is itself cartesian over every chart morphism
(`AlgebraicGeometry.Space.bijective_sectionsBaseChange_unit`), the inclusion of a submodule is
injective on sections, and the restriction map between affine charts is flat
(`AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine`), so tensoring the inclusion keeps it
injective.  That is `AlgebraicGeometry.Space.injective_sectionsBaseChange_submodule_unit`, and
with it `AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective` reduces
the cartesian condition on a sheaf of ideals to the surjectivity condition alone.

What remains in this file is therefore **surjectivity**: that for a quasi-coherent sheaf of
ideals the sections over an affine étale chart generate, over the smaller chart's ring of
functions, the sections over every smaller affine étale chart.  It is carried here as the
explicit named hypothesis `hsurj` of
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_surjective_sectionsBaseChange`.

**That hypothesis, and Stacks 03MB itself, are proved elsewhere in this tree; nothing below is
blocked for want of them.**

* Surjectivity for a quasi-coherent sheaf of ideals is
  `AlgebraicGeometry.Space.surjective_sectionsBaseChange_submodule_unit_of_isQuasicoherentOnSite`
  (`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceFromQuasicoherentIdeal.lean:251`), proved
  by faithfully flat descent for a pair of nested ideals of the smaller chart's ring along a
  refinement of the covering that quasi-coherence supplies.  That file then reaches Stacks 03MB:
  the bijection is `AlgebraicGeometry.Space.toDual_definingIdealSheaf_bijective'` (line 340) and
  the order isomorphism with its kernel formula is
  `AlgebraicGeometry.Space.closedSubspaceQuasicoherentIdealOrderIso` (line 358).
* The *whole* forward implication of Descent 03DX(2), for an arbitrary `𝒪_X`-module, is
  `AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`
  (`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentCartesianOnAffineCharts.lean:640`, carrying
  `@[stacks 03DX]`), by the descent argument of Stacks 0H04 on the affine étale site.  It is
  restated in the `h03DX` spelling the two order isomorphisms below use, so that it can be
  supplied with no adapter, as
  `AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`
  (`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentImpliesCartesian.lean:233`).

Why the remaining half is not obtained *in this file*.
`CategoryTheory.SheafOfModules.IsQuasicoherentOnSite` provides a global presentation only on the
members of *some* covering of each object of the site, never over the object itself, so passing
from it to a statement about the sections over an affine chart is a localization argument.  Even
granted a presentation over the chart,
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_presentation` still asks for surjectivity
and exactness of the presentation *on sections* over every affine chart, which its own
documentation identifies as the content of Descent 03DX(2).  The injectivity half proved here is
exactly the part of the comparison that needs none of that, and it is the part a sheaf of ideals
gets for free from the inclusion into `𝒪_X`.  Neither of the two proofs that do supply the
missing half takes this route: the one for sheaves of ideals descends an equality of ideals along
a faithfully flat refinement, and the one for an arbitrary module runs Stacks 0H04 on the affine
étale site.

Two further reductions of Descent, Proposition 03DX(2) live in this tree; both are superseded by
those proofs.  Its fullness input, Descent, Lemma 0GN7, is available on the slice at an affine
chart as `AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice`, subject to the
sheaf condition of Stacks 03DT, and unconditionally as
`AlgebraicGeometry.Space.SmallEtale.bijective_associatedModuleMap_slice_unconditional`
(`StacksFrontier/AlgebraicGeometry/Spaces/SliceAssociatedModuleSheafCondition.lean:121`); fullness
is, however, a different clause of the equivalence from the *essential surjectivity* of `(-)ᵃ`,
which is the hypothesis `hEss` of
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_essSurj` and is the one
statement that reduction still leaves open.  Descent, Proposition 03DW is available in its
uniform form as `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian`,
subject to degree-one Čech vanishing; it produces surjectivity of a morphism on affine-chart
sections only for a morphism whose *kernel* is already cartesian on affine charts, and
`CategoryTheory.SheafOfModules.IsQuasicoherentOnSite` exhibits a sheaf of ideals as a quotient of
a coproduct of copies of `𝒪_X` only on the members of a covering, so no such morphism onto `I`
is in hand.

## Main definitions

* `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_surjective_sectionsBaseChange` is the
  order isomorphism of Stacks 03MB together with its kernel formula, conditional on the
  surjectivity half of Descent 03DX(2) for sheaves of ideals and on nothing else.
* `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_h03DX` is the same conclusion from the
  whole forward implication of Descent 03DX(2), which is the spelling the tree's other carriers
  of `h03DX` use.

## Main results

* `AlgebraicGeometry.Space.injective_sectionsBaseChange_of_injective_app`: the base change
  comparison of a module mapping injectively into a module cartesian over a chart morphism with
  flat restriction map is injective.
* `AlgebraicGeometry.Space.surjective_sectionsBaseChange_of_surjective_app`: the base change
  comparison of the target of a morphism surjective on the sections over the smaller chart is
  surjective as soon as the comparison of the source is.  This is the surjectivity companion of
  the previous result, and it needs neither flatness nor exactness.
* `AlgebraicGeometry.Space.injective_sectionsBaseChange_submodule_unit`: **the injectivity half
  of Descent 03DX(2) for a sheaf of ideals of `𝒪_X`, unconditionally.**
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective`: **for a
  sheaf of ideals, surjectivity of the base change comparison on affine charts already gives
  the cartesian condition.**
* `AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective_app`: a sheaf
  of ideals receiving a morphism from a module cartesian on affine charts, surjective on the
  sections over every affine chart, is cartesian on affine charts.  Its hypothesis is equivalent
  to `hsurj` below rather than weaker; what it gains is that the residue becomes a statement
  about a morphism being surjective on affine-chart sections, which is the conclusion of
  `AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf`: **the defining ideal sheaf
  of a closed subspace is quasi-coherent on the small étale site, unconditionally.**  This is
  the hypothesis `hq` of `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso`.
* `AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts`: **a sheaf
  of ideals of `𝒪_X` which is cartesian on affine charts is the defining ideal sheaf of a closed
  subspace, unconditionally.**  Together with the surjectivity half of Descent 03DX(2) this is
  the hypothesis `hr` of `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso`.

## Implementation notes

The quasi-coherence clause of Stacks 03MB — "the kernel of `i♯` is a quasi-coherent sheaf of
ideals" — is stated in the source for an arbitrary closed immersion `i : Z ⟶ X`, whereas
`AlgebraicGeometry.Space.isQuasicoherentOnSite_definingIdealSheaf` is stated for a closed
*subspace* of `X` and for the submodule of `𝒪_X` rather than for the kernel object; the
identification of the two is `AlgebraicGeometry.Space.definingIdealAt_eq_ker_fSharp`.  The two
order isomorphisms below both carry the surjectivity half of Descent 03DX(2) for sheaves of
ideals as a hypothesis, which is proved downstream — see the module documentation for where —
so neither is blocked.

The atlas used by
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts` is the one
`AlgebraicGeometry.IsAlgebraicSpace.exists_atlas` provides, and *which* atlas is irrelevant:
both the chartwise construction and its consumer are stated for an arbitrary surjective étale
chart, and the conclusion names no chart.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

/-! ### Injectivity of the base change comparison of a submodule -/

section Submodule

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **The base change comparison of a module with an injective map into a module cartesian over
`f` is injective**, as soon as the restriction map of regular functions along `f` is flat.

Only injectivity of `φ` on the sections over the *larger* chart `U` is used: flatness turns it
into injectivity of `𝒪_F(V) ⊗ φ_U`, and the naturality square
`AlgebraicGeometry.Space.app_sectionsBaseChange` factors the comparison of `G` through that map
and through the comparison of `G'`, which is bijective.  Nothing is assumed over `V`.

This is the companion of `AlgebraicGeometry.Space.bijective_sectionsBaseChange_kernel`: there a
two-sided exactness hypothesis buys bijectivity, here a one-sided injectivity hypothesis buys
injectivity, and the exactness that bijectivity needs is exactly what is not available for a
submodule of the structure sheaf. -/
theorem injective_sectionsBaseChange_of_injective_app
    {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G')
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hflat : RingHom.Flat (chartRestrict (hF := hF) f))
    (hφ : Function.Injective (φ.val.app (op U)))
    (hG' : Function.Bijective (sectionsBaseChange G' f)) :
    Function.Injective (sectionsBaseChange G f) := by
  let _ := chartAlgebra (hF := hF) f
  have _ : Module.Flat (chartRing B S hS F hF U) (chartRing B S hS F hF V) := hflat
  intro z w h
  have h1 : LinearMap.lTensor (chartRing B S hS F hF V) (φ.val.app (op U)).hom z =
      LinearMap.lTensor (chartRing B S hS F hF V) (φ.val.app (op U)).hom w :=
    hG'.1 (by rw [← app_sectionsBaseChange φ f z, ← app_sectionsBaseChange φ f w, h])
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ h1

/-- **The base change comparison of the target of a morphism is surjective** as soon as the
comparison of the source is surjective and the morphism is surjective on the sections over the
*smaller* chart `V`.

This is the surjectivity companion of
`AlgebraicGeometry.Space.injective_sectionsBaseChange_of_injective_app`, and the two are
asymmetric in which chart they constrain: injectivity is bought by injectivity over the larger
chart `U` together with flatness, surjectivity by surjectivity over the smaller chart `V` and
nothing else.  No flatness, no exactness and no hypothesis over the other chart are used.

The whole content is the naturality square
`AlgebraicGeometry.Space.app_sectionsBaseChange`, which writes `φ_V ∘ c_G` as
`c_{G'} ∘ (𝒪_F(V) ⊗ φ_U)`; a surjective composite factoring through `c_{G'}` forces `c_{G'}` to
be surjective.

This asks strictly less of `φ` than
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_cokernel`, which additionally needs `φ` to
be exact on the sections over both charts and to be preceded by a second morphism; in exchange it
concludes only surjectivity.  For a sheaf of ideals of `𝒪_F` that is no loss, injectivity being
unconditional there — see
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective_app`. -/
theorem surjective_sectionsBaseChange_of_surjective_app
    {G G' : Modules.{u, m} B S hS F hF} (φ : G ⟶ G')
    {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (hφ : Function.Surjective (φ.val.app (op V)))
    (hG : Function.Surjective (sectionsBaseChange G f)) :
    Function.Surjective (sectionsBaseChange G' f) := by
  let _ := chartAlgebra (hF := hF) f
  intro y
  obtain ⟨x, hx⟩ := hφ y
  obtain ⟨z, hz⟩ := hG x
  refine ⟨LinearMap.lTensor (chartRing B S hS F hF V) (φ.val.app (op U)).hom z, ?_⟩
  rwa [← app_sectionsBaseChange φ f z, hz]

end Submodule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The injectivity half of Descent 03DX(2) for a sheaf of ideals of `𝒪_X`, unconditionally.**
For every morphism of affine étale charts the base change comparison of a sheaf submodule of the
structure sheaf is injective, with no quasi-coherence hypothesis and no cohomological input.

A sheaf of ideals has more structure than a general `𝒪_X`-module — it comes with an injection
into `𝒪_X` — and that is all the argument uses:
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_unit` says `𝒪_X` itself is cartesian over
every chart morphism, the inclusion of a submodule is injective on sections because it is
`Subtype.val`, and `AlgebraicGeometry.Space.flat_chartRestrict_of_isAffine` supplies the
flatness that `AlgebraicGeometry.Space.injective_sectionsBaseChange_of_injective_app` needs.

So for a sheaf of ideals the content of Descent 03DX(2) is confined to *surjectivity* of the
comparison; see
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective`. -/
theorem injective_sectionsBaseChange_submodule_unit (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {U V : SmallEtale B S hS X.1} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V)) :
    Function.Injective (sectionsBaseChange I.toSheafOfModules f) :=
  injective_sectionsBaseChange_of_injective_app I.ι f
    (flat_chartRestrict_of_isAffine f hU hV)
    (fun _ _ hab => Subtype.val_injective hab)
    (bijective_sectionsBaseChange_unit (hF := X.2) f)

/-- **For a sheaf of ideals of `𝒪_X`, surjectivity of the base change comparison on affine
charts already gives `AlgebraicGeometry.Space.IsCartesianOnAffineCharts`.**  The injectivity
half is the unconditional
`AlgebraicGeometry.Space.injective_sectionsBaseChange_submodule_unit`.

Equivalently: for sheaves of ideals the cartesian condition and the surjectivity condition are
the same condition.  That is what lets the residue of Stacks 03MB be stated as a surjectivity
statement, which is where the geometry of Descent 03DX(2) actually sits — surjectivity says that
the sections over the smaller chart are generated by the restrictions of the sections over the
larger one. -/
theorem isCartesianOnAffineCharts_submodule_unit_of_surjective (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hsurj : ∀ U V : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
          ∀ f : V ⟶ U, Function.Surjective (sectionsBaseChange I.toSheafOfModules f)) :
    IsCartesianOnAffineCharts I.toSheafOfModules := fun U V hU hV f =>
  ⟨injective_sectionsBaseChange_submodule_unit B S hS X I f hU hV, hsurj U V hU hV f⟩

/-- **A sheaf of ideals of `𝒪_X` receiving a morphism from a module cartesian on affine charts,
surjective on the sections over every affine étale chart, is itself cartesian on affine
charts.**

Only the surjectivity of `φ` on sections is used, and only over the smaller of the two charts;
the morphism is not asked to be an epimorphism, no kernel of it appears, and no exactness on
sections is required.  Surjectivity of the comparison of `I` is
`AlgebraicGeometry.Space.surjective_sectionsBaseChange_of_surjective_app` and its injectivity is
the unconditional `AlgebraicGeometry.Space.injective_sectionsBaseChange_submodule_unit`.

Only the surjectivity half of `hG` is used.  It is nevertheless stated as
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts`, which is the form every witness in this tree
comes in (`AlgebraicGeometry.Space.isCartesianOnAffineCharts_free`,
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_coproduct`,
`AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`), and nothing is lost by
it: the statement with the minimal hypothesis is
`AlgebraicGeometry.Space.surjective_sectionsBaseChange_of_surjective_app` itself.

This asks strictly less than the ideal case of
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_presentation`, which needs the source to be
a coproduct of copies of `𝒪_X` presented by a second such coproduct and needs exactness of the
presentation on sections, and strictly less than the ideal case of
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_shortExact_X₃`, which needs a short exact
sequence whose left term is already known to be cartesian on affine charts.

It does **not** discharge the residue of Stacks 03MB.  Its hypothesis is *equivalent* to the
`hsurj` of
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_surjective_sectionsBaseChange`, not
weaker: `hsurj` supplies it at `φ := 𝟙 I.toSheafOfModules` with
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective`.  What it does is
convert that residue into a statement about a *morphism* being surjective on affine-chart
sections, which is the shape produced by
`AlgebraicGeometry.Space.surjective_val_app_of_epi_of_kernel_isCartesian`, the uniform form of
Descent, Proposition 03DW. -/
theorem isCartesianOnAffineCharts_submodule_unit_of_surjective_app
    (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    {G : Modules.{u, u} B S hS X.1 X.2} (φ : G ⟶ I.toSheafOfModules)
    (hG : IsCartesianOnAffineCharts G)
    (hφ : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Function.Surjective (φ.val.app (op W))) :
    IsCartesianOnAffineCharts I.toSheafOfModules :=
  isCartesianOnAffineCharts_submodule_unit_of_surjective B S hS X I
    fun U V hU hV f =>
      surjective_sectionsBaseChange_of_surjective_app φ f (hφ V hV) (hG U V hU hV f).2

/-- **The defining ideal sheaf of a closed subspace of an algebraic space is quasi-coherent on
its small étale site**, unconditionally.

This is the hypothesis `hq` of `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso`.  Only the
implication "cartesian on affine charts ⟹ quasi-coherent" of Descent 03DX(2) is used, and that
implication is the unconditional
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`; the cartesianity is
the unconditional `AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts`. -/
theorem isQuasicoherentOnSite_definingIdealSheaf (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    (definingIdealSheaf B S hS X Z).toSheafOfModules.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
    (definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z)

/-- **The surjectivity half of Stacks 03MB for a sheaf of ideals which is cartesian on affine
charts**, unconditionally: such a sheaf of ideals of `𝒪_X` is the defining ideal sheaf of a
closed subspace of `X`.

This is the hypothesis `hr` of `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso` with its
quasi-coherence antecedent replaced by cartesianity on affine charts, discharged.  An atlas of
`X` is extracted from `AlgebraicGeometry.IsAlgebraicSpace.exists_atlas`;
`AlgebraicGeometry.Space.exists_idealSheafData_of_isCartesianOnAffineCharts` turns the sheaf of
ideals into an invariant sheaf of ideals on the scheme underlying that chart, cutting out the
given sections over every affine chart above it; and
`AlgebraicGeometry.Space.exists_definingIdealSheaf_eq_of_isInvariantSubscheme` descends the
resulting closed subscheme to a closed subspace of `X`. -/
theorem exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts (X : AlgebraicSpaces B S hS)
    (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hI : IsCartesianOnAffineCharts I.toSheafOfModules) :
    ∃ Z : ClosedSubspaces B S hS X.1, definingIdealSheaf B S hS X Z = I := by
  obtain ⟨U, φ, hs, he⟩ := X.2.exists_atlas
  obtain ⟨J, hinv, hmatch⟩ :=
    exists_idealSheafData_of_isCartesianOnAffineCharts B S hS X hs he I hI
  exact exists_definingIdealSheaf_eq_of_isInvariantSubscheme B S hS X hs he J hinv I hmatch

/-- **Stacks 03MB, conditional on the surjectivity half of Descent 03DX(2) for sheaves of ideals
and on nothing else.**  Granted that for a quasi-coherent sheaf of ideals of `𝒪_X` the sections
over an affine étale chart generate the sections over every smaller affine étale chart
(`hsurj`), the closed subspaces of `X` are order-isomorphic to the order dual of the
quasi-coherent sheaves of ideals of `𝒪_X`, by the isomorphism sending a closed subspace to the
kernel of the structure map of its inclusion on every étale chart.

This asks strictly less than
`AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_h03DX`, which it proves, along two
independent axes.  The quantifier runs over sheaf submodules of `𝒪_X` rather than over all
`𝒪_X`-modules, and the demand is surjectivity of the base change comparison rather than its
bijectivity; both make `hsurj` easier to satisfy, hence this statement stronger.  Along the
second axis the two are in fact equivalent, by
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_submodule_unit_of_surjective`, whose
injectivity input is unconditional — which is the point: for a sheaf of ideals the whole residue
of Stacks 03MB is a statement about generation of sections.

`hsurj` is not vacuous: it holds unconditionally at every defining ideal sheaf, since
`AlgebraicGeometry.Space.definingIdealSheaf_isCartesianOnAffineCharts` is unconditional.

**This is not a proof of Stacks 03MB and carries no `@[stacks]` attribute.**  `hsurj` is half of
one implication of Descent, Proposition 03DX(2), and a hypothesis-carrying form must not be
presented as the tag.  It is not an obstruction: `hsurj` is discharged by
`AlgebraicGeometry.Space.surjective_sectionsBaseChange_submodule_unit_of_isQuasicoherentOnSite`
(`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceFromQuasicoherentIdeal.lean:251`), and the
tag itself is carried there by
`AlgebraicGeometry.Space.toDual_definingIdealSheaf_bijective'` (line 340). -/
noncomputable def closedSubspaceIdealOrderIso_of_surjective_sectionsBaseChange
    (X : AlgebraicSpaces B S hS)
    (hsurj : ∀ I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule,
      I.toSheafOfModules.IsQuasicoherentOnSite →
        ∀ U V : SmallEtale B S hS X.1,
          IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
            IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj V) →
              ∀ f : V ⟶ U, Function.Surjective (sectionsBaseChange I.toSheafOfModules f)) :
    {e : ClosedSubspaces B S hS X.1 ≃o (QuasicoherentIdeals B S hS X)ᵒᵈ //
      ∀ (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ),
        (OrderDual.ofDual (e Z)).1.obj U =
          RingHom.ker (((smallEtaleRingedToposHom B S hS
            (ObjectProperty.homMk Z.1.ι :
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).fSharp.hom.app U).hom)} :=
  closedSubspaceIdealOrderIso B S hS X (isQuasicoherentOnSite_definingIdealSheaf B S hS X)
    fun I hI =>
      exists_definingIdealSheaf_eq_of_isCartesianOnAffineCharts B S hS X I
        (isCartesianOnAffineCharts_submodule_unit_of_surjective B S hS X I (hsurj I hI))

/-- **Stacks 03MB, conditional on the forward implication of Descent 03DX(2) and on nothing
else.** Granted that a quasi-coherent `𝒪_X`-module is cartesian on affine charts (`h03DX`), the
closed subspaces of `X` are order-isomorphic to the order dual of the quasi-coherent sheaves of
ideals of `𝒪_X`, by the isomorphism sending a closed subspace to the kernel of the structure map
of its inclusion on every étale chart.

`h03DX` is the implication "quasi-coherent ⟹ cartesian on affine charts" of Descent,
Proposition 03DX(2), spelled exactly as in
`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_of_h03DX`.  Its converse is not a
hypothesis, being the proved
`AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isCartesianOnAffineCharts`.  The proof below
applies `h03DX` only to sheaves of *ideals* of `𝒪_X`, so the hypothesis restricted to those
would suffice; it is stated in the general form to avoid a third spelling of Descent 03DX(2) in
this tree.

This is `AlgebraicGeometry.Space.closedSubspaceIdealOrderIso_of_surjective_sectionsBaseChange`,
which asks less, with `hsurj` supplied by the `.2` half of `h03DX` at a sheaf of ideals.  It is
kept under this name and with this statement because it is the spelling the tree's other
carriers of `h03DX` use, so a single discharge of Descent 03DX(2) serves them all with no
adapter; everything it adds to that result is the forgetting of a hypothesis.

**This is not a proof of Stacks 03MB and carries no `@[stacks]` attribute.**  `h03DX` is one
implication of Descent, Proposition 03DX(2), and a hypothesis-carrying form must not be
presented as the tag.  It is not an obstruction: `h03DX` is proved, in exactly this spelling, by
`AlgebraicGeometry.Space.SmallEtale.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`
(`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentImpliesCartesian.lean:233`).  See the module
documentation for why it is not discharged in this file. -/
noncomputable def closedSubspaceIdealOrderIso_of_h03DX (X : AlgebraicSpaces B S hS)
    (h03DX : ∀ G : Modules.{u, u} B S hS X.1 X.2,
      G.IsQuasicoherentOnSite → IsCartesianOnAffineCharts G) :
    {e : ClosedSubspaces B S hS X.1 ≃o (QuasicoherentIdeals B S hS X)ᵒᵈ //
      ∀ (Z : ClosedSubspaces B S hS X.1) (U : (SmallEtale B S hS X.1)ᵒᵖ),
        (OrderDual.ofDual (e Z)).1.obj U =
          RingHom.ker (((smallEtaleRingedToposHom B S hS
            (ObjectProperty.homMk Z.1.ι :
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)).fSharp.hom.app U).hom)} :=
  closedSubspaceIdealOrderIso_of_surjective_sectionsBaseChange B S hS X
    fun I hI U V hU hV f => (h03DX I.toSheafOfModules hI U V hU hV f).2

end AlgebraicGeometry.Space

end
