module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartwiseIsomorphismDetection
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# A terminal affine chart detects isomorphisms of quasi-coherent modules

Let `Y` be an algebraic space over a scheme `S` which has a **terminal affine étale chart** `V₀`
— as an affine algebraic space does, by
`AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart`.  Then a morphism of *quasi-coherent*
`𝒪_Y`-modules which is bijective on the sections over `V₀` alone is an isomorphism.

This is the affine identification that a statement about modules needs before it says anything
about sheaves, in the only form in which a statement over an affine base can supply it: `V₀` is
one object of the small étale site, and nothing is assumed about the sections over any other
chart.

## Main results

* `AlgebraicGeometry.Space.bijective_val_app_of_bijective_val_app_isTerminal`: bijectivity on the
  sections over a terminal affine chart propagates to every affine chart.
* `AlgebraicGeometry.Space.isIso_of_bijective_val_app_isTerminal`: **a morphism of quasi-coherent
  `𝒪_Y`-modules which is bijective on the sections over a terminal affine chart is invertible.**
* `AlgebraicGeometry.Space.isIso_of_bijective_val_app_isIso_chart`: the same with the terminal
  chart presented as a chart whose structure morphism is an isomorphism, which is the shape in
  which an affine base enters this development.

## Implementation notes

*Why this is not the equivalence of Descent, Proposition 03DX (2), and must not be.*  The
natural thing to want is the affine identification as an equivalence of categories with global
sections as its inverse, so that invertibility of the module map transports back to the sheaf
map along an equivalence.  At the seating where it would be used that equivalence **does not
exist**: `AlgebraicGeometry.Space.globalSectionRingSmallEtale` is a subring of a product indexed
by the objects of the small étale site and so lies in `Type (u + 1)`, whereas
`AlgebraicGeometry.Space.QuasicoherentSheaves.{u, u}` has Hom-sets in bijection with those of
`ModuleCat.{u}` over a ring in `Type u`, and
`ModuleCat.not_nonempty_equivalence_of_category_succ`
(`StacksFrontier/Algebra/Category/ModuleCat/NoUniverseEquivalence.lean`) rules out an equivalence
between the two by a cardinality argument in a single Hom-set;
`AlgebraicGeometry.Space.not_nonempty_equivalence_moduleCat_quasicoherentSheaves_yoneda` is that
conclusion for a representable affine algebraic space.  So the two `08H0` statements of
`StacksFrontier/AlgebraicGeometry/Spaces/AffineCoheratorGlobalSections.lean` are vacuous at the
module universe `u`, and no amount of transport produces the functor they describe.

What a consumer actually needs of the affine identification is weaker than an equivalence and is
*reflection of isomorphisms*, which is what is proved here.  It does not go through
`AlgebraicGeometry.Space.affineRepresentedQuasicoherentModulesEquivalence` either — that
equivalence is at module universe `u` over `Γ(T, ⊤)` in `Type u`, so composing it with sections
on the small étale site would reintroduce the universe crossing just ruled out.  The route taken
instead is the forward implication of **Descent, Proposition 03DX (2)** itself, which this
development has unconditionally and at any universe of module sections:
`AlgebraicGeometry.Space.bijective_sectionsBaseChange_of_isQuasicoherentOnSite`.  A quasi-coherent
module is cartesian on affine charts, so for every affine chart `V` the sections over `V` are the
base change of the sections over `V₀` along `𝒪_Y(V₀) ⟶ 𝒪_Y(V)` — the terminal chart being the
target of a unique chart morphism out of `V` — and
`AlgebraicGeometry.Space.app_sectionsBaseChange` says the morphism's component over `V` is the
base change of its component over `V₀` read through those two comparisons.  Tensoring a bijective
linear map with a fixed module keeps it bijective
(`AlgebraicGeometry.Space.bijective_lTensor_of_bijective`), so bijectivity over `V₀` gives
bijectivity over every affine chart, and the affine charts detect isomorphisms
(`AlgebraicGeometry.Space.isIso_of_forall_bijective_val_app_affine_chart`).

*The affine charts, not all charts.*  An étale scheme over an affine scheme need not be affine, so
the quantification over affine charts is essential and the all-charts statement
`AlgebraicGeometry.Space.isIso_of_forall_isIso_etaleModulePullback_chartToSpace` could not be used:
the base change comparison of 03DX (2) is bijective only between affine charts.  Sections over the
non-affine charts are reached by the sheaf condition inside
`Stacks.SheafOfModules.isIso_of_hasEnoughObjects_bijective_val_app`, whose geometric input is
`AlgebraicGeometry.Space.hasEnoughObjects_isAffineChart`.

*No Stacks tag is carried.*  Neither statement below is a clause of a tag.  The forward
implication of 03DX (2) that they consume is registered on
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_of_isQuasicoherentOnSite`, and the detection of
an isomorphism on a covering family is not itself a tagged result.  In particular nothing here
asserts any clause of **Stacks 073K**, whose part (2) is carried by
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Bijectivity on the sections over a terminal affine chart propagates to every affine
chart**, for a morphism of quasi-coherent `𝒪_Y`-modules.

The unique chart morphism `V ⟶ V₀` out of the affine chart `V` into the terminal one has both
ends affine, so the base change comparison of **Descent, Proposition 03DX (2)** is bijective at
both modules, and `AlgebraicGeometry.Space.app_sectionsBaseChange` identifies the component over
`V` with the base change of the component over `V₀` through them. -/
theorem bijective_val_app_of_bijective_val_app_isTerminal (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (hV₀aff : IsAffineChart B S hS Y.1 V₀)
    (V : SmallEtale B S hS Y.1) (hV : IsAffineChart B S hS Y.1 V)
    (h : Function.Bijective (φ.val.app (op V₀)).hom) :
    Function.Bijective (φ.val.app (op V)).hom := by
  set f : V ⟶ V₀ := hV₀.from V
  let _ := chartAlgebra (hF := Y.2) f
  have hMbc : Function.Bijective (sectionsBaseChange M f) :=
    bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS Y.1 Y.2 M hM hV₀aff hV f
  have hNbc : Function.Bijective (sectionsBaseChange N f) :=
    bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS Y.1 Y.2 N hN hV₀aff hV f
  have ht : Function.Bijective
      (LinearMap.lTensor (chartRing B S hS Y.1 Y.2 V) (φ.val.app (op V₀)).hom) :=
    bijective_lTensor_of_bijective _ _ h
  have hcomp : Function.Bijective
      (fun z => (φ.val.app (op V)).hom (sectionsBaseChange M f z)) := by
    have hfun : (fun z => (φ.val.app (op V)).hom (sectionsBaseChange M f z)) =
        fun z => sectionsBaseChange N f
          (LinearMap.lTensor (chartRing B S hS Y.1 Y.2 V) (φ.val.app (op V₀)).hom z) :=
      funext (app_sectionsBaseChange φ f)
    rw [hfun]
    exact hNbc.comp ht
  exact ⟨hcomp.1.of_comp_right hMbc.2, hcomp.2.of_comp⟩

/-- **A morphism of quasi-coherent `𝒪_Y`-modules which is bijective on the sections over a
terminal affine chart is an isomorphism.**

This is the affine identification in the form a reduction to an affine base can use: `V₀` is a
single object of the small étale site of `Y`, and nothing is assumed about the sections over any
other chart.  Over an affine algebraic space such a chart exists —
`AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart` — and
`AlgebraicGeometry.Space.isIso_of_bijective_val_app_isIso_chart` is the form in which this
development presents one.

It is **not** an equivalence of categories and cannot be made into one at this seating; see the
implementation notes. -/
theorem isIso_of_bijective_val_app_isTerminal (Y : AlgebraicSpaces B S hS)
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N) {V₀ : SmallEtale B S hS Y.1}
    (hV₀ : IsTerminal V₀) (hV₀aff : IsAffineChart B S hS Y.1 V₀)
    (h : Function.Bijective (φ.val.app (op V₀)).hom) :
    IsIso φ :=
  isIso_of_forall_bijective_val_app_affine_chart B S hS Y φ fun V hV =>
    bijective_val_app_of_bijective_val_app_isTerminal B S hS Y hM hN φ hV₀ hV₀aff V hV h

/-- **A morphism of quasi-coherent `𝒪_Y`-modules which is bijective on the sections over an
affine chart whose structure morphism is an isomorphism is an isomorphism.**

This is `AlgebraicGeometry.Space.isIso_of_bijective_val_app_isTerminal` with terminality supplied
by `AlgebraicGeometry.Space.isTerminal_of_isIso_chart`, so its hypotheses on the chart are the
ones under which this development states an affine base:  `[IsIso V₀.obj.hom]` and
`[IsAffine (chartScheme V₀)]`, exactly the pair carried by
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`. -/
theorem isIso_of_bijective_val_app_isIso_chart (Y : AlgebraicSpaces B S hS)
    (V₀ : SmallEtale B S hS Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    {M N : Modules.{u, u} B S hS Y.1 Y.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (h : Function.Bijective (φ.val.app (op V₀)).hom) :
    IsIso φ :=
  isIso_of_bijective_val_app_isTerminal B S hS Y hM hN φ
    (isTerminal_of_isIso_chart B S hS Y V₀) ‹IsAffine (chartScheme V₀)› h

end AlgebraicGeometry.Space

end
