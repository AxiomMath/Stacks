module

public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangePushforwardTensorIso
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyTensorBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatBaseChangePushforwardCollapse
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactQuasiSeparatedOverAffine
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 073K, part (2), over `A`: `H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')`

For the cartesian square of **Stacks 073J**

```
X' --g'--> X
 |         |
 f'        f
 v         v
Y' --g-->  Y
```

with `𝓕` a quasi-coherent `𝒪_X`-module and `𝓕' = (g')^*𝓕`, **Stacks 073K, part (2)** says that
if `g` is flat, `f` is quasi-compact and quasi-separated and the two bases are affine,
`Y = Spec(A)` and `Y' = Spec(B)`, then

`H^i(X, 𝓕) ⊗_A B = H^i(X', 𝓕')`

in every degree `i ≥ 0`.  This file assembles that isomorphism out of the three steps the
source's proof runs through, each of which is already available:

1. the identification `g'_*𝓕' = 𝓕 ⊗_{\underline{A}} \underline{B}` of
   `AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorChartIso`;
2. the collapse `H^i(X', 𝓕') = H^i(X, g'_*𝓕')` of
   `AlgebraicGeometry.Space.BaseChangeDiagram.cohomologyPushforwardIso`, which is the vanishing
   of the higher direct images along the affine morphism `g'` (**Stacks 073H**) fed to the Leray
   spectral sequence (**Stacks 0733**);
3. the dévissage along Lazard's theorem (**Stacks 058G**)
   `AlgebraicGeometry.Space.isIso_cohomologyTensorComparison_app_of_flat`, which turns
   `H^i(X, 𝓕 ⊗_A B)` into `H^i(X, 𝓕) ⊗_A B` because `B` is a flat `A`-module.

`Y = Spec(A)` is carried as it is elsewhere in this development: a chart `V₀` of the small étale
site of `Y` whose structure morphism is an isomorphism and whose scheme is affine, with
`A = Γ(chartScheme V₀, ⊤) = Γ(Y, 𝒪_Y)` its coordinate ring — the coordinate ring of an affine
algebraic space *is* its ring of global regular functions.  See the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/CohomologyFlatBaseChange.lean`.

## Main definitions

* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyOverBaseChart` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyTargetOverBaseChart`: the two sides
  `H^i(X, 𝓕)` and `H^i(X', 𝓕')` of part (2), read as modules over the coordinate ring `A` of the
  base — the second one through `f'` and then `g`, that is by restricting its `B`-module
  structure along `A ⟶ B`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIso`: the **`A`-linear
  half** of Stacks 073K, part (2) — the isomorphism `H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')` of
  `A`-modules, under exactly the source's hypotheses.  It carries **no** `@[stacks 073K]`
  attribute: the source asserts an identification of `B`-modules, and restricting both actions
  to `A` is strictly weaker.  The `B`-linear form that closed that gap is
  `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeBLinear.lean`), and the
  canonical form is
  `AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
  (`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`);
  this declaration's docstring records both.

## Main results

* `AlgebraicGeometry.Space.isTerminal_of_isIso_chart` and
  `AlgebraicGeometry.Space.isAffineSpace_of_isIso_chart`: a chart whose structure morphism is an
  isomorphism is a terminal object of the small étale site, and presents the space as the scheme
  of the chart; so an affine such chart is exactly the datum `Y = Spec(A)`.
* `AlgebraicGeometry.Space.BaseChangeDiagram.flat_appTop_baseChartHom` and
  `AlgebraicGeometry.Space.BaseChangeDiagram.flat_baseModule`: **`B` is a flat `A`-module**,
  because `g` is flat.  This is where the flatness hypothesis of Stacks 073K is consumed.

## Implementation notes

*Where each hypothesis of the source goes.*  Flatness of `g` is used twice: once through
flatness of `A ⟶ B` for the dévissage, and once through flatness of `g'` for the collapse.
Quasi-compactness and quasi-separatedness of `f` are used only through the two finiteness
properties of `X` that **Stacks 073E** asks for, and those are *derived* here rather than
assumed: an affine algebraic space is quasi-compact and quasi-separated, so
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace` and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace` turn
them into quasi-compactness and absolute quasi-separatedness of `X`.  Representability of `g'`
is likewise derived, from affineness of the two bases, by
`AlgebraicGeometry.Space.BaseChangeDiagram.relativelyRepresentable_g'`.  Affineness of `Y` and
`Y'` is derived from the affine charts.  Nothing beyond the source's hypotheses is carried;
`hZ : B.Contains (⊤_ Scheme)` is a closure condition on the ambient big fppf site, not a
hypothesis on the geometry, and is what lets absolute quasi-separatedness be spoken of at all.

*Flatness of `A ⟶ B`.*  The ring map is `Γ` of the morphism of schemes
`AlgebraicGeometry.Space.baseChartHom` of the two charts, which lies over `g`; so it is one of
the commuting squares of étale charts that the definition of flatness of a morphism of
algebraic spaces (**Stacks 03ML**) quantifies over, and flatness of the scheme morphism gives
flatness of the ring map because both schemes are affine
(`AlgebraicGeometry.Scheme.Hom.flat_appTop`).

*The two direct images.*  The identification of step 1 is stated for the base-change direct
image `AlgebraicGeometry.Space.smallBaseChangeModulePushforward` and the collapse of step 2 for
the direct image `AlgebraicGeometry.Space.modulePushforward` of **Stacks 03LU**; the two are
identified for a representable morphism by
`AlgebraicGeometry.Space.modulePushforwardChartIso`, which is the bridge between the two steps.

*What the isomorphism is linear over.*  Both sides are modules over the coordinate ring `A` of
`Y`, and the isomorphism below is `A`-linear.  The `B`-module structures of the two sides — the
one the source's `⊗_A B` carries and the one `H^i(X', 𝓕')` carries through `f'` — are not
compared here: the dévissage of step 3 produces an `A`-linear natural transformation of functors
on `A`-modules, and `B`-linearity of its component at `B` would need the `B`-action on
`H^i(X, 𝓕 ⊗_A B)` to be identified with the geometric one across steps 1 and 2.

## References

* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 073J](https://stacks.math.columbia.edu/tag/073J)
* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 058G](https://stacks.math.columbia.edu/tag/058G)
* [Stacks Project, Tag 03ML](https://stacks.math.columbia.edu/tag/03ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules
open Stacks.FlatDevissage

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] AlgebraicGeometry.RingedSite.globalSectionsCommRing

noncomputable section

universe v w u

namespace Stacks.FlatDevissage

variable {A : Type u} [CommRing A]

/-- **Tensoring on the left is functorial in the left factor**, at a fixed second factor: an
isomorphism `P ≅ P'` of `A`-modules gives `P ⊗_A M ≅ P' ⊗_A M`. -/
def tensorLeftObjIso {P P' : ModuleCat.{w} A} (e : P ≅ P') (M : ModuleCat.{v} A) :
    (tensorLeftFunctor.{u, w, v} P).obj M ≅ (tensorLeftFunctor.{u, w, v} P').obj M :=
  (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl A M)).toModuleIso

end Stacks.FlatDevissage

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A chart whose structure morphism is an isomorphism is a terminal object of the small étale
site.**  It is `AlgebraicGeometry.Space.etaleChartOfIso` of the inverse isomorphism, so
`AlgebraicGeometry.Space.isTerminalEtaleChartOfIso` applies to it. -/
def isTerminal_of_isIso_chart (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1)
    [IsIso V.obj.hom] : IsTerminal V :=
  isTerminalEtaleChartOfIso B S hS (asIso V.obj.hom).symm

/-- **A space with an affine chart whose structure morphism is an isomorphism is an affine
algebraic space.**  This is the datum `Y = Spec(A)`: the chart exhibits `Y` as the scheme of the
chart, and that scheme is affine. -/
theorem isAffineSpace_of_isIso_chart (X : AlgebraicSpaces B S hS) (V : SmallEtale B S hS X.1)
    [IsIso V.obj.hom] [IsAffine (chartScheme V)] : IsAffineSpace B S hS X.1 :=
  ⟨(SmallEtale.toOver B S hS X.1).obj V, ‹IsAffine (chartScheme V)›, ⟨(asIso V.obj.hom).symm⟩⟩

variable {B S hS}

namespace BaseChangeDiagram

variable (D : BaseChangeDiagram B S hS)

/-! ### `B` is flat over `A` -/

/-- **The ring map `A ⟶ B` is flat**, for `g` flat and the two bases affine.

The map is `Γ` of the morphism of schemes `AlgebraicGeometry.Space.baseChartHom` of the two
charts, which lies over `g` by
`AlgebraicGeometry.Space.yoneda_map_baseChartHom_comp`; so the two charts and that morphism form
one of the commuting squares of étale charts over which flatness of a morphism of algebraic
spaces (**Stacks 03ML**) is defined, and the scheme morphism is flat.  Both schemes are affine,
so `AlgebraicGeometry.Scheme.Hom.flat_appTop` turns that into flatness of the ring map. -/
theorem flat_appTop_baseChartHom (hg : IsFlat B S hS D.g.hom)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀')] :
    ((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS D.g V₀ V₀')).appTop.hom.Flat := by
  have : Flat ((BigFppfOver.toScheme B S hS).map (baseChartHom B S hS D.g V₀ V₀')) :=
    hg ((SmallEtale.toOver B S hS D.Y'.1).obj V₀') ((SmallEtale.toOver B S hS D.Y.1).obj V₀)
      V₀'.obj.hom V₀.obj.hom (baseChartHom B S hS D.g V₀ V₀') V₀'.property V₀.property
      (yoneda_map_baseChartHom_comp B S hS D.g V₀ V₀')
  exact Scheme.Hom.flat_appTop _

/-- **`B` is a flat `A`-module**, for `g` flat and the two bases affine.  This is where the
flatness hypothesis of **Stacks 073K** is consumed by the dévissage of **Stacks 058G**. -/
theorem flat_baseModule (hg : IsFlat B S hS D.g.hom)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀')] :
    Module.Flat (baseChartRing B S hS D.Y V₀) (D.baseModule V₀ V₀') :=
  D.flat_appTop_baseChartHom hg V₀ V₀'

/-! ### The two sides of part (2), over the coordinate ring of the base -/

/-- **The left hand side of Stacks 073K, part (2) before the extension of scalars**: the
cohomology `H^i(X, 𝓕)` read as a module over the coordinate ring `A` of the base. -/
abbrev affineCohomologyOverBaseChart (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    ModuleCat.{u + 1} (baseChartRing B S hS D.Y V₀) :=
  have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  (cohomologyFunctorOverBaseChart B S hS D.f
    (isTerminal_of_isIso_chart B S hS D.Y V₀) i).obj D.F

/-- **The right hand side of Stacks 073K, part (2)**: the cohomology `H^i(X', 𝓕')` read as a
module over the coordinate ring `A` of the base, through `f'` and then `g` — that is, its
`B`-module structure restricted along `A ⟶ B`. -/
abbrev affineCohomologyTargetOverBaseChart (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom]
    (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    ModuleCat.{u + 1} (baseChartRing B S hS D.Y V₀) :=
  have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  (baseChartRestrictScalars B S hS D.Y (isTerminal_of_isIso_chart B S hS D.Y V₀)).obj
    ((globalSectionsRestrictScalars B S hS D.g).obj (D.affineCohomologyTarget i))

/-! ### Part (2) -/

/-- **The `A`-linear half of Stacks 073K, part (2).**  For the cartesian square of **Stacks
073J** with `g` flat, `f` quasi-compact and quasi-separated and the two bases affine —
`Y = Spec(A)` and `Y' = Spec(B)`, presented by the charts `V₀` and `V₀'` — the cohomology of the
pulled back coefficient is the cohomology of the coefficient extended along `A ⟶ B`:

`H^i(X, 𝓕) ⊗_A B ≅ H^i(X', 𝓕')`

in every degree `i`, **as modules over `A`**.

The composite runs through the three steps of the source's proof.  Reading it from the left:
the dévissage along Lazard's theorem identifies `H^i(X, 𝓕) ⊗_A B` with `H^i(X, 𝓕 ⊗_A B)`,
because `B` is flat over `A` — that is where flatness of `g` is consumed, through
`AlgebraicGeometry.Space.BaseChangeDiagram.flat_baseModule`; the sheaf identification
`𝓕 ⊗_{\underline A} \underline B = g'_*𝓕'` turns that into `H^i(X, g'_*𝓕')`; and the collapse
of the Leray spectral sequence along the affine morphism `g'` turns *that* into `H^i(X', 𝓕')`.

**This is not yet the tag, and carries no `@[stacks 073K]` attribute.**  Part (2) of the source
asserts an identification of `B`-modules: both sides are `B`-modules — the left by the second
tensor factor, the right because `X'` lives over `Y' = Spec(B)` — and it is that identification
which makes the statement a *base change* result and which its consumers use.  What is
established here is the isomorphism after restricting both `B`-actions to `A`, which is strictly
weaker and does not determine the `B`-linear one.  The hypothesis list is already exactly the
source's; the gap is in the conclusion, not in the assumptions.

What closing it needs: the `B`-action on `H^i(X, 𝓕 ⊗_A B)` is `tensorLeftFunctor`'s action,
i.e. the map induced by multiplication by `b` on the second factor, and it must be matched with
the geometric `B`-action on `H^i(X', 𝓕')`.

**That upgrade exists**:
`AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeIsoBase`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeBLinear.lean`) is this same
isomorphism in `ModuleCat` over the coordinate ring of `Y'`, under the same hypotheses, and it
is what carries the `@[stacks 073K]` attribute for part (2).  The declaration below is that one
with both `B`-actions restricted to `A`; it is kept because it is the form the `A`-linear
consumers want, and it stays untagged.

**The canonical form of part (2) is also proved**, and it is this `A`-linear
declaration that it is proved from:
`AlgebraicGeometry.Space.BaseChangeDiagram.isIso_affineCohomologyBaseChangeMap`
(`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyBaseChangeCanonicalIsIso.lean`) says
that `AlgebraicGeometry.Space.BaseChangeDiagram.affineCohomologyBaseChangeMap`, the transpose of
the pullback map on cohomology, is invertible.  Restriction of scalars reflects isomorphisms, so
the `A`-linear form suffices for that and the comparison of two collapses that the `B`-linear
form would force is avoided.

This paragraph previously said the upgrade needed "a section-level description of the gluing
isomorphism and of `Stacks.Cohomology.SiteModules.globalSectionsRingHom` on an actual family of
sections", citing the notes of
`StacksFrontier/AlgebraicGeometry/Spaces/FlatAffineCohomologyPullback.lean` for the latter being out
of reach.  **Both halves were wrong.**  No description of `globalSectionsRingHom` on sections
enters the proof — what was needed was `AlgebraicGeometry.Space.baseChartRingHom_apply` together
with the chart-level identity
`AlgebraicGeometry.Space.BaseChangeDiagram.pushforwardTensorAppLinear_globalSmul` — and the
`FlatAffineCohomologyPullback.lean` note being cited had itself already been retracted in place
(see its own text at the "**is** available, contrary to what this passage said" correction).  The
guess also misplaced the obstruction: the hard step was neither the sheaf identification nor the
ring map but the *collapse*, whose `Stacks.RightDerivedComp.objIsoOfAcyclicImage` form carries no
naturality.  The fix was to route through `Stacks.RightDerivedComp.objIso`, available because
`g'` is flat, which does have `objIso_hom_naturality`. -/
def affineCohomologyBaseChangeIso (hZ : B.Contains (⊤_ Scheme.{u}))
    (hg : IsFlat B S hS D.g.hom) (hqc : IsQuasiCompact B S hS D.f.hom)
    (hqs : IsQuasiSeparated B S hS D.f.hom)
    (V₀ : SmallEtale B S hS D.Y.1) [IsIso V₀.obj.hom] [IsAffine (chartScheme V₀)]
    (V₀' : SmallEtale B S hS D.Y'.1) [IsIso V₀'.obj.hom] [IsAffine (chartScheme V₀')]
    (i : ℕ) :
    have := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
    have := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
    have := enoughInjectives_modules B S hS D.X.1 D.X.2
    (tensorLeftFunctor.{u, u + 1, u} (D.affineCohomologyOverBaseChart V₀ i)).obj
        (D.baseModule V₀ V₀') ≅
      D.affineCohomologyTargetOverBaseChart V₀ i := by
  have h1 := hasInjectiveResolutions_modules B S hS D.X.1 D.X.2
  have h2 := hasInjectiveResolutions_modules B S hS D.X'.1 D.X'.2
  have h3 := enoughInjectives_modules B S hS D.X.1 D.X.2
  letI hV₀ : IsTerminal V₀ := isTerminal_of_isIso_chart B S hS D.Y V₀
  have hY : IsAffineSpace B S hS D.Y.1 := isAffineSpace_of_isIso_chart B S hS D.Y V₀
  have hY' : IsAffineSpace B S hS D.Y'.1 := isAffineSpace_of_isIso_chart B S hS D.Y' V₀'
  have hg' : yoneda.relativelyRepresentable D.g'.hom := D.relativelyRepresentable_g' hY hY'
  have hXqc : IsQuasiCompactSpace B S hS D.X.1 :=
    isQuasiCompactSpace_of_isQuasiCompact_of_isAffineSpace B S hS D.f.hom hY hqc
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ D.X.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated_of_isAffineSpace B S hS hZ D.f.hom
      D.X.property hY hqs
  haveI := D.flat_baseModule hg V₀ V₀'
  haveI : IsIso ((cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).app
      (D.baseModule V₀ V₀')) :=
    isIso_cohomologyTensorComparison_app_of_flat B S hS hZ D.f hV₀ hXqc hXqs D.F i
      (D.baseModule V₀ V₀')
  exact
    tensorLeftObjIso (cohomologyTensorFunctorUnitIso B S hS D.f hV₀ D.F i).symm
        (D.baseModule V₀ V₀') ≪≫
      asIso ((cohomologyTensorComparison B S hS hZ D.f hV₀ hXqc hXqs D.F i).app
        (D.baseModule V₀ V₀')) ≪≫
      (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).mapIso
        (D.pushforwardTensorChartIso hg' V₀ V₀' hV₀) ≪≫
      (cohomologyFunctorOverBaseChart B S hS D.f hV₀ i).mapIso
        ((modulePushforwardChartIso B S hS D.g' hg').app D.pulledBack).symm ≪≫
      ((globalSectionsRestrictScalars B S hS D.f ⋙
          baseChartRestrictScalars B S hS D.Y hV₀).mapIso
        (D.cohomologyPushforwardIso hg hY hY' i)).symm ≪≫
      (baseChartRestrictScalars B S hS D.Y hV₀).mapIso
        (D.restrictScalarsSquareIso.app
          (((globalSectionsFunctor.{u + 1, u, u, u}
            (ringSheaf (smallEtaleRingedSite B S hS D.X'.1 D.X'.2).O)).rightDerived
              i).obj D.pulledBack))

end BaseChangeDiagram

end AlgebraicGeometry.Space

end

end
