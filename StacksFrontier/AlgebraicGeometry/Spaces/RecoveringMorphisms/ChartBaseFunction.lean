module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartMapIdealTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Glue

/-!
# The functions pulled back from the base and the chart morphisms of a morphism of ringed topoi

Let `(g, g♯) : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)` be a morphism of the small étale ringed
topoi of two algebraic spaces over a base scheme `S`, let `V` be an affine étale chart of `Y`,
let `U` be an étale chart of `X` and let `s` be a section over `U` of `g⁻¹h_V`.  The morphism of
schemes `f_s : U ⟶ V` of `AlgebraicGeometry.Space.chartSchemeHom` is defined over every base,
but the proof of [Stacks Project, Tag 04KL] needs it as a morphism of the big fppf site of `S`,
which asks for the one equation

`f_s ≫ (V ⟶ S) = (U ⟶ S)`.

Over a terminal base it is `IsTerminal.hom_ext` (`AlgebraicGeometry.Space.OverBase.chartOverHom`).
This file reduces that equation, **for a base whose canonical morphism `S ⟶ Spec Γ(S, ⊤)` is a
monomorphism**, to a statement about `g` alone: that `g` transports the functions pulled back from
the base to themselves.

A regular function `r` on `S` pulls back along the structure morphism of each étale chart to a
global regular function on an algebraic space over `S`
(`AlgebraicGeometry.Space.baseGlobalFunction`); the compatibility with restriction is
`AlgebraicGeometry.Space.chartToBase_comp_map`, that a morphism of charts is a morphism over
`S`.  The two things proved here are:

* the chart ring map of `g` sends the function pulled back from the base to the function `g`
  transports it to, **independently of the section `s`** — because the map `h_V ⟶ 𝒪_Y` of a
  function pulled back from the base factors through the terminal sheaf, whose inverse image
  along `g` has a single section over every chart
  (`AlgebraicGeometry.Space.uniqueInverseImageTerminal`);
* when `S ⟶ Spec Γ(S, ⊤)` is a monomorphism a morphism of schemes into `S` is determined by its
  ring map on global functions (`AlgebraicGeometry.ext_of_mono_toSpecΓ`), so the displayed
  equation follows once the transported functions are the pulled back ones.

## Main definitions

* `AlgebraicGeometry.Space.baseGlobalFunction`: the global regular function on an algebraic space
  over `S` pulled back from a regular function on `S`.
* `AlgebraicGeometry.Space.baseFunctionTransport`: the function on an étale chart of `X` to which
  `g` transports a regular function on `S`.

## Main results

* `AlgebraicGeometry.ext_of_mono_toSpecΓ`: a morphism of schemes into a scheme whose canonical
  morphism to the spectrum of its global functions is a monomorphism is determined by its ring
  map on global functions.
* `AlgebraicGeometry.Space.chartRingHom_baseGlobalFunction`: the chart ring map of `g` on a
  function pulled back from the base is the transported function, for every section `s`.
* `AlgebraicGeometry.Space.chartSchemeHom_comp_chartToBase_of_baseFunctionTransport`: **when
  `S ⟶ Spec Γ(S, ⊤)` is a monomorphism the chart morphisms of `g` are morphisms over the base**
  as soon as `g` transports every function pulled back from the base to itself.
* `AlgebraicGeometry.Space.chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport`: the same
  equation in the spelling the proof of Tag 04KL consumes.

## Implementation notes

The hypothesis `baseFunctionTransport g r U = ...` holds for every `g` 2-compatible with a pair
of structure morphisms to a third algebraic space, which is what
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale` assumes of `g`
(`AlgebraicGeometry.Space.baseFunctionTransport_eq_of_twoCompatible`).  For `g` the morphism of
ringed topoi of a morphism of algebraic spaces over `S` it holds outright, the structure map of
such a morphism being pullback of functions along the vertical morphism of a diagram of étale
charts, which is a morphism over `S`
(`AlgebraicGeometry.Space.baseFunctionTransport_smallEtaleRingedToposHom`).

The hypothesis `Mono S.toSpecΓ` is **exactly** what this argument can be run under: the displayed
equation is an equality of morphisms of schemes *into* `S`, while the chart construction produces
only ring maps on global functions, and by the Γ–Spec adjunction
(`AlgebraicGeometry.Scheme.toSpecΓ_naturality`, whose `appTop` is the isomorphism
`AlgebraicGeometry.Scheme.ΓSpecIso`) a morphism of schemes into `S` is determined by its ring map
on global functions precisely when `S ⟶ Spec Γ(S, ⊤)` is a monomorphism.  An affine base satisfies
it — there `S.toSpecΓ` is an isomorphism — and so does a quasi-affine one, where it is an open
immersion (`AlgebraicGeometry.Scheme.IsQuasiAffine`), and so does any base which embeds in an
affine scheme.  A base that does not, such as `S = ℙ¹`, is out of reach of global functions
altogether: there `Γ(S, ⊤)` is the ground field and no nonconstant pulled back function exists.
For such a base the equation is a Zariski-local question on `S`, which needs the pulled back
functions over the affine opens of `S` and the matching of the two morphisms on points.

## References

* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **A morphism of schemes into `S` is determined by its ring map on global functions as soon as
`S ⟶ Spec Γ(S, ⊤)` is a monomorphism.**  This is `AlgebraicGeometry.ext_of_isAffine` with the
affineness of the target relaxed to the one property of it that proof uses; an affine target
satisfies it because `S.toSpecΓ` is then an isomorphism, and a quasi-affine one because it is
then an open immersion. -/
theorem ext_of_mono_toSpecΓ {W S : Scheme.{u}} (hmono : Mono S.toSpecΓ) {a b : W ⟶ S}
    (e : a.appTop = b.appTop) : a = b := by
  have := hmono
  rw [← cancel_mono S.toSpecΓ, Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality, e]

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] smallEtaleTopology_subcanonical

/-! ### The global functions pulled back from the base -/

/-- **The global regular function on an algebraic space over `S` pulled back from a regular
function on `S`.**  Over an étale chart `U` it is `r` pulled back along the structure morphism of
`U` to the base; the compatibility with restriction is that a morphism of étale charts is a
morphism over `S`. -/
def baseGlobalFunction (X : AlgebraicSpaces B S hS) (r : Γ(S, ⊤)) :
    (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)) ⟶ setO X :=
  ⟨{ app U := ↾fun _ ↦ (chartToBase B S hS X U.unop).appTop.hom r
     naturality U U' i := by
      ext x
      change (chartToBase B S hS X U'.unop).appTop.hom r =
        (setO X).obj.map i ((chartToBase B S hS X U.unop).appTop.hom r)
      have h := congrArg (fun k : chartScheme U'.unop ⟶ S => k.appTop.hom r)
        (chartToBase_comp_map B S hS X i.unop)
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
      exact h.symm }⟩

/-- Over an étale chart `U`, `baseGlobalFunction X r` is `r` pulled back along the structure
morphism of `U` to the base. -/
@[simp]
theorem baseGlobalFunction_app (X : AlgebraicSpaces B S hS) (r : Γ(S, ⊤))
    (U : SmallEtale B S hS X.1)
    (x : (⊤_ Sheaf (SmallEtale.topology B S hS X.1) (Type u)).obj.obj (op U)) :
    (baseGlobalFunction X r).hom.app (op U) x = (chartToBase B S hS X U).appTop.hom r :=
  rfl

/-! ### The functions a morphism of ringed topoi transports from the base -/

variable {X Y : AlgebraicSpaces B S hS}
  (g : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))

/-- **The function on an étale chart `U` of `X` to which `g` transports a regular function `r` on
the base**: the inverse image along `g` of the global function `r` determines on `Y`, followed by
the inverse-image form of the structure map of `g`, read over `U`.  The inverse image of the
terminal sheaf has a single section over `U`, so no further datum enters. -/
def baseFunctionTransport (r : Γ(S, ⊤)) (U : SmallEtale B S hS X.1) :
    (setO X).obj.obj (op U) :=
  (g.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g.fSharpSet).hom.app (op U) default

/-- **The chart ring map of `g` on a function pulled back from the base is the function `g`
transports it to**, for every section `s` of `g⁻¹h_V` over `U`: the map `h_V ⟶ 𝒪_Y` of such a
function factors through the terminal sheaf, and the inverse image of the terminal sheaf has a
single section over `U`, so `s` does not enter. -/
theorem chartRingHom_baseGlobalFunction (V : SmallEtale B S hS Y.1)
    (U : SmallEtale B S hS X.1) (s : (invRep g V).obj.obj (op U)) (r : Γ(S, ⊤))
    (x : (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u)).obj.obj (op V)) :
    (chartRingHom g V U s).hom ((baseGlobalFunction Y r).hom.app (op V) x) =
      baseFunctionTransport g r U := by
  rw [chartRingHom_apply]
  have h : invCoord g V ((baseGlobalFunction Y r).hom.app (op V) x) =
      g.toToposHom.inverseImage.map ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x) ≫
        (g.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g.fSharpSet) := by
    rw [invCoord, ← GrothendieckTopology.yonedaEquiv_symm_naturality_right,
      Functor.map_comp, Category.assoc]
  rw [h]
  show (g.toToposHom.inverseImage.map (baseGlobalFunction Y r) ≫ g.fSharpSet).hom.app (op U)
      ((g.toToposHom.inverseImage.map
        ((SmallEtale.topology B S hS Y.1).yonedaEquiv.symm x)).hom.app (op U) s) =
    baseFunctionTransport g r U
  exact congrArg _ (Subsingleton.elim (α := (g.toToposHom.inverseImage.obj
    (⊤_ Sheaf (SmallEtale.topology B S hS Y.1) (Type u))).obj.obj (op U)) _ _)

/-! ### The chart morphisms over the base -/

/-- **When `S ⟶ Spec Γ(S, ⊤)` is a monomorphism the chart morphisms of `g` are morphisms over the
base** as soon as `g` transports every function pulled back from the base to itself; neither the
chart `V` nor the section `s` occurs in that hypothesis.

The hypothesis on the base holds for an affine base scheme and for a quasi-affine one. -/
theorem chartSchemeHom_comp_chartToBase_of_baseFunctionTransport (hSmono : Mono S.toSpecΓ)
    (htr : ∀ (r : Γ(S, ⊤)) (U : SmallEtale B S hS X.1),
      baseFunctionTransport g r U = (chartToBase B S hS X U).appTop.hom r)
    (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    chartSchemeHom g V U s ≫ chartToBase B S hS Y V = chartToBase B S hS X U := by
  refine ext_of_mono_toSpecΓ hSmono ?_
  rw [Scheme.Hom.comp_appTop, chartSchemeHom_appTop]
  ext r
  have h := chartRingHom_baseGlobalFunction g V U s r
    ((SmallEtale.topology B S hS Y.1).yonedaEquiv
      (terminal.from ((SmallEtale.topology B S hS Y.1).yoneda.obj V)))
  rwa [baseGlobalFunction_app, htr r U] at h

/-- `AlgebraicGeometry.Space.chartSchemeHom_comp_chartToBase_of_baseFunctionTransport` with the
structure morphisms of the charts to `S` written through the inclusion of the big fppf site. -/
theorem chartSchemeHom_comp_inclusion_map_of_baseFunctionTransport (hSmono : Mono S.toSpecΓ)
    (htr : ∀ (r : Γ(S, ⊤)) (U : SmallEtale B S hS X.1),
      baseFunctionTransport g r U = (chartToBase B S hS X U).appTop.hom r)
    (V : SmallEtale B S hS Y.1) [IsAffine (chartSch V)] (U : SmallEtale B S hS X.1)
    (s : (invRep g V).obj.obj (op U)) :
    chartSchemeHom g V U s ≫ B.inclusion.map V.obj.left.hom =
      B.inclusion.map U.obj.left.hom := by
  have h := chartSchemeHom_comp_chartToBase_of_baseFunctionTransport g hSmono htr V U s
  rwa [chartToBase_eq, chartToBase_eq] at h

end Space

end AlgebraicGeometry

end
