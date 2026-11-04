module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.TwoTermExtZero
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentHomologyZeroDifferentials
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentHomologyZero
public import StacksFrontier.Homology.DerivedCategory.LocallySmall
import StacksCore.Tactic.StacksAttribute

/-!
# `Ext⁰` out of the naive cotangent complex of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes and let `𝒢` be a sheaf of `𝒪_X`-modules. The naive
cotangent complex `NL_{X/Y}` of [Stacks Project, Tag 0D0H] is the two-term complex
`I/I² ⟶ 𝒪_X ⊗ Ω` in cohomological degrees `-1` and `0`, so it lives in degrees `≤ 0` and

`Ext⁰_{𝒪_X}(NL_{X/Y}, 𝒢) = Hom_{𝒪_X}(H⁰(NL_{X/Y}), 𝒢) = Hom_{𝒪_X}(Ω_{X/Y}, 𝒢)`,

the second equality being [Stacks Project, Tag 0D0J]
(`AlgebraicGeometry.Scheme.naiveCotangentComplexHomologyZeroIso`). The groups
`Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢)` vanish for `i < 0`.

This is the `Ext⁰` term of the infinitesimal-automorphism clause of [Stacks Project, Tag 0DY9],
which writes `Inf(𝓓_X)` first as `Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` and then as
`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`. The passage between those two spellings is what this file supplies,
at scheme level and for an arbitrary sheaf of coefficients.

## Main definitions

* `AlgebraicGeometry.RingedSpace.siteModules`: the sheaves of `𝒪_X`-modules on the open-cover
  site of a ringed space, in the spelling the naive cotangent complex is stated over.
* `AlgebraicGeometry.RingedSpace.naiveCotangentConormalShortComplex`: the conormal sequence of
  the canonical presentation, whose left-hand map is the only differential of `NL_{X/Y}`.
* `AlgebraicGeometry.RingedSpace.naiveCotangentObj`: `NL_{X/Y}` as an object of the derived
  category of sheaves of `𝒪_X`-modules.
* `AlgebraicGeometry.Scheme.naiveCotangentExt`: `Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢)`.
* `AlgebraicGeometry.Scheme.naiveCotangentExtZeroAddEquiv`: **the identification
  `Ext⁰_{𝒪_X}(NL_{X/Y}, 𝒢) = Hom_{𝒪_X}(Ω_{X/Y}, 𝒢)`.**

## Main results

* `AlgebraicGeometry.RingedSpace.naiveCotangentComplex_eq_twoTermComplex`: `NL_{X/Y}` is the
  two-term complex of the conormal map of the canonical presentation.
* `AlgebraicGeometry.RingedSpace.naiveCotangentComplexHomologyZeroIsoCokernel`: `H⁰(NL)` is the
  cokernel of the conormal map.
* `AlgebraicGeometry.RingedSpace.naiveCotangentCokernelIsoDifferentials`: that cokernel is
  `Ω_{X/Y}`.
* `AlgebraicGeometry.Scheme.naiveCotangentExt_eq_zero_of_neg`:
  `Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢) = 0` for `i < 0`.

## Implementation notes

Everything is the general statement about a complex concentrated in degrees `-1` and `0` of
`StacksFrontier/Algebra/Homology/DerivedCategory/TwoTermExtZero.lean`, read at the conormal map of
the canonical presentation. `AlgebraicGeometry.RingedSpace.naiveCotangentComplex` is by
construction `HomologicalComplex.double` of that conormal map, so the complex and
`StacksDraft.TwoTermExt.twoTermComplex` of the map are *equal* — the proof is `rfl`, the two
proofs of `(ComplexShape.up ℤ).Rel (-1) 0` involved being proofs of one proposition. Hence the
`Ext⁰` identification with the `Hom` out of the cokernel needs no transport.

The cokernel of the conormal map is `Ω_{X/Y}` by composing the two halves of the degree `0`
statement in opposite directions: `H⁰(NL)` is that cokernel because the complex is a
`HomologicalComplex.double` with nothing in degree `1`, and it is `Ω_{X/Y}` because the conormal
sequence is exact at its middle term, which is
`AlgebraicGeometry.RingedSpace.naiveCotangentComplexHomologyZeroIso`.

### Where each statement is made

The complex, the conormal sequence and the two isomorphisms are stated for a morphism of *ringed
spaces*; the scheme-level `Ext` is their instance along `f.toLRSHom.toShHom`, which is how
`AlgebraicGeometry.Scheme.naiveCotangentComplex` itself is defined, so the two are the same term
and the delegation below is a bare term with nothing transported. Written directly for a
morphism of schemes the conormal sequence carries `X.toRingedSpace.carrier` inside the
Grothendieck topology and inside two sheaf arguments, and elaborating it exhausts the heartbeat
budget at `whnf` — the sequence is a reducible `abbrev` produced by a tactic block, so
unification unfolds it. At ringed-space level, where the carrier is a projection rather than a
coercion, the same term elaborates at once. This is the hoisting of a costly region into its own
declaration, not a weakening.

The category of coefficients is `AlgebraicGeometry.RingedSpace.siteModules`, which spells the
structure sheaf as `Stacks.SheafOfModules.Tensor.ringSheaf` of the sheaf of
the ringed space. That is the spelling `AlgebraicGeometry.RingedSpace.naiveCotangentComplex`
already carries, and it is `structureSheafRing` and `AlgebraicGeometry.Scheme.Modules` by `rfl`;
the reason to write it out is that `structureSheafRing` is only `instance_reducible` and
`AlgebraicGeometry.Scheme.Modules` is a `def`, so instance search finds neither the additive
structure on the hom groups nor the derived category through them. Written as the site spelling,
the derived category is not a hypothesis: the opens of a ringed space form a small category, so
`SheafOfModules.hasDerivedCategory` applies and fixes the model. That differs from the
site-level `Ext⁰` file, which takes `HasDerivedCategory` as a hypothesis because its site is
arbitrary.

For the same reason `Ω_{X/Y}` appears here in two spellings, which are the same term.
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentials` is stated over
`AlgebraicGeometry.SheafOfModules.underlyingRingSheaf` of the sheaf of the ringed space, read
through `TopCat.Sheaf`, while `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite` is
stated over `Stacks.SheafOfModules.Tensor.ringSheaf` of it; both are the corepresenting object
of the functor of relative derivations, and that they are equal is
`AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite_eq_moduleOfDifferentials`, which
holds by `rfl`. The `Ext⁰` identification states its hom group at the second spelling. The
cokernel isomorphism can use either, because an isomorphism needs only `Category`, which is
found through both; but `Add` on a hom group comes from `Preadditive.homGroup`, whose two object
arguments have to be typed at the category instance search has already fixed from the `Quiver`
instance, and at the `underlyingRingSheaf` spelling that check runs at `.instances` transparency
and fails. So `AlgebraicGeometry.RingedSpace.naiveCotangentCokernelIsoDifferentials` keeps the
`moduleOfDifferentials` spelling, which is the one its consumer
`AlgebraicGeometry.RingedSpaceThickening.cokernelConormalMapIsoDifferentials` states, and the
`Ext⁰` identification names the site spelling by supplying `Q` to
`StacksDraft.TwoTermExt.precompAddEquiv` explicitly.

## References

* [Stacks Project, Tag 0D0H](https://stacks.math.columbia.edu/tag/0D0H), the naive cotangent
  complex of a morphism of schemes
* [Stacks Project, Tag 0D0J](https://stacks.math.columbia.edu/tag/0D0J), `H⁰(NL) = Ω`
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
* [Stacks Project, Tag 0DY9](https://stacks.math.columbia.edu/tag/0DY9)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS), `Ext` between complexes
  with disjoint homology ranges
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
attribute [local instance] SheafOfModules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The sheaves of `𝒪_X`-modules on the open-cover site of a ringed space, with the structure
sheaf spelled as `Stacks.SheafOfModules.Tensor.ringSheaf` — the spelling
`AlgebraicGeometry.RingedSpace.naiveCotangentComplex` is stated over. -/
abbrev siteModules (X : RingedSpace.{u, u}) :=
  _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)

/-- The conormal sequence of the canonical polynomial presentation of `f^{-1}𝒪_Y ⟶ 𝒪_X`. Its
left-hand map is the only differential of `NL_{X/Y}`, and its cokernel is `Ω_{X/Y}`. -/
abbrev naiveCotangentConormalShortComplex {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :=
  Stacks.SheafOfModules.canonicalConormalSequence.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)

/-- **The naive cotangent complex is the two-term complex of the conormal map.** Both are
`HomologicalComplex.double` of that map; the two proofs of `(ComplexShape.up ℤ).Rel (-1) 0`
involved are proofs of one proposition. -/
theorem naiveCotangentComplex_eq_twoTermComplex {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    AlgebraicGeometry.RingedSpace.naiveCotangentComplex f
      = StacksDraft.TwoTermExt.twoTermComplex (naiveCotangentConormalShortComplex f).f :=
  rfl

/-- **The degree `0` cohomology sheaf of `NL_{X/Y}` is the cokernel of the conormal map**: the
complex is a `HomologicalComplex.double`, which has nothing in degree `1`. -/
def naiveCotangentComplexHomologyZeroIsoCokernel {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    (AlgebraicGeometry.RingedSpace.naiveCotangentComplex f).homology 0
      ≅ cokernel (naiveCotangentConormalShortComplex f).f :=
  Stacks.SheafOfModules.naiveCotangentComplexHomologyZeroIsoCokernel.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier)
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
    (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)

/-- **The cokernel of the conormal map is the sheaf of relative differentials**: it is
`H⁰(NL_{X/Y})`, which is `Ω_{X/Y}` by the degree `0` half of [Stacks Project, Tag 08TY]. -/
def naiveCotangentCokernelIsoDifferentials {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    cokernel (naiveCotangentConormalShortComplex f).f
      ≅ AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u}
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) :=
  (naiveCotangentComplexHomologyZeroIsoCokernel f).symm ≪≫
    AlgebraicGeometry.RingedSpace.naiveCotangentComplexHomologyZeroIso f

/-- `NL_{X/Y}` as an object of the derived category of sheaves of `𝒪_X`-modules. -/
abbrev naiveCotangentObj {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    DerivedCategory (siteModules X) :=
  DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.naiveCotangentComplex f)

/-- `Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢)` for a morphism of ringed spaces. -/
abbrev naiveCotangentExt {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (G : siteModules X) (i : ℤ) :
    Type _ :=
  DerivedCategory.Ext (naiveCotangentObj f) ((DerivedCategory.singleFunctor _ 0).obj G) i

/-- The identification of `Ext⁰_{𝒪_X}(NL_{X/Y}, 𝒢)` with the homomorphisms out of the cokernel
of the conormal map, by taking `H⁰`. -/
def naiveCotangentExtZeroAddEquivCokernel {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : siteModules X) :
    naiveCotangentExt f G 0 ≃+ (cokernel (naiveCotangentConormalShortComplex f).f ⟶ G) :=
  StacksDraft.TwoTermExt.twoTermExtZeroAddEquiv (naiveCotangentConormalShortComplex f).f G

/-- **`Ext⁰_{𝒪_X}(NL_{X/Y}, 𝒢) = Hom_{𝒪_X}(Ω_{X/Y}, 𝒢)` for a morphism of ringed spaces.** -/
def naiveCotangentExtZeroAddEquiv {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (G : siteModules X) :
    naiveCotangentExt f G 0 ≃+
      (AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u, u, u}
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f) ⟶ G) :=
  (naiveCotangentExtZeroAddEquivCokernel f G).trans
    (StacksDraft.TwoTermExt.precompAddEquiv
      (Q := AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite.{u, u, u, u}
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
        (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f))
      (naiveCotangentCokernelIsoDifferentials f) G).symm

/-- **`Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢)` vanishes in negative degrees**, the naive cotangent complex
living in cohomological degrees `≤ 0`. -/
theorem naiveCotangentExt_eq_zero_of_neg {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (G : siteModules X) {i : ℤ} (hi : i < 0) (ξ : naiveCotangentExt f G i) : ξ = 0 :=
  StacksDraft.TwoTermExt.twoTermExt_eq_zero_of_neg
    (naiveCotangentConormalShortComplex f).f G hi ξ

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry.Scheme

/-- `Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢)`, the `Ext` groups out of the naive cotangent complex of a
morphism of schemes: those of the underlying morphism of ringed spaces, the two naive cotangent
complexes being the same term. -/
abbrev naiveCotangentExt {X Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules) (i : ℤ) : Type _ :=
  RingedSpace.naiveCotangentExt f.toLRSHom.toShHom G i

/-- **`Ext⁰_{𝒪_X}(NL_{X/Y}, 𝒢) = Hom_{𝒪_X}(Ω_{X/Y}, 𝒢)`.** The naive cotangent complex of a
morphism of schemes lives in cohomological degrees `≤ 0`, so `Ext⁰` out of it is the group of
homomorphisms out of its degree `0` cohomology sheaf, and that sheaf is the sheaf of relative
differentials by [Stacks Project, Tag 0D0J].

This is the `Ext⁰` term of the infinitesimal-automorphism clause of
[Stacks Project, Tag 0DY9]: the source writes that clause's group first as
`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X)` and then as `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`, and this is the passage
between the two. `f` is an arbitrary morphism of schemes and `𝒢` an arbitrary sheaf of
`𝒪_X`-modules. -/
@[stacks 0D0J "the Ext^0 reading of the degree-zero identification: Ext^0(NL_{X/Y}, G) = \
Hom(Omega_{X/Y}, G) for a morphism of schemes and an arbitrary sheaf of coefficients, the naive \
cotangent complex living in cohomological degrees at most zero",
  sga "7 VI 4.16" "identification Ext⁰(X₀"]
def naiveCotangentExtZeroAddEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules) :
    naiveCotangentExt f G 0 ≃+ (Hom.relativeDifferentials f ⟶ G) :=
  RingedSpace.naiveCotangentExtZeroAddEquiv f.toLRSHom.toShHom G

/-- **`Ext^i_{𝒪_X}(NL_{X/Y}, 𝒢)` vanishes in negative degrees** for a morphism of schemes. -/
theorem naiveCotangentExt_eq_zero_of_neg {X Y : Scheme.{u}} (f : X ⟶ Y) (G : X.Modules)
    {i : ℤ} (hi : i < 0) (ξ : naiveCotangentExt f G i) : ξ = 0 :=
  RingedSpace.naiveCotangentExt_eq_zero_of_neg f.toLRSHom.toShHom G hi ξ

end AlgebraicGeometry.Scheme

end
