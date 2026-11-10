module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivationsIntoDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# Differentials of a universal first-order thickening of algebraic spaces

Let `h : Z ⟶ X` be a formally unramified morphism of algebraic spaces over `S`, let `Z ⊂ Z'` be
a universal first-order thickening of `Z` over `X` with structure morphism `h' : Z' ⟶ X`, and
let `p : X ⟶ Y` be a morphism to a base algebraic space `Y`.  Stacks 060E asserts that the
canonical map `(h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` induces an isomorphism
`h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z`.

The map called `dh'` in the source is the comparison map `c_{h'}` of Stacks 04CX of the square
with top edge `h'`, right edge `p` and base morphism the identity of `Y`, as the proof of the
source says; in this library it is `AlgebraicGeometry.Space.sheafOfDifferentialsMap`,
characterized by `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap`.  The two modules of the
conclusion are read, as the source reads them, through the inclusion `ι : Z ⟶ Z'`: the tensor
product `Ω_{Z'/Y} ⊗ 𝒪_Z` is `ι^*Ω_{Z'/Y}` and `h^*Ω_{X/Y}` is `ι^*(h')^*Ω_{X/Y}` because
`ι ≫ h' = h`.  So the content of the tag is that `ι^*c_{h'}` is an isomorphism.

Two things are proved.  The tag itself is proved the way the source proves it — by the étale
localization of Stacks 04CU and Stacks 060D, which is carried as a hypothesis, followed by the
case of schemes, Stacks 04FB, which is applied.  Independently of that hypothesis, and with no
hypothesis at all beyond the characterization of `c_{h'}`, the tag is *reduced* to a statement
about lifting derivations: it holds exactly when every `Y`-derivation of `𝒪_X` with values in
`h_*F` extends uniquely to a `Y`-derivation of `𝒪_{Z'}` with values in `ι_*F`.  That reduction
is the shape in which the universal property of Stacks 0602 would prove the tag outright, and
the *What is not proved here* section records what it would still need.

## Main definitions

* `AlgebraicGeometry.Space.universalThickeningSubSpace` and
  `AlgebraicGeometry.Space.universalThickeningInclusion` promote the smaller space of a
  universal first-order thickening to an algebraic space and its inclusion `ι` to a morphism of
  algebraic spaces.
* `AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` is the map of Stacks 060E: the
  restriction along `ι` of the comparison map `c_{h'}` of Stacks 04CX.
* `AlgebraicGeometry.Space.IsEtaleLocalThickeningDifferentialsMap` records the étale
  localization of Stacks 04CU and Stacks 060D for this situation: over every object of the small
  étale site of `Z` the restricted comparison map is the map of Stacks 04FB of a universal
  first-order thickening of schemes assembled from charts of `Z'`, `X` and `Y` over that object.
* `AlgebraicGeometry.Space.pushforwardDerivationRestriction` is the restriction map on
  derivations against which Stacks 060E is tested: it carries a morphism `Ω_{Z'/Y} ⟶ ι_*F` —
  equivalently, by Stacks 04CT, a `Y`-derivation of `𝒪_{Z'}` with values in `ι_*F` — to the
  `Y`-derivation of `𝒪_X` obtained by composing with the structure map `(h')^♯`.

## Main results

* `AlgebraicGeometry.Space.isIso_restrict_of_isSheafOfDifferentialsMap`: **Stacks 060E**, for an
  arbitrary realization of the comparison map of Stacks 04CX.
* `AlgebraicGeometry.Space.isIso_thickeningSheafOfDifferentialsMap`: the same for the comparison
  map as Stacks 04CX constructs it.
* `AlgebraicGeometry.Space.derivationDirectImageEquiv_comp_restrict`: the commuting square that
  identifies restriction along `ι^*c_{h'}` of the morphisms out of `ι^*Ω_{Z'/Y}` with
  `AlgebraicGeometry.Space.pushforwardDerivationRestriction`.  This is where the
  characterization of Stacks 04CX is used.
* `AlgebraicGeometry.Space.isIso_restrict_iff_bijective_pushforwardDerivationRestriction`: the
  reduction of Stacks 060E to that lifting statement, proved with no carried hypothesis.

## Implementation notes

**What is granted, and the tie to the chart.**  The étale localization of the sheaf of
differentials is the input the tree does not have, and it is carried as
`AlgebraicGeometry.Space.IsEtaleLocalThickeningDifferentialsMap`, in the shape in which the
source's argument delivers it and consumes nothing more.  This follows Stacks 05ZC
and Stacks 05ZD, `AlgebraicGeometry.Space.isIso_of_isSheafOfDifferentialsMap_of_isPullback` and
`AlgebraicGeometry.Space.isIso_biprodDesc_of_isSheafOfDifferentialsMap`, which carry the same
input for the same reason; the scheme case, here Stacks 04FB, is applied and not granted.

Unlike those two predicates, the one below does **not** quantify over unrelated schemes.  Its
scheme-level data is tied to the situation at hand: the source scheme *is* the scheme of the
étale chart the sections are taken over, the other three schemes are charts of `Z'`, `X` and `Y`
through given étale chart morphisms, and the four scheme morphisms are required to realize `ι`,
`h`, `h'` and `p` on those charts, by four commuting squares.  Fixing the open subscheme to be
the whole chart is part of the same tie.  These conjuncts make the hypothesis stronger, hence
the theorem formally weaker, and that is deliberate: without them the hypothesis says only that
`ι^*c_{h'}` is conjugate, chart by chart, to some map of some universal first-order thickening
of schemes, whereas with them it says that the étale localization the source actually performs
has the effect the source claims.  It is a deliberate strengthening relative to the untied
Stacks 05ZC and Stacks 05ZD precedent.

**Formal unramifiedness is not assumed.**  The source assumes `h` formally unramified and then
speaks of *the* universal first-order thickening, whose existence is Stacks 0606.  Here a
universal first-order thickening is a hypothesis, and formal unramifiedness of `h` follows from
it by Stacks 0609,
`AlgebraicGeometry.Space.formallyUnramified_of_isUniversalFirstOrderThickening`, so nothing is
lost by dropping it.  The scheme-level Stacks 04FB,
`Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap`, makes the same choice, and so do
the other universal-thickening files of this directory.

**The reduction uses no comparison of inverse images.**  The source of the map of Stacks 060E is
`ι^*(h')^*Ω_{X/Y}`, which the source of the tag writes `h^*Ω_{X/Y}` through the comparison
`(ι ≫ h')^* ≅ ι^*(h')^*` of Stacks 03LU.  That comparison is not used: the morphisms out of a
double pullback are transposed twice, once along `ι^* ⊣ ι_*` and once along
`(h')^* ⊣ (h')_*`, and the second transpose lands in the `Y`-derivations of `𝒪_X` with values
in `(h')_*ι_*F` — the module `h_*F` of the source — by
`AlgebraicGeometry.Space.derivationDirectImageEquiv`, Equation 0619.  So the only input of the
square is the characterization of `c_{h'}`, applied through the naturality of the two
adjunctions in each variable.

**The shape of the data.**  As in
`StacksFrontier/AlgebraicGeometry/Spaces/Thickenings/Universal.lean`, the smaller space of the
thickening is a `CategoryTheory.Subfunctor` of the ambient space, so the morphism `h` of the
source is not a separate datum: it is the composite `Z.ι ≫ h'.hom`.  The base algebraic space of
the source is called `Y` here, the letter `B` being taken by the big fppf site.

## What is not proved here

Proving Stacks 060E outright, rather than from the étale localization, would take either of two
routes, and each stops at an input this library does not have.  The obstructions are recorded
because they, and not the transport, are what closing this properly requires.

**The source's route: étale localization.**  Discharging
`AlgebraicGeometry.Space.IsEtaleLocalThickeningDifferentialsMap` needs four things, of which
this library has one.  The comparison of Stacks 04CS between the differentials of a morphism of
schemes on its small Zariski and small étale sites is available in the scheme's own spelling:
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedRelativeDifferentialsDerivation`
of the module
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsCorepresentable`
proves that `(Ω_{X/Y})^a` with its derivation `d^a` corepresents the derivations, and
`AlgebraicGeometry.SmallEtale.isIso_differentialsComparison_of_universal` turns that into
invertibility of `AlgebraicGeometry.SmallEtale.differentialsComparison` at a universal pair.
What is still missing is the transport of that identification to the *spaces*-level sheaf of
differentials `AlgebraicGeometry.Space.sheafOfDifferentials` of a morphism of represented
algebraic spaces, whose relative structure is the inverse image `f⁻¹𝒪_Y` rather than the
vanishing on functions pulled back from opens of `Y` that the scheme-level statement uses.  The
étale-source
half of Stacks 04CU is the one that is available:
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleSourceLocalizationIso` proves it, and
`AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` is unconditional because of
it.  The representable étale extension of a chart of `Z` across `Z ⊂ Z'`, which Stacks 060D
clause (2),
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening.etaleLocalization`, takes as a
hypothesis because the topological invariance of the spaces-étale site, Stacks 05ZH, is absent.
And a passage from the spaces-level universal property of Stacks 0602 for a representable
thickening to the scheme-level `Stacks.Thickenings.IsUniversalFirstOrderThickening` that
Stacks 04FB consumes; `AlgebraicGeometry.Space.formallyUnramified_of_etaleLocalization` and the
criteria of Stacks 0603 test the spaces-level property on schemes but do not produce the
scheme-level predicate.

**The corepresentability route.**  `AlgebraicGeometry.Space.sheafOfDifferentials` is defined by
its universal property, so the tag is equivalent to the bijectivity of
`AlgebraicGeometry.Space.pushforwardDerivationRestriction` for every `𝒪_Z`-module `F`; that
equivalence is proved below.  What remains is to deduce that bijectivity from the universal
property of Stacks 0602, which quantifies over *given* first-order thickenings of algebraic
spaces: to apply it to a module `F` one needs the trivial square-zero extension of `Z` by `F` —
an algebraic space `Z[F]` with `Z ⊂ Z[F]` a first-order thickening of conormal module `F` —
together with the identification of the morphisms `Z[F] ⟶ X` over `Y` extending `h` with the
`Y`-derivations of `𝒪_X` with values in `h_*F`.  Neither is constructed in this library, which
is also why Stacks 0606 is absent from it; see the *What is not proved here* section of
`StacksFrontier/AlgebraicGeometry/Spaces/UniversalFirstOrderThickening.lean`.

## References

* [Stacks Project, Tag 060E](https://stacks.math.columbia.edu/tag/060E)
* [Stacks Project, Tag 04FB](https://stacks.math.columbia.edu/tag/04FB), the case of schemes.
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX), the comparison map of a
  commutative square and its characterization.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal property.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the bijection between
  the morphisms out of a pullback of differentials and the derivations into a direct image.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU),
  [Tag 04CS](https://stacks.math.columbia.edu/tag/04CS) and
  [Tag 060D](https://stacks.math.columbia.edu/tag/060D), the étale localization of the sheaf of
  differentials and of the universal first-order thickening.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site,
  whose objects are the étale charts.
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602), the universal
  first-order thickening.
* [Stacks Project, Tag 0606](https://stacks.math.columbia.edu/tag/0606) and
  [Tag 0609](https://stacks.math.columbia.edu/tag/0609), its existence for a formally unramified
  morphism and the formal unramifiedness it implies.
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-! ### The smaller space of a universal first-order thickening -/

/-- The smaller space of a universal first-order thickening, as an algebraic space: the
subfunctor is a closed subspace of the ambient algebraic space, by Stacks 05ZK, and a closed
subspace of an algebraic space is an algebraic space. -/
abbrev universalThickeningSubSpace (hZ : IsUniversalFirstOrderThickening B S hS Z h') :
    AlgebraicSpaces B S hS :=
  ⟨Z.toFunctor, (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1.1⟩

/-- The inclusion `ι : Z ⟶ Z'` of the smaller space of a universal first-order thickening, as a
morphism of algebraic spaces.  The morphism `h : Z ⟶ X` of Stacks 060E is the composite of this
inclusion with the structure morphism `h' : Z' ⟶ X`. -/
abbrev universalThickeningInclusion (hZ : IsUniversalFirstOrderThickening B S hS Z h') :
    universalThickeningSubSpace B S hS hZ ⟶ Z' :=
  ObjectProperty.homMk Z.ι

/-! ### The map of Stacks 060E -/

/-- **The map of Stacks 060E.**  The restriction along the inclusion `ι : Z ⟶ Z'` of the
comparison map `c_{h'} : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` of Stacks 04CX, for the square with top edge
`h'`, right edge `p : X ⟶ Y` and base morphism the identity of `Y`.

Its source `ι^*(h')^*Ω_{X/Y}` is the module `h^*Ω_{X/Y}` of the source of the tag, through
`ι ≫ h' = h`, and its target `ι^*Ω_{Z'/Y}` is written `Ω_{Z'/Y} ⊗ 𝒪_Z` there.  The map `dh'` of
the statement of the tag is `c_{h'}`, as its proof says. -/
noncomputable def thickeningSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) ⟶
      (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
        (sheafOfDifferentials B S hS (h' ≫ p)) :=
  (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map
    (sheafOfDifferentialsMap B S hS h' p (h' ≫ p) (𝟙 Y) (Category.comp_id (h' ≫ p)).symm)

/-! ### The étale localization of Stacks 04CU and Stacks 060D -/

/-- **The étale localization of Stacks 04CU and Stacks 060D for the map of Stacks 060E.**  Let
`U` be an object of the small étale site of `Z`, that is an étale chart `yoneda.obj U ⟶ Z`, and
let `Zs` be the scheme representing it.  The hypothesis asks for étale charts `aX`, `aY`, `mZ'`
of `X`, `Y` and `Z'`, for morphisms of the big fppf site realizing `ι`, `h`, `h'` and `p` on
those charts — the four commuting squares `hjU`, `hkX`, `hk'X`, `hrXY` — such that the resulting
morphisms of schemes `Zs ⟶ Zs'` over `Xs` exhibit a universal first-order thickening of schemes,
and for an identification, as abelian groups, of the sections over `U` of the two sides of the
map of Stacks 060E with the global sections of the two corresponding modules of that thickening,
carrying the restricted comparison map to the map of Stacks 04FB.

The identification is `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` of Stacks 04CU read on sections, for the
rows of the square of Stacks 060D; clause (2) of Stacks 060D is what makes the thickening of
schemes over the chart a universal one, and it enters only through the universal property
asserted here.

All of the scheme-level data is tied to the chart and to the morphisms of the situation; see the
implementation notes of this file, which explain why this is a deliberate strengthening relative
to the untied `AlgebraicGeometry.Space.IsEtaleLocalBaseChangeMap` of Stacks 05ZC. -/
def IsEtaleLocalThickeningDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (c : (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
          ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) ⟶
        (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
          (sheafOfDifferentials B S hS (h' ≫ p))) : Prop :=
  ∀ U : (SmallEtale B S hS (universalThickeningSubSpace B S hS hZ).obj)ᵒᵖ,
    ∃ (cX cY cZ' : BigFppfOver B S hS)
      (aX : yoneda.obj cX ⟶ X.obj) (aY : yoneda.obj cY ⟶ Y.obj)
      (mZ' : yoneda.obj cZ' ⟶ Z'.obj)
      (_haX : IsEtale B S hS aX) (_haY : IsEtale B S hS aY) (_hmZ' : IsEtale B S hS mZ')
      (jU : U.unop.obj.left ⟶ cZ') (kX : U.unop.obj.left ⟶ cX) (k'X : cZ' ⟶ cX)
      (rXY : cX ⟶ cY)
      (_hjU : yoneda.map jU ≫ mZ' = U.unop.obj.hom ≫ Z.ι)
      (_hkX : yoneda.map kX ≫ aX = U.unop.obj.hom ≫ Z.ι ≫ h'.hom)
      (_hk'X : yoneda.map k'X ≫ aX = mZ' ≫ h'.hom)
      (_hrXY : yoneda.map rXY ≫ aY = aX ≫ p.hom)
      (_huniv : Stacks.Thickenings.IsUniversalFirstOrderThickening
          ((BigFppfOver.toScheme B S hS).map kX) ((BigFppfOver.toScheme B S hS).map jU)
          ((BigFppfOver.toScheme B S hS).map k'X))
      (α : ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
              ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p))).val.obj U ≃+
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map jU)).obj
              ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map k'X)).obj
                (Scheme.Hom.relativeDifferentials
                  ((BigFppfOver.toScheme B S hS).map rXY)))).val.obj
              (op (⊤ : ((BigFppfOver.toScheme B S hS).obj U.unop.obj.left).Opens)))
          (β : ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
              (sheafOfDifferentials B S hS (h' ≫ p))).val.obj U ≃+
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map jU)).obj
              (Scheme.Hom.relativeDifferentials
                ((BigFppfOver.toScheme B S hS).map k'X ≫
                  (BigFppfOver.toScheme B S hS).map rXY))).val.obj
              (op (⊤ : ((BigFppfOver.toScheme B S hS).obj U.unop.obj.left).Opens))),
          ∀ x, β ((c.val.app U).hom x) =
            ((Scheme.Hom.thickeningRelativeDifferentialsMap
              ((BigFppfOver.toScheme B S hS).map jU) ((BigFppfOver.toScheme B S hS).map k'X)
              ((BigFppfOver.toScheme B S hS).map rXY)).val.app
                (op (⊤ : ((BigFppfOver.toScheme B S hS).obj U.unop.obj.left).Opens))).hom (α x)

/-! ### Stacks 060E -/

/-- **Stacks 060E.**  Let `h : Z ⟶ X` be a morphism of algebraic spaces over `S`, presented as
the composite `Z.ι ≫ h'` of the inclusion of a closed subspace `Z` of an algebraic space `Z'`
with a structure morphism `h' : Z' ⟶ X`, and let `Z ⊂ Z'` be a universal first-order thickening
of `Z` over `X`.  For a morphism `p : X ⟶ Y` to a base algebraic space, the comparison map
`c_{h'} : (h')^*Ω_{X/Y} ⟶ Ω_{Z'/Y}` of Stacks 04CX induces an isomorphism
`h^*Ω_{X/Y} ⟶ Ω_{Z'/Y} ⊗ 𝒪_Z`, namely its restriction along the inclusion of `Z`.

The map is named by the characterizing property of Stacks 04CX, which determines it uniquely by
`AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`; that uniqueness carries the
étale-local input from the realization `c₀` it is stated for to the realization `c` in hand.
The proof is the source's: over an étale chart of `Z` the restricted comparison map is the map
of Stacks 04FB of a universal first-order thickening of schemes, which is an isomorphism, and a
morphism of `𝒪_Z`-modules which is bijective on the sections over every chart is an
isomorphism.

Formal unramifiedness of `h`, a hypothesis of the source, is not assumed: it is what makes a
universal first-order thickening exist, one is given, and by Stacks 0609 it follows. -/
@[stacks 060E "granted, as `hetale`, the étale localization of 04CU and 060D: over each object
  of the small étale site of `Z` the restriction along `Z ⟶ Z'` of the comparison map of 04CX
  is, on sections, the map 04FB of a universal first-order thickening of schemes assembled from
  charts of `Z'`, `X` and `Y` over that object.  The scheme case 04FB is applied, not granted;
  formal unramifiedness of `h` is not assumed, a universal first-order thickening being given"]
theorem isIso_restrict_of_isSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (c c₀ : (modulePullback B S hS h').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (h' ≫ p))
    (hc : IsSheafOfDifferentialsMap B S hS h' p (h' ≫ p) c)
    (hc₀ : IsSheafOfDifferentialsMap B S hS h' p (h' ≫ p) c₀)
    (hetale : IsEtaleLocalThickeningDifferentialsMap B S hS hZ p
      ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map c₀)) :
    IsIso ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map c) := by
  rw [eq_of_isSheafOfDifferentialsMap B S hS h' p (h' ≫ p) hc hc₀]
  refine isIso_of_bijective_app B S hS _ fun U => ?_
  obtain ⟨cX, cY, cZ', aX, aY, mZ', -, -, -, jU, kX, k'X, rXY, -, -, -, -, huniv, α, β, hcomp⟩ :=
    hetale U
  have hiso : IsIso (Scheme.Hom.thickeningRelativeDifferentialsMap
      ((BigFppfOver.toScheme B S hS).map jU) ((BigFppfOver.toScheme B S hS).map k'X)
      ((BigFppfOver.toScheme B S hS).map rXY)) :=
    Stacks.Thickenings.isIso_thickeningRelativeDifferentialsMap huniv
      ((BigFppfOver.toScheme B S hS).map rXY)
  have hb := @Stacks.SheafOfModules.bijective_app_of_isIso _ _ _ _ _ _ _ hiso
    (op (⊤ : ((BigFppfOver.toScheme B S hS).obj U.unop.obj.left).Opens))
  have hcomposed : Function.Bijective fun x =>
      β ((((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map
        c₀).val.app U).hom x) := by
    simp only [hcomp]
    exact hb.comp (EquivLike.bijective α)
  exact (Function.Bijective.of_comp_iff' (EquivLike.bijective β) _).1 hcomposed

/-- **Stacks 060E** for the comparison map constructed by
`AlgebraicGeometry.Space.sheafOfDifferentialsMap`: the map
`AlgebraicGeometry.Space.thickeningSheafOfDifferentialsMap` is an isomorphism.

This is `AlgebraicGeometry.Space.isIso_restrict_of_isSheafOfDifferentialsMap` at the realization
of the comparison map which Stacks 04CX constructs, whose characterizing property is
`AlgebraicGeometry.Space.isSheafOfDifferentialsMap_sheafOfDifferentialsMap`. -/
@[stacks 060E "granted, as `hetale`, the étale localization of 04CU and 060D, as for
  `isIso_restrict_of_isSheafOfDifferentialsMap`; stated for the comparison map of 04CX as
  constructed"]
theorem isIso_thickeningSheafOfDifferentialsMap
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (hetale : IsEtaleLocalThickeningDifferentialsMap B S hS hZ p
      (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) :=
  isIso_restrict_of_isSheafOfDifferentialsMap B S hS hZ p _ _
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS h' p (h' ≫ p) (𝟙 Y)
      (Category.comp_id (h' ≫ p)).symm)
    (isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS h' p (h' ≫ p) (𝟙 Y)
      (Category.comp_id (h' ≫ p)).symm)
    hetale

/-! ### Restriction of derivations along the structure map of the thickening -/

section Reduction

variable (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)

/-- Restriction of derivations along the structure map of the thickening.  A morphism
`x : Ω_{Z'/Y} ⟶ ι_*F` is, by the universal property of Stacks 04CT, a `Y`-derivation of
`𝒪_{Z'}` with values in `ι_*F`; composing it with the structure map
`(h')^♯ : 𝒪_X ⟶ (h')_*𝒪_{Z'}` gives a `Y`-derivation of `𝒪_X` with values in `(h')_*ι_*F`,
which is the module `h_*F` of Stacks 060E.

Concretely this is the direct image along `h'` of `x`, postcomposed onto the `Y`-derivation
`(h')_*d_{Z'/Y} ∘ (h')^♯` of Stacks 04CX. -/
noncomputable def pushforwardDerivationRestriction
    (F : Modules.{u, u} B S hS (universalThickeningSubSpace B S hS hZ).obj
      (universalThickeningSubSpace B S hS hZ).property) :
    (sheafOfDifferentials B S hS (h' ≫ p) ⟶
        (modulePushforward B S hS (universalThickeningInclusion B S hS hZ)).obj F) →
      PresheafOfModulesOfCommRing.Derivation' ((modulePushforward B S hS h').obj
          ((modulePushforward B S hS (universalThickeningInclusion B S hS hZ)).obj F)).val
        (structureSharpInverseImage B S hS p).hom :=
  fun x ↦ (pushforwardUniversalDerivation B S hS h' p (h' ≫ p) (𝟙 Y)
      (Category.comp_id (h' ≫ p)).symm).postcomp
    ((modulePushforward B S hS h').map x).val

/-- The comparison map of Stacks 04CX, read as an equality of `Y`-derivations of `𝒪_X`: the
adjoint transpose of `c_{h'}` carries the universal derivation `d_{X/Y}` to the `Y`-derivation
`(h')_*d_{Z'/Y} ∘ (h')^♯`.  This is the characterizing property of Stacks 04CX with its
sectionwise quantifiers discharged. -/
theorem postcomp_homEquiv_of_isSheafOfDifferentialsMap
    {c : (modulePullback B S hS h').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (h' ≫ p)}
    (hc : IsSheafOfDifferentialsMap B S hS h' p (h' ≫ p) c) :
    (universalDerivation B S hS p).postcomp
        (((modulePullbackAdjunction B S hS h').homEquiv (sheafOfDifferentials B S hS p)
          (sheafOfDifferentials B S hS (h' ≫ p))) c).val =
      pushforwardUniversalDerivation B S hS h' p (h' ≫ p) (𝟙 Y)
        (Category.comp_id (h' ≫ p)).symm := by
  apply PresheafOfModulesOfCommRing.Derivation.ext
  ext U t
  exact hc U t

/-- **The square the reduction rests on.**  For an `𝒪_Z`-module `F` and a morphism
`x : ι^*Ω_{Z'/Y} ⟶ F`, the `Y`-derivation attached by Equation 0619 to the composite of
`ι^*c_{h'}` with `x` is the restriction along the structure map `(h')^♯` of the transpose of
`x`.

Both transposes are read off from the naturality of the two adjunctions — in the left variable
for `ι^*c_{h'}`, in the right variable for `c_{h'}` — and the characterization of `c_{h'}` of
Stacks 04CX then replaces the transpose of `c_{h'}` by the `Y`-derivation
`(h')_*d_{Z'/Y} ∘ (h')^♯`. -/
theorem derivationDirectImageEquiv_comp_restrict
    {c : (modulePullback B S hS h').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (h' ≫ p)}
    (hc : IsSheafOfDifferentialsMap B S hS h' p (h' ≫ p) c)
    (F : Modules.{u, u} B S hS (universalThickeningSubSpace B S hS hZ).obj
      (universalThickeningSubSpace B S hS hZ).property)
    (x : (modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
      (sheafOfDifferentials B S hS (h' ≫ p)) ⟶ F) :
    derivationDirectImageEquiv B S hS h' p
        ((modulePushforward B S hS (universalThickeningInclusion B S hS hZ)).obj F)
        (((modulePullbackAdjunction B S hS
            (universalThickeningInclusion B S hS hZ)).homEquiv _ F)
          ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map c ≫ x)) =
      pushforwardDerivationRestriction B S hS hZ p F
        (((modulePullbackAdjunction B S hS
          (universalThickeningInclusion B S hS hZ)).homEquiv _ F) x) := by
  rw [derivationDirectImageEquiv_apply,
    (modulePullbackAdjunction B S hS
      (universalThickeningInclusion B S hS hZ)).homEquiv_naturality_left,
    (modulePullbackAdjunction B S hS h').homEquiv_naturality_right]
  refine Eq.trans ?_
    (congrArg (fun D ↦ PresheafOfModulesOfCommRing.Derivation.postcomp D
        ((modulePushforward B S hS h').map
          (((modulePullbackAdjunction B S hS
            (universalThickeningInclusion B S hS hZ)).homEquiv _ F) x)).val)
      (postcomp_homEquiv_of_isSheafOfDifferentialsMap B S hS p hc))
  apply PresheafOfModulesOfCommRing.Derivation.ext
  rfl

/-- **The reduction of Stacks 060E to a statement about derivations.**  The map of Stacks 060E
is an isomorphism exactly when, for every `𝒪_Z`-module `F`, restriction along the structure map
`(h')^♯` is a bijection from the `Y`-derivations of `𝒪_{Z'}` with values in `ι_*F` onto the
`Y`-derivations of `𝒪_X` with values in `h_*F`.

Both sheaves of differentials corepresent their functors of derivations, by Stacks 04CT, and the
two adjunctions turn the morphisms out of the two sides of the map of Stacks 060E into those two
sets of derivations; the square
`AlgebraicGeometry.Space.derivationDirectImageEquiv_comp_restrict` identifies restriction along
the map with restriction of derivations, and a morphism is an isomorphism exactly when
precomposition with it is bijective at every target.

Nothing is carried here: this is an equivalent form of Stacks 060E, not a proof of it.  It is
the shape in which the universal property of Stacks 0602 would prove the tag: a `Y`-derivation
of `𝒪_X` with values in `h_*F` is a morphism to `X` out of the trivial square-zero extension of
`Z` by `F`, and lifting it across `Z ⊂ Z'` is the unique-extension clause of Stacks 0602.  That
extension is not available in this library; see the *What is not proved here* section of this
file. -/
theorem isIso_restrict_iff_bijective_pushforwardDerivationRestriction
    {c : (modulePullback B S hS h').obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS (h' ≫ p)}
    (hc : IsSheafOfDifferentialsMap B S hS h' p (h' ≫ p) c) :
    IsIso ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).map c) ↔
      ∀ F : Modules.{u, u} B S hS (universalThickeningSubSpace B S hS hZ).obj
        (universalThickeningSubSpace B S hS hZ).property,
        Function.Bijective (pushforwardDerivationRestriction B S hS hZ p F) := by
  have key (F : Modules.{u, u} B S hS (universalThickeningSubSpace B S hS hZ).obj
      (universalThickeningSubSpace B S hS hZ).property) :
      Function.Bijective (fun x ↦ (modulePullback B S hS
          (universalThickeningInclusion B S hS hZ)).map c ≫ x :
        ((modulePullback B S hS (universalThickeningInclusion B S hS hZ)).obj
            (sheafOfDifferentials B S hS (h' ≫ p)) ⟶ F) → _) ↔
        Function.Bijective (pushforwardDerivationRestriction B S hS hZ p F) := by
    set e := ((modulePullbackAdjunction B S hS
      (universalThickeningInclusion B S hS hZ)).homEquiv
        (sheafOfDifferentials B S hS (h' ≫ p)) F)
    set e' := (((modulePullbackAdjunction B S hS
      (universalThickeningInclusion B S hS hZ)).homEquiv
        ((modulePullback B S hS h').obj (sheafOfDifferentials B S hS p)) F).trans
      (derivationDirectImageEquiv B S hS h' p
        ((modulePushforward B S hS (universalThickeningInclusion B S hS hZ)).obj F)))
    have hsq : ∀ x, e' ((modulePullback B S hS
        (universalThickeningInclusion B S hS hZ)).map c ≫ x) =
          pushforwardDerivationRestriction B S hS hZ p F (e x) :=
      derivationDirectImageEquiv_comp_restrict B S hS hZ p hc F
    exact (Equiv.comp_bijective _ e').symm.trans <|
      (iff_of_eq (congrArg Function.Bijective (funext hsq))).trans <|
        Equiv.bijective_comp e (pushforwardDerivationRestriction B S hS hZ p F)
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' key

end Reduction

end AlgebraicGeometry.Space

end
