module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.AffineQcohUnit.Equivalence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FiniteAlgebraization
public import StacksFrontier.AlgebraicGeometry.RelativeSpecOpenRestriction.RelativeSpecBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# The base change of a proper morphism along `Spec B ⟶ Spec A`

Let `A` be a ring, `B` an `A`-algebra, `X` a scheme and `f : X ⟶ Spec A` a morphism. This file
builds the base change

`X' = X ×_{Spec A} Spec B`,

with its two projections `π : X' ⟶ X` and `f' : X' ⟶ Spec B`, and records the three properties
of it that the cohomological applications use: `f'` is proper when `f` is, `π` is affine, and
`π` exhibits `X'` as the *relative spectrum over `X`* of the quasi-coherent sheaf of
`𝒪_X`-algebras `f^* B̃`.

That last identification is what makes `π` usable: by [Stacks, Tag 01SB] direct image along an
affine morphism is an equivalence from quasi-coherent `𝒪_{X'}`-modules to quasi-coherent
`π_* 𝒪_{X'}`-modules, and `pushforwardProjIso` says which algebra `π_* 𝒪_{X'}` is, namely
`f^* B̃`. A quasi-coherent module over `f^* B̃` therefore comes from a unique quasi-coherent
module on `X'`.

## Main definitions

* `Stacks.ProperAlgebraBaseChange.specAlgebraMap` is `Spec B ⟶ Spec A`, and
  `Stacks.ProperAlgebraBaseChange.specAlgebraSheaf` is the quasi-coherent sheaf of
  `𝒪_{Spec A}`-algebras `B̃`, realised as the pushforward of the structure sheaf along it.
* `Stacks.ProperAlgebraBaseChange.baseChangeOver` is `X' = X ×_{Spec A} Spec B` as a scheme over
  `X`; `Stacks.ProperAlgebraBaseChange.proj` is `π` and
  `Stacks.ProperAlgebraBaseChange.toSpec` is `f'`.

## Main results

* `Stacks.ProperAlgebraBaseChange.universallyClosed_of_isPullback` and
  `Stacks.ProperAlgebraBaseChange.isProper_of_isPullback` are **[Stacks, Tag 01W4]**: the base
  change of a universally closed morphism is universally closed, and the base change of a proper
  morphism is proper. They are stated for an arbitrary cartesian square, which is the tag's own
  generality, and specialise to the instances `isProper_toSpec` and `isAffineHom_proj` for the
  square at hand.
* `Stacks.ProperAlgebraBaseChange.isLocallyNoetherian_scheme`: **`X'` is locally Noetherian**
  when `A` is Noetherian, `B` is of finite type over `A` and `f` is proper — the hypothesis under
  which [Stacks, Tag 01XZ] reads coherence off quasi-coherence and finite type.
* `Stacks.ProperAlgebraBaseChange.baseChangeOverIso`: `X ×_{Spec A} Spec B` is the relative
  spectrum over `X` of `f^* B̃`.
* `Stacks.ProperAlgebraBaseChange.pushforwardProjIso`: `π_* 𝒪_{X'} ≅ f^* B̃`.
* `Stacks.ProperAlgebraBaseChange.isEquivalence_pushforward_proj`: direct image along `π` is an
  equivalence of quasi-coherent categories.

## Implementation notes

Nothing here is glued by hand. `B̃` is not built from the module `B` either: `Spec B ⟶ Spec A` is
a morphism of affine schemes, hence affine, so its pushed-forward structure sheaf
`pushforwardAlgebra` *is* `B̃` and is quasi-coherent by
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_pushforwardAlgebra`. The identification of the
base change with a relative spectrum is then two existing isomorphisms composed: `Spec B` is the
relative spectrum of `B̃` over `Spec A` ([Stacks, Tag 01S8],
`Stacks.AffineAlgebraEquivalence.overRelativeSpecIso`), and the relative spectrum commutes with
the base change along `f` ([Stacks, Tag 01LX] part (2),
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`).

The two [Stacks, Tag 01W4] statements are the Mathlib instances
`AlgebraicGeometry.universallyClosed_isStableUnderBaseChange` and
`AlgebraicGeometry.IsProper.isStableUnderBaseChange` read through
`CategoryTheory.MorphismProperty.of_isPullback`; neither Mathlib declaration carries the tag, and
the tag's statement is exactly the conjunction of the two.

**No `@[stacks 01LX]`, `@[stacks 01SB]` or `@[stacks 01XZ]` attribute is placed here.** All three
tags are carried, in their full generality, by
`Stacks.AffineAlgebraEquivalence.isAffineOpen_preimage_relativeSpecToBase`,
`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso` and
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` for the three parts of 01LX,
`Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward` together
with `Stacks.AlgebraicGeometry.QcohLimits.affine_isQuasicoherent_restrictScalars_iff` for 01SB,
and `Stacks.AlgebraicGeometry.CoherenceCriteria.coherent_tfae` for 01XZ. What this file adds is
the *instance* of those statements at `X ×_{Spec A} Spec B`, which is a specialisation and so
must not carry the tags.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01S8](https://stacks.math.columbia.edu/tag/01S8)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 01W4](https://stacks.math.columbia.edu/tag/01W4)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.ProperAlgebraBaseChange

/-! ### Stacks Tag 01W4: base change of proper and of universally closed morphisms -/

/-- **Stacks Project, Tag 01W4, second statement.** The base change of a universally closed
morphism is universally closed: in a cartesian square

```
Y' --f'--> Y
|          |
g'         g
v          v
X ---f---> S
```

if `g` is universally closed then so is `g'`. -/
@[stacks 01W4 "the base change of a universally closed morphism is universally closed"]
theorem universallyClosed_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : UniversallyClosed g) :
    UniversallyClosed g' :=
  MorphismProperty.of_isPullback (P := @UniversallyClosed) sq hg

/-- **Stacks Project, Tag 01W4, first statement.** The base change of a proper morphism is
proper: in a cartesian square

```
Y' --f'--> Y
|          |
g'         g
v          v
X ---f---> S
```

if `g` is proper then so is `g'`. -/
@[stacks 01W4 "the base change of a proper morphism is proper"]
theorem isProper_of_isPullback {X Y Y' S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S}
    {f' : Y' ⟶ Y} {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsProper g) :
    IsProper g' :=
  MorphismProperty.of_isPullback (P := @IsProper) sq hg

/-! ### The algebra `B̃` on `Spec A` -/

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The morphism `Spec B ⟶ Spec A` of affine schemes attached to an `A`-algebra `B`. -/
noncomputable abbrev specAlgebraMap : Spec (.of B) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The quasi-coherent sheaf of `𝒪_{Spec A}`-algebras `B̃` attached to an `A`-algebra `B`: the
pushforward of the structure sheaf of `Spec B` along `Spec B ⟶ Spec A`, which is affine because
both schemes are. -/
noncomputable abbrev specAlgebraSheaf : Stacks.RelativeSpec.AlgebraSheaf (Spec (.of A)) :=
  pushforwardAlgebra (specAlgebraMap A B)

/-- The sheaf of `𝒪_{Spec A}`-algebras `B̃` is quasi-coherent. -/
instance isQuasicoherent_specAlgebraSheaf :
    Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (specAlgebraSheaf A B) :=
  isQuasicoherent_pushforwardAlgebra _

/-! ### The base change `X ×_{Spec A} Spec B` -/

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The base change `X' = X ×_{Spec A} Spec B`, as a scheme over `X`. -/
noncomputable abbrev baseChangeOver : Over X :=
  (Over.pullback f).obj (Over.mk (specAlgebraMap A B))

/-- The base change `X' = X ×_{Spec A} Spec B`. -/
noncomputable abbrev scheme : Scheme.{u} := (baseChangeOver A B f).left

/-- The projection `π : X' ⟶ X`, the base change of `Spec B ⟶ Spec A` along `f`. -/
noncomputable abbrev proj : scheme A B f ⟶ X := (baseChangeOver A B f).hom

/-- The projection `f' : X' ⟶ Spec B`, the base change of `f` along `Spec B ⟶ Spec A`. -/
noncomputable abbrev toSpec : scheme A B f ⟶ Spec (.of B) :=
  pullback.fst (specAlgebraMap A B) f

/-- The square exhibiting `X'` as the fibre product of `f` and `Spec B ⟶ Spec A`. -/
theorem isPullback_baseChange :
    IsPullback (toSpec A B f) (proj A B f) (specAlgebraMap A B) f :=
  IsPullback.of_hasPullback _ _

/-- **The base change of a proper morphism is proper** ([Stacks, Tag 01W4]) at the square at
hand: `f' : X' ⟶ Spec B` is proper as soon as `f : X ⟶ Spec A` is. -/
instance isProper_toSpec [IsProper f] : IsProper (toSpec A B f) :=
  isProper_of_isPullback (isPullback_baseChange A B f).flip ‹IsProper f›

/-- **The base change of an affine morphism is affine** at the square at hand: the projection
`π : X' ⟶ X` is affine because `Spec B ⟶ Spec A` is. -/
instance isAffineHom_proj : IsAffineHom (proj A B f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_baseChange A B f)
    inferInstance

/-- **`B` is Noetherian** when `A` is and `B` is of finite type over `A`: the Hilbert basis
theorem, which is the Noetherianness [Stacks, Tag 0897]'s proof uses on the base `Spec B`. -/
@[sga "5 V 5.1.4" "special case"]
theorem isNoetherianRing_of_finiteType [IsNoetherianRing A] [Algebra.FiniteType A B] :
    IsNoetherianRing B :=
  Algebra.FiniteType.isNoetherianRing A B

/-- **`X' = X ×_{Spec A} Spec B` is locally Noetherian** when `A` is Noetherian, `B` is of finite
type over `A` and `f` is proper.

This is the hypothesis [Stacks, Tag 01XZ] needs in order to read coherence of a module on `X'`
off quasi-coherence and finite type, and it is the first of the two things [Stacks, Tag 0897]
part (1) asks of the module `F'` built on `X'`.

`B` is Noetherian by the Hilbert basis theorem, so `Spec B` is locally Noetherian; `f` is proper,
so its base change `f' : X' ⟶ Spec B` is proper by [Stacks, Tag 01W4] and in particular locally of
finite type; and a scheme locally of finite type over a locally Noetherian scheme is locally
Noetherian (`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`). The morphism the last
step is applied to is `f'`, not the projection `π`: `π` is affine but not of finite type. -/
@[ega "I 6.3.8" "special case"]
instance isLocallyNoetherian_scheme [IsNoetherianRing A] [Algebra.FiniteType A B] [IsProper f] :
    IsLocallyNoetherian (scheme A B f) :=
  have : IsNoetherianRing B := isNoetherianRing_of_finiteType A B
  LocallyOfFiniteType.isLocallyNoetherian (toSpec A B f)

/-! ### The base change is the relative spectrum of `f^* B̃` -/

/-- **`X ×_{Spec A} Spec B` is the relative spectrum over `X` of `f^* B̃`**, as schemes over `X`.

This is the instance at `Spec B ⟶ Spec A` of [Stacks, Tag 01LX] part (2)
(`Stacks.AffineAlgebraEquivalence.relativeSpecBaseChangeIso`), composed with the presentation of
`Spec B` itself as the relative spectrum of `B̃` over `Spec A` ([Stacks, Tag 01S8],
`Stacks.AffineAlgebraEquivalence.overRelativeSpecIso`). -/
noncomputable def baseChangeOverIso :
    baseChangeOver A B f ≅
      Over.mk (relativeSpecToBase ((algebraPullback f).obj (specAlgebraSheaf A B))) :=
  (Over.pullback f).mapIso (overRelativeSpecIso (specAlgebraMap A B)) ≪≫
    relativeSpecBaseChangeIso f (specAlgebraSheaf A B)

/-- `X ×_{Spec A} Spec B` is the relative spectrum of `f^* B̃`, as schemes. -/
noncomputable def schemeIso :
    scheme A B f ≅ relativeSpec ((algebraPullback f).obj (specAlgebraSheaf A B)) :=
  (Over.forget X).mapIso (baseChangeOverIso A B f)

/-- **The algebra `π` is the relative spectrum of: `π_* 𝒪_{X'} ≅ f^* B̃`.**

Together with [Stacks, Tag 01SB] (`isEquivalence_pushforward_proj`) this is what lets a
quasi-coherent module over `f^* B̃` be read as a quasi-coherent module on `X'`. -/
noncomputable def pushforwardProjIso :
    pushforwardAlgebra (proj A B f) ≅ (algebraPullback f).obj (specAlgebraSheaf A B) :=
  (pushforwardAlgebraIsoOfOverIso (baseChangeOverIso A B f)).symm ≪≫
    pushforwardAlgebraIso ((algebraPullback f).obj (specAlgebraSheaf A B))

/-- **[Stacks, Tag 01SB] at the affine projection `π : X' ⟶ X`.** Direct image along `π` is an
equivalence from the quasi-coherent `𝒪_{X'}`-modules to the quasi-coherent
`π_* 𝒪_{X'}`-modules, and `pushforwardProjIso` identifies `π_* 𝒪_{X'}` with `f^* B̃`. -/
theorem isEquivalence_pushforward_proj :
    (Stacks.AlgebraicGeometry.AffineQcohEquivalence.affineQuasicoherentPushforward
      (proj A B f)).IsEquivalence :=
  Stacks.AlgebraicGeometry.AffineQcohUnit.isEquivalence_affineQuasicoherentPushforward _

end Stacks.ProperAlgebraBaseChange

end
