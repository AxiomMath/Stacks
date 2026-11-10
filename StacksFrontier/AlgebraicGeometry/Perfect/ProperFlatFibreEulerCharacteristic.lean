module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatModuleDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# The Euler characteristic of the fibres of a proper flat family

Let `f : X ⟶ S` be a proper morphism of finite presentation and let `ℱ` be an `𝒪_X`-module of
finite presentation, flat over `S`. [Stacks, Tag 0B9T] asserts that

* the function `s ↦ χ(X_s, ℱ_s)` is locally constant on `S`, and
* formation of that function commutes with base change.

The source proof is a reduction: by cohomology and base change ([Stacks, Tag 0B91]) the object
`K = Rf_*ℱ` of `D(𝒪_S)` is perfect and its formation commutes with arbitrary base change, so the
function in question is `s ↦ ∑ (-1)^i dim_{κ(s)} H^i(K ⊗^L_{𝒪_S} κ(s))`, and that function is
locally constant by [Stacks, Tag 0BDJ].

This file is that reduction, with nothing granted. [Stacks, Tag 0BDJ] is
`AlgebraicGeometry.DerivedFibreBetti.isLocallyConstant_chiDerivedFibre`, and the base-change
property of the derived-fibre Euler characteristic is
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_derivedPullback`. The two halves of
[Stacks, Tag 0B91] (2) used are proved in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatModuleDirectImage.lean`, which this file
imports: perfection of `Rf_*ℱ` is `isPerfect_derivedPushforward_singleFunctor_of_isProper`, and the
base-change isomorphism `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ` is
`nonempty_derivedPullback_derivedPushforward_singleFunctor_iso`, both in the namespace
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic`.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.derivedPushforwardModule`: the object
  `Rf_*ℱ` of `D(𝒪_S)`, for an `𝒪_X`-module `ℱ` placed in degree zero.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.PerfectDerivedPushforward`: the statement
  of the perfection half of [Stacks, Tag 0B91], clause (2), as a proposition; it is proved as
  `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.perfectDerivedPushforward`.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.BaseChangeDerivedPushforward`: the
  statement of the base-change half of [Stacks, Tag 0B91], clause (2), in the untensored form the
  source uses it, as a proposition; it is proved as
  `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.baseChangeDerivedPushforward`.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.chiFibre`: the function
  `s ↦ ∑ (-1)^i dim_{κ(s)} H^i(Rf_*ℱ ⊗^L_{𝒪_S} κ(s))` on `S`.

## Main results

* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isLocallyConstant_chiFibre`: **the first
  conclusion of [Stacks, Tag 0B9T]**, that function is locally constant on `S`.
* `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.chiFibre_baseChange`: **the second
  conclusion of [Stacks, Tag 0B9T]**, formation of that function commutes with base change: for a
  cartesian square its value at `s'` is its value at the image of `s'`.

## Implementation notes

**In what form the function is taken.** The function below is the derived-fibre Euler
characteristic of `Rf_*ℱ`, `AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre`, which is the
form the source's own proof works with after its first sentence. The identification with
`s ↦ χ(X_s, ℱ_s)`, which the source gets by applying the base-change half of
[Stacks, Tag 0B91] to `Spec κ(s) ⟶ S`, is made downstream of this file, in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatFibreEulerCharacteristicUnconditional.lean`, as
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic_eq_chiDerivedFibre`;
the two conclusions of [Stacks, Tag 0B9T] for `s ↦ χ(X_s, ℱ_s)` itself are
`AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.isLocallyConstant_fibreEulerCharacteristic`
and `AlgebraicGeometry.ProperFlatFibreEulerCharacteristic.fibreEulerCharacteristic_baseChange`
there.

**The inputs from [Stacks, Tag 0B91].** Both are proved, in
`StacksFrontier/AlgebraicGeometry/Perfect/ProperFlatModuleDirectImage.lean`. Perfection of `Rf_*ℱ`
is the support form of [Stacks, Tag 0A1H] for a module at the closed subset `X`, which is proper
over `S`; the base-change isomorphism comes from [Stacks, Tag 0DJ9] and the stalk check of
[Stacks, Tag 0DJ8]. They are stated there in terms of `derivedPushforward` and
`DerivedCategory.singleFunctor` rather than with `derivedPushforwardModule`, because that module
sits below this one in the import graph; the propositions `PerfectDerivedPushforward` and
`BaseChangeDerivedPushforward` of this file are proved further downstream, as
`perfectDerivedPushforward` and `baseChangeDerivedPushforward`.

**What is proved.** Local constancy is [Stacks, Tag 0BDJ] at the perfect object `Rf_*ℱ`.
Commutation with base change is the base-change isomorphism combined with
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_derivedPullback` — the base-change clause of
[Stacks, Tag 0BDI], summed over the degrees — and with the invariance of the derived-fibre Euler
characteristic under isomorphism. The function `chiFibre` takes a proof of pseudo-coherence of the
object as an argument, which is what `chiDerivedFibre` needs; the base-change statement holds for
every such proof `hpc`, `hpc'` on the two sides (they exist, by perfection of `Rf_*ℱ` and of
`Rf'_*(g')^*ℱ`, and the value of the function does not depend on them).

## References

* [Stacks Project, Tag 0B9T](https://stacks.math.columbia.edu/tag/0B9T)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance] HasDerivedCategory.standard

/-! ### The derived pushforward of a module -/

/-- **The object `Rf_*ℱ` of `D(𝒪_S)`**, for an `𝒪_X`-module `ℱ`: the derived pushforward along
`f` of `ℱ` placed in degree zero. This is the object `K` of the proof of [Stacks, Tag 0B9T]. -/
public abbrev derivedPushforwardModule {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    DerivedCategory S.Modules :=
  (derivedPushforward f.toLRSHom.toShHom).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj F)

/-! ### The two clauses of Stacks 0B91 used, as propositions -/

/-- **The perfection half of [Stacks, Tag 0B91], clause (2)**, as a proposition: for every
proper morphism `f : X ⟶ S` of finite presentation and every `𝒪_X`-module `ℱ` of finite
presentation, flat over `S`, the object `Rf_*ℱ` of `D(𝒪_S)` is perfect.

It is proved as `perfectDerivedPushforward`, and, written out, as
`isPerfect_derivedPushforward_singleFunctor_of_isProper`. -/
public def PerfectDerivedPushforward : Prop :=
  ∀ {X S : Scheme.{u}} (f : X ⟶ S), FinitePresentation f → IsProper f →
    ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
      RingedSpace.IsPerfect.{u, u + 1} (X := S.toRingedSpace) (derivedPushforwardModule f F)

/-- **The base-change half of [Stacks, Tag 0B91], clause (2)**, as a proposition, in the
untensored form the source's proof uses it: for every cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

with `f` proper of finite presentation and every `𝒪_X`-module `ℱ` of finite presentation, flat
over `S`, there is an isomorphism `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ` in `D(𝒪_{S'})` — note the ordinary
pullback of `ℱ`, as the source's boldface demands.

It is proved as `baseChangeDerivedPushforward`, and, written out, follows from
`nonempty_derivedPullback_derivedPushforward_singleFunctor_iso`. -/
public def BaseChangeDerivedPushforward : Prop :=
  ∀ {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X),
    IsPullback g' f' f g → FinitePresentation f → IsProper f →
    ∀ F : X.Modules, F.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom F →
      Nonempty ((derivedPullback g.toLRSHom.toShHom).obj (derivedPushforwardModule f F) ≅
        derivedPushforwardModule f' ((Scheme.Modules.pullback g').obj F))

/-! ### The fibre Euler characteristic -/

/-- **The Euler characteristic of the derived fibres of `Rf_*ℱ`**, the function

`s ↦ ∑ (-1)^i dim_{κ(s)} H^i(Rf_*ℱ ⊗^L_{𝒪_S} κ(s))`

on `S`. This is the function the proof of [Stacks, Tag 0B9T] works with; the source states its
conclusion for `s ↦ χ(X_s, ℱ_s)`, and the implementation notes of this file say where the two
are identified. -/
public abbrev chiFibre {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (h : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (derivedPushforwardModule f F)) :
    S → ℤ :=
  DerivedFibreBetti.chiDerivedFibre S (derivedPushforwardModule f F) h

/-- **[Stacks, Tag 0B9T], the first conclusion.** For a proper morphism `f : X ⟶ S` of finite
presentation and an `𝒪_X`-module `ℱ` of finite presentation, flat over `S`, the Euler
characteristic of the derived fibres of `Rf_*ℱ` is a locally constant function on `S`.

`Rf_*ℱ` is perfect by the perfection half of [Stacks, Tag 0B91] (2),
`isPerfect_derivedPushforward_singleFunctor_of_isProper`, and this is [Stacks, Tag 0BDJ] at
`Rf_*ℱ`. -/
@[stacks 0B9T "the local constancy conclusion, with the function in the derived-fibre form \
s |-> sum (-1)^i dim_k(s) H^i(Rf_*F tensor^L k(s)) that the source's proof passes to. Rf_*F is \
perfect by Tag 0B91 (2), proved as isPerfect_derivedPushforward_singleFunctor_of_isProper, and \
the conclusion is Tag 0BDJ at Rf_*F. The identification with s |-> chi(X_s, F_s) and the \
statement in that form are in ProperFlatFibreEulerCharacteristicUnconditional.lean \
(isLocallyConstant_fibreEulerCharacteristic). The base-change conclusion is chiFibre_baseChange"]
public theorem isLocallyConstant_chiFibre
    {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) :
    IsLocallyConstant (chiFibre f F
      (DerivedFibreBetti.isPseudoCoherent_of_isPerfect _
        (isPerfect_derivedPushforward_singleFunctor_of_isProper f hf hproper F hfp hflat))) :=
  DerivedFibreBetti.isLocallyConstant_chiDerivedFibre S (derivedPushforwardModule f F)
    (isPerfect_derivedPushforward_singleFunctor_of_isProper f hf hproper F hfp hflat)

/-- **[Stacks, Tag 0B9T], the second conclusion.** Formation of the Euler characteristic of the
derived fibres of `Rf_*ℱ` commutes with base change: for a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

the function on `S'` attached to `f'` and `(g')^*ℱ` is the function on `S` attached to `f` and
`ℱ`, composed with `g`.

The base-change isomorphism `Lg^*Rf_*ℱ ≅ Rf'_*(g')^*ℱ` is the base-change half of
[Stacks, Tag 0B91] (2), `nonempty_derivedPullback_derivedPushforward_singleFunctor_iso`; with it,
this is the base-change clause of [Stacks, Tag 0BDI] summed over the degrees,
`AlgebraicGeometry.DerivedFibreBetti.chiDerivedFibre_derivedPullback`, together with the
invariance of the derived-fibre Euler characteristic under isomorphism. The function is defined
from a proof of pseudo-coherence of each object, `hpc` and `hpc'`; the equality holds for every
such proof. -/
@[stacks 0B9T "the base-change conclusion ('formation of this function commutes with base \
change'), with the function in the derived-fibre form s |-> sum (-1)^i dim_k(s) H^i(Rf_*F \
tensor^L k(s)), for every cartesian square. The isomorphism Lg^*Rf_*F = Rf'_*(g')^*F is Tag 0B91 \
(2), proved as nonempty_derivedPullback_derivedPushforward_singleFunctor_iso; the conclusion is \
then Tag 0BDI summed over the degrees, chiDerivedFibre_derivedPullback, and invariance under \
isomorphism, chiDerivedFibre_congr. hpc and hpc' are the pseudo-coherence proofs the function is \
built from, and the equality holds for all of them. The statement for s |-> chi(X_s, F_s) itself \
is fibreEulerCharacteristic_baseChange in ProperFlatFibreEulerCharacteristicUnconditional.lean. \
The local constancy conclusion is isLocallyConstant_chiFibre"]
public theorem chiFibre_baseChange
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
    (hsq : IsPullback g' f' f g) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hpc : RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) (derivedPushforwardModule f F))
    (hpc' : RingedSpace.IsPseudoCoherent (X := S'.toRingedSpace)
      (derivedPushforwardModule f' ((Scheme.Modules.pullback g').obj F))) :
    chiFibre f' ((Scheme.Modules.pullback g').obj F) hpc' =
      chiFibre f F hpc ∘ g.base := by
  have : QuasiCompact f := hf.2.1
  have := hproper
  have := hfp
  obtain ⟨e⟩ := nonempty_derivedPullback_derivedPushforward_singleFunctor_iso hsq F
    (Stacks.Modules.isQuasicoherent_of_isFinitePresentation F)
    (Stacks.Modules.isQuasicoherent_of_isFinitePresentation _) hflat
  refine Eq.trans ?_
    (DerivedFibreBetti.chiDerivedFibre_derivedPullback g (derivedPushforwardModule f F) hpc)
  exact (DerivedFibreBetti.chiDerivedFibre_congr S' _ _ e).symm

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
