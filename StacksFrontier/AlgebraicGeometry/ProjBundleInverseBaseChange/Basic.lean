module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.AlgebraicGeometry.TensorPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.PullbackIsos
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Base change of the inverse of an invertible module sheaf

Tag 0B3V compares the conormal sheaf of a section of a projective bundle across a base change,
and the left-hand side of that comparison is the tensor product of the kernel of the quotient
with the **inverse** of the quotient line bundle. The comparison therefore needs, as one of its
two inputs, an identification

`g^*(L^{⊗ -1}) ≅ (L')^{⊗ -1}` for `g : X' ⟶ X` and `L' ≅ g^* L`,

which is the `inverseQuotientBaseChangeIso` of Tag 0B3V. **This file constructs it**, under library
names.

`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` already has `g^*(L^{⊗ n}) ≅ (g^*L)^{⊗ n}`
for a *natural number* `n`, and `Stacks.AlgebraicGeometry.ProjRepresentsF1.`
`pullbackTensorPowerIso` has the same for the `SheafOfModules.tensorPower` family; both are
inductions on `n` out of Tag 01CD, and neither reaches a negative exponent, where the power is
no longer an iterated tensor product but the image of the structure sheaf under the *inverse* of
the autoequivalence "tensor by `L`". The negative case is what is supplied here, and the route
is not an induction at all.

## The route

The whole construction rests on a lemma of pure monoidal-category theory which this repository
did not have: **a two-sided tensor inverse is unique up to canonical isomorphism**
(`Stacks.TensorPowers.TensorInverse.invIso`). No braiding is needed for it —

`M ≅ M ⊗ 𝟙 ≅ M ⊗ (L ⊗ N) ≅ (M ⊗ L) ⊗ N ≅ 𝟙 ⊗ N ≅ N`

uses the right trivialization of one inverse and the left trivialization of the other. Given it,
the construction is three short steps:

1. `negOneTensorInverse`: the `(-1)`st tensor power of Tag 01CU *is* a two-sided tensor inverse.
   The one-sided trivialization is the successor comparison
   `Stacks.SheafOfModules.TensorPower.tensorPowerSuccIso` at `n = -1`, reindexed to degree zero;
   the other side is that one composed with
   `Stacks.SheafOfModules.tensorSheafBraiding`. The braiding is used on
   `Stacks.SheafOfModules.Tensor.sheafTensor` directly, so no `BraidedCategory`
     instance has to be put on the
   category of sheaves of modules.
2. `pullbackTensorInverse`: the pullback of a two-sided tensor inverse along a morphism of
   schemes is a two-sided tensor inverse of the pullback. This is Tag 01CD (as
   `pullbackTensorIso`) together with `g^* 𝒪_X ≅ 𝒪_{X'}`, and nothing else; in particular it
   needs no invertibility hypothesis of its own.
3. `inverseQuotientBaseChangeIso` is `TensorInverse.invIso` applied to the two tensor inverses of
   `g^* L` that steps 1 and 2 produce — the second transported along `L' ≅ g^* L` by
   `Stacks.TensorPowers.TensorInverse.ofIso`.

## Main definitions

* `Stacks.TensorPowers.TensorInverse.invIso`: **two two-sided tensor inverses of the same object
  of a monoidal category are canonically isomorphic.**
* `Stacks.TensorPowers.TensorInverse.ofIso`: a tensor inverse of `M` is a tensor inverse of
  anything isomorphic to `M`.
* `Stacks.ProjBundleInverseBaseChange.negOneTensorInverse`: **Tag 01CU's `(-1)`st tensor power is
  a two-sided tensor inverse**, with both trivializations.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` and `pullbackUnitMonoidalIso`: Tag 01CD
  and `g^* 𝒪_X ≅ 𝒪_{X'}` for the monoidal structure on `X.Modules`, i.e. with `⊗` and `𝟙_`
  rather than `Stacks.SheafOfModules.Tensor.sheafTensor` and `SheafOfModules.unit`.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorInverse`: the pullback of a two-sided tensor
  inverse.
* `Stacks.ProjBundleInverseBaseChange.pullbackTensorPowerNegOneIso`: **`g^*(L^{⊗ -1}) ≅
  (g^*L)^{⊗ -1}`.**
* `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso`: **`g^*(L^{⊗ -1}) ≅
  (L')^{⊗ -1}` for any `L' ≅ g^* L`.** This is Tag 0B3V's `inverseQuotientBaseChangeIso`,
  restated over library names.

## Implementation notes

**The spelling, and why `Mods` exists.** The tensor powers of Tag 01CU and this repository's
`Stacks.SheafOfModules.IsInvertible` are stated over
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪`, while
`AlgebraicGeometry.Scheme.Modules.pullback` is stated over `X.Modules`. The two types are equal
by `Stacks.SheafInternalHom.structureSheaf_eq_ringCatSheaf`, which is `rfl`, but
`Stacks.SheafInternalHom.monoidalCategory` does **not** synthesize for `X.Modules`, which is a
`def`. Nor does it synthesize for
`SheafOfModules.{u} (structureSheaf X.presheaf X.ringCatSheaf.2)` either, because unifying the
*type* of `X.ringCatSheaf.2` with `Presheaf.IsSheaf ?J (structureRingPresheaf ?𝒪)` has to unfold
`X.ringCatSheaf`. Writing the sheaf condition as
`Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X` makes the match syntactic and the
instance is found. `Mods X` is that spelling, as an `abbrev`, and
`Stacks.ProjBundleInverseBaseChange.pullbackFunctor` is `Scheme.Modules.pullback` read at it --
by `rfl`, with no transport. A caller holding `X.Modules` objects is unaffected: the sheaf
conditions are propositions, so the two spellings are definitionally equal.

**Both comparisons use the canonical tensor product.**
`Stacks.SheafOfModules.Tensor.sheafTensor` supplies the tensor objects in Tags 01CU and 01CD.
Thus `pullbackTensorIso` composes the two library isomorphisms without a spelling comparison.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)

## Not done here

**No tag of Tag 0B3V is attached, and none is earned.** `inverseQuotientBaseChangeIso` is one of
the unlabelled definitions of Tag 0B3V: of its nine `@[stacks 0B3V "..."]` labels it is used
only by `conormal isomorphism compatible with base change`, whose other inputs — the bijection
between sections and invertible quotients, and the projective-bundle base-change comparison —
are not available. The companion normalization `inverseQuotientBaseChangeIso_evaluation`, which
pins this isomorphism down by the evaluation pairings against `g^*L`, carries no label either and
is not proved *here*: it is the compatibility of `Stacks.TensorPowers.TensorInverse.invIso` with
the two trivializations, a statement about the isomorphism constructed here rather than a further
construction, and it is proved in the sibling module
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Evaluation`. That normalization is an
equation between morphisms. Reading it **on a section** needs the three constraints of
`Stacks.SheafInternalHom.monoidalCategory` on a product section — the two unitors and the
associator — and those **are** supplied, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalLocalizedSections`; the reading itself is
`Stacks.ProjBundleInverseBaseChange.invIso_inv_val_app`, in the sibling module
`StacksFrontier.AlgebraicGeometry.ProjBundleInverseBaseChange.Sections`. The pairing hypothesis
`hpair` which that reading feeds is itself discharged, on a chart, by
`Stacks.ProjectiveBundleConormal.tensorPairing_chartTrivialisation_eq_unitSection`.

**Only the exponent `-1`.** The general `g^*(L^{⊗ n}) ≅ (g^*L)^{⊗ n}` for every `n : ℤ` at this
spelling is not proved. The positive half is a one-directional induction out of
`pullbackTensorIso`, but the negative half beyond `-1` needs the multiplication isomorphisms
`L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n + m)}` of Tag 01CU, which at this pin exist only as the
existential `Stacks.SheafOfModules.TensorPower.TensorPowerCoherence` and not as a chosen family.
Nothing in Tag 0B3V needs an exponent other than `-1`.
-/

@[expose] public noncomputable section

universe v u w

open CategoryTheory MonoidalCategory Limits AlgebraicGeometry

namespace Stacks.TensorPowers

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Two two-sided tensor inverses of the same object are canonically isomorphic.**

`h.inv ≅ h.inv ⊗ 𝟙 ≅ h.inv ⊗ (L ⊗ k.inv) ≅ (h.inv ⊗ L) ⊗ k.inv ≅ 𝟙 ⊗ k.inv ≅ k.inv`, using the
left trivialization of `h` and the right trivialization of `k`. No braiding is involved, so this
holds in an arbitrary monoidal category. -/
public def TensorInverse.invIso {L : C} (h k : TensorInverse L) : h.inv ≅ k.inv :=
  (ρ_ h.inv).symm ≪≫ whiskerLeftIso h.inv k.mulIso.symm ≪≫
    (α_ h.inv L k.inv).symm ≪≫ whiskerRightIso h.mulIso' k.inv ≪≫ λ_ k.inv

/-- A two-sided tensor inverse of `M` is a two-sided tensor inverse of any `L ≅ M`: the
trivializations are transported by whiskering the isomorphism into the appropriate factor. -/
public def TensorInverse.ofIso {L M : C} (e : L ≅ M) (h : TensorInverse M) :
    TensorInverse L where
  inv := h.inv
  mulIso := whiskerRightIso e h.inv ≪≫ h.mulIso
  mulIso' := whiskerLeftIso h.inv e ≪≫ h.mulIso'

end Stacks.TensorPowers

namespace Stacks.ProjBundleInverseBaseChange

open Stacks.SheafOfModules.TensorSheafification Stacks.TensorPowers Stacks.SheafOfModules
open Stacks.SheafOfModules.TensorPower
open Stacks.AlgebraicGeometry.ProjRepresentsF1 (pullbackTensorSchemeIso)
open Stacks.SheafInternalHom (isSheaf_structureRingPresheaf)

attribute [local instance] Stacks.SheafInternalHom.monoidalCategory

/-! ### Tag 01CU's `(-1)`st tensor power is a two-sided tensor inverse -/

section Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [Stacks.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- **The right trivialization `L^{⊗ -1} ⊗ L ≅ 𝟙`.** This is the successor comparison of Tag
01CU at `n = -1`, which lands in `L^{⊗ (-1 + 1)}`, reindexed to `L^{⊗ 0}` and read as the
monoidal unit. -/
public def negOneMulIso :
    tensorPower 𝒪 h𝒪 L (-1) ⊗ L ≅ 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) L ≪≫
    tensorPowerSuccIso 𝒪 h𝒪 L (-1) ≪≫
    tensorPowerReindex 𝒪 h𝒪 L (show (-1 : ℤ) + 1 = 0 by omega) ≪≫
    eqToIso (tensorPower_zero 𝒪 h𝒪 L) ≪≫
    (AlgebraicGeometry.SheafOfModules.unitIso 𝒪 h𝒪).symm

/-- **The left trivialization `L ⊗ L^{⊗ -1} ≅ 𝟙`.** The right trivialization composed with
`Stacks.SheafOfModules.tensorSheafBraiding`, which is used on
  `Stacks.SheafOfModules.Tensor.sheafTensor` itself, so
that no `BraidedCategory` instance on sheaves of modules is needed. -/
public def negOneMulIso' :
    L ⊗ tensorPower 𝒪 h𝒪 L (-1) ≅ 𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) :=
  AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 L (tensorPower 𝒪 h𝒪 L (-1)) ≪≫
    tensorSheafBraiding 𝒪 h𝒪 L (tensorPower 𝒪 h𝒪 L (-1)) ≪≫
    (AlgebraicGeometry.SheafOfModules.tensorIso 𝒪 h𝒪 (tensorPower 𝒪 h𝒪 L (-1)) L).symm ≪≫
    negOneMulIso 𝒪 h𝒪 L

/-- **The `(-1)`st tensor power of Tag 01CU is a two-sided tensor inverse of `L`.** -/
public def negOneTensorInverse : TensorInverse L where
  inv := tensorPower 𝒪 h𝒪 L (-1)
  mulIso := negOneMulIso' 𝒪 h𝒪 L
  mulIso' := negOneMulIso 𝒪 h𝒪 L

end Site

/-! ### The monoidal structure and the pullback, on a scheme -/

section Scheme

variable {X X' : Scheme.{u}} (g : X' ⟶ X)

/-- The sheaves of modules on `X`, at the
  `Stacks.SheafOfModules.TensorSheafification.structureSheaf` spelling over which the
tensor powers of Tag 01CU, this repository's invertibility and the monoidal structure are all
stated. Definitionally `X.Modules`; see the implementation notes for why the sheaf condition is
written this way. -/
public abbrev Mods (X : Scheme.{u}) : Type (u + 1) :=
  SheafOfModules.{u} (structureSheaf X.presheaf (isSheaf_structureRingPresheaf X))

/-- `AlgebraicGeometry.Scheme.Modules.pullback` read at the `Mods` spelling, by `rfl`. -/
public def pullbackFunctor : Mods X ⥤ Mods X' := Scheme.Modules.pullback g

/-- **Stacks Tag 01CD for the monoidal tensor product**: `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N`. This is
`Stacks.AlgebraicGeometry.ProjRepresentsF1.pullbackTensorSchemeIso` with
`AlgebraicGeometry.SheafOfModules.tensorIso` on each side to pass between `⊗` and
`Stacks.SheafOfModules.Tensor.sheafTensor`; no spelling comparison is needed. -/
public def pullbackTensorIso (M N : Mods X) :
    (pullbackFunctor g).obj (M ⊗ N) ≅
      (pullbackFunctor g).obj M ⊗ (pullbackFunctor g).obj N :=
  (pullbackFunctor g).mapIso (AlgebraicGeometry.SheafOfModules.tensorIso X.presheaf
      (isSheaf_structureRingPresheaf X) M N) ≪≫
    pullbackTensorSchemeIso g M N ≪≫
    (AlgebraicGeometry.SheafOfModules.tensorIso X'.presheaf
      (isSheaf_structureRingPresheaf X') ((pullbackFunctor g).obj M)
      ((pullbackFunctor g).obj N)).symm

/-- **The pullback of the monoidal unit is the monoidal unit**: `g^* 𝒪_X ≅ 𝒪_{X'}`. This is
`AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` with
`AlgebraicGeometry.SheafOfModules.unitIso` on each side. -/
public def pullbackUnitMonoidalIso :
    (pullbackFunctor g).obj (𝟙_ (Mods X)) ≅ 𝟙_ (Mods X') :=
  (pullbackFunctor g).mapIso
      (AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (isSheaf_structureRingPresheaf X)) ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g ≪≫
    (AlgebraicGeometry.SheafOfModules.unitIso X'.presheaf
      (isSheaf_structureRingPresheaf X')).symm

/-- **The pullback of a two-sided tensor inverse is a two-sided tensor inverse of the pullback.**
The two trivializations are the given ones carried through `pullbackTensorIso` and
`pullbackUnitMonoidalIso`; no invertibility hypothesis is used, only that the pullback functor is
monoidal in the two components that the trivializations mention. -/
public def pullbackTensorInverse (L : Mods X) (h : TensorInverse L) :
    TensorInverse ((pullbackFunctor g).obj L) where
  inv := (pullbackFunctor g).obj h.inv
  mulIso := (pullbackTensorIso g L h.inv).symm ≪≫
    (pullbackFunctor g).mapIso h.mulIso ≪≫ pullbackUnitMonoidalIso g
  mulIso' := (pullbackTensorIso g h.inv L).symm ≪≫
    (pullbackFunctor g).mapIso h.mulIso' ≪≫ pullbackUnitMonoidalIso g

/-! ### Base change of the inverse -/

variable (L : Mods X) [h : Stacks.SheafOfModules.IsInvertible X.presheaf
  (isSheaf_structureRingPresheaf X) L]

include h in
/-- **Stacks Tag 0B8L at the `Mods` spelling**: the pullback of an invertible module sheaf is
invertible.

This is `Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj`, whose statement writes the
sheaf condition as `X.ringCatSheaf.2`. The two spellings are definitionally equal by proof
irrelevance, but instance search does not cross between them, because matching the
*type* of `X.ringCatSheaf.2` against `Presheaf.IsSheaf ?J (structureRingPresheaf ?𝒪)` has to
unfold `Scheme.ringCatSheaf`, which it will not do. The instance is therefore applied explicitly,
which forces the check at default transparency, where it succeeds. -/
public instance isInvertible_pullbackFunctor_obj :
    Stacks.SheafOfModules.IsInvertible X'.presheaf (isSheaf_structureRingPresheaf X')
      ((pullbackFunctor g).obj L) :=
  @_root_.Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj X X' g L h

/-- **Pullback commutes with the `(-1)`st tensor power**: `g^*(L^{⊗ -1}) ≅ (g^*L)^{⊗ -1}`.

Both sides are the inverse object of a two-sided tensor inverse of `g^* L` — the left by
`pullbackTensorInverse` applied to `negOneTensorInverse`, the right by `negOneTensorInverse` for
`g^* L`, which is invertible by Tag 0B8L — so `Stacks.TensorPowers.TensorInverse.invIso`
identifies them. Unlike the nonnegative case this is not an induction on the exponent. -/
public def pullbackTensorPowerNegOneIso :
    (pullbackFunctor g).obj
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) ≅
      tensorPower X'.presheaf (isSheaf_structureRingPresheaf X')
        ((pullbackFunctor g).obj L) (-1) :=
  TensorInverse.invIso
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L))
    (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X')
      ((pullbackFunctor g).obj L))

/-- **Tag 0B3V's `inverseQuotientBaseChangeIso`, under library names.** For `g : X' ⟶ X`, an
invertible `L` on `X`, an invertible `L'` on `X'` and a comparison `hL : L' ≅ g^* L`, the
pullback of the inverse of `L` is the inverse of `L'`:

`g^*(L^{⊗ -1}) ≅ (L')^{⊗ -1}`.

`negOneTensorInverse` for `L'`, transported along `hL.symm` by
`Stacks.TensorPowers.TensorInverse.ofIso`, is a two-sided tensor inverse of `g^* L` whose
inverse object is `(L')^{⊗ -1}`; the pullback of `negOneTensorInverse` for `L` is another, whose
inverse object is `g^*(L^{⊗ -1})`; and `Stacks.TensorPowers.TensorInverse.invIso` identifies the
two. In particular no hypothesis relating `L'` to a *quotient* is used: Tag 0B3V states this
definition for arbitrary invertible quotients `Q`, `Q'` and uses only the comparison of their
targets, which is exactly `hL`. -/
public def inverseQuotientBaseChangeIso (L' : Mods X')
    [Stacks.SheafOfModules.IsInvertible X'.presheaf (isSheaf_structureRingPresheaf X') L']
    (hL : L' ≅ (pullbackFunctor g).obj L) :
    (pullbackFunctor g).obj
        (tensorPower X.presheaf (isSheaf_structureRingPresheaf X) L (-1)) ≅
      tensorPower X'.presheaf (isSheaf_structureRingPresheaf X') L' (-1) :=
  TensorInverse.invIso
    (pullbackTensorInverse g L
      (negOneTensorInverse X.presheaf (isSheaf_structureRingPresheaf X) L))
    (TensorInverse.ofIso hL.symm
      (negOneTensorInverse X'.presheaf (isSheaf_structureRingPresheaf X') L'))

end Scheme

end Stacks.ProjBundleInverseBaseChange

end
