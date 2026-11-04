module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushPull
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativeInverseImageUnitSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.BoxProductFunctor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderRelativeModules

/-!
# The comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖`

Let `a : X ⟶ S` and `b : Y ⟶ S` be morphisms of schemes, let `W = X ×_S Y` with projections
`p` and `q`, and write `f = p ∘ a = q ∘ b`. A finite-order differential operator on `X/S` is
`a^{-1}𝒪_S`-linear, so a quasi-coherent `𝒪_X`-module read over `a^{-1}𝒪_S` has an inverse image
`p^{-1}𝓕`, a module over `f^{-1}𝒪_S`, functorially in differential operators. This file forms
the two bifunctors

`(𝓕, 𝓖) ↦ p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖`  and  `(𝓕, 𝓖) ↦ 𝓕 ⊠ 𝓖`

of `f^{-1}𝒪_S`-modules on `W` and the canonical morphism between them, in each pair of degrees.

## Main definitions

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.leftRelativeInverseImage` and
  `rightRelativeInverseImage`: the two functors `𝓕 ↦ p^{-1}𝓕` and `𝓖 ↦ q^{-1}𝓖` from the
  categories of finite-order differential operators on `X/S` and on `Y/S` to the
  `f^{-1}𝒪_S`-modules on `W`.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeInverseImageTensor`: **the
  bifunctor `(𝓕, 𝓖) ↦ p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖`.**
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.boxProductRelative`: the bifunctor
  `(𝓕, 𝓖) ↦ 𝓕 ⊠ 𝓖` of [Stacks, Tag 0G46], read over `f^{-1}𝒪_S`.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.relativeBoxComparison`: **the
  comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖`**, the composite of its two legs
  `relativeBoxComparisonLeg₁` and `relativeBoxComparisonLeg₂` through `relativeBoxMid`.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory`
  `.relativeInverseImageToPullbackOfFactors`: the comparison `p^{-1}𝓕 ⟶ p^*𝓕` of
  `g^{-1}𝒪_S`-modules for a morphism `g` presented as a factorization `p ∘ a`, and
  `sndRelativeInverseImageToPullback`, its instance for the second projection of a fibre
  product.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory`
  `.relativeInverseImageToPullbackOfFactors_rfl` and
  `relativeInverseImageProjectionOfFactors_rfl`: **the characterisation of the transported
  comparison and of the transported projection**: at the literal composite they are the
  comparison `p^{-1}𝓕 ⟶ p^*𝓕` and the canonical morphism of ringed spaces of
  `Stacks.DeRhamDirectImage`. Together with the definition of `relativeBoxComparison` as the
  tensor product of the two comparisons followed by the lax comparison
  `Stacks.DeRhamDirectImage.inverseImageTensorLax` of restriction of scalars along
  `f^{-1}𝒪_S ⟶ 𝒪_W`, this pins the comparison: nothing is chosen, since each comparison is
  characterised by its transpose along `p^{-1} ⊣ p_*`
  (`Stacks.DeRhamDirectImage.homEquiv_relativeInverseImageToPullback`) and the lax comparison
  carries a pure tensor to the same pure tensor read over the larger ring
  (`Stacks.DeRhamDirectImage.inverseImageTensorLax_toTensorSheafSection`).

## Implementation notes

*Why the lax comparison and not the tensorator of the direct image.* Restriction of scalars
along `f^{-1}𝒪_S ⟶ 𝒪_W` is also lax monoidal as the right adjoint of the monoidal pullback
(`Stacks.PushforwardGradedAlgebra.pushforwardFunctorLaxMonoidal`), and its tensorator has the
same source and target. The two agree, but the identification is the open dedup recorded in the
"Not done here" section of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit`: it
is equivalent to comparing the tensorator of
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` with the comparison of [Stacks, Tag 01CD],
for which only the site-level computation
(`Stacks.PullbackTensorSectionsSite.delta_pullbackStrictMonoidal_pullSec_tmul`) exists. The
tensorator therefore has no formula on local sections, and a comparison with no formula on
sections is not natural in *differential operators*: a differential operator is not
`𝒪_W`-linear, so the naturality of a tensorator — which is naturality in `𝒪_W`-linear maps —
says nothing about it. `inverseImageTensorLax` does have a section formula, and
`StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxComparisonSections` turns it into the evaluation
of this comparison on the sections attached to a pair of local sections, which is the shape in
which `boxHom_externalTensorSection` decides the naturality in differential operators that
step (5) of [Stacks, Tag 0G4A] needs; that naturality is
`relativeBoxComparison_naturality`, in
`StacksFrontier.AlgebraicGeometry.DeRham.DiffOpBoxComparisonNaturality`.

*The comparison is split into two named legs.* `relativeBoxComparisonLeg₁` and
`relativeBoxComparisonLeg₂` have ascribed types meeting at `relativeBoxMid`, and
`relativeBoxComparison` is their composite. Written as one composite instead, merely stating
`relativeBoxComparison_eq` exhausted the elaboration budget: the equation makes the elaborator
unify `(boxProductRelative a b).obj (𝓕, 𝓖)` with the direct image of the `𝒪_W`-tensor product
from scratch, whereas with the legs both sides are the same two constants.

The two projections give the *same* morphism `W ⟶ S` only up to `pullback.condition`, so the
ringed space `(W, q^{-1}𝒪_S)` built from the second projection is not literally the one built
from the first. The transport is made once, inside
`relativeInverseImageProjectionOfFactors` and `relativeInverseImageToPullbackOfFactors`, by
taking the morphism `W ⟶ S` as a variable constrained by a factorization hypothesis and
substituting it; no `eqToHom` then appears in any statement. This is the idiom of
`Stacks.DeRhamDirectImage.relativePushforwardHigherIsoOfFactors` in the same situation.

No monoidal structure on `Modules` is used. The tensor product of [Stacks, Tag 01CA] is taken
in its bare spelling, the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor`, with its
uncurried action on pairs of morphisms; the monoidal tensor product of
`Stacks.PullbackGradedAlgebra.monoidalCategory` is that sheaf on the nose, but instance search
does not cross the abbreviation `Modules`, so using it would need the instance restated at these
binders for no gain.

## References

* [Stacks Project, Tag 0G45](https://stacks.math.columbia.edu/tag/0G45)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DeRhamDirectImage

universe u

namespace AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

variable {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

section Factors

variable {W X' S' : Scheme.{u}} (p : W ⟶ X') (c : X' ⟶ S') (g : W ⟶ S') (hg : p ≫ c = g)

/-- The canonical morphism of ringed spaces `(W, g^{-1}𝒪_{S'}) ⟶ (X', c^{-1}𝒪_{S'})` over `p`,
for a morphism `g` presented as a factorization `p ∘ c` rather than literally equal to it. -/
def relativeInverseImageProjectionOfFactors : inverseImageBase g ⟶ inverseImageBase c :=
  hg ▸ relativeInverseImageProjection p c

/-- At the literal composite the transported morphism is the canonical one. -/
theorem relativeInverseImageProjectionOfFactors_rfl :
    relativeInverseImageProjectionOfFactors p c (p ≫ c) rfl =
      relativeInverseImageProjection p c :=
  rfl

/-- **The comparison `p^{-1}𝓕 ⟶ p^*𝓕`** of `g^{-1}𝒪_{S'}`-modules, for a morphism `g` presented
as a factorization `p ∘ c`. -/
def relativeInverseImageToPullbackOfFactors (F : Modules X'.toRingedSpace) :
    (_root_.pullback (relativeInverseImageProjectionOfFactors p c g hg)).obj
        ((pushforward (toInverseImageBase c)).obj F) ⟶
      (pushforward (toInverseImageBase g)).obj
        ((_root_.pullback p.toLRSHom.toShHom).obj F) := by
  subst hg
  exact relativeInverseImageToPullback p c F

/-- At the literal composite the transported comparison is `p^{-1}𝓕 ⟶ p^*𝓕`. -/
theorem relativeInverseImageToPullbackOfFactors_rfl (F : Modules X'.toRingedSpace) :
    relativeInverseImageToPullbackOfFactors p c (p ≫ c) rfl F =
      relativeInverseImageToPullback p c F :=
  rfl

end Factors

/-- The canonical morphism of ringed spaces `(W, f^{-1}𝒪_S) ⟶ (Y, b^{-1}𝒪_S)` over the second
projection, with `f = p ∘ a`: the two projections of a fibre product compose to the same
morphism to the base, so the source may be read through the first projection. -/
def sndRelativeInverseImageProjection :
    inverseImageBase (pullback.fst a b ≫ a) ⟶ inverseImageBase b :=
  relativeInverseImageProjectionOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
    pullback.condition.symm

/-- **The comparison `q^{-1}𝓖 ⟶ q^*𝓖`** of `f^{-1}𝒪_S`-modules on `X ×_S Y`, with `f = p ∘ a`:
the comparison for the second projection, read over the ringed space attached to the first. -/
def sndRelativeInverseImageToPullback (G : Modules Y.toRingedSpace) :
    (_root_.pullback (sndRelativeInverseImageProjection a b)).obj
        ((pushforward (toInverseImageBase b)).obj G) ⟶
      (pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G) :=
  relativeInverseImageToPullbackOfFactors (pullback.snd a b) b (pullback.fst a b ≫ a)
    pullback.condition.symm G

/-- **The inverse image `𝓕 ↦ p^{-1}𝓕`** along the first projection, from the finite-order
differential operators on `X/S` to the `f^{-1}𝒪_S`-modules on `X ×_S Y`. -/
abbrev leftRelativeInverseImage :
    FiniteOrderDifferentialOperatorCategory a ⥤
      Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  toInverseImageModules a ⋙ relativeInverseImage (pullback.fst a b) a

/-- **The inverse image `𝓖 ↦ q^{-1}𝓖`** along the second projection, from the finite-order
differential operators on `Y/S` to the `f^{-1}𝒪_S`-modules on `X ×_S Y`. -/
abbrev rightRelativeInverseImage :
    FiniteOrderDifferentialOperatorCategory b ⥤
      Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  toInverseImageModules b ⋙ _root_.pullback (sndRelativeInverseImageProjection a b)

/-- **The bifunctor `(𝓕, 𝓖) ↦ p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖`** of `f^{-1}𝒪_S`-modules on
`X ×_S Y`, the source of the comparison with the external tensor product. -/
abbrev relativeInverseImageTensor :
    FiniteOrderDifferentialOperatorCategory a × FiniteOrderDifferentialOperatorCategory b ⥤
      Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  Functor.prod (leftRelativeInverseImage a b) (rightRelativeInverseImage a b) ⋙
    Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
        (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)

/-- **The bifunctor `(𝓕, 𝓖) ↦ 𝓕 ⊠ 𝓖` read over `f^{-1}𝒪_S`**: the external tensor product of
[Stacks, Tag 0G46], with its `𝒪_W`-module structure restricted along `f^{-1}𝒪_S ⟶ 𝒪_W`. This
is the target of the comparison with the relative tensor product of the inverse images. -/
abbrev boxProductRelative :
    FiniteOrderDifferentialOperatorCategory a × FiniteOrderDifferentialOperatorCategory b ⥤
      Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  boxProductFunctor a b ⋙ toInverseImageModules (pullback.fst a b ≫ a)

/-- The tensor product over `f^{-1}𝒪_S` of the restrictions of scalars of `p^*𝓕` and `q^*𝓖`
along `f^{-1}𝒪_S ⟶ 𝒪_W`, as an `f^{-1}𝒪_S`-module on `X ×_S Y`. -/
abbrev relativeBoxMid (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    Modules (inverseImageBase (pullback.fst a b ≫ a)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
        (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩).obj
    ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
      ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module))).obj
    ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
      ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module))

/-- **The first leg of the comparison**: the tensor product of `p^{-1}𝓕 ⟶ p^*𝓕` with
`q^{-1}𝓖 ⟶ q^*𝓖`, landing in the tensor product over `f^{-1}𝒪_S` of the two restrictions of
scalars. -/
def relativeBoxComparisonLeg₁ (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    (relativeInverseImageTensor a b).obj (F, G) ⟶ relativeBoxMid a b F G :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
        (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)).map
    (X := ((relativeInverseImage (pullback.fst a b) a).obj
        ((pushforward (toInverseImageBase a)).obj F.module),
      (_root_.pullback (sndRelativeInverseImageProjection a b)).obj
        ((pushforward (toInverseImageBase b)).obj G.module)))
    (Y := ((pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module),
      (pushforward (toInverseImageBase (pullback.fst a b ≫ a))).obj
        ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module)))
    (relativeInverseImageToPullback (pullback.fst a b) a F.module,
      sndRelativeInverseImageToPullback a b G.module) :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(inverseImageBase (pullback.fst a b ≫ a)).presheaf,
        (inverseImageBase (pullback.fst a b ≫ a)).IsSheaf⟩)).obj
      ((relativeInverseImage (pullback.fst a b) a).obj
          ((pushforward (toInverseImageBase a)).obj F.module),
        (_root_.pullback (sndRelativeInverseImageProjection a b)).obj
          ((pushforward (toInverseImageBase b)).obj G.module)) ⟶ relativeBoxMid a b F G)

/-- **The second leg of the comparison**: the lax comparison of the tensor product with
restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_W`. -/
def relativeBoxComparisonLeg₂ (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    relativeBoxMid a b F G ⟶ (boxProductRelative a b).obj (F, G) :=
  inverseImageTensorLax (pullback.fst a b ≫ a)
    ((_root_.pullback (pullback.fst a b).toLRSHom.toShHom).obj F.module)
    ((_root_.pullback (pullback.snd a b).toLRSHom.toShHom).obj G.module)

/-- **The comparison `p^{-1}𝓕 ⊗_{f^{-1}𝒪_S} q^{-1}𝓖 ⟶ 𝓕 ⊠ 𝓖`** of `f^{-1}𝒪_S`-modules on
`X ×_S Y`: the two comparisons `p^{-1}𝓕 ⟶ p^*𝓕` and `q^{-1}𝓖 ⟶ q^*𝓖` tensored together,
followed by the lax comparison
`(p^*𝓕)|_{f^{-1}𝒪_S} ⊗_{f^{-1}𝒪_S} (q^*𝓖)|_{f^{-1}𝒪_S} ⟶ (p^*𝓕 ⊗_{𝒪_W} q^*𝓖)|_{f^{-1}𝒪_S}`
of restriction of scalars along `f^{-1}𝒪_S ⟶ 𝒪_W`. -/
def relativeBoxComparison (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    (relativeInverseImageTensor a b).obj (F, G) ⟶ (boxProductRelative a b).obj (F, G) :=
  relativeBoxComparisonLeg₁ a b F G ≫ relativeBoxComparisonLeg₂ a b F G

/-- The comparison `relativeBoxComparison` is the composite of `relativeBoxComparisonLeg₁` and
`relativeBoxComparisonLeg₂`. -/
theorem relativeBoxComparison_eq (F : FiniteOrderDifferentialOperatorCategory a)
    (G : FiniteOrderDifferentialOperatorCategory b) :
    relativeBoxComparison a b F G =
      relativeBoxComparisonLeg₁ a b F G ≫ relativeBoxComparisonLeg₂ a b F G :=
  rfl

end AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory

end
