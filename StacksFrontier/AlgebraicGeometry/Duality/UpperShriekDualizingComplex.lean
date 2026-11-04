module

public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexScheme
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Dualizing

/-!
# The exceptional inverse image of a dualizing complex is dualizing

Let `f : X ⟶ Y` be a morphism of schemes separated and of finite type over a Noetherian base,
that is, a morphism of the category `AlgebraicGeometry.FTS` of [Stacks, Tag 0F42]. If `K` is a
dualizing complex for `Y` then `f^!K` is a dualizing complex for `X`. This is
[Stacks, Tag 0AA3] (Lemma 48.17.7).

## Main definitions

* `Stacks.Duality.quasiCoherentDerivedCategoryPlus` — `D⁺_QCoh(𝒪_Z)`, the bounded-below part of
  the quasi-coherent derived category, which is the domain and codomain of `f^!`.
* `Stacks.Duality.IsTildeModelOn` — the modelling condition of
  `Stacks.Duality.HasDualizingModelOn` with the model named and with no requirement that the
  model be dualizing: `K|_U` is the associated sheaf of `ω ∈ D(Γ(X, U))`.

## Main results

* `Stacks.Duality.hasDualizingModelOn_of_isTildeModelOn` and
  `Stacks.Duality.exists_isTildeModelOn_of_hasDualizingModelOn` — the two halves of the
  identification of `Stacks.Duality.HasDualizingModelOn` with the existence of a dualizing
  `Stacks.Duality.IsTildeModelOn` model.
* `Stacks.Duality.isDualizingComplex_upperShriek_of_fts` — [Stacks, Tag 0AA3].

## Implementation notes

The exceptional inverse image is taken as an *explicit parameter together with its
characterising hypothesis*: `fShriek` is an argument, and the hypothesis `h0AA1` says what it
does on affine charts. Nothing is constructed, nothing is chosen, and no existence statement for
`f^!` is used. This is the idiom of `Stacks.Duality.sheafyTrace`, and it is why the statement
needs no compactification of `f`.

Two inputs of the source's proof are not available in this tree and appear as explicit
hypotheses, both named in the `@[stacks 0AA3]` description:

* `h0A86` is the conclusion of [Stacks, Tag 0A86], that being a dualizing complex may be checked
  on the members of a single affine open cover. The definition
  `Stacks.Duality.IsDualizingComplex` is deliberately the all-affine-open condition, and the
  equivalence with the one-cover condition is that tag's content, which is open; see the
  implementation notes of
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DualizingComplexScheme.lean`.
* `h0AA1` is the affine-chart description of `f^!`: over an affine `V ⊆ Y` and an affine
  `U ⊆ f⁻¹(V)`, the restriction of `f^!K` to `U` is the associated sheaf of the *algebraic* upper
  shriek, along a polynomial presentation of the chart ring map `f.appLE V U`, of a model of `K`
  on `V`. This is the content of [Stacks, Tag 0AA1] together with the affine comparison of
  [Stacks, Tag 0BV2]. Writing the chart ring map as `f.appLE V U` rather than as an arbitrary
  finite type homomorphism is what ties the hypothesis to `f`.

What is *proved* is the rest of the source's argument, and it is not formal: the affine charts of
`X` lying over affine opens of `Y` are produced and shown to cover `X`; the dualizing model of
`K` over each such `V` is extracted from the hypothesis that `K` is dualizing; the library's
[Stacks, Tag 0BZL], `Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex`,
upgrades that model to a dualizing complex over `Γ(X, U)`; and the resulting local models are
glued by `h0A86`. In particular the two carried hypotheses do not by themselves give the
conclusion: `h0AA1` says nothing about any complex being dualizing.

Both derived categories of a ring and of an affine open are read at
`HasDerivedCategory.standard`, which is the instance sealed inside the body of
`Stacks.Duality.HasDualizingModelOn`; the whole file is read at that instance so that the two
statements compose. The local attribute carries priority `10000` because the import closure
reaches `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, whose `HasDerivedCategory`
instances are global and would otherwise displace that choice.

## References

* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0BZL](https://stacks.math.columbia.edu/tag/0BZL)
* [Stacks Project, Tag 0F42](https://stacks.math.columbia.edu/tag/0F42)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

/-- `D⁺_QCoh(𝒪_Z)`: the bounded-below objects of the quasi-coherent derived category of a
scheme. The exceptional inverse image of [Stacks, Tag 0AA0] is a functor between these
categories, and a dualizing complex, having bounded coherent cohomology, lies in this part. -/
abbrev quasiCoherentDerivedCategoryPlus (Z : Scheme.{u}) : Type (u + 1) :=
  ObjectProperty.FullSubcategory (isBoundedBelowQuasiCoherent Z)

section TildeModel

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- `K` restricted to an affine open `U` is the associated sheaf of the complex `ω` over
`Γ(X, U)`, transported along `U ≅ Spec Γ(X, U)`.

This is the modelling condition inside `Stacks.Duality.HasDualizingModelOn` with the model `ω`
named as an argument, and with the requirement that `ω` be dualizing dropped. Naming the model
is what lets the chart description of `f^!` be stated separately from the statement that what it
produces is dualizing. -/
def IsTildeModelOn (K : DerivedCategory X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (ω : DerivedCategory (ModuleCat.{u} Γ(X, U))) : Prop :=
  Nonempty ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj K ≅
    (tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategory.obj ω)

/-- A dualizing model is a dualizing model: an `ω` which is a dualizing complex over `Γ(X, U)`
and models `K` on `U` witnesses `Stacks.Duality.HasDualizingModelOn`. -/
theorem hasDualizingModelOn_of_isTildeModelOn {K : DerivedCategory X.Modules} {U : X.Opens}
    {hU : IsAffineOpen U} [IsNoetherianRing Γ(X, U)]
    {ω : DerivedCategory (ModuleCat.{u} Γ(X, U))}
    (hω : Dualizing.IsDualizingComplex ω) (h : IsTildeModelOn K U hU ω) :
    HasDualizingModelOn K U hU :=
  ⟨ω, hω, h⟩

/-- Conversely, `Stacks.Duality.HasDualizingModelOn` hands back the model it asserts to exist,
together with the fact that it is a dualizing complex over `Γ(X, U)`. -/
theorem exists_isTildeModelOn_of_hasDualizingModelOn {K : DerivedCategory X.Modules}
    {U : X.Opens} {hU : IsAffineOpen U} [IsNoetherianRing Γ(X, U)]
    (h : HasDualizingModelOn K U hU) :
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U)),
      Dualizing.IsDualizingComplex ω ∧ IsTildeModelOn K U hU ω :=
  h

end TildeModel

/-- **Stacks Project, Tag 0AA3 (Lemma 48.17.7).** In Situation 48.16.1, let `f : X ⟶ Y` be a
morphism of `FTS S` and let `f^!` be an exceptional inverse image functor
`D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)` for it, in the sense that on affine charts it is the algebraic
upper shriek of a polynomial presentation of the chart ring map. If `K` is a dualizing complex
for `Y`, then `f^!K` is a dualizing complex for `X`. -/
@[stacks 0AU3 "clause (4)(a) of Section 48.19: the normalized complex f^! of a dualizing \
  complex is dualizing, under the same carried hypotheses as the Tag 0AA3 key below",
  stacks 0AA3 "granted the conclusion of Tag 0A86 (dualizing may be checked on one affine \
  cover) and the affine-chart description of f^! of Tag 0AA1 together with Tag 0BV2, carried \
  as the explicit hypotheses h0A86 and h0AA1; f^! itself is an explicit parameter fShriek \
  characterised by h0AA1, not a constructed or chosen functor. What is proved is the rest of \
  the source argument: the affine charts of X lying over affine opens of Y cover X, the \
  dualizing model of K over each such V comes from hK, Tag 0BZL upgrades its \
  algebraic upper shriek to a dualizing complex over the chart ring of X, and h0A86 glues \
  the local models. Neither carried hypothesis asserts that anything is dualizing"]
theorem isDualizingComplex_upperShriek_of_fts {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S}
    (f : X ⟶ Y)
    (fShriek : quasiCoherentDerivedCategoryPlus Y.left ⥤ quasiCoherentDerivedCategoryPlus X.left)
    (K : quasiCoherentDerivedCategoryPlus Y.left)
    (h0A86 : ∀ L : DerivedCategory X.left.Modules,
      (∀ x : X.left, ∃ (U : X.left.Opens) (hU : IsAffineOpen U),
        x ∈ U ∧ HasDualizingModelOn L U hU) → IsDualizingComplex L)
    (h0AA1 : ∀ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
      (ω : DerivedCategory (ModuleCat.{u} Γ(Y.left, V))),
      IsTildeModelOn K.obj.obj V hV ω →
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        IsTildeModelOn (fShriek.obj K).obj.obj U hU (p.upperShriekFunctor.{u, u}.obj ω))
    (hK : IsDualizingComplex K.obj.obj) :
    IsDualizingComplex (fShriek.obj K).obj.obj := by
  refine h0A86 _ fun x => ?_
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := f.left.base x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := f.left ⁻¹ᵁ V) hxV
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, hmodel⟩ := exists_isTildeModelOn_of_hasDualizingModelOn (hK V hV)
  obtain ⟨p, hp⟩ := h0AA1 U hU V hV hUV ω hmodel
  exact ⟨U, hU, hxU,
    hasDualizingModelOn_of_isTildeModelOn
      (Dualizing.PolynomialPresentation.upperShriekFunctor_isDualizingComplex p ω hω) hp⟩

end Stacks.Duality

end
