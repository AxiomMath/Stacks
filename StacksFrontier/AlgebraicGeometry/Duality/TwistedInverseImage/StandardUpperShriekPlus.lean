module

public import StacksFrontier.AlgebraicGeometry.Duality.AnyModelRightAdjoint.SheafyTraceUnconditionalAdjoint
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekDualizingComplexChart
import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointBoundedBelow

/-!
# The twisted inverse image on `D⁺_QCoh` at the standard model

The functors `f^!` of [Stacks, Section 0AU3] go between the categories `D⁺_QCoh`. In this
repository that category is `Stacks.Duality.quasiCoherentDerivedCategoryPlus`, read at
`CategoryTheory.HasDerivedCategory.standard`, because that is the model at which
`Stacks.Duality.HasDualizingModelOn` and hence `Stacks.Duality.IsDualizingComplex` are used in
`StacksFrontier/AlgebraicGeometry/Duality/UpperShriekDualizingComplex.lean`. The twisted inverse
image, on the other hand, used to exist only at the locally small model, because the Brown
representability argument of [Stacks, Tag 0A9E] runs only there. So the `fShriek` parameter of
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts` had no constructed inhabitant: the
obstruction was the model, not a missing theorem.

`Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward` removes it, by transporting
the adjoint to an arbitrary chosen model. This file carries out the one step still needed to land
in `D⁺`: [Stacks, Tag 0A9I], that `f^×` preserves bounded-below complexes, at the standard model.
Its proof is the one already in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BoundedBelow.lean`, and both of its
inputs are model-free — `Stacks.Duality.isGE_rightAdjoint_obj` and
`Stacks.Duality.AnyModel.exists_isLE_derivedPushforward_obj_anyModel` — so only the adjunction
needed replacing.

The result is `Stacks.Duality.standardUpperShriekPlus`, a *constructed* functor
`D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)` of exactly the type that parameter has.

## Main results

All in the namespace `Stacks.Duality`.

* `exists_isGE_standardTwistedInverseImage_obj` and
  `isBoundedBelow_standardTwistedInverseImage_obj` — **[Stacks, Tag 0A9I] at the standard model**.
* `standardUpperShriekPlus` — `f^×` restricted to `D⁺_QCoh`, at the standard model.
* `isDualizingComplex_standardUpperShriekPlus_of_fts` — clause (4)(a) of
  [Stacks, Section 0AU3] read at that constructed functor.

## Implementation notes

*No `@[stacks]` attribute is placed on anything below, and the coverage of
[Stacks, Section 0AU3] is unchanged by this file.*

* [Stacks, Tag 0A9I] is already registered, on
  `Stacks.Duality.isBoundedBelow_twistedInverseImage_obj_and_exists_bound`, which states both
  of its sentences. What is here is the same statement at a second model, which adds no content
  of the tag.
* `isDualizingComplex_standardUpperShriekPlus_of_fts` is clause (4)(a) *instantiated* at one
  functor. Instantiating a universally quantified parameter makes a statement weaker, not
  stronger, so it does not carry the tag; the form that quantifies over every `fShriek` is the
  one that states the clause, and it is the registered
  `Stacks.Duality.isDualizingComplex_upperShriek_of_fts`. The statement used below is
  `Stacks.Duality.isDualizingComplex_upperShriek_of_fts_of_chart` of
  `StacksFrontier/AlgebraicGeometry/Duality/UpperShriekDualizingComplexChart.lean`, the same
  statement with its hypothesis `h0A86` discharged by the cover criterion of
  [Stacks, Tag 0A86]; it carries no attribute either.

*What this does and does not discharge.* It makes the `fShriek` parameter inhabited by a
construction at the right model, so the clause is no longer a statement about a functor nobody
can produce. It does **not** discharge `hchart`, the affine-chart description of `f^!`: that is
[Stacks, Tag 0AA1] together with the affine comparison of [Stacks, Tag 0BV2], and proving it
*of* the constructed `f^×` is exactly the content of those two tags, which are absent from this
repository. So clause (4)(a) still carries one hypothesis, and this file does not reduce the
count.

*Properness is not assumed.* For a general morphism of `FTS S` the section's `f^!` is built from
a compactification and agrees with the right adjoint of `Rf_*` only when `f` is proper
(clause (2); `Stacks.Duality.upperShriek_isRightAdjointOnBoundedBelow_of_isProper`). The functor
below is the right adjoint, so for a non-proper `f` it is `f^×` and not the section's `f^!`; what
makes `isDualizingComplex_standardUpperShriekPlus_of_fts` a statement about `f^!` for either kind
of morphism is `hchart`, which is what ties the functor to the charts of `f`.

## References

* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A86](https://stacks.math.columbia.edu/tag/0A86)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0AA1](https://stacks.math.columbia.edu/tag/0AA1)
* [Stacks Project, Tag 0AA3](https://stacks.math.columbia.edu/tag/0AA3)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Stacks.Duality

section BoundedBelow

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **The bound of [Stacks, Tag 0A9I] at the standard model.** For a morphism `f : X ⟶ Y` of
quasi-compact quasi-separated schemes there is an integer `N` such that the twisted inverse image
`f^×` of `Stacks.Duality.AnyModel.standardTwistedInverseImage` carries an object of
`D_QCoh(𝒪_Y)` living in degrees `≥ c` to one living in degrees `≥ c - N`.

The proof is the one of `Stacks.Duality.exists_isGE_twistedInverseImage_obj`: the argument
`Stacks.Duality.isGE_rightAdjoint_obj` and the uniform bound
`Stacks.Duality.AnyModel.exists_isLE_derivedPushforward_obj_anyModel` are both stated with the
model left free, so only the adjunction changes. -/
theorem exists_isGE_standardTwistedInverseImage_obj :
    ∃ N : ℤ, ∀ (K : quasiCoherentDerivedCategory Y) (c : ℤ), K.obj.IsGE c →
      ((AnyModel.standardTwistedInverseImage f).obj K).obj.IsGE (c - N) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj_anyModel f
  exact ⟨N, fun K c hK ↦ isGE_rightAdjoint_obj f _
    (AnyModel.standardTwistedInverseImageAdjunction f) N hN K c hK⟩

/-- **[Stacks, Tag 0A9I] at the standard model.** For a morphism `f : X ⟶ Y` of quasi-compact
quasi-separated schemes the twisted inverse image `f^×` carries an object of `D_QCoh(𝒪_Y)` with
bounded-below cohomology to one with bounded-below cohomology, that is, it maps `D⁺_QCoh(𝒪_Y)`
into `D⁺_QCoh(𝒪_X)`. -/
theorem isBoundedBelow_standardTwistedInverseImage_obj (K : quasiCoherentDerivedCategory Y)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow ((AnyModel.standardTwistedInverseImage f).obj K).obj := by
  obtain ⟨N, hN⟩ := exists_isGE_standardTwistedInverseImage_obj f
  obtain ⟨n₀, hn₀⟩ := hK
  have := hN K n₀ ((DerivedCategory.isGE_iff _ _).2 fun i hi ↦ hn₀ i hi)
  exact ⟨n₀ - N, fun n hn ↦ DerivedCategory.isZero_of_isGE _ (n₀ - N) n hn⟩

/-- **The twisted inverse image on `D⁺_QCoh`, at the standard model.** For a morphism `f : X ⟶ Y`
of quasi-compact quasi-separated schemes this is the right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` — which exists at this model by
`Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward`, [Stacks, Tag 0A9E] —
restricted to the bounded-below parts, which is possible by [Stacks, Tag 0A9I].

This is a constructed functor of exactly the type of the `fShriek` parameter of
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`. -/
def standardUpperShriekPlus :
    quasiCoherentDerivedCategoryPlus Y ⥤ quasiCoherentDerivedCategoryPlus X :=
  ObjectProperty.lift _
    (ObjectProperty.ι (isBoundedBelowQuasiCoherent Y) ⋙ AnyModel.standardTwistedInverseImage f)
    fun K ↦ isBoundedBelow_standardTwistedInverseImage_obj f K.obj K.property

/-- The value of `Stacks.Duality.standardUpperShriekPlus` is the value of the right adjoint, by
construction. -/
theorem standardUpperShriekPlus_obj_obj (K : quasiCoherentDerivedCategoryPlus Y) :
    ((standardUpperShriekPlus f).obj K).obj =
      (AnyModel.standardTwistedInverseImage f).obj K.obj :=
  rfl

end BoundedBelow

section FTS

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : AlgebraicGeometry.FTS S} (f : X ⟶ Y)

/-- **Clause (4)(a) of [Stacks, Section 0AU3] at the constructed twisted inverse image.** Let `S`
be a Noetherian scheme, let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S` and let `K` be
a dualizing complex on `Y`. If the right adjoint of `Rf_*`, restricted to `D⁺_QCoh` by
[Stacks, Tag 0A9I], has the affine-chart description of [Stacks, Tag 0AA1] and
[Stacks, Tag 0BV2], then it carries `K` to a dualizing complex on `X`.

This is `Stacks.Duality.isDualizingComplex_upperShriek_of_fts_of_chart` — which quantifies over
every candidate `f^!` — instantiated at the constructed functor
`Stacks.Duality.standardUpperShriekPlus`. It carries no attribute: instantiating a parameter
weakens a statement, and the registered clause (4)(a) is the quantified
`Stacks.Duality.isDualizingComplex_upperShriek_of_fts`. What it shows is that the parameter is
inhabited by a construction at the model its type is read at, which before
`Stacks.Duality.AnyModel.isLeftAdjoint_restrictedDerivedPushforward` it was not. -/
theorem isDualizingComplex_standardUpperShriekPlus_of_fts
    (K : quasiCoherentDerivedCategoryPlus Y.left)
    (hchart : ∀ (U : X.left.Opens) (hU : IsAffineOpen U) (V : Y.left.Opens)
      (hV : IsAffineOpen V) (hUV : U ≤ f.left ⁻¹ᵁ V)
      (ω : DerivedCategory (ModuleCat.{u} Γ(Y.left, V))),
      IsTildeModelOn K.obj.obj V hV ω →
      ∃ p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom,
        IsTildeModelOn ((standardUpperShriekPlus f.left).obj K).obj.obj U hU
          (p.upperShriekFunctor.{u, u}.obj ω))
    (hK : IsDualizingComplex K.obj.obj) :
    IsDualizingComplex ((standardUpperShriekPlus f.left).obj K).obj.obj :=
  isDualizingComplex_upperShriek_of_fts_of_chart f (standardUpperShriekPlus f.left) K hchart hK

end FTS

end Stacks.Duality

end
