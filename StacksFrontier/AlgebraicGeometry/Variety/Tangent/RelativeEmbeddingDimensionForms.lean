module

public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator
public import StacksFrontier.AlgebraicGeometry.Different.TheDifferent.SmoothFormula
public import StacksFrontier.AlgebraicGeometry.NumericalCriterion.Cotangent
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The numerical consequence of a bound on the embedding dimension

`AlgebraicGeometry.Scheme.Hom.HasEmbeddingDimensionLE` embeds a neighbourhood of each point of
`X` into a scheme `Y` smooth of relative dimension `e` over `S`.  This file records what that
buys numerically: the relative differential forms of such a `Y` **vanish above degree `e`**, so
the de Rham complex of `Y/S` is supported in degrees `≤ e`.

That is the step the module documentation of
`StacksFrontier/AlgebraicGeometry/Variety/Tangent/RelativeEmbeddingDimension.lean` and of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/DirectImageConcentration.lean` both record
as missing — "nothing anywhere consumes that predicate numerically".  The missing link is in fact
only the two-line composition below, because the rank statement it needs is already a theorem of
this library:

* `Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials` of
  `StacksFrontier/AlgebraicGeometry/Different/TheDifferent/SmoothFormula.lean`: the sheaf of
  relative differentials of a morphism smooth of relative dimension `e` is finite locally free of
  rank `e`;
* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerRank.lean`: its degree-`m` exterior
  power is then finite locally free of rank `binom(e, m)`, which is `0` for `m > e`;
* `Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero` of
  `StacksFrontier/AlgebraicGeometry/Chow/SecondAdamsOperator.lean`: a sheaf of modules finite
  locally free of rank zero is a zero object.

So the rank bound on `Ω` is available after all, and the two docstrings above are corrected
accordingly.  It remains true that `HasEmbeddingDimensionLE` says nothing about the relative
tangent spaces of `X` itself — only about those of the ambient `Y` — and that is a different
statement; see the module documentation of `RelativeEmbeddingDimension.lean`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension`:
  **`Ω^m_{Y/S} = 0` for `m > e` when `Y ⟶ S` is smooth of relative dimension `e`.**
* `AlgebraicGeometry.Scheme.Hom.exists_closedImmersion_isZero_relativeDifferentialForms`: **the
  numerical consequence of `HasEmbeddingDimensionLE e`** — each point of `X` has a neighbourhood
  closed-immersed over `S` into a scheme whose relative differential forms vanish above degree
  `e`.
* `AlgebraicGeometry.Scheme.Hom.finrank_relativeCotangentSpace_of_smoothOfRelativeDimension` and
  `AlgebraicGeometry.Scheme.Hom.finrank_dottedTangentArrow_of_smoothOfRelativeDimension`: the
  pointwise form of the same rank bound — the relative cotangent space and the relative tangent
  space of a morphism smooth of relative dimension `e` are `e`-dimensional over the residue
  field.

## References

* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 0CBK](https://stacks.math.columbia.edu/tag/0CBK)
* [Stacks Project, Tag 07MR](https://stacks.math.columbia.edu/tag/07MR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The relative differential `m`-forms of a morphism smooth of relative dimension `e` vanish
for `m > e`.**  The sheaf of relative differentials is finite locally free of rank `e`, so its
degree-`m` exterior power is finite locally free of rank `binom(e, m) = 0`, and a sheaf of modules
finite locally free of rank zero is a zero object.

This is the statement that makes the de Rham complex of such a morphism have length `e`, and it
is the numerical content that
`AlgebraicGeometry.Scheme.Hom.HasEmbeddingDimensionLE` supplies through
`Scheme.Hom.exists_closedImmersion_isZero_relativeDifferentialForms` below. -/
@[sga "1 III 5.2" "special case"]
theorem Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension
    {Y S : Scheme.{u}} (g : Y ⟶ S) (e : ℕ) [SmoothOfRelativeDimension e g] (m : ℕ) (hm : e < m) :
    IsZero (Scheme.Hom.relativeDifferentialForms g (m : ℤ)) := by
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials g e
  show IsZero (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) (m : ℤ))
  refine Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero _ ?_
  simpa only [Nat.choose_eq_zero_of_lt hm] using
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (Scheme.Hom.relativeDifferentials g) e m

/-- **The numerical consequence of a bound on the embedding dimension.**  If `f : X ⟶ S` has
embedding dimension at most `e`, then every point of `X` has an open neighbourhood `U` admitting a
closed immersion `i : U ⟶ Y` over `S` into a scheme `Y` smooth of relative dimension `e` over `S`
whose relative differential forms vanish above degree `e`: `Ω^m_{Y/S} = 0` for every `m > e`.

The data returned is that of `AlgebraicGeometry.Scheme.Hom.HasEmbeddingDimensionLE` itself, with
the vanishing appended; so this is that predicate together with the only numerical fact the
source's local computation of crystalline cohomology asks of it, namely that the de Rham complex
of the ambient smooth scheme stops in degree `e`. -/
theorem Scheme.Hom.exists_closedImmersion_isZero_relativeDifferentialForms {X S : Scheme.{u}}
    (f : X ⟶ S) (e : ℕ) (hf : f.HasEmbeddingDimensionLE e) (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (Y : Scheme.{u}) (i : U.toScheme ⟶ Y) (g : Y ⟶ S),
      IsClosedImmersion i ∧ SmoothOfRelativeDimension e g ∧ i ≫ g = U.ι ≫ f ∧
        ∀ m : ℕ, e < m → IsZero (Scheme.Hom.relativeDifferentialForms g (m : ℤ)) := by
  obtain ⟨U, hxU, Y, i, g, hi, hg, hig⟩ := hf x
  refine ⟨U, hxU, Y, i, g, hi, hg, hig, fun m hm => ?_⟩
  have := hg
  exact Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension g e m hm

/-! ### The pointwise rank, over the ambient smooth scheme -/

/-- **The relative cotangent space of a morphism smooth of relative dimension `e` is
`e`-dimensional.**  On the chart of
`Stacks.Discriminant.exists_isAffineOpen_basis_kaehlerDifferential` the Kähler differentials are
free on `Fin e`, and `Stacks.Tag01V9NumericalCriterion.finrank_relativeCotangentSpace_eq_chart`
reads the cotangent space at the point off that chart as the residue-field base change of them,
which a basis transports. -/
theorem Scheme.Hom.finrank_relativeCotangentSpace_of_smoothOfRelativeDimension
    {Y S : Scheme.{u}} (g : Y ⟶ S) (e : ℕ) [SmoothOfRelativeDimension e g] (y : Y) :
    Module.finrank (Y.residueField y)
      (Stacks.SmoothAtJacobian.relativeCotangentSpace g y) = e := by
  classical
  obtain ⟨W, hW, hyW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := g.base y) (U := ⊤)
      (TopologicalSpace.Opens.mem_top _)
  obtain ⟨U, hU, hyU, hUW, hb⟩ :=
    Stacks.Discriminant.exists_isAffineOpen_basis_kaehlerDifferential (n := e) g y hW
      (T := g ⁻¹ᵁ W) hyW le_rfl
  let := Stacks.Smooth.algebraAppLE g (hUW.trans (le_refl (g ⁻¹ᵁ W)))
  rw [Stacks.Tag01V9NumericalCriterion.finrank_relativeCotangentSpace_eq_chart g y
      ⟨U, hU⟩ ⟨W, hW⟩ hyU hUW,
    Module.finrank_eq_card_basis (Algebra.TensorProduct.basis _ hb.some),
    Fintype.card_fin]

/-- **The relative tangent space of a morphism smooth of relative dimension `e` is
`e`-dimensional**, by the second equality of [Stacks, Tag 0CBK].

This is the rank computation the module documentation of
`StacksFrontier/AlgebraicGeometry/Variety/Tangent/RelativeEmbeddingDimension.lean` records as
unavailable; with it, `Scheme.Hom.hasEmbeddingDimensionLE_of_finrank_dottedTangentArrow` — Tag
0CBL — has a converse at the ambient smooth scheme.  What is still missing for a converse at `X`
itself is the transport of the dimension along the closed immersion of
`AlgebraicGeometry.exists_injective_tangentMap_of_hasEmbeddingDimensionLE`, whose source and
target tangent spaces sit over the two residue fields of a closed immersion rather than over one
field, and the invariance of the tangent space under restriction to an open. -/
theorem Scheme.Hom.finrank_dottedTangentArrow_of_smoothOfRelativeDimension
    {Y S : Scheme.{u}} (g : Y ⟶ S) (e : ℕ) [SmoothOfRelativeDimension e g] (y : Y) :
    Module.finrank (Y.residueField y) (DottedTangentArrow g y) = e :=
  (finrank_relativeCotangentSpace_eq_finrank_dottedTangentArrow g y).symm.trans
    (Scheme.Hom.finrank_relativeCotangentSpace_of_smoothOfRelativeDimension g e y)

end AlgebraicGeometry

end
