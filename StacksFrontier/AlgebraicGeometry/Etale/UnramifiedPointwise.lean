module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FormallyEtaleCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# Charts of a flat unramified morphism are formally étale

Unramifiedness of a morphism of schemes `f : X ⟶ S` is a *pointwise* condition: each point of `X`
has an affine open neighbourhood `U` lying over an affine open `V` of `S` such that
`Γ(S, V) ⟶ Γ(X, U)` is an unramified ring map. Flatness, by contrast, is a condition on *every*
pair of affine opens, `AlgebraicGeometry.Flat.flat_appLE`. Combining the two at one chart and
feeding the result to `Stacks.FormallyEtale.formallyEtale_of_flat` shows that the chart is
formally étale, and hence formally smooth.

This is the pointwise input to the proof of [Stacks Project, Tag 04FF].

## Main results

* `AlgebraicGeometry.formallyEtale_appLE_of_unramified`: a chart of a flat morphism on which the
  map of sections is unramified is formally étale, and
  `AlgebraicGeometry.formallySmooth_appLE_of_unramified` is the formally smooth consequence.
* `AlgebraicGeometry.exists_formallyEtale_appLE` and
  `AlgebraicGeometry.exists_formallySmooth_appLE`: a flat unramified morphism has, around every
  point of its source, an affine chart over an affine open of the target whose map of sections is
  formally étale, respectively formally smooth.

## Implementation notes

The witness produced by `AlgebraicGeometry.UnramifiedAt` carries its own algebra structure, namely
`(f.appLE V U e).hom.toAlgebra`, and `RingHom.FormallyEtale`, `RingHom.FormallySmooth` and
`RingHom.Flat` are all defined at that same instance. So no transport of instances is needed: the
three hypotheses of `Stacks.FormallyEtale.formallyEtale_of_flat` — formal unramifiedness,
essential finite type and flatness — are read off `Algebra.Unramified` (through
`Algebra.Unramified.formallyUnramified`, `Algebra.Unramified.finiteType` and
`Algebra.EssFiniteType.of_finiteType`) and off `AlgebraicGeometry.Flat.flat_appLE`.

The global bridge from pointwise unramifiedness to the morphism property
`AlgebraicGeometry.FormallyUnramified` is not proved here; it is
`AlgebraicGeometry.formallyUnramified_of_unramified`.

## References

* [Stacks Project, Tag 02G4](https://stacks.math.columbia.edu/tag/02G4)
* [Stacks Project, Tag 04FF](https://stacks.math.columbia.edu/tag/04FF)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **A chart of a flat morphism on which the sections are unramified is formally étale.** For
`f : X ⟶ S` flat, `V` an affine open of `S` and `U` an affine open of `X` with `U ≤ f ⁻¹ᵁ V`, if
`Γ(S, V) ⟶ Γ(X, U)` is an unramified ring map then it is formally étale. This is
`Stacks.FormallyEtale.formallyEtale_of_flat` at one chart, the flatness coming from
`AlgebraicGeometry.Flat.flat_appLE`. -/
theorem formallyEtale_appLE_of_unramified {f : X ⟶ S} [Flat f] {V : S.Opens} {U : X.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (h : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(S, V) Γ(X, U)) :
    (f.appLE V U e).hom.FormallyEtale := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra.Unramified Γ(S, V) Γ(X, U) := h
  let : Module.Flat Γ(S, V) Γ(X, U) := Flat.flat_appLE f hV hU e
  exact Stacks.FormallyEtale.formallyEtale_of_flat

/-- A chart of a flat morphism on which the sections are unramified is formally smooth: a formally
étale algebra is formally smooth. -/
theorem formallySmooth_appLE_of_unramified {f : X ⟶ S} [Flat f] {V : S.Opens} {U : X.Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V)
    (h : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(S, V) Γ(X, U)) :
    (f.appLE V U e).hom.FormallySmooth := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let : Algebra.FormallyEtale Γ(S, V) Γ(X, U) := formallyEtale_appLE_of_unramified hV hU e h
  exact inferInstanceAs (Algebra.FormallySmooth Γ(S, V) Γ(X, U))

/-- **A flat unramified morphism is formally étale on charts.** Every point of the source of a
flat unramified morphism `f : X ⟶ S` has an affine open neighbourhood `U` lying over an affine
open `V` of `S` such that `Γ(S, V) ⟶ Γ(X, U)` is formally étale. -/
theorem exists_formallyEtale_appLE (f : X ⟶ S) [Unramified f] [Flat f] (x : X) :
    ∃ (U : X.Opens) (V : S.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
      x ∈ U ∧ (f.appLE V U e).hom.FormallyEtale := by
  obtain ⟨U, hU, hx, V, hV, e, h⟩ := Unramified.unramifiedAt (f := f) x
  exact ⟨U, V, hU, hV, e, hx, formallyEtale_appLE_of_unramified hV hU e h⟩

/-- **A flat unramified morphism is formally smooth on charts.** Every point of the source of a
flat unramified morphism `f : X ⟶ S` has an affine open neighbourhood `U` lying over an affine
open `V` of `S` such that `Γ(S, V) ⟶ Γ(X, U)` is formally smooth. -/
theorem exists_formallySmooth_appLE (f : X ⟶ S) [Unramified f] [Flat f] (x : X) :
    ∃ (U : X.Opens) (V : S.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
      x ∈ U ∧ (f.appLE V U e).hom.FormallySmooth := by
  obtain ⟨U, hU, hx, V, hV, e, h⟩ := Unramified.unramifiedAt (f := f) x
  exact ⟨U, V, hU, hV, e, hx, formallySmooth_appLE_of_unramified hV hU e h⟩

end AlgebraicGeometry

end
