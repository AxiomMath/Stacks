module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms of finite presentation

A morphism of schemes is of finite presentation at a point if, on suitable affine
neighbourhoods of that point and its image, the induced ring map is of finite
presentation. It is locally of finite presentation when this holds at every point, and it
is of finite presentation when it is additionally quasi-compact and quasi-separated.

Part (1) of Stacks 01TP is `AlgebraicGeometry.FinitePresentationAt`; affine neighbourhoods
are bundled as `Scheme.affineOpens`, and their coordinate ring map is `Scheme.Hom.appLE`.
Part (2) is Mathlib's `AlgebraicGeometry.LocallyOfFinitePresentation`, whose
`HasRingHomProperty.iff_exists_appLE` characterization identifies it with the pointwise
condition defined here. Part (3) is the conjunction of Mathlib's three constituent
morphism properties; its projection lemmas make the corresponding typeclass assumptions
available to clients.

## Main definitions

* `AlgebraicGeometry.FinitePresentationAt` expresses finite presentation at a point.
* `AlgebraicGeometry.LocallyOfFinitePresentation` (Mathlib) expresses local finite
  presentation.
* `AlgebraicGeometry.FinitePresentation` expresses finite presentation.

## Main results

There are no results beyond the definitions and the projections of
`AlgebraicGeometry.FinitePresentation`.

## References

* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is of finite presentation at `x` if it induces a
ring map of finite presentation on some affine neighbourhood of `x` mapping
into an affine open of the target. -/
@[stacks 01TP "part (1)", ega "IV 1.4.2" "fin. presentation at x"]
public abbrev FinitePresentationAt {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  ∃ (V : S.affineOpens) (U : X.affineOpens) (_ : x ∈ U.1) (e : U.1 ≤ f ⁻¹ᵁ V.1),
    (f.appLE V U e).hom.FinitePresentation

add_to_stacks 01TP "part (2)" AlgebraicGeometry.LocallyOfFinitePresentation
add_to_sga "3 VIB 1.3" AlgebraicGeometry.LocallyOfFinitePresentation
add_to_ega "IV 1.4.2" AlgebraicGeometry.LocallyOfFinitePresentation

/-- A morphism of schemes is of finite presentation if it is locally of finite
presentation, quasi-compact, and quasi-separated. -/
@[stacks 01TP "part (3)"]
public abbrev FinitePresentation {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  LocallyOfFinitePresentation f ∧ QuasiCompact f ∧ QuasiSeparated f

/-- The three constituent properties define a morphism of finite presentation. -/
public lemma FinitePresentation.mk {X S : Scheme.{u}} {f : X ⟶ S}
    (hlfp : LocallyOfFinitePresentation f) (hqc : QuasiCompact f)
    (hqs : QuasiSeparated f) : FinitePresentation f :=
  ⟨hlfp, hqc, hqs⟩

/-- A morphism of finite presentation is locally of finite presentation. -/
public lemma FinitePresentation.locallyOfFinitePresentation {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FinitePresentation f) : LocallyOfFinitePresentation f := hf.1

/-- A morphism of finite presentation is quasi-compact. -/
public lemma FinitePresentation.quasiCompact {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FinitePresentation f) : QuasiCompact f := hf.2.1

/-- A morphism of finite presentation is quasi-separated. -/
public lemma FinitePresentation.quasiSeparated {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : FinitePresentation f) : QuasiSeparated f := hf.2.2

end AlgebraicGeometry
