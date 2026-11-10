module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Transport
public import StacksFrontier.CategoryTheory.Localization.LeftFraction.AsColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Where a right or left derived functor is defined, and objects computing it

This file collects the formalizations of [Stacks, Tag 05S9], [Stacks, Tag 05SV],
[Stacks, Tag 05SX], together with the dictionary between a value of `RF`, resp. `LF`, and an
essential-constancy witness in the sense of Tag 05PU, and the facts that a value is a colimit,
resp. limit, and is carried along a reindexing of the index categories.

## References

* [Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
* [Stacks, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV)
* [Stacks, Tag 05SX](https://stacks.math.columbia.edu/tag/05SX)
-/

section

/-!
# Values of the right and left derived functors at an object

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟`. For an object `X`
of `𝒟` write `X/W` for the category of morphisms `s : X ⟶ X'` of `𝒟` that lie in `W`, a
morphism `s → t` being an arbitrary morphism `X' ⟶ X''` of `𝒟` under `X`, and `W/X` for the
category of morphisms `s : X' ⟶ X` of `𝒟` that lie in `W`, a morphism `s → t` being an
arbitrary morphism of `𝒟` over `X`; in Lean these are `MorphismProperty.Under W ⊤ X` and
`MorphismProperty.Over W ⊤ X`. Composing the forgetful functors with `F` gives the ind-object
$$ X/W ⟶ 𝒟', \quad (s : X ⟶ X') ⟼ F(X') $$
and the pro-object
$$ W/X ⟶ 𝒟', \quad (s : X' ⟶ X) ⟼ F(X') $$
of `𝒟'`. Following Deligne, the right derived functor `RF` is said to be *defined at* `X` when
the first is essentially constant, the left derived functor `LF` to be *defined at* `X` when the
second is; the value of the ind-object, resp. of the pro-object, is then called the *value of
`RF`*, resp. *of `LF`*, *at* `X`, denoted `RF(X)`, resp. `LF(X)`.

Essential constancy of the ind-object with respect to a cocone `c` unwinds to: there are an
index `s₀ : X ⟶ X'₀` and a morphism `r : c.pt ⟶ F(X'₀)` such that `r` is a section of the
coprojection `F(X'₀) ⟶ c.pt`, and such that for every index `s` some transition morphism out of
`F(X')` factors as `F(X') ⟶ c.pt ⟶ F(X'₀) ⟶ F(X'')`. Dually, essential constancy of the
pro-object with respect to a cone `c` says that there are an index `s₀ : X'₀ ⟶ X` and a morphism
`r : F(X'₀) ⟶ c.pt` such that `r` is a retraction of the projection `c.pt ⟶ F(X'₀)`, and such
that for every index `s` some transition morphism into `F(X')` factors as
`F(X'') ⟶ F(X'₀) ⟶ c.pt ⟶ F(X')`. These are the source's two notions of an essentially
constant ind-object, resp. pro-object (Tag 05PU(1), resp. 05PU(2)), at these two diagrams.

## Main definitions

* `CategoryTheory.Functor.IsRightDerivedValueAt`: the cocone `c` on the ind-object above
  exhibits `c.pt` as a value of the right derived functor of `F` at `X`. The statement that
  `RF` is defined at `X` is `∃ c, F.IsRightDerivedValueAt W X c`, and `c.pt` is then `RF(X)`.
* `CategoryTheory.Functor.IsLeftDerivedValueAt`: the cone `c` on the pro-object above exhibits
  `c.pt` as a value of the left derived functor of `F` at `X`. The statement that `LF` is
  defined at `X` is `∃ c, F.IsLeftDerivedValueAt W X c`, and `c.pt` is then `LF(X)`.

## Implementation notes

*What is assumed, and what is pinned.* (1) The data of each definition is `F`, `W`, `X` and the
cocone, resp. cone, and each of the four occurs in the condition; in particular none of
Situation 05S8's hypotheses — `F` exact between triangulated categories, `W` a saturated
multiplicative system compatible with the triangulated structure — is assumed, because
conditions (a) and (b) of essential constancy mention none of them, and the source's `X/S` being
filtered, resp. `S/X` cofiltered, is used by the results *about* `RF` and `LF` rather than by
the definition. (2) The index categories are the source's: objects are the morphisms of `𝒟`
*lying in `W`* out of, resp. into, the given `X`, and morphisms between them are arbitrary
morphisms of `𝒟` under, resp. over, `X` — hence `Q = ⊤` in `MorphismProperty.Under W ⊤ X` and
`MorphismProperty.Over W ⊤ X` — and the diagram takes values in `𝒟'` through `F`, not in `𝒟`
nor in a localization of `𝒟`. (3) The value is pinned together with its structure maps rather
than merely asserted to exist: the cocone, resp. cone, is a parameter, so `c.pt` comes with the
coprojections `c.ι.app s : F(X') ⟶ c.pt`, resp. the projections `c.π.app s : c.pt ⟶ F(X')`,
which are the maps the source uses to characterise `RF` and `LF` on morphisms, and the
retraction `r` and the factorisation are 05PU's clauses (a) and (b) at those maps. (4) The
instantiation is not degenerate: for `W = MorphismProperty.isomorphisms 𝒟` the object `𝟙 X` is
both initial and terminal in `X/W`, and likewise in `W/X`, the map to it from `s : X ⟶ X'` being
`s⁻¹`; so both conditions hold at every `X`, with value `F(X)`, coprojections, resp. projections,
`F(s)⁻¹`, resp. `F(s)`, index `s₀ = 𝟙 X` and `r = 𝟙`. Both are also falsifiable: for `W = ⊥` the
index categories are empty, so no cocone and no cone is a value.

*Where the essential-constancy clauses come from.* The two conditions of each definition are
clauses (a) and (b) of Tag 05PU at the prescribed cocone, resp. cone: up to the order of the two
transition maps they are `CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith`, resp.
`CategoryTheory.EssentiallyConstantPro.IsEssentiallyConstantWith`. Consequently a value in the
sense below is the same thing as a colimit, resp. limit, of the diagram at which the diagram is
essentially constant in the sense of
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantInd`:
`IsEssentiallyConstantWith.isColimit` shows that a value is a colimit, and
`IsEssentiallyConstantInd.exists_retraction_of_isColimit` produces a value on any prescribed
colimit cocone.

*Uniqueness of the value.* The value is unique up to unique isomorphism compatible with the
coprojections, resp. projections; that is a statement about essentially constant ind-objects and
pro-objects, not part of these definitions.

*Duality.* `IsLeftDerivedValueAt` is stated directly, in the pro-object form the source gives it,
rather than as `F.op.IsRightDerivedValueAt W.op (Opposite.op X)`; the two agree through the
equivalence `(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)` and the correspondence between cones
on a diagram and cocones on its opposite, which is a separate lemma. Mathlib treats its own
pointwise derived functors the same way, with `HasPointwiseLeftDerivedFunctorAt` a direct
dualization of `HasPointwiseRightDerivedFunctorAt` rather than an opposite-category abbreviation.

*Relation to Mathlib's condition.* `Functor.HasPointwiseRightDerivedFunctorAt` and
`Functor.HasPointwiseLeftDerivedFunctorAt` ask that the pointwise Kan extension of `F` along a
localization functor exist at `L(X)`; that is a different condition from essential constancy,
which in addition makes the value a retract of a term of the diagram, and no bridge between the
two is claimed here.

## References

* Stacks project, Tag 05S9 (Definition 13.14.2); essential constancy of an ind-object,
  resp. pro-object, is Tag 05PU(1), resp. 05PU(2), the index categories are Tags 05Q0 and 05Q4,
  and the situation is Tag 05S8.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- **Stacks 05S9(1)**. The cocone `c` on the ind-object
`X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')`
exhibits its vertex `c.pt` as a *value of the right derived functor `RF` at `X`*: the ind-object
is essentially constant with value `c.pt`, i.e. there are an index `s₀` and a section
`r : c.pt ⟶ F(X'₀)` of the coprojection at `s₀` such that every transition morphism of the
ind-object factors through `r` after enlarging the index.

Accordingly, `RF` *is defined at* `X` means `∃ c, F.IsRightDerivedValueAt W X c`, and the value
`RF(X)` is `c.pt`. -/
@[stacks 05S9, sga "4 XVII 1.2.1" "(ii)", sga "4 XVII 5.5.5" "right derivable at K"]
public def IsRightDerivedValueAt (F : D ⥤ D') (W : MorphismProperty D) (X : D)
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) : Prop :=
  ∃ (s₀ : W.Under ⊤ X) (r : c.pt ⟶ F.obj s₀.right),
    r ≫ c.ι.app s₀ = 𝟙 c.pt ∧
      ∀ s : W.Under ⊤ X, ∃ (t : W.Under ⊤ X) (u : s ⟶ t) (v : s₀ ⟶ t),
        F.map u.right = c.ι.app s ≫ r ≫ F.map v.right

/-- **Stacks 05S9(2)**. The cone `c` on the pro-object
`W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')`
exhibits its vertex `c.pt` as a *value of the left derived functor `LF` at `X`*: the pro-object
is essentially constant with value `c.pt`, i.e. there are an index `s₀` and a retraction
`r : F(X'₀) ⟶ c.pt` of the projection at `s₀` such that every transition morphism of the
pro-object factors through `r` after refining the index.

Accordingly, `LF` *is defined at* `X` means `∃ c, F.IsLeftDerivedValueAt W X c`, and the value
`LF(X)` is `c.pt`. -/
@[stacks 05S9, sga "4 XVII 5.5.5" "left derivable at K"]
public def IsLeftDerivedValueAt (F : D ⥤ D') (W : MorphismProperty D) (X : D)
    (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) : Prop :=
  ∃ (s₀ : W.Over ⊤ X) (r : F.obj s₀.left ⟶ c.pt),
    c.π.app s₀ ≫ r = 𝟙 c.pt ∧
      ∀ s : W.Over ⊤ X, ∃ (t : W.Over ⊤ X) (u : t ⟶ s) (v : t ⟶ s₀),
        F.map u.left = F.map v.left ≫ r ≫ c.π.app s

end CategoryTheory.Functor

end

end

section

/-!
# Right derivable and left derivable functors

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟`. For an object `X`
of `𝒟`, the right derived functor `RF` is *defined at* `X` when the ind-object
$$ X/W ⟶ 𝒟', \quad (s : X ⟶ X') ⟼ F(X') $$
is essentially constant, and the left derived functor `LF` is *defined at* `X` when the
pro-object
$$ W/X ⟶ 𝒟', \quad (s : X' ⟶ X) ⟼ F(X') $$
is essentially constant; the value is then `RF(X)`, resp. `LF(X)`. This is Tag 05S9, rendered in
Lean as the existence of a cocone, resp. cone, satisfying
`CategoryTheory.Functor.IsRightDerivedValueAt`, resp. `IsLeftDerivedValueAt`.

Following Deligne, `F` is called *right derivable*, and `RF` *everywhere defined*, when `RF` is
defined at every object of `𝒟`; dually `F` is *left derivable*, and `LF` *everywhere defined*,
when `LF` is defined at every object of `𝒟`. These are the two properties defined here. In that
case `RF`, resp. `LF`, descends to a functor `W⁻¹𝒟 ⥤ 𝒟'` (Tag 05SW, via Tag 05SE); the passage
from everywhere-definedness to that functor is a separate result and is not part of these
definitions.

## Main definitions

* `CategoryTheory.Functor.IsRightDerivable`: `F` is right derivable with respect to `W`, i.e.
  `RF` is everywhere defined: every object of `𝒟` carries a value of `RF`.
* `CategoryTheory.Functor.IsLeftDerivable`: `F` is left derivable with respect to `W`, i.e.
  `LF` is everywhere defined: every object of `𝒟` carries a value of `LF`.

## Implementation notes

*What is assumed, and what is pinned.* (1) The data of each definition is `F` and `W`, and both
occur in the condition; none of Situation 05S8's hypotheses — `F` exact between triangulated
categories, `W` a saturated multiplicative system compatible with the triangulated structure — is
assumed, because being defined at an object mentions none of them, exactly as in Tag 05S9; the
results *about* derivable functors carry them. (2) The class of morphisms is the source's `S`,
taken on `𝒟` itself: the index categories are the source's `X/W` and `W/X`, and the ind-object,
resp. pro-object, takes its values in `𝒟'` through `F`, not in `𝒟` nor in a localization of `𝒟`.
(3) The source names no map in this definition; "defined at `X`" is spelled here as
`∃ c, F.IsRightDerivedValueAt W X c`, resp. `∃ c, F.IsLeftDerivedValueAt W X c`, which is the
form Tag 05S9 fixes for it and the form the dependent statements already use, so a value comes
with the coprojections `c.ι.app s`, resp. the projections `c.π.app s`, that characterise `RF`,
resp. `LF`, on morphisms. (4) The instantiation is not degenerate: for
`W = MorphismProperty.isomorphisms 𝒟` the object `𝟙 X` is initial in `X/W` and terminal in `W/X`,
so — as recorded for Tag 05S9 — every object carries a value, with `RF(X) = LF(X) = F(X)`, and
`F` is both right and left derivable; both properties are also falsifiable, since for `W = ⊥` on
a nonempty `𝒟` the index categories are empty and no object carries a value.

*Why an `abbrev`.* Each property is the universal quantification of Tag 05S9's condition and has
no content of its own, so it is reducible: `intro` and application see through it and no unfolding
lemma is needed. Mathlib spells its own everywhere-defined condition the same way, with
`CategoryTheory.Functor.HasPointwiseRightDerivedFunctor` an `abbrev` for
`∀ X, F.HasPointwiseRightDerivedFunctorAt W X`.

*Duality.* `IsLeftDerivable` is stated directly, through the pro-object form of Tag 05S9 that the
source gives, rather than as `F.op.IsRightDerivable W.op`; the two agree by the duality of
Tag 05S9, which is a separate lemma.

*Relation to Mathlib's condition.* `Functor.HasPointwiseRightDerivedFunctor` and
`Functor.HasPointwiseLeftDerivedFunctor` ask for the pointwise Kan extension of `F` along a
localization functor at every object; that is a different condition from essential constancy,
which in addition makes the value a retract of a term of the diagram, and no bridge between the
two is claimed here.

## References

* [Stacks project, Tag 05SV](https://stacks.math.columbia.edu/tag/05SV) (Definition 13.14.9);
  being defined at an object is Tag 05S9, the situation is Tag 05S8, the functor on the
  localization is (05SW), and the reference for the notion is Deligne's exposé XVII in [SGA4].
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- **Stacks 05SV(1)**. `F` is *right derivable* with respect to `W`, equivalently the right
derived functor `RF` is *everywhere defined*: `RF` is defined at every object `X` of `𝒟`, i.e.
every `X` carries a cocone on the ind-object `X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')` exhibiting its
vertex as a value `RF(X)` in the sense of `CategoryTheory.Functor.IsRightDerivedValueAt`. -/
@[stacks 05SV, sga "4 XVII 1.2.1" "(iii)"]
public abbrev IsRightDerivable (F : D ⥤ D') (W : MorphismProperty D) : Prop :=
  ∀ X : D, ∃ c, F.IsRightDerivedValueAt W X c

/-- **Stacks 05SV(2)**. `F` is *left derivable* with respect to `W`, equivalently the left
derived functor `LF` is *everywhere defined*: `LF` is defined at every object `X` of `𝒟`, i.e.
every `X` carries a cone on the pro-object `W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')` exhibiting its
vertex as a value `LF(X)` in the sense of `CategoryTheory.Functor.IsLeftDerivedValueAt`. -/
@[stacks 05SV]
public abbrev IsLeftDerivable (F : D ⥤ D') (W : MorphismProperty D) : Prop :=
  ∀ X : D, ∃ c, F.IsLeftDerivedValueAt W X c

end CategoryTheory.Functor

end

end

section

/-!
# Objects computing the right and left derived functor

Let `F : 𝒟 ⥤ 𝒟'` be a functor and let `W` be a class of morphisms of `𝒟` containing the
identities. For an object `X` of `𝒟`, the right derived functor `RF` is *defined at* `X` when the
ind-object
$$ X/W ⟶ 𝒟', \quad (s : X ⟶ X') ⟼ F(X') $$
is essentially constant, its value being `RF(X)`; this is Tag 05S9, transcribed as
`CategoryTheory.Functor.IsRightDerivedValueAt`. The identity `𝟙 X` is one of the indices of that
ind-object, so a value comes with a *canonical map* `F(X) ⟶ RF(X)`: the coprojection of the value
cocone at the index `𝟙 X`. Following Deligne, `X` *computes* `RF` when `RF` is defined at `X` and
this canonical map is an isomorphism. Dually, `LF` is *defined at* `X` when the pro-object
$$ W/X ⟶ 𝒟', \quad (s : X' ⟶ X) ⟼ F(X') $$
is essentially constant with value `LF(X)`, the projection of the value cone at the index `𝟙 X`
is the canonical map `LF(X) ⟶ F(X)`, and `X` *computes* `LF` when that map is an isomorphism.

The point of the notion is that the derived functor on the localized category, when it exists,
rarely satisfies `RF ∘ Q = F`; it can happen that `F(X) ⟶ RF(X)` is an isomorphism for no `X` at
all. In practice one proves that `F` is right derivable by exhibiting objects at which `F` may be
evaluated — bounded below complexes of injectives, K-injective complexes — that is, objects
computing `RF`.

## Main definitions

* `CategoryTheory.Functor.ComputesRightDerived`: the object `X` computes the right derived
  functor `RF` of `F` relative to `W`: some cocone exhibits a value `RF(X)` of the ind-object
  above, and its coprojection at the index `𝟙 X`, the canonical map `F(X) ⟶ RF(X)`, is an
  isomorphism.
* `CategoryTheory.Functor.ComputesLeftDerived`: the object `X` computes the left derived functor
  `LF` of `F` relative to `W`: some cone exhibits a value `LF(X)` of the pro-object above, and
  its projection at the index `𝟙 X`, the canonical map `LF(X) ⟶ F(X)`, is an isomorphism.

## Implementation notes

*Faithfulness.* (1) No hypothesis is idle: `F`, `W` and `X` all occur in each condition, and
`[W.ContainsIdentities]` is what produces the index `𝟙 X` at which the canonical map lives; of
Situation 05S8 nothing else is assumed — `F` exact between triangulated categories and `W` a
saturated multiplicative system compatible with the triangulated structure are used by the
results *about* computing objects (through filteredness of `X/W`, resp. cofilteredness of
`W/X`), not by the definition, exactly as in the statement of Tag 05S9.
(2) The base is the source's:
the index category is the source's `X/S`, resp. `S/X` — morphisms of `𝒟` lying in `W` out of,
resp. into, `X`, with arbitrary morphisms of `𝒟` under, resp. over, `X` between them — the
diagram takes its values in `𝒟'` through `F`, and "defined at" is the source's essential
constancy of that ind-object, resp. pro-object, not the localization-and-Kan-extension condition
`CategoryTheory.Functor.HasPointwiseRightDerivedFunctorAt`. (3) The canonical map is pinned, not
merely asserted to exist: it is `c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) _)`, of type
`F.obj X ⟶ c.pt`, resp. `c.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) _)`, of type
`c.pt ⟶ F.obj X`, for the very cocone, resp. cone, that exhibits the value — so the condition is
invertibility of the source's map, not existence of some isomorphism `F(X) ≅ RF(X)`. (4) The
instantiation is not degenerate: for `W = MorphismProperty.isomorphisms 𝒟` every object computes
both `RF` and `LF`, the index `𝟙 X` being terminal in `X/W` and initial in `W/X` (the map to,
resp. from, `s` is `s⁻¹`), and non-trivially, for `W` the quasi-isomorphisms of the homotopy
category of an abelian category every K-injective complex computes `RF` — the first clause of
`CategoryTheory.Functor.exists_isRightDerivedValueAt_and_isIso_of_isKInjective` (Tag 070Y, proved
in this repository) is literally this predicate. Neither condition is vacuously true: each
implies that `RF`, resp. `LF`, is defined at `X`, which is a genuine condition.

*Why a class rather than a hypothesis.* Only `W (𝟙 X)` is used, but it is required as the
instance `[W.ContainsIdentities]` rather than as an argument `W (𝟙 X)`, so that the predicates
depend on `F`, `W` and `X` alone and the identity index is produced by inference; the hypothesis
holds in Situation 05S8, where `W` is a multiplicative system.

*Existential form.* "`RF` is defined at `X`" is `∃ c, F.IsRightDerivedValueAt W X c` (Tag 05SV
spells this out as `CategoryTheory.Functor.IsRightDerivable` over all `X`), and the isomorphism
is asked of that same `c`; the value of an essentially constant ind-object being unique up to a
coprojection-compatible isomorphism, this is the source's condition, and it agrees with the
form quantifying over all value cocones as soon as that uniqueness is available — which is a
statement about essentially constant ind-objects, not part of this definition. Invertibility at
every value cocone also follows directly whenever the index `𝟙 X` is terminal in `X/W`, which is
how the known computing objects arise.

*Duality.* `ComputesLeftDerived` is stated in the pro-object form the source gives it, rather
than as `F.op.ComputesRightDerived W.op (Opposite.op X)`; the two agree through the equivalence
`(W.Over ⊤ X)ᵒᵖ ≌ W.op.Under ⊤ (Opposite.op X)`, as for the underlying notions of value.

## References

* [Stacks Project, Tag 05SX](https://stacks.math.columbia.edu/tag/05SX); "defined at" and the
  value of `RF`, resp. `LF`, are Tag 05S9, the index categories are Tags 05Q0 and 05Q4, the
  situation is Tag 05S8, and `SGA4` XVII is the source's reference for the section.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- **Stacks 05SX(1)**. The object `X` of `𝒟` *computes* the right derived functor `RF` of
`F : 𝒟 ⥤ 𝒟'` relative to `W`: the right derived functor is defined at `X`, i.e. some cocone `c`
on the ind-object `X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')` exhibits its vertex as a value `RF(X)`, and
the canonical map `F(X) ⟶ RF(X)` — the coprojection of `c` at the index `𝟙 X` — is an
isomorphism. -/
@[stacks 05SX, sga "4 XVII 1.2.1", sga "4 XVII 5.5.5"]
public abbrev ComputesRightDerived (F : D ⥤ D') (W : MorphismProperty D)
    [W.ContainsIdentities] (X : D) : Prop :=
  ∃ c, F.IsRightDerivedValueAt W X c ∧
    IsIso (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)))

/-- **Stacks 05SX(2)**. The object `X` of `𝒟` *computes* the left derived functor `LF` of
`F : 𝒟 ⥤ 𝒟'` relative to `W`: the left derived functor is defined at `X`, i.e. some cone `c` on
the pro-object `W/X ⟶ 𝒟'`, `(s : X' ⟶ X) ↦ F(X')` exhibits its vertex as a value `LF(X)`, and
the canonical map `LF(X) ⟶ F(X)` — the projection of `c` at the index `𝟙 X` — is an
isomorphism. -/
@[stacks 05SX, sga "4 XVII 5.5.5"]
public abbrev ComputesLeftDerived (F : D ⥤ D') (W : MorphismProperty D)
    [W.ContainsIdentities] (X : D) : Prop :=
  ∃ c, F.IsLeftDerivedValueAt W X c ∧
    IsIso (c.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)))

end CategoryTheory.Functor

end

end

section

/-!
# Values of derived functors as essentially constant (co)cones

A cocone `c` on the ind-object `X/W ⟶ 𝒟'`, `(s : X ⟶ X') ↦ F(X')`, is a value of `RF` at `X`
exactly when it carries an essential-constancy witness in the sense of Tag 05PU(1),
`CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith`, and dually for `LF`; the two
conditions are the same clauses. Consequently `RF` is defined at `X` iff the ind-object is an
essentially constant ind-object, a value is a colimit cocone (so it is unique up to unique
isomorphism), and "`RF` is defined at `X`" is carried along any reindexing of `X/W` by an
equivalence compatible with the diagrams. Dually for `LF`.

The index category `X/W` is filtered when `W` has a left calculus of fractions (Stacks 05Q0);
this is recorded as an instance, dual to the instance that `W/X` is cofiltered (Stacks 05Q4).
The comma categories `W.Under ⊤ X` and `W.Over ⊤ X` are also identified with the full
subcategories of `StructuredArrow X (𝟭 D)` and `CostructuredArrow (𝟭 D) X` on the arrows lying
in `W` (`MorphismProperty.underEquivStructuredArrow`,
`MorphismProperty.overEquivCostructuredArrow`), the presentation used by several results of
§13.14–§13.15, the diagrams agreeing on the nose.
-/

@[expose] public section

namespace CategoryTheory.MorphismProperty

open Limits

universe v₁ u₁

variable {D : Type u₁} [Category.{v₁} D] (W : MorphismProperty D)

/-- **Stacks 05Q0**, index category form: `X/W` is filtered when `W` has a left calculus of
fractions. A cocone on two objects is the Ore condition and a cocone on two parallel arrows is the
cancellation axiom. -/
@[sga "4 VI 6.5" "more general"]
theorem isFiltered_under_of_hasLeftCalculusOfFractions [W.HasLeftCalculusOfFractions] (X : D) :
    IsFiltered (W.Under ⊤ X) := by
  have : IsFilteredOrEmpty (W.Under ⊤ X) := by
    constructor
    · intro A B
      obtain ⟨q, hq⟩ := (RightFraction.mk A.hom A.prop B.hom).exists_leftFraction
      exact ⟨Under.mk ⊤ (B.hom ≫ q.s) (W.comp_mem _ _ B.prop q.hs),
        Under.homMk q.f hq.symm, Under.homMk q.s rfl, trivial⟩
    · intro A B a b
      obtain ⟨V, t, ht, hab⟩ := HasLeftCalculusOfFractions.ext a.right b.right A.hom A.prop
        (by rw [Under.w a, Under.w b])
      exact ⟨Under.mk ⊤ (B.hom ≫ t) (W.comp_mem _ _ B.prop ht), Under.homMk t rfl,
        Under.Hom.ext hab⟩
  exact { nonempty := ⟨Under.mk ⊤ (𝟙 X) (W.id_mem X)⟩ }

/-- If `W` has a left calculus of fractions, then `X/W` is filtered. -/
instance [W.HasLeftCalculusOfFractions] (X : D) : IsFiltered (W.Under ⊤ X) :=
  W.isFiltered_under_of_hasLeftCalculusOfFractions X

/-- `X/W` as Mathlib's `W.Under ⊤ X` maps to the full subcategory of `CategoryTheory.Under X`
(that is, of `StructuredArrow X (𝟭 D)`) on the arrows lying in `W`; see
`underEquivStructuredArrow`. -/
@[simps]
def underToStructuredArrow (X : D) :
    W.Under ⊤ X ⥤ ObjectProperty.FullSubcategory (fun f : CategoryTheory.Under X => W f.hom) where
  obj t := ⟨CategoryTheory.StructuredArrow.mk t.hom, t.prop⟩
  map f := ObjectProperty.homMk (CategoryTheory.StructuredArrow.homMk f.right (Under.w f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `underToStructuredArrow` is an equivalence of categories. -/
instance (X : D) : (W.underToStructuredArrow X).IsEquivalence where
  faithful := ⟨fun h => Under.Hom.ext (congrArg (fun g => g.hom.right) h)⟩
  full := ⟨fun f => ⟨Under.homMk f.hom.right (CategoryTheory.StructuredArrow.w f.hom), rfl⟩⟩
  essSurj := ⟨fun t => ⟨Under.mk ⊤ t.obj.hom t.property,
    ⟨ObjectProperty.isoMk _ (CategoryTheory.StructuredArrow.isoMk (Iso.refl _)
      (Category.comp_id _))⟩⟩⟩

/-- `X/W` as Mathlib's `W.Under ⊤ X` and as the full subcategory of `CategoryTheory.Under X`
(that is, of `StructuredArrow X (𝟭 D)`) on the arrows lying in `W` are equivalent. -/
noncomputable def underEquivStructuredArrow (X : D) :
    W.Under ⊤ X ≌ ObjectProperty.FullSubcategory (fun f : CategoryTheory.Under X => W f.hom) :=
  (W.underToStructuredArrow X).asEquivalence

/-- `W/X` as Mathlib's `W.Over ⊤ X` maps to the full subcategory of `CategoryTheory.Over X`
(that is, of `CostructuredArrow (𝟭 D) X`) on the arrows lying in `W`; see
`overEquivCostructuredArrow`. -/
@[simps]
def overToCostructuredArrow (X : D) :
    W.Over ⊤ X ⥤
      ObjectProperty.FullSubcategory (fun f : CategoryTheory.Over X => W f.hom) where
  obj t := ⟨CategoryTheory.CostructuredArrow.mk t.hom, t.prop⟩
  map f := ObjectProperty.homMk (CategoryTheory.CostructuredArrow.homMk f.left (Over.w f))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor `overToCostructuredArrow` is an equivalence of categories. -/
instance (X : D) : (W.overToCostructuredArrow X).IsEquivalence where
  faithful := ⟨fun h => Over.Hom.ext (congrArg (fun g => g.hom.left) h)⟩
  full := ⟨fun f => ⟨Over.homMk f.hom.left (CategoryTheory.CostructuredArrow.w f.hom), rfl⟩⟩
  essSurj := ⟨fun t => ⟨Over.mk ⊤ t.obj.hom t.property,
    ⟨ObjectProperty.isoMk _ (CategoryTheory.CostructuredArrow.isoMk (Iso.refl _)
      (Category.id_comp _))⟩⟩⟩

/-- `W/X` as Mathlib's `W.Over ⊤ X` and as the full subcategory of `CategoryTheory.Over X`
(that is, of `CostructuredArrow (𝟭 D) X`) on the arrows lying in `W` are equivalent. -/
noncomputable def overEquivCostructuredArrow (X : D) :
    W.Over ⊤ X ≌
      ObjectProperty.FullSubcategory (fun f : CategoryTheory.Over X => W f.hom) :=
  (W.overToCostructuredArrow X).asEquivalence

section Diagrams

variable {X : D}

/-- The target of `MorphismProperty.Under.mk` (Mathlib records only its `hom` and `left`). -/
@[simp]
lemma Under.mk_right {A : D} (f : X ⟶ A) (hf : W f) : (Under.mk ⊤ f hf).right = A :=
  rfl

variable {D' : Type*} [Category D'] (F : D ⥤ D')

/-- The ind-object `(s : X ⟶ X') ↦ F(X')` of Tag 05S9 on objects. -/
@[simp high]
lemma Under.forget_comp_forget_comp_obj (t : W.Under ⊤ X) :
    (Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F).obj t = F.obj t.right :=
  rfl

/-- The ind-object `(s : X ⟶ X') ↦ F(X')` of Tag 05S9 on morphisms. -/
@[simp high]
lemma Under.forget_comp_forget_comp_map {s t : W.Under ⊤ X} (u : s ⟶ t) :
    (Under.forget W ⊤ X ⋙ CategoryTheory.Under.forget X ⋙ F).map u = F.map u.right :=
  rfl

/-- The pro-object `(s : X' ⟶ X) ↦ F(X')` of Tag 05S9 on objects. -/
@[simp high]
lemma Over.forget_comp_forget_comp_obj (t : W.Over ⊤ X) :
    (Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F).obj t = F.obj t.left :=
  rfl

/-- The pro-object `(s : X' ⟶ X) ↦ F(X')` of Tag 05S9 on morphisms. -/
@[simp high]
lemma Over.forget_comp_forget_comp_map {s t : W.Over ⊤ X} (u : s ⟶ t) :
    (Over.forget W ⊤ X ⋙ CategoryTheory.Over.forget X ⋙ F).map u = F.map u.left :=
  rfl

end Diagrams

end CategoryTheory.MorphismProperty

namespace CategoryTheory.Functor

open Limits

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']
  (F : D ⥤ D') (W : MorphismProperty D) (X : D)

/-- A value of `RF` at `X` is a cocone carrying an essential-constancy witness (Tag 05PU(1)). -/
theorem isRightDerivedValueAt_iff
    (c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) :
    F.IsRightDerivedValueAt W X c ↔ ∃ s₀ r, EssentiallyConstantInd.IsEssentiallyConstantWith
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) c s₀ r :=
  ⟨fun ⟨s₀, r, h₁, h₂⟩ => ⟨s₀, r, h₁, fun s => (h₂ s).imp fun _ => exists_comm.1⟩,
    fun ⟨s₀, r, h⟩ => ⟨s₀, r, h.1, fun s => (h.2 s).imp fun _ => exists_comm.1⟩⟩

/-- `RF` is defined at `X` iff the ind-object `(s : X ⟶ X') ↦ F(X')` is essentially constant. -/
theorem exists_isRightDerivedValueAt_iff :
    (∃ c, F.IsRightDerivedValueAt W X c) ↔ EssentiallyConstantInd.IsEssentiallyConstantInd
      (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F) :=
  ⟨fun ⟨c, hc⟩ => ⟨c, (F.isRightDerivedValueAt_iff W X c).1 hc⟩,
    fun ⟨c, hc⟩ => ⟨c, (F.isRightDerivedValueAt_iff W X c).2 hc⟩⟩

/-- A value of `LF` at `X` is a cone carrying an essential-constancy witness (Tag 05PU(2)). -/
theorem isLeftDerivedValueAt_iff
    (c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)) :
    F.IsLeftDerivedValueAt W X c ↔ ∃ s₀ r, EssentiallyConstantPro.IsEssentiallyConstantWith
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) c s₀ r :=
  ⟨fun ⟨s₀, r, h₁, h₂⟩ => ⟨s₀, r, h₁, fun s => (h₂ s).imp fun _ => exists_comm.1⟩,
    fun ⟨s₀, r, h⟩ => ⟨s₀, r, h.1, fun s => (h.2 s).imp fun _ => exists_comm.1⟩⟩

/-- `LF` is defined at `X` iff the pro-object `(s : X' ⟶ X) ↦ F(X')` is essentially constant. -/
theorem exists_isLeftDerivedValueAt_iff :
    (∃ c, F.IsLeftDerivedValueAt W X c) ↔ EssentiallyConstantPro.IsEssentiallyConstantPro
      (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) :=
  ⟨fun ⟨c, hc⟩ => ⟨c, (F.isLeftDerivedValueAt_iff W X c).1 hc⟩,
    fun ⟨c, hc⟩ => ⟨c, (F.isLeftDerivedValueAt_iff W X c).2 hc⟩⟩

/-- `X` computes `RF` iff some essentially constant cocone on the ind-object has an invertible
coprojection at the index `𝟙 X`. -/
theorem computesRightDerived_iff [W.ContainsIdentities] :
    F.ComputesRightDerived W X ↔
      ∃ c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F),
        (∃ s₀ r, EssentiallyConstantInd.IsEssentiallyConstantWith _ c s₀ r) ∧
          IsIso (c.ι.app (MorphismProperty.Under.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X))) :=
  exists_congr fun c => and_congr_left' (F.isRightDerivedValueAt_iff W X c)

/-- `X` computes `LF` iff some essentially constant cone on the pro-object has an invertible
projection at the index `𝟙 X`. -/
theorem computesLeftDerived_iff [W.ContainsIdentities] :
    F.ComputesLeftDerived W X ↔
      ∃ c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F),
        (∃ s₀ r, EssentiallyConstantPro.IsEssentiallyConstantWith _ c s₀ r) ∧
          IsIso (c.π.app (MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X))) :=
  exists_congr fun c => and_congr_left' (F.isLeftDerivedValueAt_iff W X c)

variable {F W X}

/-- A value of `RF` at `X` is a colimit cocone of the ind-object. -/
noncomputable def IsRightDerivedValueAt.isColimit
    {c : Cocone (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)}
    (h : F.IsRightDerivedValueAt W X c) : IsColimit c :=
  ((F.isRightDerivedValueAt_iff W X c).1 h).choose_spec.choose_spec.isColimit

/-- A value of `LF` at `X` is a limit cone of the pro-object. -/
noncomputable def IsLeftDerivedValueAt.isLimit
    {c : Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F)}
    (h : F.IsLeftDerivedValueAt W X c) : IsLimit c :=
  isLimitOfOp ((EssentiallyConstantPro.isEssentiallyConstantWith_op
    ((F.isLeftDerivedValueAt_iff W X c).1 h).choose_spec.choose_spec).isColimit)

end CategoryTheory.Functor

end

end
