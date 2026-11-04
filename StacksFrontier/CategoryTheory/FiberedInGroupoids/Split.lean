module

import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.CategoryTheory.FiberedInGroupoids
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic.NormNum.Parity
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.Data.NNRat.Floor
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Sheaves.Init
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic

public import StacksFrontier.CategoryTheory.FiberedCategory.Split

/-!
# Split categories fibred in groupoids

Let `𝒞` be a category. A presheaf of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd` gives rise to a category fibred
in groupoids `p_F : 𝒮_F ⥤ 𝒞` by the Grothendieck construction (Stacks 0049), and a category fibred
in groupoids is *split* (Stacks 04TL) when it is isomorphic over `𝒞` — isomorphic, not merely
equivalent — to one of these.

## Main definitions

* `CategoryTheory.presheafOfGroupoids`: the category over `𝒞` attached to a presheaf of
  groupoids, i.e. `𝒮_F` together with `p_F`;
* `CategoryTheory.Functor.IsSplitFiberedInGroupoids`: Stacks 04TL.

## Implementation notes

Stacks 0049 is the special case of Stacks 02XV where the presheaf of categories takes values in
groupoids, and the source's construction of `𝒮_F` is verbatim the same; accordingly
`presheafOfGroupoids F` is `presheafOfCategories (F ⋙ Grpd.forgetToCat)`, with `Grpd.forgetToCat`
the inclusion of groupoids into categories. Its being a fibred category is Mathlib's
`Pseudofunctor.CoGrothendieck.instIsFiberedForget`; that its fibre categories are groupoids, so
that it is fibred in groupoids, is the extra content of Stacks 0049 and is not proved here, which
is why the definition below carries the source's hypothesis that `p` is fibred in groupoids as an
explicit conjunct rather than deriving it.

See `StacksFrontier/CategoryTheory/FiberedCategory/Split.lean` for the universe conventions, which
are the same here.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **Stacks 0049**, as a category over `𝒞`: the category `p_F : 𝒮_F ⥤ 𝒞` attached to a presheaf
of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd`, viewed as an object of the 2-category of categories over `𝒞`. It is
the category attached by Stacks 02XV to `F` regarded as a presheaf of categories. -/
abbrev presheafOfGroupoids (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂}) : BasedCategory 𝒞 :=
  presheafOfCategories (F ⋙ Grpd.forgetToCat)

/-- **Stacks 04TL.**
A *split category fibred in groupoids* over `𝒞` is a category fibred in groupoids `p : 𝒮 ⥤ 𝒞`
that is isomorphic over `𝒞` to the category `𝒮_F` attached to some presheaf of groupoids
`F : 𝒞ᵒᵖ ⥤ Grpd` (Stacks 0049). The source is explicit that isomorphism over `𝒞`, and not merely
equivalence over `𝒞`, is meant. -/
@[stacks 04TL]
def Functor.IsSplitFiberedInGroupoids (p : 𝒮 ⥤ 𝒞) : Prop :=
  p.IsFiberedInGroupoids ∧ ∃ F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, u₂},
    (BasedCategory.ofFunctor p).IsoOver (presheafOfGroupoids F)

/-- A split category fibred in groupoids is a category fibred in groupoids. -/
lemma Functor.IsSplitFiberedInGroupoids.isFiberedInGroupoids {p : 𝒮 ⥤ 𝒞}
    (h : p.IsSplitFiberedInGroupoids) : p.IsFiberedInGroupoids :=
  h.1

/-- A split category fibred in groupoids is in particular a split fibred category (Stacks 02XW):
a presheaf of groupoids is a presheaf of categories, and a category fibred in groupoids is a
fibred category. -/
lemma Functor.IsSplitFiberedInGroupoids.isSplitFibered {p : 𝒮 ⥤ 𝒞}
    (h : p.IsSplitFiberedInGroupoids) : p.IsSplitFibered := by
  obtain ⟨hp, F, hF⟩ := h
  exact ⟨hp.isFibered, F ⋙ Grpd.forgetToCat, hF⟩

end CategoryTheory
