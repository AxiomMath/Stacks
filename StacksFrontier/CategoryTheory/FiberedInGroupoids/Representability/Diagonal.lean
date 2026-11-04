module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
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

/-! # Representability of the diagonal

Stacks 02YA (Lemma 4.42.6): for a category `𝒮` fibred in groupoids over a category `𝒞` having
products of pairs and fibre products, the diagonal `𝒮 ⟶ 𝒮 ×_𝒞 𝒮` is representable if and only
if for every object `U` every 1-morphism `𝒞/U ⟶ 𝒮` is representable.

Under the fibred-category ↔ functor dictionary, representability of 1-morphisms is Mathlib's
`Functor.relativelyRepresentable`: the diagonal condition becomes
`F.relativelyRepresentable (Limits.diag X)` for the classifying functor `F`, and the second
condition becomes `F.relativelyRepresentable g` for every `g : F.obj a ⟶ X`, the morphisms out
of a representable being the images of the slice functors `𝒞/U ⟶ 𝒮`.  The equivalence of the
two is `Functor.relativelyRepresentable.diag_iff`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.relativelyRepresentable

/-- **Stacks 02YA.** The diagonal is representable iff every morphism out of a representable
object is representable. Here `F : C ⥤ D` is full and preserves binary products and
pullbacks (the classifying functor of a category fibred in groupoids), `𝒞` has products of
pairs and fibre products, and `X : D`. -/
@[stacks 02YA]
theorem diagonal_representable_iff
    {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D) (X : D)
    [HasPullbacks C] [HasBinaryProducts C]
    [HasBinaryProducts D] [HasPullbacks D] [HasTerminal D]
    [F.Full] [PreservesLimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape WalkingCospan F] :
    F.relativelyRepresentable (Limits.diag X) ↔
      ∀ ⦃a : C⦄ (g : F.obj a ⟶ X), F.relativelyRepresentable g :=
  Functor.relativelyRepresentable.diag_iff

end CategoryTheory.Functor.relativelyRepresentable
