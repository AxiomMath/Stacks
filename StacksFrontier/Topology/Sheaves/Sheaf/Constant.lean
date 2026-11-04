module
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Presheaf
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
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 006W — The constant sheaf

Let $X$ be a topological space and $A$ a set. The *constant sheaf* with value $A$, denoted
$\underline{A}$ or $\underline{A}_X$, is the sheafification of the constant presheaf with value
$A$; equivalently, by the previous example, it is the sheaf of locally constant maps into $A$.

`constantSheafOnSpace` is that sheafification, taken here for an arbitrary target category `C`
in place of sets, with `constantPresheafOnSpace` the constant presheaf it sheafifies. The
sheafification is for the Grothendieck topology `Opens.grothendieckTopology X` on the opens of
`X`, and `constantSheafOnSpace_eq_constantSheaf` identifies the result with Mathlib's
`CategoryTheory.constantSheaf` for that topology.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite

/-- The constant presheaf on a topological space `X` with value `A : C`,
i.e., the functor `(Opens X)ᵒᵖ ⥤ C` sending every open set to `A`
and every restriction map to the identity. -/
@[ega "0 3.6.1",
  sga "3 I 3.1.3" "special case",
  sga "4 IV 13.8" "special case",
  sga "4 IV 2.7.5" "special case",
  sga "4 IV 4.3.4" "special case",
  sga "4 IX 2.0" "partial",
  sga "4 V 7.3.1.6" "special case"]
noncomputable def constantPresheafOnSpace (X : TopCat) (C : Type*) [Category C] (A : C) :
    Presheaf C X :=
  (Functor.const (Opens X)ᵒᵖ).obj A

/-- The constant sheaf on a topological space `X` with value `A : C`,
defined as the sheafification of the constant presheaf with value `A`.
This is Stacks Tag 006W. -/
@[stacks 006W,
  ega "0 3.6.1" "simple sheaf",
  sga "4 IV 4.3.4" "sheaves on a space",
  sga "4 IV 11.1.5" "special case",
  sga "4 IV 2.7.5" "special case",
  sga "4 IX 2.0" "special case",
  sga "4 Vbis 4.1.0" "partial"]
noncomputable def constantSheafOnSpace (X : TopCat) (C : Type*) [Category C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (A : C) :
    Sheaf (Opens.grothendieckTopology X) C :=
  (presheafToSheaf (Opens.grothendieckTopology X) C).obj (constantPresheafOnSpace X C A)

/-- The constant sheaf on `X` with value `A` agrees with
`constantSheaf (Opens.grothendieckTopology X) C |>.obj A` from Mathlib. -/
noncomputable def constantSheafOnSpace_eq_constantSheaf (X : TopCat) (C : Type*) [Category C]
    [HasWeakSheafify (Opens.grothendieckTopology X) C] (A : C) :
    constantSheafOnSpace X C A ≅
      (constantSheaf (Opens.grothendieckTopology X) C).obj A :=
  Iso.refl _

