module

public import Mathlib.Topology.Sheaves.Stalks
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
# Stacks 007A — separated presheaves of sets

Stacks 007A calls a presheaf of sets `F` on a topological space `X` *separated* when for every
open `U ⊆ X` the map `F(U) → ∏ x ∈ U, F_x` sending a section to the family of its germs is
injective.

Mathlib has the stalks and the germ maps but no form of this predicate, so both the germ-family
map `TopCat.Presheaf.toStalkProduct` and the predicate `TopCat.Presheaf.IsSeparated'` are
defined here. `isSeparated'_iff` restates the predicate in pointwise form: two sections over an
open `U` having the same germ at every point of `U` are equal.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (F : Presheaf (Type u) X)

/--
The canonical map from sections of a presheaf of sets `F` over an open `U`
to the product of stalks at all points of `U`, sending a section to the
family of its germs.
-/
@[ega "IV 21.9.1" "(21.9.1.1)"]
noncomputable def toStalkProduct (U : Opens X) :
    F.obj (Opposite.op U) → ∀ x : U, F.stalk x.1 :=
  fun s x => F.germ U x.1 x.2 s

/--
A presheaf of sets `F` on a topological space `X` is *separated* if for
every open subset `U ⊆ X`, the canonical map sending a section to the
family of its germs at the points of `U` is injective.
-/
@[stacks 007A,
  sga "3 IV 4.3.1" "special case",
  sga "3 IV 4.3.18" "special case",
  sga "4 II 2.1" "special case"]
def IsSeparated' : Prop :=
  ∀ U : Opens X, Function.Injective (toStalkProduct F U)

/--
Characterization of `IsSeparated'`: a presheaf of sets is separated if and
only if, for every open `U` and every pair of sections `s, t ∈ F(U)`,
if all germs of `s` and `t` agree at every point of `U` then `s = t`.
-/
theorem isSeparated'_iff :
    IsSeparated' F ↔
      ∀ (U : Opens X) (s t : F.obj (Opposite.op U)),
        (∀ x : X, ∀ h : x ∈ U, F.germ U x h s = F.germ U x h t) → s = t :=
  ⟨fun hSep U _ _ hGerms => hSep U (funext fun x => hGerms x.1 x.2),
    fun h U s t hst => h U s t fun x hx => congr_fun hst ⟨x, hx⟩⟩

end TopCat.Presheaf

