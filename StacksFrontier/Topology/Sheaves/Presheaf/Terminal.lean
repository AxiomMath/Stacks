module
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
# Stacks 006H — The singleton presheaf is a final presheaf of sets

Stacks 006H observes that the rule assigning a singleton set to every open of a topological
space `X` is a presheaf of sets — the restriction maps exist and are unique because every set
has a unique map to a singleton — and that it is a final object of the category of presheaves
of sets on `X`, hence unique up to unique isomorphism. It is written `*` in the Stacks Project.

Here `singletonPresheaf` is the constant functor at `PUnit`, `singletonPresheaf_isTerminal`
proves it is a terminal object, and `singletonPresheaf_uniqueUpToUniqueIso` deduces the
uniqueness: for any terminal presheaf `F`, the isomorphisms `F ≅ *` form a nonempty
subsingleton.
-/

@[expose] public section


universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- The singleton presheaf on a topological space `X`: the constant functor at
`PUnit` from `(Opens X)^op` to `Type u`; this is the presheaf written `*` in Stacks 006H, whose
final-object and uniqueness claims are registered on `singletonPresheaf_isTerminal` and
`singletonPresheaf_uniqueUpToUniqueIso`. -/
@[ega "0 8.1.10" "special case"]
def singletonPresheaf (X : TopCat) : TopCat.Presheaf (Type u) X :=
  (Functor.const (Opens X)ᵒᵖ).obj PUnit.{u+1}

/-- The singleton presheaf is a terminal object in the category of presheaves
of sets on `X`. -/
@[stacks 006H "final object", sga "4 VI 7.4.13.5" "special case"]
def singletonPresheaf_isTerminal (X : TopCat) :
    IsTerminal (singletonPresheaf.{u} X) :=
  IsTerminal.ofUniqueHom
    (fun _ => { app := fun _ => ↾fun _ => PUnit.unit })
    (fun _ _ => by ext; rfl)

/-- The singleton presheaf is unique up to unique isomorphism: for any terminal
presheaf `F`, the type of isomorphisms `F ≅ *` is nonempty and a subsingleton. -/
@[stacks 006H "unique up to unique isomorphism", ega "0 8.1.10" "special case"]
theorem singletonPresheaf_uniqueUpToUniqueIso (X : TopCat)
    (F : TopCat.Presheaf (Type u) X) (hF : IsTerminal F) :
    Nonempty (F ≅ singletonPresheaf.{u} X) ∧
      Subsingleton (F ≅ singletonPresheaf.{u} X) :=
  ⟨⟨hF.uniqueUpToIso (singletonPresheaf_isTerminal X)⟩,
    ⟨fun α β => Iso.ext ((singletonPresheaf_isTerminal X).hom_ext α.hom β.hom)⟩⟩

