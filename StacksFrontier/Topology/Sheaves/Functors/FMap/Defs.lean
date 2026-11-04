module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Sheaves.Functors
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
# Stacks 008J — f-maps as morphisms into the pushforward

A family of component maps `app V : G(V) → F(f⁻¹V)` satisfies the Stacks compatibility square
iff it is the family of components of a sheaf morphism `G ⟶ f_* F`, where `f_*` is
`TopCat.Sheaf.pushforward (Type u) f`. The compatibility condition is `IsStacksCompatible`,
the identification is `isStacksCompatible_iff_pushforward_hom`, and `FMap` names the type of
`f`-maps itself.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite


universe u

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- The type of `f`-maps from `G` to `F` along `f : X ⟶ Y`, realized as the morphisms of sheaves
of sets `G ⟶ f_* F` on `Y`. -/
@[ega "0 3.5.1" "special case", sga "4 XVII 0.2.1" "(ii), special case"]
abbrev FMap (G : TopCat.Sheaf (Type u) Y) (F : TopCat.Sheaf (Type u) X) : Type u :=
  G ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj F

/-- **Stacks 008J.** The compatibility condition on a family of section-level maps
`app V : G(V) → F(f⁻¹V)`: for every inclusion `V' ≤ V` of opens of `Y`, restricting `app V s` to
`f⁻¹V'` gives `app V'` applied to the restriction of `s`.  This is the commuting square of the
Stacks text. -/
@[stacks 008J]
def IsStacksCompatible
    (G : TopCat.Sheaf (Type u) Y) (F : TopCat.Sheaf (Type u) X)
    (app : ∀ V : Opens Y, G.1.obj (op V) → F.1.obj (op ((Opens.map f).obj V))) :
    Prop :=
  ∀ {V V' : Opens Y} (hV : V' ⟶ V) (s : G.1.obj (op V)),
    F.1.map ((Opens.map f).map hV).op (app V s) = app V' (G.1.map hV.op s)

/-- A family of section-level maps `app V : G(V) → F(f⁻¹V)` satisfies the compatibility square of
Stacks 008J if and only if it is the family of components of a morphism of sheaves
`G ⟶ f_* F`.  Naturality of such a morphism is exactly the square, and conversely a compatible
family assembles into a natural transformation of the underlying presheaves. -/
theorem isStacksCompatible_iff_pushforward_hom
    (G : TopCat.Sheaf (Type u) Y) (F : TopCat.Sheaf (Type u) X)
    (app : ∀ V : Opens Y, G.1.obj (op V) → F.1.obj (op ((Opens.map f).obj V))) :
    IsStacksCompatible f G F app ↔
      ∃ η : FMap f G F,
        ∀ (V : Opens Y) (s : G.1.obj (op V)),
          ((TopCat.Sheaf.forget (Type u) Y).map η).app (op V) s = app V s := by
  refine ⟨fun hcompat => ?_, fun ⟨η, hrec⟩ V V' hV s => ?_⟩
  · -- Package `app` as a natural transformation between underlying presheaves.
    refine ⟨⟨{ app := fun V => TypeCat.ofHom (app V.unop)
               naturality := ?_ }⟩, fun _ _ => rfl⟩
    intro V V' φ
    ext s
    exact (hcompat φ.unop s).symm
  · -- Naturality of `η.val` at `hV.op` gives the Stacks compatibility square.
    rw [← hrec V s, ← hrec V' (G.1.map hV.op s)]
    exact (NatTrans.naturality_apply ((TopCat.Sheaf.forget (Type u) Y).map η) hV.op s).symm
