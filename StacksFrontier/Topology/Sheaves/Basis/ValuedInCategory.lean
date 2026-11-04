module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
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
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 009P — Presheaves and sheaves with values in a category on a basis

Stacks 009P defines presheaves and sheaves with values in a category `C` on a basis `B` for the
topology of a space `X`.

The basis is packaged as `SheafOnBasis.Basis X`, a set of opens whose underlying sets form a
topological basis, and `SheafOnBasis.BasisOpens` is the full subcategory of `Opens X` it cuts out.

Clause (1) is `PresheafOnBasis`: a presheaf with values in `C` on `B` is a functor
`(BasisOpens B)ᵒᵖ ⥤ C`, i.e. a functor on the poset `B` ordered by reverse inclusion. Clause (2),
`MorphismOnBasis`, is a morphism of such presheaves, namely a natural transformation. Clause (3),
`underlyingPresheafOnBasis`, is the underlying set-valued presheaf obtained by post-composing with
a forgetful functor `F₀ : C ⥤ Type`. Clause (4) is `SheafOnBasisStruct`: a presheaf with values in
`C` on `B` together with the sheaf condition, which by definition is the set-valued basis-sheaf
condition `IsSheafOnBasisOfTypes` on its underlying presheaf — every family of sections over a
basis cover of `U ∈ B` that agrees on all basis opens contained in pairwise intersections glues
to a unique section over `U`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe v u

variable {X : Type} [TopologicalSpace X]

namespace SheafOnBasis

/-- A basis for the topology of `X`, packaged as a set of opens of `X` whose underlying sets form
a topological basis. -/
structure Basis (X : Type) [TopologicalSpace X] where
  /-- The opens belonging to the basis. -/
  carrier : Set (Opens X)
  /-- Their underlying sets form a basis for the topology of `X`. -/
  isBasis : IsTopologicalBasis ((fun U : Opens X => (U : Set X)) '' carrier)

/-- The basis `B` viewed as a category: the full subcategory of `Opens X`, ordered by inclusion,
spanned by the members of `B`. -/
abbrev BasisOpens (B : Basis X) : Type :=
  ObjectProperty.FullSubcategory (C := Opens X) (fun U => U ∈ B.carrier)

/-- A presheaf with values in `C` on the basis `B` (Stacks 009P (1)): a functor on the members of
`B` ordered by reverse inclusion. -/
@[stacks 009P "(1)", ega "0 3.2.1" "definition"]
abbrev PresheafOnBasis (B : Basis X) (C : Type u) [Category.{v} C] :
    Type max v u :=
  (BasisOpens B)ᵒᵖ ⥤ C

/-- A morphism of presheaves with values in `C` on the basis `B` (Stacks 009P (2)): a natural
transformation. -/
@[stacks 009P "(2)", ega "0 3.2.3" "morphism definition", sga "3 I 2.1.1" "morphism of Ĉ-groups"]
abbrev MorphismOnBasis {B : Basis X} {C : Type u} [Category.{v} C]
    (F G : PresheafOnBasis B C) : Type _ := F ⟶ G

/-- The underlying set-valued presheaf on the basis `B` of a presheaf with values in `C`
(Stacks 009P (3)), obtained by post-composing with a forgetful functor `F₀ : C ⥤ Type v`. -/
@[stacks 009P "(3)", sga "4 II 6.3.0" "object assignment of ε^"]
def underlyingPresheafOnBasis {B : Basis X} {C : Type u} [Category.{v} C]
    (F₀ : C ⥤ Type v) (F : PresheafOnBasis B C) : PresheafOnBasis B (Type v) :=
  F ⋙ F₀

/-- The sheaf condition for a set-valued presheaf on the basis `B`: for every `U ∈ B` and every
cover of `U` by basis opens `V i`, a family of sections `s i` that agree after restriction to
every basis open contained in `V i ⊓ V j` glues to a unique section over `U`. -/
@[ega "0 3.2.2"]
def IsSheafOnBasisOfTypes {B : Basis X} (F : PresheafOnBasis B (Type v)) :
    Prop :=
  ∀ ⦃U : Opens X⦄ (hU : U ∈ B.carrier) ⦃ι : Type v⦄ (V : ι → Opens X)
    (hV : ∀ i, V i ∈ B.carrier) (hcov : U = iSup V)
    (s : ∀ i, F.obj (op ⟨V i, hV i⟩)),
    (∀ (i j : ι) ⦃W : Opens X⦄ (hW : W ∈ B.carrier)
      (hWi : W ≤ V i) (hWj : W ≤ V j),
      F.map (Quiver.Hom.op
        ((⟨homOfLE hWi⟩ : (⟨W, hW⟩ : BasisOpens B) ⟶ ⟨V i, hV i⟩))) (s i) =
      F.map (Quiver.Hom.op
        ((⟨homOfLE hWj⟩ : (⟨W, hW⟩ : BasisOpens B) ⟶ ⟨V j, hV j⟩))) (s j)) →
    ∃! σ : F.obj (op ⟨U, hU⟩),
      ∀ i, F.map (Quiver.Hom.op
        ((⟨homOfLE (hcov.symm ▸ (le_iSup V i : V i ≤ iSup V))⟩ :
          (⟨V i, hV i⟩ : BasisOpens B) ⟶ ⟨U, hU⟩))) σ = s i

/-- A presheaf with values in `C` on the basis `B` is a sheaf when its underlying set-valued
presheaf, taken along the forgetful functor `F₀`, satisfies the basis-sheaf condition. -/
def IsSheafOnBasis {B : Basis X} {C : Type u} [Category.{v} C]
    (F₀ : C ⥤ Type v) (F : PresheafOnBasis B C) : Prop :=
  IsSheafOnBasisOfTypes (underlyingPresheafOnBasis F₀ F)

/-- A sheaf with values in `C` on the basis `B` (Stacks 009P (4)): a presheaf with values in `C`
on `B` together with the sheaf condition on its underlying sets. -/
@[stacks_fixed 009P "(4)"]
structure SheafOnBasisStruct (B : Basis X) (C : Type u) [Category.{v} C]
    (F₀ : C ⥤ Type v) where
  /-- The underlying presheaf with values in `C` on `B`. -/
  presheaf : PresheafOnBasis B C
  /-- The sheaf condition, imposed on the underlying set-valued presheaf. -/
  is_sheaf : IsSheafOnBasis F₀ presheaf

end SheafOnBasis

