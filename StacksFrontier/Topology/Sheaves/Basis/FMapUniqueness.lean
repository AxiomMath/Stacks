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
# Stacks Project, Tag 009V — Lemma 6.30.14

A compatible family of basis-level morphisms `(φ_i : G(B i) ⟶ (f_*F)(B i))_{i : ι}`
extends uniquely to a sheaf morphism `G ⟶ f_*F` (i.e. an `f`-map `G ⟶ F`).

* Existence uses `TopCat.Sheaf.restrictHomEquivHom`, the equivalence between
  basis-restricted presheaf morphisms and presheaf morphisms into a sheaf.
* The basis-level recovery is `TopCat.Sheaf.extend_hom_app`.
* Uniqueness is `TopCat.Sheaf.hom_ext`: a sheaf morphism is determined by its
  restriction to a basis.
-/

@[expose] public section

universe v w u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

/-- The type of `f`-maps `G → F` for sheaves with values in an arbitrary category `C`, realized as
the morphisms of sheaves `G ⟶ f_* F` on `Y`. -/
@[sga "4 XVII 0.2.1" "(ii), special case"]
abbrev FMapParameterizedC {C : Type u} [Category.{v} C] {X Y : TopCat}
    (f : X ⟶ Y) (G : TopCat.Sheaf C Y) (F : TopCat.Sheaf C X) : Type _ :=
  G ⟶ (TopCat.Sheaf.pushforward C f).obj F

/-- A compatible family of basis-level morphisms for the family of opens `B : ι → Opens Y`: maps
`φ i : G(B i) ⟶ (f_* F)(B i)` commuting with the restrictions along the inclusions between the
`B i`.  Equivalently, a morphism between the presheaves `G` and `f_* F` restricted along `B`. -/
abbrev BasisCompatibleFamily {C : Type u} [Category.{v} C] {X Y : TopCat}
    (f : X ⟶ Y) (G : TopCat.Sheaf C Y) (F : TopCat.Sheaf C X)
    {ι : Type w} (B : ι → Opens Y) : Type _ :=
  (inducedFunctor B).op.comp G.obj ⟶
    (inducedFunctor B).op.comp ((TopCat.Sheaf.pushforward C f).obj F).obj

/-- **Stacks 009V.** Let `B : ι → Opens Y` be a family of opens whose range is a basis of `Y`.
Then every compatible family of basis-level morphisms `φ i : G(B i) ⟶ (f_* F)(B i)` extends to a
unique `f`-map `ψ : G ⟶ f_* F`, i.e. a unique sheaf morphism whose component at each `B i` is
`φ i`. -/
@[stacks 009V, ega "0 3.2.5" "second paragraph", ega "0 3.5.1" "special case"]
theorem fMap_basis_unique_extension
    {C : Type u} [Category.{v} C]
    {FC : C → C → Type _} {CC : C → Type v}
    [∀ (X Y : C), FunLike (FC X Y) (CC X) (CC Y)]
    [ConcreteCategory C FC]
    [HasLimits C] [HasColimits C]
    [PreservesLimits (forget C)] [PreservesFilteredColimits (forget C)]
    [(forget C).ReflectsIsomorphisms]
    {X Y : TopCat} (f : X ⟶ Y)
    (F : TopCat.Sheaf C X) (G : TopCat.Sheaf C Y)
    {ι : Type w} (B : ι → Opens Y) (hB : Opens.IsBasis (Set.range B))
    (φ : BasisCompatibleFamily f G F B) :
    ∃! ψ : FMapParameterizedC f G F, ∀ i : ι, ψ.hom.app (op (B i)) = φ.app (op i) := by
  let F' := (TopCat.Sheaf.pushforward C f).obj F
  refine ⟨ObjectProperty.homMk
      (TopCat.Sheaf.restrictHomEquivHom (B := B) G.obj F' hB φ),
    TopCat.Sheaf.extend_hom_app G.obj F' hB φ, fun ψ hψ => ?_⟩
  -- Uniqueness: a sheaf morphism is determined by its restriction to a basis.
  refine CategoryTheory.Sheaf.hom_ext <|
    TopCat.Sheaf.hom_ext G.obj F' hB fun i => ?_
  exact (hψ i).trans (TopCat.Sheaf.extend_hom_app G.obj F' hB φ i).symm
