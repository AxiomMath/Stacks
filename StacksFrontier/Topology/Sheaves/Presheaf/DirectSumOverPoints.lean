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
/-!
# Stacks tag 006L — the direct-sum-of-points presheaf

Let `X` be a topological space, and for each `x : X` an abelian group `M x`. For an
open `U ⊆ X` set `F(U) = ⨁_{x ∈ U} M x`. Restriction `F(U) → F(V)` for `V ≤ U` sends a
generator `m ∈ M x` to itself if `x ∈ V` and to `0` otherwise. This assembles into a
presheaf of abelian groups on `X`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u


variable (X : TopCat.{u}) (M : X → Type u) [∀ x, AddCommGroup (M x)]

/-- The underlying type of `F(U) = ⨁_{x ∈ U} M x`. -/
@[implicit_reducible]
noncomputable def F_obj (U : Opens X) : Type u :=
  DirectSum {x : X // x ∈ U} (fun i => M i.val)

/-- The abelian group structure on `F(U) = ⨁_{x ∈ U} M x`, namely the componentwise one carried
by the direct sum. -/
noncomputable instance F_obj_addCommGroup (U : Opens X) :
    AddCommGroup (F_obj X M U) := by
  unfold F_obj
  infer_instance

open Classical in
/-- The restriction map `F(U) → F(V)` for an inclusion `V ⊆ U`, defined on a generator
`m ∈ M x` (with `x ∈ U`) by keeping it if `x ∈ V` and sending it to zero otherwise. -/
noncomputable def F_map {U V : Opens X} :
    F_obj X M U →+ F_obj X M V :=
  DirectSum.toAddMonoid fun (i : {x : X // x ∈ U}) =>
    if hi : i.val ∈ V then
      (DirectSum.of (fun j : {x // x ∈ V} => M j.val) ⟨i.val, hi⟩)
    else 0

open Classical in
/-- Characterisation of `F_map` on a generator: it preserves the generator if the index
lies in `V`, and sends it to zero otherwise. -/
theorem F_map_of {U V : Opens X} (x : X) (hxU : x ∈ U) (m : M x) :
    F_map X M (U := U) (V := V)
        ((DirectSum.of (fun i : {x : X // x ∈ U} => M i.val) ⟨x, hxU⟩) m) =
      if hxV : x ∈ V then
        (DirectSum.of (fun j : {x : X // x ∈ V} => M j.val) ⟨x, hxV⟩) m
      else 0 := by
  rw [F_map, DirectSum.toAddMonoid_of]
  dsimp only
  split_ifs with h <;> rfl

/-- The restriction along the identity inclusion `U ≤ U` is the identity map. -/
theorem F_map_id (U : Opens X) :
    F_map X M (U := U) (V := U) = AddMonoidHom.id (F_obj X M U) := by
  classical
  refine DirectSum.addHom_ext fun ⟨x, hxU⟩ m => ?_
  rw [F_map_of X M (V := U) x hxU m, dite_eq_left hxU]
  rfl

/-- Restriction is compatible with composition of inclusions. -/
theorem F_map_comp {U V W : Opens X} (hWV : W ≤ V) :
    F_map X M (U := U) (V := W) =
      (F_map X M (U := V) (V := W)).comp (F_map X M (U := U) (V := V)) := by
  classical
  refine DirectSum.addHom_ext fun ⟨x, hxU⟩ m => ?_
  rw [AddMonoidHom.comp_apply, F_map_of X M (V := W) x hxU m, F_map_of X M (V := V) x hxU m]
  by_cases hxV : x ∈ V
  · rw [dite_eq_left hxV, F_map_of X M (V := W) x hxV m]
  · rw [dite_eq_right hxV, dite_eq_right (fun hxW => hxV (hWV hxW))]
    exact (map_zero _).symm

/-- The direct-sum-of-points presheaf of abelian groups on `X`. -/
@[stacks 006L]
noncomputable def F : TopCat.Presheaf AddCommGrpCat.{u} X where
  obj U := AddCommGrpCat.of (F_obj X M (Opposite.unop U))
  map {U V} _ := AddCommGrpCat.ofHom (F_map X M)
  map_id U := by
    rw [F_map_id X M (Opposite.unop U)]
    rfl
  map_comp {U V W} _ g := by
    rw [F_map_comp X M g.unop.le]
    rfl
