module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
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
public import Mathlib.Topology.Sheaves.LocalPredicate
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0074 — continuous real-valued functions form a sheaf of `ℝ`-algebras

Stacks 0074 considers, on a topological space `X`, the presheaf assigning to an open `U ⊆ X` the
commutative `ℝ`-algebra `C(U, ℝ)` of continuous real-valued functions on `U`, with restriction
along `V ⊆ U` given by precomposition with the inclusion, and asserts that it is a sheaf of
`ℝ`-algebras over `X`.

## Main definitions

* `presheafC0`: the presheaf `U ↦ C(U, ℝ)` on `X` with values in `CommAlgCat ℝ`.

## Main results

* `presheafC0_isSheaf`: `presheafC0 X` is a sheaf of `ℝ`-algebras.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits


/-- The presheaf of (commutative) `ℝ`-algebras on a topological space `X`
whose sections over an open `U ⊆ X` are the commutative `ℝ`-algebra
`C(U, ℝ)` of continuous real-valued functions on `U`. The restriction map
associated to an inclusion of opens `V ⊆ U` is precomposition with the
inclusion `V ↪ U`, which is an `ℝ`-algebra homomorphism via
`ContinuousMap.compRightAlgHom`. -/
def presheafC0 (X : TopCat.{0}) : TopCat.Presheaf (CommAlgCat.{0} ℝ) X where
  obj U := CommAlgCat.of ℝ C((unop U : Opens X), ℝ)
  map {U V} i := CommAlgCat.ofHom (ContinuousMap.compRightAlgHom ℝ ℝ
    ⟨fun x => ⟨x.1, i.unop.le x.2⟩, by fun_prop⟩)
  map_id U := by ext f x; rfl
  map_comp {U V W} f g := by ext h x; rfl

/-- A continuous function `U → ℝ`, as a morphism of topological spaces from `U` to `ℝ`. -/
def presheafC0ForgetIsoCompUp (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    C(↑(unop U), ℝ) →
      ((Opens.toTopCat X).obj (unop U) ⟶ TopCat.of ℝ) := fun f =>
  TopCat.ofHom (f : C(↑(unop U), ℝ))

/-- A morphism of topological spaces from `U` to `ℝ`, as a continuous function `U → ℝ`. -/
def presheafC0ForgetIsoCompDown (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    ((Opens.toTopCat X).obj (unop U) ⟶ TopCat.of ℝ) →
      C(↑(unop U), ℝ) := fun g =>
  TopCat.Hom.hom g

/-- Componentwise iso between `(presheafC0 X ⋙ forget _).obj U` and
`(TopCat.presheafToTop X (TopCat.of ℝ)).obj U`. -/
def presheafC0_forget_isoComp (X : TopCat.{0}) (U : (Opens X)ᵒᵖ) :
    (presheafC0 X ⋙ forget (CommAlgCat.{0} ℝ)).obj U ≅
      (TopCat.presheafToTop X (TopCat.of ℝ)).obj U where
  hom := TypeCat.ofHom (presheafC0ForgetIsoCompUp X U)
  inv := TypeCat.ofHom (presheafC0ForgetIsoCompDown X U)
  hom_inv_id := by ext f; rfl
  inv_hom_id := by ext g; rfl

/-- Natural iso between the type-valued presheaf `presheafC0 X ⋙ forget (CommAlgCat ℝ)`
and `TopCat.presheafToTop X (TopCat.of ℝ)`. -/
def presheafC0_forget_iso_presheafToTop (X : TopCat.{0}) :
    presheafC0 X ⋙ forget (CommAlgCat.{0} ℝ) ≅
      TopCat.presheafToTop X (TopCat.of ℝ) :=
  NatIso.ofComponents (fun U => presheafC0_forget_isoComp X U)
    (fun {U V} i => by ext f; rfl)

/-- The `Type`-valued presheaf obtained by composing `presheafC0 X` with the forgetful functor
`forget (CommAlgCat ℝ)` is a sheaf. -/
theorem presheafC0_forget_isSheaf (X : TopCat.{0}) :
    TopCat.Presheaf.IsSheaf (presheafC0 X ⋙ forget (CommAlgCat ℝ)) := by
  rw [TopCat.Presheaf.isSheaf_iso_iff (presheafC0_forget_iso_presheafToTop X)]
  exact (TopCat.sheafToTop (X := X) (TopCat.of ℝ)).property

/-- The forgetful functor `forget₂ (CommAlgCat ℝ) CommRingCat` preserves all small limits. -/
instance commAlgCat_forget₂_commRingCat_preservesLimits :
    PreservesLimits (forget₂ (CommAlgCat.{0} ℝ) CommRingCat.{0}) :=
  preservesLimits_of_natIso
    (F := (commAlgCatEquivUnder (CommRingCat.of ℝ)).functor ⋙ Under.forget _)
    (NatIso.ofComponents (fun _ => Iso.refl _) fun _ => by
      dsimp [commAlgCatEquivUnder, CommRingCat.mkUnder]
      rfl)

/-- The forgetful functor `forget (CommAlgCat ℝ) : CommAlgCat ℝ ⥤ Type _` preserves all small
limits. -/
@[sga "4 I 5.8.3" "Clause 2, special case"]
instance commAlgCat_forget_preservesLimits :
    PreservesLimits (forget (CommAlgCat.{0} ℝ)) :=
  inferInstanceAs (PreservesLimits (forget₂ (CommAlgCat.{0} ℝ) CommRingCat ⋙ forget CommRingCat))

/-- The presheaf of (commutative) `ℝ`-algebras of continuous real-valued
functions on a topological space `X` is a sheaf of `ℝ`-algebras. -/
@[stacks 0074, sga "4½ Arcata 1.2.3" "special case", sga "6 II AppII.3.0.1" "Y = ℝ"]
theorem presheafC0_isSheaf (X : TopCat.{0}) :
    (presheafC0 X).IsSheaf :=
  (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (forget (CommAlgCat.{0} ℝ)) (presheafC0 X)).mpr
    (presheafC0_forget_isSheaf X)


end
