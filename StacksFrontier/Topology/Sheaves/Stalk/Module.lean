module

public import Mathlib.Algebra.Category.ModuleCat.Stalk
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
# The stalk of a presheaf of modules is a module over the stalk of rings

Let `X` be a topological space, `R` a presheaf of rings on `X`, `M` a presheaf of `R`-modules
and `x` a point of `X`. Tag 007J states that the map `R_x × M_x → M_x` induced by the
multiplication `R × M → M` makes the abelian group `M_x` a module over the ring `R_x`.

The module structure is Mathlib's instance `Module (R.stalk x) (M.presheaf.stalk x)`, named
here `stalk_module_structure`. The multiplication map `muStalk` is the scalar action, and the
action is characterized by `germ (r • m) = germ r • germ m` (`germ_smul_eq`).

## Main definitions

* `stalk_module_structure`: the `R_x`-module structure on `M_x`.
* `muStalk`: the multiplication map `R_x × M_x → M_x`.

## Main results

* `mu_x_eq_smul`: `muStalk` is the scalar action.
* `germ_smul_eq`: the germ of `r • m` is the germ of `r` acting on the germ of `m`.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace Opposite

universe u

variable {X : TopCat.{u}} (R : TopCat.Presheaf RingCat.{u} X)
  (M : PresheafOfModules.{u} R) (x : X)

/-- The stalk at `x` of the presheaf of rings `R`. -/
noncomputable def stalkRing : RingCat.{u} := R.stalk x

/-- The stalk at `x` of the underlying abelian-group-valued presheaf of `M`. -/
noncomputable def stalkMod : Ab.{u} := TopCat.Presheaf.stalk M.presheaf x

/-- The multiplication map `R_x × M_x → M_x` on stalks. -/
noncomputable def muStalk :
    ↑(R.stalk x) × ↑(TopCat.Presheaf.stalk M.presheaf x) →
      ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  fun p => p.1 • p.2

/-- The canonical `Module (R.stalk x)`-structure on `TopCat.Presheaf.stalk M.presheaf x`. -/
@[reducible, stacks 007J]
noncomputable def stalk_module_structure :
    Module ↑(R.stalk x) ↑(TopCat.Presheaf.stalk M.presheaf x) :=
  inferInstance

/-- `muStalk` is the scalar action of `R_x` on `M_x`. -/
theorem mu_x_eq_smul (r : ↑(R.stalk x)) (m : ↑(TopCat.Presheaf.stalk M.presheaf x)) :
    muStalk R M x (r, m) = r • m :=
  rfl

