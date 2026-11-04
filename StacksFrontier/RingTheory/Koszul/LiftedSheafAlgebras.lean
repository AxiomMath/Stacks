module

public import StacksFrontier.RingTheory.Koszul.IdealPowerQuotientSystem
public import Mathlib.Order.ULift

/-!
# The towers of Section 24.35 as sheaves on the natural numbers lifted to the universe of the ring

Proposition 0GZK and Remark 0H1E compare sheaves of differential graded algebras on `ℕ` with the
chaotic topology. The triangulated structure of the derived category of such a sheaf and the
calculus of fractions on its quasi-isomorphisms (Tag 0FT4) are available in this library for a
site whose category, morphisms and sheaf of rings live in one universe. For a ring `R : Type u`
the site is therefore taken to be `Stacks.LiftedNat.{u}`, the natural numbers lifted to `Type u`
with their order, which as a category is isomorphic to `ℕ`. It is a type synonym of
`ULift.{u} ℕ` carrying only the order, so that the category structure is the one of the
preorder, with morphisms in `Type u`, and not the one `ULift` inherits from `ℕ`.

## Main definitions

* `Stacks.LiftedNat`: the natural numbers in `Type u`, with their order.
* `Stacks.LiftedNat.toNat`, `Stacks.LiftedNat.ofNat`: the two mutually inverse order isomorphisms,
  as functors.
* `Stacks.LiftedNat.liftDiagram`: an inverse system indexed by `ℕ` read as one indexed by
  `Stacks.LiftedNat`.
* `DifferentialGradedAlgebra.SystemProIso.lift`: a pro-isomorphism of inverse systems indexed by
  `ℕ`, read over `Stacks.LiftedNat`.
* `Koszul.liftedPowSheafAlgebra`, `Koszul.liftedPowQuotientSheafAlgebra` and
  `Koszul.liftedIdealPowSheafAlgebra`: the sheaves `ℬ = (K_n)`, `𝒜' = (R / (f₁ ^ n, …, f_r ^ n))`
  and `𝒜 = (R / I ^ n)` of the proof of Proposition 0GZK, on the chaotic site
  `Stacks.LiftedNat.{u}`.

## References

* [Stacks Project, Section 24.35 (Tag 0GZG)](https://stacks.math.columbia.edu/tag/0GZG)
* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace Stacks

/-- **The natural numbers in `Type u`, with their order.** A type synonym of `ULift.{u} ℕ` that
carries only the order, so that as a category it is the preorder category, with morphisms in
`Type u`. -/
def LiftedNat : Type u := ULift.{u} ℕ

namespace LiftedNat

/-- The linear order on `LiftedNat` transported from `ℕ`. -/
instance : LinearOrder LiftedNat.{u} := inferInstanceAs (LinearOrder (ULift.{u} ℕ))

/-- The underlying natural number. -/
def down (n : LiftedNat.{u}) : ℕ := ULift.down n

/-- A natural number, lifted. -/
def up (n : ℕ) : LiftedNat.{u} := ULift.up n

/-- Lowering a lifted natural number recovers it. -/
@[simp] theorem down_up (n : ℕ) : (up.{u} n).down = n := rfl

/-- Lifting the underlying natural number recovers the element of `LiftedNat`. -/
@[simp] theorem up_down (n : LiftedNat.{u}) : up n.down = n := rfl

/-- `down` preserves and reflects the order. -/
theorem down_le_down_iff {m n : LiftedNat.{u}} : m.down ≤ n.down ↔ m ≤ n := Iff.rfl

/-- `up` preserves and reflects the order. -/
theorem up_le_up_iff {m n : ℕ} : up.{u} m ≤ up n ↔ m ≤ n := Iff.rfl

/-- The underlying natural number, as a functor. -/
def toNat : LiftedNat.{u} ⥤ ℕ := Monotone.functor fun _ _ h => down_le_down_iff.2 h

/-- Lifting a natural number, as a functor. -/
def ofNat : ℕ ⥤ LiftedNat.{u} := Monotone.functor fun _ _ h => up_le_up_iff.2 h

/-- The functor `toNat` sends `n` to its underlying natural number. -/
@[simp] theorem toNat_obj (n : LiftedNat.{u}) : toNat.obj n = n.down := rfl

/-- The functor `ofNat` sends a natural number to its lift. -/
@[simp] theorem ofNat_obj (n : ℕ) : ofNat.{u}.obj n = up n := rfl

/-- An inverse system indexed by `ℕ`, read as one indexed by `LiftedNat`. -/
def liftDiagram {D : Type*} [Category D] (A : ℕᵒᵖ ⥤ D) : LiftedNat.{u}ᵒᵖ ⥤ D :=
  toNat.op ⋙ A

/-- The value of `liftDiagram A` at `n` is the value of `A` at the underlying natural number. -/
@[simp] theorem liftDiagram_obj {D : Type*} [Category D] (A : ℕᵒᵖ ⥤ D) (n : LiftedNat.{u}ᵒᵖ) :
    (liftDiagram A).obj n = A.obj (op n.unop.down) := rfl

end LiftedNat

end Stacks

namespace DifferentialGradedAlgebra.SystemProIso

open Stacks

variable {R : Type u} [CommRing R] {A B : ℕᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- A pro-isomorphism of inverse systems indexed by `ℕ`, read over `LiftedNat`: the reindexings
are conjugated by the order isomorphism, and the representatives are unchanged. -/
def lift (e : SystemProIso A B) :
    SystemProIso (LiftedNat.liftDiagram.{u} A) (LiftedNat.liftDiagram.{u} B) where
  F₁ := LiftedNat.toNat ⋙ e.F₁ ⋙ LiftedNat.ofNat
  F₂ := LiftedNat.toNat ⋙ e.F₂ ⋙ LiftedNat.ofNat
  hom := { app := fun i => e.hom.app (op i.unop.down)
           naturality := fun _ _ g => e.hom.naturality (LiftedNat.toNat.op.map g) }
  inv := { app := fun i => e.inv.app (op i.unop.down)
           naturality := fun _ _ g => e.inv.naturality (LiftedNat.toNat.op.map g) }
  le₁ := fun i => e.le₁ i.down
  le₂ := fun i => e.le₂ i.down
  hom_inv := fun i => e.hom_inv i.down
  inv_hom := fun i => e.inv_hom i.down

end DifferentialGradedAlgebra.SystemProIso

namespace Koszul

open Stacks

variable {R : Type u} [CommRing R] {r : ℕ}

/-- **The sheaf `ℬ` of Proposition 0GZK**: the Koszul algebras on `f₁ ^ n, …, f_r ^ n`, on the
chaotic site `LiftedNat.{u}`. -/
def liftedPowSheafAlgebra (f : Fin r → R) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := LiftedNat.{u}) R) :=
  Stacks.ChaoticSite.systemAlgebra (LiftedNat.liftDiagram (powAlgebraDiagram f))

/-- **The sheaf `𝒜'`**: the quotients `R / (f₁ ^ n, …, f_r ^ n)`, on the chaotic site
`LiftedNat.{u}`. -/
def liftedPowQuotientSheafAlgebra (f : Fin r → R) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := LiftedNat.{u}) R) :=
  Stacks.ChaoticSite.systemAlgebra (LiftedNat.liftDiagram (powQuotientAlgebraDiagram f))

/-- **The sheaf `𝒜` of Proposition 0GZK and Remark 0H1E**: the quotients `R / I ^ n`, on the
chaotic site `LiftedNat.{u}`. -/
def liftedIdealPowSheafAlgebra (I : Ideal R) :
    SheafOfModules.DifferentialGradedAlgebra.{u, u}
      (Stacks.PresheafOfModules.constRingSheaf (C := LiftedNat.{u}) R) :=
  Stacks.ChaoticSite.systemAlgebra (LiftedNat.liftDiagram (idealPowQuotientAlgebraDiagram I))

/-- The quotient systems by the powers of `I = (f₁, …, f_r)` and by the ideals of powers of the
generators are pro-isomorphic, over `LiftedNat.{u}`. -/
def liftedPowQuotientIdealPowProIso (f : Fin r → R) :
    DifferentialGradedAlgebra.SystemProIso (LiftedNat.liftDiagram.{u} (powQuotientAlgebraDiagram f))
      (LiftedNat.liftDiagram.{u} (idealPowQuotientAlgebraDiagram (Ideal.span (Set.range f)))) :=
  (powQuotientIdealPowProIso f).lift

end Koszul
