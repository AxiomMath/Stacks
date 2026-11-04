module

public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.TotalSpace
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.AffineOpenDeRhamComparison

/-!
# Affine charts of the base of a line bundle

Let `f : X ⟶ S` be a morphism of schemes and `L` an invertible `𝒪_X`-module. An *affine chart* is
an affine open `U` of `X` lying over an affine open `V` of `S`. Over such a chart the relative
forms of `X` over `S` are the Kähler forms of `Γ(X, U)` over `Γ(S, V)`, by
`Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso`.

The charts of the total space of the line bundle (`Stacks.LineBundle.Situation.TotalChart`) and of
the complement of its zero section (`Stacks.LineBundle.Situation.BaseChart`) are affine charts with
extra data over `U`; the part of their local computations that only concerns `X` is stated here
once.

## Main definitions

* `CommRingCat.KaehlerDifferential.exteriorPowerEquiv`: the identity between the exterior powers of
  the two spellings of the Kähler differentials of a map of commutative rings.
* `Stacks.LineBundle.Situation.AffineChart`: an affine open of `X` lying over an affine open of
  `S`.
* `Stacks.LineBundle.Situation.AffineChart.formsX`: the relative forms of `X` over `U`, as Kähler
  forms of `Γ(X, U)` over `Γ(S, V)`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

universe u

/-- **The exterior powers of the Kähler differentials of a map of commutative rings
`φ : R ⟶ B`, in its two spellings** `CommRingCat.KaehlerDifferential φ` and `Ω[B⁄R]`: the same
module, and this is the identity between them. -/
def CommRingCat.KaehlerDifferential.exteriorPowerEquiv {R B : CommRingCat.{u}} (φ : R ⟶ B)
    (p : ℕ) :
    letI := φ.hom.toAlgebra
    ⋀[B]^p (CommRingCat.KaehlerDifferential φ) ≃ₗ[B] ⋀[B]^p Ω[B⁄R] :=
  letI := φ.hom.toAlgebra
  LinearEquiv.refl B _

namespace Stacks.LineBundle

variable (D : Situation.{u})

/-- **An affine chart of the base**: an affine open `U` of `X` lying over an affine open `V` of
`S`. -/
structure Situation.AffineChart where
  /-- The affine open of `X`. -/
  U : D.X.affineOpens
  /-- The affine open of `S`. -/
  V : D.S.affineOpens
  /-- `U` lies over `V`. -/
  le : U.1 ≤ D.f ⁻¹ᵁ V.1

namespace Situation.AffineChart

variable {D} (c : D.AffineChart)

/-- The functions on `U`. -/
abbrev A : Type u := Γ(D.X, c.U.1)

/-- The functions on `V`. -/
abbrev R : Type u := Γ(D.S, c.V.1)

/-- `Γ(X, U)` as a `Γ(S, V)`-algebra. -/
abbrev algebraRA : Algebra c.R c.A := (D.f.appLE c.V.1 c.U.1 c.le).hom.toAlgebra

/-- The Kähler differentials of `Γ(S, V) → Γ(X, U)`. -/
abbrev ΩA : ModuleCat.{u} c.A := CommRingCat.KaehlerDifferential (D.f.appLE c.V.1 c.U.1 c.le)

/-- **The relative forms of `X` over `U`, as Kähler forms** `⋀^p Ω[Γ(X, U)⁄Γ(S, V)]`. -/
abbrev formsX (p : ℕ) :
    ModuleCat.of c.A Γ(Scheme.Hom.relativeDifferentialForms D.f (p : ℤ), c.U.1) ≅
      ModuleCat.of c.A (⋀[c.A]^p c.ΩA) :=
  Stacks.AlgebraicGeometry.AffineOpenDeRham.formsSectionsIso D.f c.U.2 c.V.2 c.le p

end Situation.AffineChart

end Stacks.LineBundle

end
