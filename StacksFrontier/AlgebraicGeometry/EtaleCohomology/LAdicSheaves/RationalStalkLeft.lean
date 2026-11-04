module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.Rational
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rational stalk of an `ℓ`-adic sheaf as a `ℚ_ℓ`-vector space

`Stacks.EtaleCohomology.LAdicSheaf.rationalStalk` (Tag 03UR) is the `ℤ_ℓ`-module stalk of a
`ℤ_ℓ`-sheaf `F` tensored with `ℚ_ℓ` on the right, `F_x̄ ⊗_{ℤ_ℓ} ℚ_ℓ`. This file extends the
scalars on the left instead, `ℚ_ℓ ⊗_{ℤ_ℓ} F_x̄`: the two are the same tensor product up to the
symmetry of `⊗`, but the left factor is the side on which Mathlib puts the `ℚ_ℓ`-module
structure of a base change, so this form is a `ℚ_ℓ`-vector space by instance search. It is the
space over which the determinant `det(1 - π_x^* T ^ (deg x) | F_x̄)` of Tag 03UX is taken.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkLeft`: the stalk `ℚ_ℓ ⊗_{ℤ_ℓ} F_x̄`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [Fact ℓ.Prime] [IsNoetherian X.1]

/-- The stalk at a geometric point `x` of the `ℚ_ℓ`-sheaf `F ⊗ ℚ_ℓ`, for `F` a `ℤ_ℓ`-sheaf, with
the scalars extended on the left: `ℚ_ℓ ⊗_{ℤ_ℓ} F_x̄`, a `ℚ_ℓ`-vector space. It is
`Stacks.EtaleCohomology.LAdicSheaf.rationalStalk` (Tag 03UR) up to the symmetry of the tensor
product. -/
@[sga "4½ Rapport 2.9" "partial"]
public abbrev LAdicSheaf.rationalStalkLeft (F : LAdicSheaf.{u, u + 1} B X ℓ)
    (x : GeometricPoint X.1) : Type (u + 1) :=
  TensorProduct (PadicInt ℓ) (Padic ℓ) (LAdicSheaf.stalk B X ℓ F x)

end Stacks.EtaleCohomology

end
