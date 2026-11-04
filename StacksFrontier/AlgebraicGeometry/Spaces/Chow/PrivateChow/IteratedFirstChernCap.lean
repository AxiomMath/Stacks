module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CanonicalFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProjectiveBundleProjection

/-!
# Iterated cap products with first Chern classes

In Situation 0EDT let `X/B` be good and let `ℒ₁, …, ℒ_d` be invertible `𝒪_X`-modules. The
iterated cap product

`c₁(ℒ₁) ∩ c₁(ℒ₂) ∩ ⋯ ∩ c₁(ℒ_d) ∩ - : Z_{k+d}(X) → Z_k(X)`

is the composite of the cap products of Stacks 0EQJ, innermost `ℒ_d`, each taken at the
canonical choices (`AlgebraicGeometry.Space.canonicalFirstChernRule`): the component cycle on an
integral closed subspace `W` is the Weil divisor of the regular meromorphic section of `ℒ|_W`
given by Stacks 0EPQ.

## Main definitions

* `AlgebraicGeometry.Space.iteratedFirstChernCapCycle`: the iterated cap product on cycles.

## Implementation notes

The source's iterated cap product is an operation on Chow groups: each step
`c₁(ℒ) ∩ - : CH_{k+1}(X) → CH_k(X)` is the cap product of Stacks 0EQJ on a representing cycle,
which is well defined on classes by Stacks 0EQY. The operation here is that composite read on
the cycles produced by the canonical choices at each step, so its class is the source's iterated
cap product of the class of the cycle it is applied to.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX)

/-- **The iterated cap product with first Chern classes on cycles**,
`α ↦ c₁(ℒ₁) ∩ c₁(ℒ₂) ∩ ⋯ ∩ c₁(ℒ_d) ∩ α`, from `Z_{k+d}(X)` to `Z_k(X)`, the cap with `ℒ_d`
applied first, each cap at the canonical choices of Stacks 0EQJ. -/
def iteratedFirstChernCapCycle :
    (d : ℕ) → (L : Fin d → Modules.{u, u} D.site D.base D.base_mem X hX.1) →
    (∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) (L j)) →
    (k : ℤ) → CycleGroup D sX (k + d) →+ CycleGroup D sX k
  | 0, _, _, k => cycleGroupCast D sX (by simp)
  | d + 1, L, hL, k =>
    (iteratedFirstChernCapCycle d (Fin.init L) (fun j => hL _) k).comp
      ((firstChernCapCycleMap D sX hX ((k + d : ℤ))
        (canonicalFirstChernRule D sX hX (L (Fin.last d)) (hL _) (k + d))).comp
        (cycleGroupCast D sX (by push_cast; ring)))

/-- The iterated cap product with no invertible modules is the identity on the underlying cycle. -/
theorem iteratedFirstChernCapCycle_zero (L : Fin 0 → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) (L j))
    (k : ℤ) (α : CycleGroup D sX (k + (0 : ℕ))) :
    (iteratedFirstChernCapCycle D sX hX 0 L hL k α).1 = α.1 :=
  rfl

/-- The iterated cap product with `ℒ₁, …, ℒ_{d+1}` is the cap with `ℒ_{d+1}` at the canonical
choices, followed by the iterated cap product with `ℒ₁, …, ℒ_d`. -/
theorem iteratedFirstChernCapCycle_succ {d : ℕ}
    (L : Fin (d + 1) → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : ∀ j, IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) (L j))
    (k : ℤ) (α : CycleGroup D sX (k + ((d + 1 : ℕ) : ℤ))) :
    iteratedFirstChernCapCycle D sX hX (d + 1) L hL k α =
      iteratedFirstChernCapCycle D sX hX d (Fin.init L) (fun j => hL _) k
        (firstChernCapCycleMap D sX hX ((k + d : ℤ))
          (canonicalFirstChernRule D sX hX (L (Fin.last d)) (hL _) (k + d))
          (cycleGroupCast D sX (by push_cast; ring) α)) :=
  rfl

end AlgebraicGeometry.Space

end
