module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.SubmoduleCompleteLattice

/-!
# Ideal-power multiples, their quotients, and adic inverse systems

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf on `X` and `M` a sheaf of modules. The
formal-geometry arguments of Stacks chapter 52 are organized around the subsheaf `I ^ n M` and
the quotient `M / I ^ n M`, and around inverse systems `(F_n)` whose transition maps realize
`F_n = F_{n+1} / I ^ n F_{n+1}`. Such a system is the sheaf-theoretic shadow of a module over
the `I`-adic completion, and its inverse limit is the object the algebraization theorems
produce.

The subsheaf `I ^ n M` is defined as the least subsheaf which, on every affine open `U`,
contains `I(U) ^ n • M(U)`; `idealPowerMultiple_le_iff` is the affine-local universal property
that this definition exists to supply. Taking a least subsheaf rather than a sectionwise image
means the construction also applies when `M` is not quasi-coherent, which is needed for the
inverse limit, where quasi-coherence is not preserved.

## Main definitions

* `Stacks.Algebraization.idealPowerMultiple` — the subsheaf `I ^ n M`.
* `Stacks.Algebraization.idealPowerQuotient` — the sheaf quotient `M / I ^ n M`.
* `Stacks.Algebraization.AdicInverseSystem` — an inverse system of quasi-coherent modules whose
  transitions are the ideal-power quotient projections.
* `Stacks.Algebraization.AdicInverseSystem.limitModule` — its inverse limit `lim F_n`.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_le_iff` — `I ^ n M ≤ N` holds exactly when `N`
  contains `I(U) ^ n • M(U)` on every affine open `U`.

## Implementation notes

An inverse system is a functor out of `ℕᵒᵖ`, and it is zero-indexed: its object at `n` is the
Stacks source's `F_{n+1}`, since the source numbers the system by positive integers. The
transition from term `n + 1` to term `n` is therefore the quotient by `I ^ {n+1} F_{n+2}`. The
fields `AdicInverseSystem.quotientIso` and `AdicInverseSystem.quotientIso_hom_comp` identify
each transition with the canonical cokernel projection, the second recording compatibility
with the quotient map rather than merely the existence of an isomorphism.

Mathlib's `Scheme.IdealSheafData` is the affine-local presentation of a quasi-coherent ideal
sheaf, which is why the defining condition and its universal property both quantify over
`X.affineOpens`.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-- The subsheaf `I ^ n M` of a sheaf of modules `M`.

It is the least subsheaf containing, on every affine open `U`, the submodule
`I(U) ^ n • M(U)`. This construction also applies when `M` is not quasi-coherent, as is
needed for the inverse limit below. -/
public noncomputable def idealPowerMultiple {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) : M.Submodule :=
  sInf { N | ∀ U : X.affineOpens,
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
      N.toSubmodule.obj (op U.1) }

/-- The canonical sheaf quotient `M / I ^ n M`. -/
public noncomputable abbrev idealPowerQuotient {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) : X.Modules :=
  cokernel ((idealPowerMultiple I n M).ι)

/-- The affine-local universal property characterizing the subsheaf `I ^ n M`. -/
public lemma idealPowerMultiple_le_iff {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) (N : M.Submodule) :
    idealPowerMultiple I n M ≤ N ↔
      ∀ U : X.affineOpens,
        I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) ≤
      N.toSubmodule.obj (op U.1) := by
  refine ⟨fun h U ↦ le_trans ?_ (h (op U.1)), fun h ↦ sInf_le h⟩
  change _ ≤ (sInf ((fun P : M.Submodule => P.toSubmodule) ''
    {P : M.Submodule | ∀ V : X.affineOpens,
      I.ideal V ^ n • (⊤ : Submodule Γ(X, V) Γ(M, V)) ≤
        P.toSubmodule.obj (op V.1)})).obj (op U.1)
  rw [PresheafOfModules.Submodule.sInf_obj]
  refine le_iInf₂ fun P hP ↦ ?_
  obtain ⟨Q, hQ, rfl⟩ := hP
  exact hQ U

/-- An inverse system `(F_n)` of quasi-coherent modules satisfying
`F_n = F_(n+1) / I^n F_(n+1)` for every positive integer `n`.

The functor is zero-indexed: its object at `n` is the source's `F_(n+1)`. The two final fields
identify its transition with the canonical projection from the sheaf quotient by
`I^(n+1) F_(n+2)`. -/
public structure AdicInverseSystem where
  /-- The underlying scheme. -/
  X : Scheme.{u}
  /-- The quasi-coherent ideal sheaf defining the system. -/
  I : X.IdealSheafData
  /-- The inverse system, with object `n` representing `F_(n+1)`. -/
  system : ℕᵒᵖ ⥤ X.Modules
  /-- Every member of the inverse system is quasi-coherent. -/
  isQuasicoherent : ∀ n, (system.obj n).IsQuasicoherent
  /-- The target of each transition is the canonical sheaf quotient by the corresponding
  ideal-power multiple. -/
  quotientIso : ∀ n : ℕ,
    idealPowerQuotient I (n + 1) (system.obj (op (n + 1))) ≅
      system.obj (op n)
  /-- Under `quotientIso`, the canonical quotient projection is the given transition map. -/
  quotientIso_hom_comp : ∀ n : ℕ,
    cokernel.π ((idealPowerMultiple I (n + 1) (system.obj (op (n + 1)))).ι) ≫
        (quotientIso n).hom =
      system.map (homOfLE (Nat.le_succ n)).op

namespace AdicInverseSystem

/-- The quasi-coherence hypothesis, available as an instance for each term. -/
public instance (S : AdicInverseSystem) (n : ℕᵒᵖ) :
    (S.system.obj n).IsQuasicoherent := S.isQuasicoherent n

/-- The inverse limit `F = lim F_n` of an adic inverse system. -/
public noncomputable abbrev limitModule (S : AdicInverseSystem) : S.X.Modules :=
  limit S.system

end AdicInverseSystem

end Stacks.Algebraization

end
