module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Product
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient

/-!
# Reducing a coherent adic system modulo a fixed power of a second ideal

Let `X` be a locally Noetherian scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves, let
`e` be a natural number and let `(F_n)` be a coherent adic system along `ℐ`. Dividing every term
by the *same* power `𝒦 ᵉ` gives a new inverse system
`n ↦ F_n / 𝒦 ᵉ F_n`,
and this file shows that it is again a coherent adic system **along the same ideal `ℐ` and with
the same indexing**: no reindexing and no change of ideal are involved, in contrast with the
change-of-ideal transfer of [Stacks, Tag 0EHR].

Each of the three defining clauses passes to the reduction for its own reason. Coherence is
preserved because a quotient of a coherent module on a locally Noetherian scheme is coherent.
The annihilation clause is preserved because annihilation by `ℐ ⁿ⁺¹` passes along the quotient
projection, which is an epimorphism of quasi-coherent modules. The quotient clause is the
symmetry of the two-ideal double quotient: the `ℐ ⁿ⁺¹`-quotient of `F_{n+1} / 𝒦 ᵉ F_{n+1}` is the
`𝒦 ᵉ`-quotient of `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1}`, and the latter is `F_n / 𝒦 ᵉ F_n` because the system
identifies `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1}` with `F_n`.

## Main definitions

* `Stacks.Coherent.idealPowerQuotientSystem` — the reduced inverse system
  `n ↦ F_n / 𝒦 ᵉ F_n`.
* `Stacks.Coherent.idealPowerQuotientAdicFunctor` — the resulting endofunctor of `Coh(X, ℐ)`.

## Main results

* `Stacks.Coherent.isCoherentAdicSystem_idealPowerQuotientSystem` — the reduced system is a
  coherent adic system along `ℐ`.

## Implementation notes

The reduced system is the composite of `F` with
`Stacks.Algebraization.idealPowerQuotientFunctor`, so its transitions are literally the induced
maps `Stacks.Algebraization.idealPowerQuotientMap` and no assembly from successor steps is
needed; this is what the absence of reindexing buys.

The quotient clause is proved by cancelling the epimorphism `F_{n+1} ⟶ F_{n+1} / 𝒦 ᵉ F_{n+1}`,
after which the only computation rules used are
`Stacks.Algebraization.idealPowerQuotientCommMap_cokernel_π`,
`Stacks.Algebraization.idealPowerQuotientMap_π` and the third clause of the given system.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-- The fixed-exponent reduction `n ↦ F_n / 𝒦 ᵉ F_n` of an inverse system of sheaves of modules,
with the same indexing as `F`. -/
public abbrev idealPowerQuotientSystem (K : X.IdealSheafData) (e : ℕ)
    (F : ℕᵒᵖ ⥤ X.Modules) : ℕᵒᵖ ⥤ X.Modules :=
  F ⋙ idealPowerQuotientFunctor K e

/-- **The fixed-exponent reduction of a coherent adic system is a coherent adic system.** For a
locally Noetherian `X`, ideal sheaves `ℐ, 𝒦`, a fixed exponent `e` and a coherent adic system
`(F_n)` along `ℐ`, the system `n ↦ F_n / 𝒦 ᵉ F_n` is a coherent adic system along `ℐ`.

Coherence is `Stacks.Algebraization.isCoherent_idealPowerQuotient`. Annihilation is
`Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot` applied to the
annihilation of `F_n`. The quotient clause composes
`Stacks.Algebraization.idealPowerQuotientCommIso`, which exchanges the two divisions, with the
`𝒦 ᵉ`-quotient of the identification `F_{n+1} / ℐ ⁿ⁺¹ F_{n+1} ≅ F_n` carried by the system. -/
public theorem isCoherentAdicSystem_idealPowerQuotientSystem [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (K : X.IdealSheafData) (e : ℕ) {F : ℕᵒᵖ ⥤ X.Modules}
    (hF : IsCoherentAdicSystem I F) :
    IsCoherentAdicSystem I (idealPowerQuotientSystem K e F) := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩
  · have : (F.obj (op n)).IsCoherent := hF.isCoherent n
    exact isCoherent_idealPowerQuotient K e (F.obj (op n))
  · have : (F.obj (op n)).IsQuasicoherent := hF.isQuasicoherent n
    exact idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot I K (n + 1) e (F.obj (op n))
      (hF.idealPowerMultiple_eq_bot n)
  · have hqc : (F.obj (op (n + 1))).IsQuasicoherent := hF.isQuasicoherent (n + 1)
    refine ⟨idealPowerQuotientCommIso I K (n + 1) e (F.obj (op (n + 1))) ≪≫
      (idealPowerQuotientFunctor K e).mapIso (hF.quotientIso n), ?_⟩
    refine (cancel_epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple K e (F.obj (op (n + 1)))).ι)).1 ?_
    change cokernel.π (C := X.Modules) (idealPowerMultiple K e (F.obj (op (n + 1)))).ι ≫
        cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1)
            (idealPowerQuotient K e (F.obj (op (n + 1))))).ι ≫
          (idealPowerQuotientCommMap I K (n + 1) e (F.obj (op (n + 1))) ≫
            idealPowerQuotientMap K K e e le_rfl (hF.quotientIso n).hom) =
      cokernel.π (C := X.Modules) (idealPowerMultiple K e (F.obj (op (n + 1)))).ι ≫
        idealPowerQuotientMap K K e e le_rfl (F.map (homOfLE (Nat.le_succ n)).op)
    rw [idealPowerQuotientCommMap_cokernel_π_assoc, idealPowerQuotientMap_π,
      ← Category.assoc (obj := X.Modules), hF.cokernel_π_comp_quotientIso n,
      idealPowerQuotientMap_π]

/-- The fixed-exponent reduction as an endofunctor of `Coh(X, ℐ)`: it divides every term of a
coherent adic system by the same power `𝒦 ᵉ`. -/
public def idealPowerQuotientAdicFunctor [IsLocallyNoetherian X] (I K : X.IdealSheafData)
    (e : ℕ) :
    CoherentAdicSystems I ⥤ CoherentAdicSystems I :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙
      (Functor.whiskeringRight _ _ _).obj (idealPowerQuotientFunctor K e))
    fun F => isCoherentAdicSystem_idealPowerQuotientSystem K e F.property

end Stacks.Coherent

end
