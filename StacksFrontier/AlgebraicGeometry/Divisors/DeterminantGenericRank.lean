module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineChart
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkGenericPoint

/-!
# The generic rank of a module which is finite locally free over a nonempty open

The hypotheses `hr` and `hr'` of `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` of
[Stacks, Tag 0B3T] ask for the rank of the torsion-free quotient of a stalk, at the generic
point of a prime divisor. The source supplies that number as the *generic rank*: the module is
finite locally free of rank `r` on some nonempty open, which is the hypothesis the tag's own
statement carries.

This file closes the gap between the two. The generic point of an integral scheme lies in
every nonempty open, so the stalk there is free on `r` generators over the function field; and
by `Stacks.ModuleStalkGenericPoint.finrank_quotient_torsion_stalk_eq` the rank of the
torsion-free quotient of the stalk at *any* point is that same dimension.

## Main results

All of them live in the namespace `AlgebraicGeometry.Scheme.Modules`.

* `nonempty_stalkLinearEquiv_fin_genericPoint` and
  `finite_stalk_genericPoint_of_isFiniteLocallyFreeOfRank_over`: the stalk at the generic point
  is free on `r` generators over the function field, in particular finite.
* `finrank_stalk_genericPoint_eq_of_isFiniteLocallyFreeOfRank_over`: the stalk at the generic
  point has dimension `r` over the function field.
* `finrank_quotient_torsion_stalk_eq_of_isFiniteLocallyFreeOfRank_over`: **the rank of the
  torsion-free quotient of the stalk at every point is `r`.**
* `finrank_quotient_torsion_modStalk_eq_of_isFiniteLocallyFreeOfRank_over`: the same statement
  in the `ringStalk`/`modStalk` spelling, which is the one
  `AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` reads its rank hypotheses in.

## Implementation notes

**Two stalk spellings, bridged once.** `modStalk F x` and `ringStalk X.sheaf x` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SheafHomStalk.lean` are `F.presheaf.stalk x` and
`X.presheaf.stalk x` by `rfl`, and the two `𝒪_{X,x}`-module structures agree by `rfl` as well,
so the last result is the previous one restated; it is written out because it is the shape the
consumer needs and because nothing else in the library records the agreement.

**No `@[stacks]` attribute.** This is a step of the proof of Tag 0B3T, not one of its
assertions: the tag asserts invertibility of the determinants and the bounded Cartier twist,
not the constancy of the generic rank.

## References

* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.SheafHomStalk

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The trivialization of a module which is finite locally free of rank `r` over a nonempty
open of an integral scheme, read at the generic point, where it lies in the one spelling of the
stalk that the rest of this development uses. -/
theorem nonempty_stalkLinearEquiv_fin_genericPoint [IsIntegral X] (F : X.Modules)
    (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U) :
    Nonempty (F.presheaf.stalk (genericPoint X) ≃ₗ[(X.presheaf.stalk (genericPoint X) : Type u)]
      (Fin r →₀ (X.presheaf.stalk (genericPoint X) : Type u))) :=
  (nonempty_stalkLinearEquiv_fin_of_isFiniteLocallyFreeOfRank_over F U r
    (genericPoint_mem_of_isOpen U.isOpen hU)).elim fun e ↦ ⟨e⟩

/-- The stalk at the generic point of a module which is finite locally free over a nonempty
open is a finite module over the function field. -/
theorem finite_stalk_genericPoint_of_isFiniteLocallyFreeOfRank_over [IsIntegral X]
    (F : X.Modules) (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U) :
    Module.Finite (X.presheaf.stalk (genericPoint X)) (F.presheaf.stalk (genericPoint X)) :=
  Module.Finite.equiv (nonempty_stalkLinearEquiv_fin_genericPoint F U r hU).some.symm

/-- **The stalk at the generic point of an integral scheme of a module which is finite locally
free of rank `r` over a nonempty open has dimension `r` over the function field.** The generic
point lies in every nonempty open, so the trivialization is available there. -/
theorem finrank_stalk_genericPoint_eq_of_isFiniteLocallyFreeOfRank_over [IsIntegral X]
    (F : X.Modules) (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U) :
    Module.finrank (X.presheaf.stalk (genericPoint X))
      (F.presheaf.stalk (genericPoint X)) = r := by
  rw [(nonempty_stalkLinearEquiv_fin_genericPoint F U r hU).some.finrank_eq,
    Module.finrank_finsupp_self, Fintype.card_fin]

/-- **The rank of the torsion-free quotient of the stalk is the generic rank, at every point.**
This is the shape of the hypotheses `hr` and `hr'` of
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap`. -/
theorem finrank_quotient_torsion_stalk_eq_of_isFiniteLocallyFreeOfRank_over [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U)
    (x : X) :
    Module.finrank (X.presheaf.stalk x)
        (F.presheaf.stalk x ⧸
          Submodule.torsion (X.presheaf.stalk x) (F.presheaf.stalk x)) = r :=
  (Stacks.ModuleStalkGenericPoint.finrank_quotient_torsion_stalk_eq F x).trans
    (finrank_stalk_genericPoint_eq_of_isFiniteLocallyFreeOfRank_over F U r hU)

/-- The previous statement in the `ringStalk`/`modStalk` spelling, the one in which
`AlgebraicGeometry.exists_pow_le_min_tensorIso_detMap` reads its rank hypotheses. -/
theorem finrank_quotient_torsion_modStalk_eq_of_isFiniteLocallyFreeOfRank_over [IsIntegral X]
    (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (F.over U) r] (hU : ∃ x : X, x ∈ U)
    (x : X) :
    Module.finrank (ringStalk X.sheaf x)
        (modStalk F x ⧸ Submodule.torsion (ringStalk X.sheaf x) (modStalk F x)) = r :=
  finrank_quotient_torsion_stalk_eq_of_isFiniteLocallyFreeOfRank_over F U r hU x

end AlgebraicGeometry.Scheme.Modules

end
