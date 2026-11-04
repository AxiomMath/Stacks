module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChange

/-!
# The coefficient of a family of cycles on fibres as a function on the total space

A family of `r`-cycles on the fibres of `f : X ⟶ S` assigns a cycle to each fibre, so its
coefficients are indexed by a point of `S` together with a point of the fibre over it. The same
data is a single function on `X`: a point `x` of `X` lies in the fibre over `f x`, and
`Stacks.Chow.familyCoeff` is the coefficient of the family there. Reading the coefficients this
way removes the transport along `g t = s` that otherwise appears whenever a family on the fibres
of `X / S` is compared with one on the fibres of a base change, because `X` does not move.

The transcendence degree of the residue field extension of `f` at a point of `X`,
`Stacks.Chow.residueTrdeg`, plays the same role for relative dimension: the relative dimension of
a point of the fibre over `s` is the transcendence degree of `f` at its image in `X`, so the
dimension conditions on cycles on fibres also become conditions on points of `X`.

## Main definitions

* `Stacks.Chow.familyCoeff` — the coefficient of a family of cycles on fibres at a point of `X`.

## Main results

* `Stacks.Chow.residueTrdeg_fiberToSpecResidueField` — the transcendence degree of a point of a
  fibre over the residue field of the base point is the transcendence degree of `f` at its image
  in `X`.
* `Stacks.Chow.familyCoeff_fiberι` — the coefficient at a point of a fibre is the coefficient of
  the family on that fibre.
* `Stacks.Chow.residueTrdeg_eq_of_familyCoeff_ne_zero` — a point carrying a nonzero coefficient
  of a family of `r`-cycles has residue transcendence degree `r`.
* `Stacks.Chow.familyCoeff_restrictedFiberMap` — the coefficient entering the base change
  formula, read on `X`.
* `Stacks.Chow.baseChangeFamily_sub` — the base change of families is compatible with
  subtraction.

## Implementation notes

`Stacks.Chow.familyCoeff_fiberι` is proved by generalizing the point of `X` and substituting the
equation `f x = s`, which is available because the point of the fibre determines its image; this
is the one place where the identification of `f.fiber s` with `f.fiber (f (f.fiberι s x))` is
made, and it is made by `subst` rather than by transporting a cycle.

## References

* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {X S S' : Scheme.{u}}

/-- The transcendence degree of the residue field of a point of the fibre over `s` over the
residue field `κ(s)` is the residue transcendence degree of `f` at the image of the point in
`X`. -/
theorem residueTrdeg_fiberToSpecResidueField (f : X ⟶ S) (s : S) (x : f.fiber s) :
    residueTrdeg (f.fiberToSpecResidueField s) x = residueTrdeg f (f.fiberι s x) :=
  (residueTrdeg_eq_of_comp_eq_comp (f.fiberι s) f (f.fiberToSpecResidueField s)
    (S.fromSpecResidueField s) pullback.condition x).symm

/-- The residue transcendence degree of a morphism locally of finite type is a natural
number. -/
theorem exists_residueTrdeg_eq_natCast (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    ∃ n : ℕ, residueTrdeg f x = n := by
  let := (f.residueFieldMap x).hom.toAlgebra
  let : Algebra.EssFiniteType ↥(S.residueField (f x)) ↥(X.residueField x) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap f x)
  exact ⟨(residueTrdeg f x).toNat, (Cardinal.cast_toNat_of_lt_aleph0
    (trdeg_lt_aleph0 ↥(S.residueField (f x)) ↥(X.residueField x))).symm⟩

/-! ### The coefficients of a family of cycles as a function on the total space -/

/-- The coefficient of a family of `r`-cycles on the fibres of `f : X ⟶ S` at a point `x` of
`X`: the coefficient at `x`, viewed in the fibre over `f x`, of the member of the family over
`f x`. -/
def familyCoeff (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ) (α : FamilyOfCycles f r)
    (x : X) : ℤ :=
  (α (f x) : AlgebraicCycle (f.fiber (f x)) ℤ) (f.asFiber x)

/-- At a point of the fibre over `s`, the coefficient function on `X` is the coefficient of the
member of the family over `s`. -/
theorem familyCoeff_fiberι (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (s : S) (x : f.fiber s) :
    familyCoeff f r α (f.fiberι s x) = (α s : AlgebraicCycle (f.fiber s) ℤ) x := by
  have hs : f (f.fiberι s x) = s := (f.fiberHomeo s x).2
  generalize hy : f.fiberι s x = y at hs ⊢
  subst s
  have hx : f.asFiber y = x := by
    apply (f.fiberι (f y)).isEmbedding.injective
    simpa only [Scheme.Hom.fiberι_asFiber] using hy.symm
  exact congrArg (α (f y) : AlgebraicCycle (f.fiber (f y)) ℤ) hx

/-- A point carrying a nonzero coefficient of a family of `r`-cycles on fibres has residue
transcendence degree `r`. -/
theorem residueTrdeg_eq_of_familyCoeff_ne_zero (f : X ⟶ S) [LocallyOfFiniteType f] (r : ℕ)
    (α : FamilyOfCycles f r) (x : X) (hx : familyCoeff f r α x ≠ 0) :
    residueTrdeg f x = r := by
  have h := @trdeg_eq_of_cycle_coeff_ne_zero ↥(S.residueField (f x)) inferInstance
    (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) inferInstance r (f.asFiber x)
    (α (f x)) hx
  change residueTrdeg (f.fiberToSpecResidueField (f x)) (f.asFiber x) = r at h
  rwa [residueTrdeg_fiberToSpecResidueField, Scheme.Hom.fiberι_asFiber] at h

/-- The coefficient of `α` entering the base change formula at a point `x` of the fibre of
`X ×_S S'` over `t`, read as a coefficient on `X`. -/
theorem familyCoeff_restrictedFiberMap (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    (r : ℕ) (α : FamilyOfCycles f r) (t : S') (x : (pullback.snd f g).fiber t) :
    (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) =
      familyCoeff f r α (pullback.fst f g ((pullback.snd f g).fiberι t x)) := by
  rw [← familyCoeff_fiberι f r α (g t)]
  apply congrArg (familyCoeff f r α)
  change (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t ≫
      f.fiberι (g t)) x = ((pullback.snd f g).fiberι t ≫ pullback.fst f g) x
  rw [restrictedFiberMap_fiberι]

/-- A base-changed family vanishes at a point whose image in `X` carries a vanishing
coefficient. -/
theorem baseChangeFamily_apply_eq_zero_of_familyCoeff_eq_zero (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S')
    (x : (pullback.snd f g).fiber t)
    (hx : familyCoeff f r α (pullback.fst f g ((pullback.snd f g).fiberι t x)) = 0) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x = 0 := by
  rw [baseChangeFamily_apply, familyCoeff_restrictedFiberMap f g r α t x, hx, zero_mul]

/-- Base change of families of cycles on fibres is compatible with subtraction. -/
theorem baseChangeFamily_sub (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α β : FamilyOfCycles f r) :
    baseChangeFamily f g r (α - β) =
      baseChangeFamily f g r α - baseChangeFamily f g r β := by
  funext t
  refine Subtype.ext <| Function.locallyFinsuppWithin.ext fun x => ?_
  change (baseChangeFamily f g r (α - β) t : AlgebraicCycle _ ℤ) x =
    (baseChangeFamily f g r α t : AlgebraicCycle _ ℤ) x -
      (baseChangeFamily f g r β t : AlgebraicCycle _ ℤ) x
  rw [baseChangeFamily_apply, baseChangeFamily_apply, baseChangeFamily_apply]
  exact sub_mul _ _ _

end Stacks.Chow

end
