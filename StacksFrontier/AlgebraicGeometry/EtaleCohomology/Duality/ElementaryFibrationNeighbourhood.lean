module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopCohomologyCount

/-!
# Elementary fibration neighbourhoods of a point

Artin's theorem on good neighbourhoods (SGA 4, Exposé XI, Proposition 3.3) is local at a point:
for `X` smooth irreducible over an algebraically closed field `k`, of relative dimension `d ≥ 1`,
every rational (that is, closed) point `x` of `X` has an open neighbourhood `U` that is an
elementary fibration `f : U → S` over an irreducible affine `S`, smooth of relative dimension
`d - 1` over `k`, compatibly with the structure morphisms. This file states that pointwise form
as the proposition `Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood`. It is the
hypothesis under which the class of every point in top compactly supported cohomology is
computed through a fibration, with no moving lemma.

The pointwise form implies the dense form `Stacks.EtaleCohomology.ExistsDenseElementaryFibration`
that the computation of `H^{2d}_c` takes. A scheme locally of finite type over a field is a
Jacobson space, so a nonempty one has a closed point, and the neighbourhood of that point is a
nonempty open.

## Main definitions

* `Stacks.EtaleCohomology.ExistsElementaryFibrationNeighbourhood`.

## Main results

* `Stacks.EtaleCohomology.existsDenseElementaryFibration_of_neighbourhood`.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (k : Type u) [Field k]

/-- **Elementary fibration neighbourhoods** (SGA 4, Exposé XI, Proposition 3.3): every closed point
`x` of a smooth irreducible `X` of relative dimension `d ≥ 1` over `k` has an open neighbourhood
`U` which is an elementary fibration `f : U → S` over an irreducible affine `S` smooth of relative
dimension `d - 1`, compatibly with the structure morphisms. -/
def ExistsElementaryFibrationNeighbourhood : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d p]
    [IrreducibleSpace X], 1 ≤ d → ∀ x : X, IsClosed ({x} : Set X) →
    ∃ (U : X.Opens) (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U.toScheme ⟶ S),
      x ∈ U ∧ IsElementaryFibration f ∧ SmoothOfRelativeDimension (d - 1) q ∧
        IsAffine S ∧ IrreducibleSpace S ∧ f ≫ q = U.ι ≫ p

variable {k}

/-- `ExistsElementaryFibrationNeighbourhood k` implies `ExistsDenseElementaryFibration k`: if every
closed point of a smooth irreducible `k`-scheme has an elementary fibration neighbourhood, then
every such scheme contains a nonempty open which is an elementary fibration. -/
theorem existsDenseElementaryFibration_of_neighbourhood
    (h : ExistsElementaryFibrationNeighbourhood k) : ExistsDenseElementaryFibration k := by
  intro X p d _ _ hd
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  obtain ⟨x₀⟩ := IrreducibleSpace.toNonempty (X := X)
  obtain ⟨x, -, hx⟩ := nonempty_inter_closedPoints (Z := Set.univ) ⟨x₀, Set.mem_univ _⟩
    isClosed_univ.isLocallyClosed
  obtain ⟨U, S, q, f, hxU, hf, hq, hS, hSi, hfq⟩ := h X p d hd x hx
  exact ⟨U, S, q, f, ⟨x, hxU⟩, hf, hq, hS, hSi, hfq⟩

end Stacks.EtaleCohomology

end
