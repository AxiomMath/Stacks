module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationSubspace

/-!
# The fibre bound of the Bertini dimension count, from the Jacobian criterion at closed points

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) with `X` smooth over
an algebraically closed field `k`. This module closes the dimension count of the proof of
[Stacks, Tag 0FD6] against **one** geometric input: that at a closed point `w` of `H_univ` lying
over a closed point `x` of `X`, if one of the linear forms of the evaluation matrix does not
vanish at `w`, then `q : H_univ → 𝔸^r_k` is smooth at `w`. That input is the Jacobian criterion
of `StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.ZeroSchemeStalkRegular` read in the Bertini
situation; everything else is supplied here.

Given it, the closed subset `L` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationSubspace` contains every closed
point of `H_univ` over `x` at which `q` is not smooth, so
`Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_closedPoints` bounds
the fibre of the projection `Σ → X` over `x` by `dim L ≤ r - #τ`, and with `#τ = n + 1` the
dimension count of
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniNonSmoothClosedPoints` produces `hsing`
and hence the conclusion of Tag 0FD6.

## Main results

* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_evalSubspace`: the
  fibre bound over a closed point of `X`.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_evalSubspace`:
  **`hsing`** — a nonempty open of `𝔸^r_k` whose preimage under `q` lies in the smooth locus.
* `Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral_of_evalSubspace`: the
  conclusion of [Stacks, Tag 0FD6] from the same input.

## What is still an input

The hypothesis `hsmooth` below. It says: for every closed point `w` of `H_univ` lying over the
closed point `x` of `X`, if some form `∑ᵢ Mᵢⱼ xᵢ` of the evaluation matrix is nonzero at `w`,
then `q` is smooth at `w`. In the source this is the Jacobian criterion: the non-vanishing of
one coordinate of `ev_x` at the coordinate vector of `w` says that the germ of the section
cutting out the fibre of `q` through `w` avoids `𝔪²ℒ`, and
`AlgebraicGeometry.smoothAt_fiberι_of_notMem_maximalSqSmul` turns that into smoothness of `q`.
Joining the two needs flatness of `q` and the identification of the fibre of `q` through `w`
with the divisor of the corresponding vector, neither of which is available unconditionally in
this library yet.

Accordingly **no `@[stacks]` attribute is attached**: Tag 0FD6 keeps its registration on
`Stacks.Bertini.FamilyDivisors.smooth_specializedDivisor_forGeneral`.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v w

namespace Stacks.Bertini.FamilyDivisors

open Stacks.LinearSubspace

variable (D : FamilyDivisors.{u, v})

/-- **The fibre bound over a closed point of `X`, from the Jacobian criterion at the closed
points of `H_univ`.** If every closed point of `H_univ` over `x` at which one of the forms of the
evaluation matrix `M` is nonzero is a point of smoothness of `q`, then the fibre of the
projection `Σ → X` over `x` has dimension at most `r - #τ`.

The non-smooth closed points over `x` are exactly those at which all the forms vanish, which is
the closed set `Stacks.Bertini.FamilyDivisors.evalSubspace`; its dimension is bounded by
`Stacks.Bertini.FamilyDivisors.topologicalKrullDim_evalSubspace_le`. -/
theorem topologicalKrullDim_fiber_nonSmoothToX_le_of_evalSubspace [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [IsAlgClosed D.k] {x : D.X}
    (hx : IsClosed ({x} : Set D.X)) {τ : Type w} [Fintype τ] (M : D.basisIndex → τ → D.k)
    (hM : Function.Surjective (coeffMap M))
    (hsmooth : ∀ w : D.universalDivisorScheme, IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm M j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    topologicalKrullDim (D.nonSmoothToX.fiber x) ≤
      ((Nat.card D.basisIndex - Fintype.card τ : ℕ) : WithBot ℕ∞) :=
  D.topologicalKrullDim_fiber_nonSmoothToX_le_of_closedPoints hx (D.evalSubspace x M)
    (D.isClosed_evalSubspace hx M)
    (fun w hwc hwns hwx => D.mem_evalZeroSet.mpr ⟨hwx, fun j hj =>
      hwns (hsmooth w hwc hwx ⟨j, hj⟩)⟩)
    (D.topologicalKrullDim_evalSubspace_le hx M hM)

/-- **`hsing` of [Stacks, Tag 0FD6] from the Jacobian criterion at closed points.** With
`#τ = n + 1`, `dim X ≤ n` and `n + 1 ≤ r`, and with the Jacobian criterion available at the
closed points of `H_univ` over every closed point of `X`, there is a nonempty open `U ⊂ 𝔸^r_k`
whose preimage under `q` lies in the smooth locus of `q`. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_evalSubspace [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] [IsAlgClosed D.k]
    {n : ℕ} (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (M : ∀ x : D.X, IsClosed ({x} : Set D.X) → D.basisIndex → Fin (n + 1) → D.k)
    (hM : ∀ (x : D.X) (hx : IsClosed ({x} : Set D.X)),
      Function.Surjective (coeffMap (M x hx)))
    (hsmooth : ∀ (x : D.X) (hx : IsClosed ({x} : Set D.X))
      (w : D.universalDivisorScheme), IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm (M x hx) j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) :=
  D.exists_nonempty_opens_subset_smoothLocus_of_closed_fiber_le hnr hX fun x hx => by
    have h := D.topologicalKrullDim_fiber_nonSmoothToX_le_of_evalSubspace hx (M x hx)
      (hM x hx) (hsmooth x hx)
    rwa [Fintype.card_fin] at h

/-- **[Stacks, Tag 0FD6] from the Jacobian criterion at closed points.** In the standing
situation of [Stacks, Tag 0G47] with `X` smooth over an algebraically closed field `k`, if
`dim X ≤ n`, if `n + 1 ≤ r`, and if at every closed point of `H_univ` over a closed point of `X`
the non-vanishing of one coordinate of the evaluation implies smoothness of `q`, then `H_v` is
smooth over `k'` for general `v ∈ V ⊗_k k'`. -/
theorem smooth_specializedDivisor_forGeneral_of_evalSubspace [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme] [IsAlgClosed D.k]
    {n : ℕ} (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (M : ∀ x : D.X, IsClosed ({x} : Set D.X) → D.basisIndex → Fin (n + 1) → D.k)
    (hM : ∀ (x : D.X) (hx : IsClosed ({x} : Set D.X)),
      Function.Surjective (coeffMap (M x hx)))
    (hsmooth : ∀ (x : D.X) (hx : IsClosed ({x} : Set D.X))
      (w : D.universalDivisorScheme), IsClosed ({w} : Set D.universalDivisorScheme) →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base w) = x →
      (∃ j, D.universalDivisor.subschemeι.base w ∈
        D.parameterSpace.basicOpen (D.evalCoordForm (M x hx) j)) →
      w ∈ D.universalFamilyMap.smoothLocus) :
    D.ForGeneral (fun K _ _ w =>
      ∀ a : Fin (Module.finrank D.k D.V) → K,
        w = ∑ i, TensorProduct.tmul D.k (D.basis i) (a i) →
          Smooth ((D.specializedDivisor K a).subschemeι ≫ D.baseChangeToSpec K)) := by
  obtain ⟨U, hU, hsing⟩ :=
    D.exists_nonempty_opens_subset_smoothLocus_of_evalSubspace hnr hX M hM hsmooth
  exact D.smooth_specializedDivisor_forGeneral U hU hsing

end Stacks.Bertini.FamilyDivisors

end
