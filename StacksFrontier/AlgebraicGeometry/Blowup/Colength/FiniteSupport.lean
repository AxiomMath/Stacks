module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Difference
public import StacksFrontier.Topology.Dimension.DimensionLEOne

/-!
# Finite support of the residual ideal after dividing out a divisor of maximal order

Let `X` be a Noetherian scheme, let `E` be an effective Cartier divisor on `X` whose support is
an irreducible curve — a reduced, irreducible closed subset of dimension at most one — and let
`J` be a sheaf of ideals supported inside `E`. Let `d` be the largest exponent with
`J ≤ E ^ d`. Then `J` factors as `E ^ d` times a residual sheaf of ideals `J'`, and the quotient
`𝒪_X / J'` is supported at finitely many closed points of `X`.

This is the finite-support assertion of [Stacks, Tag 0AGT], where `X` is the blowup of a
two-dimensional regular local ring `(A, 𝔪)` at its closed point, `E` is the exceptional divisor,
`J = I𝒪_X` for an ideal `𝔪ⁿ ⊆ I ⊆ 𝔪`, and `J' = I𝒪_X(dE)`. The source's hypothesis
`𝔪ⁿ ⊆ I` enters only through the containment of supports `supp(J) ⊆ E` that it gives, and
`I ⊆ 𝔪` only through the positivity of `d`, which is
`Stacks.Blowup.Colength.pos_order_of_le_center` and is not needed here.

## Main results

* `Stacks.Blowup.Colength.exists_finite_isClosed_support_of_maximal_order` — the factorization
  `J = E ^ d · J'` together with the finiteness of the support of `J'` and the closedness of
  each of its points.

## The argument

The residual sheaf is the ideal quotient `J' = J : E ^ d`, which satisfies `E ^ d · J' = J`
because `E ^ d` is an effective Cartier divisor containing `J`
(`AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor`). Since `J ≤ J'` its support is
contained in that of `J`, hence in `E`.

That support cannot be all of `E`: if it were, the Galois connection between supports and
vanishing ideals would give `J' ≤ vanishingIdeal(supp E)`, which is the radical of `E` and so
`E` itself, whence `J = E ^ d · J' ≤ E ^ (d + 1)`, contradicting the maximality of `d`. So the
generic point of `E` is outside the support of `J'`, which therefore contains no irreducible
component of `E`. Read inside the subspace `E`, a closed subset containing no irreducible
component of a Noetherian sober space of dimension at most one is a finite set of closed points
(`Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset` and
`Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset`); being closed
in the closed subset `E`, those points are closed in `X`.

## Implementation notes

The statement is for an arbitrary Noetherian scheme and an arbitrary effective Cartier divisor
with reduced irreducible one-dimensional support: neither the regular local surface nor the
blowup is used. Reducedness of the divisor is `E.radical = E`, equivalently that `E` is the
vanishing ideal of its support; the one-dimensionality is `topologicalKrullDim` of the support
read as a subspace.

Those three properties of the exceptional divisor are exactly the content of
[Stacks, Tag 0AGQ] part (1), which identifies it with `𝐏¹` over the residue field. They are
carried here as hypotheses because the statement is about an arbitrary effective Cartier divisor on
an arbitrary Noetherian scheme, where they are genuine assumptions and not restrictions inherited
from the source. For the exceptional divisor of the blowup of a regular local ring of dimension
two at its closed point they are discharged, in
`StacksFrontier/AlgebraicGeometry/Blowup/Colength/ExceptionalCurve.lean`
(`AlgebraicGeometry.radical_exceptionalIdeal_eq_self`,
`AlgebraicGeometry.isIrreducible_support_exceptionalIdeal` and, for the dimension,
`AlgebraicGeometry.topologicalKrullDim_exceptionalDivisor_residuePoint`), and
`AlgebraicGeometry.exists_finite_isClosed_support_of_maximal_order_blowUp` there is the resulting
form for that divisor.

The residual sheaf is produced existentially rather than named, so that no proof of finite
generation appears in the statement; the witness is the ideal quotient
`AlgebraicGeometry.Scheme.IdealSheafData.colon`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Blowup.Colength

/-- **Dividing out a reduced irreducible curve to its maximal order leaves a residual ideal with
finite closed support.** Let `E` be an effective Cartier
divisor on a Noetherian scheme `X` whose support is reduced, irreducible and of dimension at most
one, let `J` be a sheaf of ideals supported inside `E`, and let `d` be the largest exponent with
`J ≤ E ^ d`. Then `J = E ^ d · J'` for a sheaf of ideals `J'` whose support is a finite set of
closed points of `X`.

For the blowup of a two-dimensional regular local ring at its closed point this is the source's
statement that `𝒪_X / I𝒪_X(dE)` is supported in finitely many closed points: the hypothesis
`𝔪ⁿ ⊆ I` is what puts the support of `I𝒪_X` inside the exceptional divisor, and the three
hypotheses on `E` are the identification of the exceptional divisor with `𝐏¹` over the residue
field, [Stacks, Tag 0AGQ] part (1), which discharges the three hypotheses for the exceptional
divisor in `AlgebraicGeometry.exists_finite_isClosed_support_of_maximal_order_blowUp`. -/
public theorem exists_finite_isClosed_support_of_maximal_order
    {X : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X] (E J : X.IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hErad : E.radical = E)
    (hEirr : IsIrreducible (E.support : Set X))
    (hEdim : topologicalKrullDim (E.support : Set X) ≤ 1)
    (hJE : (J.support : Set X) ⊆ (E.support : Set X))
    (d : ℕ) (hJd : J ≤ E ^ d) (hmax : ∀ e : ℕ, J ≤ E ^ e → e ≤ d) :
    ∃ (J' : X.IdealSheafData) (T : Finset X),
      E ^ d * J' = J ∧
      (J'.support : Set X) = (T : Set X) ∧
      ∀ x ∈ T, IsClosed ({x} : Set X) := by
  classical
  have hEd : Stacks.Divisors.IsEffectiveCartierDivisor (E ^ d) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow hE d
  set J' : X.IdealSheafData :=
    J.colon (E ^ d) (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor (E ^ d) hEd)
    with hJ'def
  have hmul : E ^ d * J' = J :=
    AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor (E ^ d) J hEd hJd
  -- The residual sheaf contains `J`, so its support sits inside that of `J`, hence inside `E`.
  have hJJ' : J ≤ J' := fun _ => Ideal.le_colon
  have hsupp : (J'.support : Set X) ⊆ (E.support : Set X) :=
    (SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hJJ')).trans hJE
  -- The support of the residual sheaf is not all of `E`: otherwise `d` were not maximal.
  have hne : ¬ ((E.support : Set X) ⊆ (J'.support : Set X)) := by
    intro hsub
    have hle : J' ≤ E := by
      have h := (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal (I := J')
        (Z := E.support)).mp (SetLike.coe_subset_coe.1 hsub)
      rwa [Scheme.IdealSheafData.vanishingIdeal_support, hErad] at h
    have hstep : J ≤ E ^ (d + 1) := by
      rw [← hmul, pow_succ]
      intro U
      simpa using Ideal.mul_mono (le_refl ((E ^ d).ideal U)) (hle U)
    exact absurd (hmax (d + 1) hstep) (by omega)
  -- Hence the generic point of `E` is outside that support.
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hEirr E.support.isClosed
  have hξmem : ξ ∈ (E.support : Set X) := by
    rw [← hξ.def]
    exact subset_closure (Set.mem_singleton ξ)
  have hξnot : ξ ∉ (J'.support : Set X) := by
    intro hmem
    refine hne ?_
    rw [← hξ.def]
    exact J'.support.isClosed.closure_subset_iff.2 (Set.singleton_subset_iff.2 hmem)
  -- Read inside the curve `E`, the support of the residual sheaf is a finite set of closed
  -- points, because it contains no irreducible component of `E`.
  have hYcl : IsClosed (E.support : Set X) := E.support.isClosed
  have : NoetherianSpace X := AlgebraicGeometry.IsNoetherian.noetherianSpace
  have : NoetherianSpace (E.support : Set X) :=
    NoetherianSpace.of_subset (W := (Set.univ : Set X)) (Set.subset_univ _)
  have : QuasiSober (E.support : Set X) := hYcl.isClosedEmbedding_subtypeVal.quasiSober
  have : IrreducibleSpace (E.support : Set X) := isIrreducible_iff_irreducibleSpace.mp hEirr
  set T' : Set (E.support : Set X) := Subtype.val ⁻¹' (J'.support : Set X) with hT'def
  have hT'cl : IsClosed T' := J'.support.isClosed.preimage continuous_subtype_val
  have hT'comp : ∀ C ∈ irreducibleComponents (E.support : Set X), ¬ C ⊆ T' := by
    intro C hC hCsub
    have hCuniv : (Set.univ : Set (E.support : Set X)) ⊆ C :=
      hC.2 (IrreducibleSpace.isIrreducible_univ _) (Set.subset_univ C)
    exact hξnot (hCuniv.trans hCsub (Set.mem_univ (⟨ξ, hξmem⟩ : (E.support : Set X))))
  have hT'fin : T'.Finite :=
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hEdim hT'cl hT'comp
  have hT'closed : ∀ z ∈ T', IsClosed ({z} : Set (E.support : Set X)) := fun z hz =>
    Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hEdim hT'cl hT'comp hz
  -- Transport the two conclusions along the closed embedding of `E` in `X`.
  have himg : Subtype.val '' T' = (J'.support : Set X) := by
    rw [hT'def, Set.image_preimage_eq_inter_range, Subtype.range_coe_subtype]
    exact Set.inter_eq_self_of_subset_left hsupp
  have hfin : ((J'.support : Set X)).Finite := himg ▸ hT'fin.image _
  refine ⟨J', hfin.toFinset, hmul, (hfin.coe_toFinset).symm, ?_⟩
  intro x hx
  have hxX : x ∈ (J'.support : Set X) := hfin.mem_toFinset.mp hx
  have himage := hYcl.isClosedEmbedding_subtypeVal.isClosedMap _
    (hT'closed ⟨x, hsupp hxX⟩ hxX)
  simpa using himage

end Stacks.Blowup.Colength

end
