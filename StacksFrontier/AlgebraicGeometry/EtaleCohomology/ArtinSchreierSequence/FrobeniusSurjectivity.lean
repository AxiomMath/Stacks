module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.FrobeniusFibres
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.FrobeniusNilpotent

/-!
# Surjectivity of a Frobenius-semilinear map minus the identity

Over an algebraically closed field of positive characteristic, subtracting the identity from a
Frobenius-semilinear additive endomorphism of a finite-dimensional vector space gives a
surjective additive map. This is the surjectivity half of the Artin–Schreier sequence.

## Main results

* `frobeniusSemilinear_sub_id_surjective` states that `F - 1` is surjective.

## Implementation notes

The map is assumed only to be additive; its Frobenius semilinearity is recorded explicitly.
The expression `F - 1` is represented pointwise by `F v - v`. The proof passes to an invariant
subspace on which `F` is nilpotent and whose quotient `F` acts injectively on: on the quotient a
counting argument makes `F - 1` surjective, and on the nilpotent part the correction term is
produced by the induced bijection.

## References

* [Stacks Project, Tag 0A3L](https://stacks.math.columbia.edu/tag/0A3L)
-/

@[expose] public section


/-- Let `V` be a finite-dimensional vector space over an algebraically closed field `k` of
positive characteristic `p`. If the additive endomorphism `F` is Frobenius-semilinear, then
`F - 1` is surjective. -/
@[stacks 0A3L "surjectivity", sga "7 XXII 1.2" "alg. closed, q=p"]
public theorem frobeniusSemilinear_sub_id_surjective
    {p : ℕ} (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (hp : 0 < p)
    (V : Type*) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : V →+ V) (hF : ∀ (a : k) (v : V), F (a • v) = a ^ p • F v) :
    Function.Surjective (fun v ↦ F v - v) := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  let F' : V →ₛₗ[frobenius k p] V :=
    { toFun := F
      map_add' := F.map_add
      map_smul' := hF }
  obtain ⟨N, hN, _, hpre, e, he⟩ :=
    AlgebraicGeometry.exists_invariant_subspace_nilpotent_quotient_injective k p V F'
  let G : V ⧸ N →ₛₗ[frobenius k p] V ⧸ N := N.mapQ N F' hN
  have hGin : Function.Injective G.toAddMonoidHom := by
    intro a b hab
    obtain ⟨x, rfl⟩ := N.mkQ_surjective a
    obtain ⟨y, rfl⟩ := N.mkQ_surjective b
    change N.mkQ (F x) = N.mkQ (F y) at hab
    refine (Submodule.Quotient.eq N).2 (hpre _ ?_)
    rwa [map_sub, ← Submodule.Quotient.eq]
  intro y
  let qy : V ⧸ N := N.mkQ y
  obtain ⟨z, hz⟩ := (Nat.card_pos_iff.mp (by
    rw [AlgebraicGeometry.natCard_fiber_sub_id_eq p hp G.toAddMonoidHom G.map_smul' hGin qy]
    exact pow_pos hp _)).1
  obtain ⟨x, rfl⟩ := N.mkQ_surjective z
  have herr : F x - x - y ∈ N := (Submodule.Quotient.eq N).1 hz
  obtain ⟨n, hn⟩ := e.surjective ⟨-(F x - x - y), N.neg_mem herr⟩
  have hcorr : F (n : V) - (n : V) = -(F x - x - y) :=
    (he n).symm.trans (congrArg (fun z : N ↦ (z : V)) hn)
  refine ⟨x + n, ?_⟩
  change F (x + (n : V)) - (x + (n : V)) = y
  rw [F.map_add, add_sub_add_comm, hcorr]
  abel
