module

public import StacksFrontier.Homology.Perfect.Duality.DerivedDual
public import StacksFrontier.Homology.Perfect.Duality.Biduality
public import StacksFrontier.Homology.Perfect.Duality.TensorHom
public import StacksFrontier.Homology.Perfect.Duality.TensorProductTorAmplitude

/-!
# Duality for perfect complexes

Let `A` be a ring and let `K` be a perfect object of `D(A)`. Its derived dual
`Kᵛ = RHom_A(K, A)` is again perfect, the canonical biduality morphism `K ⟶ (Kᵛ)ᵛ` is an
isomorphism, the canonical comparison `L ⊗_A^L Kᵛ ⟶ RHom_A(K, L)` is an isomorphism functorially
in `L`, and in degree zero the latter identifies `H⁰(L ⊗_A^L Kᵛ)` with `Ext⁰_A(K, L)`
([stacks 07VI]). The development is split into
`StacksFrontier.Homology.Perfect.Duality.DerivedDual` (the derived dual, the two canonical morphisms
and the degree-zero identification), `StacksFrontier.Homology.Perfect.Duality.Biduality` (biduality
is an isomorphism), `StacksFrontier.Homology.Perfect.Duality.TensorHom` (the tensor--Hom comparison
and the statement of [stacks 07VI]) and
`StacksFrontier.Homology.Perfect.Duality.TensorProductTorAmplitude` (derived tensor products of
perfect complexes, [stacks 0GM0], and the Tor amplitude of the derived dual, [stacks 0H81]).
-/
