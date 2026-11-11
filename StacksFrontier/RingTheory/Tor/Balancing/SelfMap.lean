module

public import StacksFrontier.RingTheory.Tor.Balancing.Naturality
public import StacksFrontier.LinearAlgebra.TensorProduct.Swap

/-!
# The symmetry of `Tor` on `Tor_i(M, M)` is not the identity

The canonical isomorphism `Tor_i^R(M, N) ≅ Tor_i^R(N, M)` of Stacks, Tag 00M3, is
`torSymm R i`, the composite of the balancing `Tor_iso_Tor'` with the flip comparison
`torFlip_iso_Tor'`. For `M = N` its component is a self-map of `Tor_i^R(M, M)`.

In degree `0` this self-map is the switch map `m ⊗ m' ↦ m' ⊗ m` of `M ⊗_R M`
(`torSymm_zero_hom_app_app`, under the identification `torZeroIso` of `Tor_0^R(M, N)` with
`M ⊗_R N`). Hence for a vector space `V` of dimension at least `2` over a field the self-map of
`Tor_0(V, V)` is neither the identity nor its negative (`torSymm_zero_self_ne_one_and_ne_neg_one`),
and it is conjugate to `swapMap`, whose eigenspaces are computed in
`StacksFrontier.LinearAlgebra.TensorProduct.Swap` (Stacks, Remark 00M4).

## Main definitions

* `torSymm`: the canonical isomorphism `Tor_i(M, N) ≅ Tor_i(N, M)` of Tag 00M3.
* `torZeroIso`: the identification `Tor_0^R(M, N) ≅ M ⊗_R N`.

## Main results

* `torSymm_zero_hom_app_app`: in degree `0`, `torSymm` is the braiding of `ModuleCat R`.
* `torSymm_zero_self_conj`: for `M = N`, the degree-`0` self-map is conjugate to the switch map.
* `torSymm_zero_self_ne_one_and_ne_neg_one`: Remark 00M4.

## References

* [Stacks Project, Tag 00M3](https://stacks.math.columbia.edu/tag/00M3)
* [Stacks Project, Tag 00M4](https://stacks.math.columbia.edu/tag/00M4)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

variable (R : Type u) [CommRing R]

/-- The canonical isomorphism `Tor_i^R(M, N) ≅ Tor_i^R(N, M)` of bifunctors (Stacks, Tag 00M3):
the balancing `Tor_iso_Tor'` followed by the inverse of the flip comparison `torFlip_iso_Tor'`.
Its component at `(M, N)` is `((torSymm R i).hom.app M).app N`. -/
noncomputable def torSymm (i : ℕ) :
    Tor (ModuleCat.{u} R) i ≅ (Tor (ModuleCat.{u} R) i).flip :=
  (Tor_iso_Tor' R i).trans (torFlip_iso_Tor' R i).symm

/-- The identification `Tor_0^R(M, N) ≅ M ⊗_R N` of the zeroth left derived functor of the right
exact functor `M ⊗ -` with `M ⊗ -` itself. -/
noncomputable def torZeroIso (M N : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 0).obj M).obj N ≅ M ⊗ N :=
  (tensorLeft M).leftDerivedZeroIsoSelf.app N

/-- In degree `0` the symmetry `torSymm` of Tag 00M3 is the braiding `M ⊗ N ≅ N ⊗ M`, under the
identifications `torZeroIso` of `Tor_0` with the tensor product. -/
theorem torSymm_zero_hom_app_app (M N : ModuleCat.{u} R) :
    ((torSymm R 0).hom.app M).app N ≫ (torZeroIso R N M).hom
      = (torZeroIso R M N).hom ≫ (β_ M N).hom := by
  have h := NatTrans.congr_app (Tor_iso_Tor'.fromLeftDerivedZero_natTrans
    (BraidedCategory.tensorLeftIsoTensorRight N).inv) M
  simp only [NatTrans.comp_app] at h
  change ((tensorLeft M).leftDerivedZeroIsoSelf.hom.app N
      ≫ (tensorRight N).leftDerivedZeroIsoSelf.inv.app M
      ≫ (NatTrans.leftDerived (BraidedCategory.tensorLeftIsoTensorRight N).inv 0).app M)
      ≫ (tensorLeft N).leftDerivedZeroIsoSelf.hom.app M
    = (tensorLeft M).leftDerivedZeroIsoSelf.hom.app N ≫ (β_ M N).hom
  rw [Category.assoc, Category.assoc, Functor.leftDerivedZeroIsoSelf_hom (tensorLeft N), h,
    ← Functor.leftDerivedZeroIsoSelf_hom (tensorRight N), Iso.inv_hom_id_app_assoc]
  congr 1

/-- For `M = N`, the degree-`0` self-map of `Tor_0^R(M, M)` given by `torSymm` is, under
`torZeroIso`, the switch map `m ⊗ m' ↦ m' ⊗ m` of `M ⊗_R M`. -/
theorem torSymm_zero_self_conj (M : ModuleCat.{u} R) :
    (torZeroIso R M M).inv ≫ ((torSymm R 0).hom.app M).app M ≫ (torZeroIso R M M).hom
      = ModuleCat.ofHom (TensorProduct.comm R M M).toLinearMap := by
  rw [torSymm_zero_hom_app_app, Iso.inv_hom_id_assoc]
  ext : 1
  refine TensorProduct.ext' fun x y => ?_
  exact ModuleCat.MonoidalCategory.braiding_hom_apply x y

/-- If `dim_k V ≥ 2`, the switch map of `V ⊗_k V` is not a scalar multiple of the identity: for
a linearly independent pair `v, w` the four tensors `eᵢ ⊗ eⱼ` are linearly independent, so
`w ⊗ v ≠ c • (v ⊗ w)`. -/
theorem exists_swapMap_ne_smul {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (hn : 2 ≤ Module.finrank k V) (c : k) : ∃ z : TensorProduct k V V, swapMap k V z ≠ c • z := by
  have hrank : 1 < Module.rank k V := Module.lt_rank_of_lt_finrank (by omega)
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank k V)
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 := exists_ne 0
  obtain ⟨w, hvw⟩ := exists_linearIndependent_pair_of_one_lt_rank hrank hv
  refine ⟨v ⊗ₜ[k] w, fun heq => ?_⟩
  rw [swapMap_tmul] at heq
  have hli : LinearIndependent k
      (fun p : Fin 2 × Fin 2 => (![v, w] p.fst) ⊗ₜ[k] (![v, w] p.snd)) :=
    hvw.tmul_of_isDomain hvw
  have hsum := Fintype.linearIndependent_iff.mp hli
    (fun p => if p = (1, 0) then 1 else if p = (0, 1) then -c else 0)
    (by simp [Fintype.sum_prod_type, Fin.sum_univ_two, heq])
  simpa using hsum (1, 0)

/-- Stacks, Remark 00M4: for `M = N` the canonical isomorphism of Tag 00M3 gives a self-map of
`Tor_i^R(M, M)`, and this self-map is not the identity, already for `i = 0`; changing its sign
does not help either. Concretely, let `V` be a vector space of dimension at least `2` over a
field `k`. Under `torZeroIso` the self-map of `Tor_0^k(V, V)` given by `torSymm` is the switch
map `swapMap k V` of `V ⊗_k V` (whose eigenspaces have dimensions `(n² + n)/2` and `(n² − n)/2`
in characteristic `≠ 2`, `swap_eigenspace_dim`, and which is not diagonalizable in
characteristic `2`, `swap_not_isDiagonalizable`), and it is neither the identity nor minus the
identity. -/
@[stacks 00M4 "the degree-0 self-map of the 00M3 symmetry on Tor_0(V, V) is the switch map, \
  and is neither 1 nor -1 when dim V ≥ 2"]
theorem torSymm_zero_self_ne_one_and_ne_neg_one (k : Type u) [Field k] (V : ModuleCat.{u} k)
    (hn : 2 ≤ Module.finrank k V) :
    (torZeroIso k V V).inv ≫ ((torSymm k 0).hom.app V).app V ≫ (torZeroIso k V V).hom
        = ModuleCat.ofHom (swapMap k V) ∧
      ((torSymm k 0).hom.app V).app V ≠ 𝟙 _ ∧
      ((torSymm k 0).hom.app V).app V ≠ -𝟙 _ := by
  have hconj : (torZeroIso k V V).inv ≫ ((torSymm k 0).hom.app V).app V ≫ (torZeroIso k V V).hom
      = ModuleCat.ofHom (swapMap k V) := torSymm_zero_self_conj k V
  refine ⟨hconj, fun h => ?_, fun h => ?_⟩
  · obtain ⟨z, hz⟩ := exists_swapMap_ne_smul hn (1 : k)
    rw [h, Category.id_comp, Iso.inv_hom_id] at hconj
    apply hz
    have := congrArg (fun f => ModuleCat.Hom.hom f z) hconj
    simpa using this.symm
  · obtain ⟨z, hz⟩ := exists_swapMap_ne_smul hn (-1 : k)
    rw [h, Preadditive.neg_comp, Category.id_comp, Preadditive.comp_neg, Iso.inv_hom_id] at hconj
    apply hz
    have := congrArg (fun f => ModuleCat.Hom.hom f z) hconj
    simpa using this.symm
