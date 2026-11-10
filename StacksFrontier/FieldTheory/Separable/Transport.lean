module

public import StacksFrontier.FieldTheory.Separable.TFAE

/-!
# Separability of a field extension is invariant under isomorphism

A field extension `K / k` is separable in the sense of Tag 030O exactly when an isomorphic
extension `K' / k'` is: given ring isomorphisms `k ≃+* k'` and `K ≃+* K'` commuting with the two
structure maps, separability passes from either extension to the other.

The proof goes through the `p`-th power criterion of Tag 030W
(`Algebra.isSeparableExtension_tfae`): a semilinear bijection carries linearly independent
families to linearly independent families and commutes with taking `p`-th powers.

## Main results

* `Algebra.IsSeparableExtension.of_ringEquiv`: separability transported along compatible ring
  isomorphisms of the base and of the extension.
* `Algebra.IsSeparableExtension.iff_of_ringEquiv`: the two separability conditions agree.

## References

* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
* [Stacks Project, Tag 030W](https://stacks.math.columbia.edu/tag/030W)
-/

@[expose] public section

namespace Algebra.IsSeparableExtension

/-- **Separability is transported along an isomorphism of field extensions.** If `e : k ≃+* k'`
and `E : K ≃+* K'` commute with the structure maps `k → K` and `k' → K'`, and `K / k` is
separable, then so is `K' / k'`. -/
theorem of_ringEquiv {k K k' K' : Type*} [Field k] [Field K] [Field k'] [Field K']
    [Algebra k K] [Algebra k' K'] (e : k ≃+* k') (E : K ≃+* K')
    (he : ∀ a, E (algebraMap k K a) = algebraMap k' K' (e a))
    (hsep : Algebra.IsSeparableExtension k K) : Algebra.IsSeparableExtension k' K' := by
  let p := ringExpChar k
  have : ExpChar k' p := expChar_of_injective_ringHom (f := e.toRingHom) e.injective p
  have hpow := ((Algebra.isSeparableExtension_tfae k K p).out 1 2).mp hsep
  apply ((Algebra.isSeparableExtension_tfae k' K' p).out 2 1).mp
  intro s hs
  have hsmul (a : k) (x : K) : E (a • x) = e a • E x := by
    simp only [Algebra.smul_def, map_mul, he]
  have hsmul' (a : k') (x : K') : E.symm (a • x) = e.symm a • E.symm x := by
    apply E.injective
    rw [E.apply_symm_apply, hsmul, e.apply_symm_apply, E.apply_symm_apply]
  have hs' : LinearIndependent k (fun x : s => E.symm x.1) :=
    hs.map_of_surjective_injectiveₛ e.symm E.symm.toAddMonoidHom e.symm.surjective
      E.symm.injective hsmul'
  have hp' : LinearIndependent k (fun x : s => (E.symm x.1) ^ p) :=
    (linearIndepOn_range_iff hs'.injective (· ^ p)).mp
      (hpow _ hs'.linearIndepOn_id)
  have hh := hp'.map_of_surjective_injectiveₛ e E.toAddMonoidHom e.surjective
    E.injective hsmul
  change LinearIndependent k' (fun x : s => E (E.symm x.1 ^ p)) at hh
  change LinearIndependent k' (fun x : s => x.1 ^ p)
  simpa only [map_pow, E.apply_symm_apply] using hh

/-- **Isomorphic field extensions are separable together.** For ring isomorphisms
`e : k ≃+* k'` and `E : K ≃+* K'` commuting with the structure maps, `K / k` is separable exactly
when `K' / k'` is. -/
theorem iff_of_ringEquiv {k K k' K' : Type*} [Field k] [Field K] [Field k'] [Field K']
    [Algebra k K] [Algebra k' K'] (e : k ≃+* k') (E : K ≃+* K')
    (he : ∀ a, E (algebraMap k K a) = algebraMap k' K' (e a)) :
    Algebra.IsSeparableExtension k K ↔ Algebra.IsSeparableExtension k' K' := by
  refine ⟨of_ringEquiv e E he, of_ringEquiv e.symm E.symm fun a ↦ ?_⟩
  apply E.injective
  rw [E.apply_symm_apply, he, e.apply_symm_apply]

end Algebra.IsSeparableExtension
