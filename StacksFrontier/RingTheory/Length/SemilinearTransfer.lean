module

public import Mathlib.RingTheory.Length

/-!
# Transfer of module length along a surjection of rings

Let `φ : R →+* T` be a surjective homomorphism of commutative rings, let `M` be an `R`-module
and let `N` be a `T`-module. If the two underlying additive groups are isomorphic by a map
which is semilinear over `φ`, then `M` and `N` have the same length — `M` as an `R`-module and
`N` as a `T`-module.

The reason is that the `R`-submodules of `N` obtained by restricting scalars along `φ` are
exactly its `T`-submodules, since every operator `t • -` is an operator `φ r • -`; so the two
submodule lattices coincide and the length, being the Krull dimension of that lattice, is the
same. That step is Mathlib's `Module.length_eq_of_surjective`; what is added here is the
semilinear comparison, which is what a geometric application produces: a germ map of local
rings on one side and an isomorphism of stalks over it on the other.

## Main results

* `Module.length_eq_of_surjective_of_addEquiv`: the statement above.

## Implementation notes

The hypothesis is stated as an `AddEquiv` together with a semilinearity equation rather than
as a semilinear equivalence, because the comparison maps produced by stalk computations are
additive isomorphisms whose semilinearity is a separate lemma; building a
`LinearEquiv` over `φ` would require naming the restriction of scalars at the call site, which
is exactly the bookkeeping this lemma exists to absorb.

Both rings are assumed commutative because `Module.length_eq_of_surjective` is stated for an
algebra over a commutative ring; the restriction of scalars is installed here as
`Module.compHom`, so no `Algebra` instance has to be in scope at the call site.

## References

* [Stacks Project, Tag 00IX](https://stacks.math.columbia.edu/tag/00IX), part (2): length is
  unchanged by a surjective change of rings.
-/

@[expose] public section

/-- **Length transfer along a surjection.** Let `φ : R →+* T` be a surjective homomorphism of
commutative rings, let `M` be an `R`-module, let `N` be a `T`-module, and let `e : N ≃+ M` be
an isomorphism of the underlying additive groups which is semilinear over `φ`, that is
`e (φ r • n) = r • e n`. Then the length of `M` over `R` equals the length of `N` over `T`.

Restricting the scalars of `N` along `φ` does not change its length, because `φ` is surjective
(`Module.length_eq_of_surjective`), and `e` is an isomorphism of `R`-modules for that
restricted action. -/
theorem Module.length_eq_of_surjective_of_addEquiv {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (hφ : Function.Surjective φ) {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module T N] (e : N ≃+ M) (he : ∀ (r : R) (n : N), e (φ r • n) = r • e n) :
    Module.length R M = Module.length T N := by
  let _ : Algebra R T := φ.toAlgebra
  let _ : Module R N := Module.compHom N φ
  let _ : IsScalarTower R T N := .of_algebraMap_smul fun _ _ => rfl
  exact ({ e with map_smul' := he } : N ≃ₗ[R] M).length_eq.symm.trans
    (Module.length_eq_of_surjective (S := R) (R := T) (M := N)
      (by rwa [RingHom.algebraMap_toAlgebra]))

end
