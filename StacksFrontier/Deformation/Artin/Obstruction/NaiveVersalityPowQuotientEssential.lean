module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityQuotientDifferentials

/-!
# `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` is an essential surjection

The degree `-1` half of the direction `(1) ⇒ (2)` of [Stacks, Tag 07YM] drives at a
contradiction with the essential surjectivity of `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n`, which is
[Stacks, Tag 06H0] applied to the bijectivity [Stacks, Tag 07YL] supplies. Both halves of that
composition are available —
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`
and `Deformation.Artin.differentialsBaseChangeMap_bijective_powQuotient` — but they do not meet:
the second is stated with the algebra structures `Λ → A' → A → k` *rebuilt* from the three
algebra homomorphisms it quantifies over, whereas [Stacks, Tag 07YL] states its bijectivity with
whatever algebra structures are in scope where its conclusion is read. The two are propositionally
equal and not definitionally so, because `RingHom.toAlgebra` replaces the scalar action by
multiplication through the structure map, and a `Function.Bijective` assertion about a map between
tensor products formed with one of them is not an assertion about the other: the two tensor
products are different types.

This file joins them. The three algebra homomorphisms are taken as arguments — so that they do
not depend on the algebra structures — together with the statement that each is the structure map
in scope; `Algebra.algebra_ext` then makes the two structures equal and the equation is
*substituted*, after which the two statements are literally the same.

## Main results

* `Deformation.ArtinianLocalAlgCat.isEssentialSurjection_powQuotientMap_of_bijective` — **the
  essential surjection of [Stacks, Tag 07YM]**: if `A' → A` does not change differentials modulo
  `k` then `A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` is an essential surjection of `𝒞_Λ`, for `n ≥ 2`.

## Implementation notes

The substitution is what the hypotheses `hεeq`, `hε'eq` and `hφeq` are for, and it is why the
three homomorphisms are arguments rather than being built inside from the ambient structures: an
algebra homomorphism built from an instance cannot be substituted for it. Nothing is assumed about
how the ambient structures arise, so the statement applies to the output of [Stacks, Tag 07YL]
with its quantified structures as readily as to the canonical ones of a residue field.

## References

* [Stacks Project, Tag 06H0](https://stacks.math.columbia.edu/tag/06H0)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.ArtinianLocalAlgCat

/-- **The essential surjection of [Stacks, Tag 07YM].** Let `Λ → A' → A → k` be a tower with `k`
a field and both maps onto `k` surjective, let `𝔭` and `𝔭'` be the two augmentation ideals and
let `n ≥ 2`. If `A' → A` does not change differentials modulo `k`, then the induced morphism
`A' ⧸ (𝔭') ^ n ⟶ A ⧸ 𝔭 ^ n` of `𝒞_Λ` is an essential surjection.

`Deformation.Artin.differentialsBaseChangeMap_bijective_powQuotient` transfers the bijectivity to
the quotients and
`Deformation.ArtinianLocalAlgCat.isEssentialSurjection_iff_bijective_differentialsBaseChangeMap`
is [Stacks, Tag 06H0]; what this adds is the identification of the algebra structures rebuilt from
`ε`, `ε'` and `φ` with the ambient ones, which `Algebra.algebra_ext` provides and which the proof
then substitutes. -/
@[stacks 07YM "A'/(𝔭') ^ n ⟶ A/𝔭 ^ n is an essential surjection of 𝒞_Λ"]
public theorem isEssentialSurjection_powQuotientMap_of_bijective
    {Λ A' A k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] [CommRing A'] [CommRing A]
    [Algebra Λ A'] [Algebra Λ A] [IsNoetherianRing A'] [IsNoetherianRing A]
    [Algebra A' A] [Algebra A' k] [Algebra A k]
    [IsScalarTower Λ A' A] [IsScalarTower Λ A' k] [IsScalarTower Λ A k] [IsScalarTower A' A k]
    (ε : A →ₐ[Λ] k) (hεeq : ∀ a, ε a = algebraMap A k a) (hε : Function.Surjective ε)
    (ε' : A' →ₐ[Λ] k) (hε'eq : ∀ a', ε' a' = algebraMap A' k a')
    (hε' : Function.Surjective ε')
    (φ : A' →ₐ[Λ] A) (hφeq : ∀ a', φ a' = algebraMap A' A a') (hφ : ε.comp φ = ε')
    (n : ℕ) [NeZero n] (hn : 2 ≤ n)
    (hbij : Function.Bijective (Deformation.Artin.differentialsBaseChangeMap Λ A' A k)) :
    IsEssentialSurjection (powQuotientMap hφ hε' hε n) := by
  have hiA : (inferInstance : Algebra A' A) = φ.toRingHom.toAlgebra :=
    Algebra.algebra_ext _ _ fun a' => (hφeq a').symm
  have hik : (inferInstance : Algebra A k) = ε.toRingHom.toAlgebra :=
    Algebra.algebra_ext _ _ fun a => (hεeq a).symm
  have hi'k : (inferInstance : Algebra A' k) = ε'.toRingHom.toAlgebra :=
    Algebra.algebra_ext _ _ fun a' => (hε'eq a').symm
  subst hiA
  subst hik
  subst hi'k
  rw [isEssentialSurjection_iff_bijective_differentialsBaseChangeMap]
  exact Deformation.Artin.differentialsBaseChangeMap_bijective_powQuotient hφ n hn hbij

end Deformation.ArtinianLocalAlgCat
