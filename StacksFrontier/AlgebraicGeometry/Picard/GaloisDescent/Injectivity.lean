module

public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.PicardBaseChange.Injectivity

/-!
# Injectivity of the pullback of Picard classes to a field extension

Let `k` be a field and let `X` be a quasi-compact, quasi-separated scheme over `k` with
`H⁰(X, 𝒪_X) = k`. Then for every field extension `k'/k` the pullback map
`Pic(X) → Pic(X_{k'})` is injective. This is the injectivity half of
[Stacks, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT); the full identification of
`Pic(X)` with the Galois-fixed classes of `Pic(X_{k'})` is
`Stacks.Picard.bijOn_schemePullbackClass_galoisFixedClasses` in
`StacksFrontier/AlgebraicGeometry/Picard/GaloisDescent/PicardGaloisInvariants.lean`.

[Stacks, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5) proves the injectivity for
`H⁰(X, 𝒪_X)` semi-local, and is available as
`Stacks.AlgebraicGeometry.PicardBaseChange.injective_picardPullback_of_finiteDimensional`.
Semi-locality is reached here through finite dimensionality: if the canonical map
`k → H⁰(X, 𝒪_X)` is an isomorphism then `H⁰(X, 𝒪_X)` is spanned by `1` over `k`.

## Main results

* `Stacks.Picard.finiteDimensional_globalSections`: if the canonical map `k → H⁰(X, 𝒪_X)` is an
  isomorphism then `H⁰(X, 𝒪_X)` is a finite-dimensional `k`-algebra.
* `Stacks.Picard.injective_schemePullbackClass_of_globalSectionsIso`: **the injectivity half of
  Tag 0CDT.**

## Implementation notes

**`H⁰(X, 𝒪_X) = k` is spelled** `IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)`: the
canonical map from `k = H⁰(Spec k, 𝒪)` to `H⁰(X, 𝒪_X)` induced by the structure morphism is an
isomorphism of rings.

## References

* [Stacks Project, Tag 0CDT](https://stacks.math.columbia.edu/tag/0CDT)
* [Stacks Project, Tag 0CC5](https://stacks.math.columbia.edu/tag/0CC5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.PicardBaseChange (globalSectionsAlgebra
  injective_picardPullback_of_finiteDimensional)

universe u

namespace Stacks.Picard

/-- If the canonical map `k → H⁰(X, 𝒪_X)` attached to a morphism `X ⟶ Spec k` is an
isomorphism, then `H⁰(X, 𝒪_X)` is a finite-dimensional `k`-algebra, being spanned by `1`. -/
theorem finiteDimensional_globalSections {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (hf : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) :
    letI := globalSectionsAlgebra f
    FiniteDimensional k Γ(X, ⊤) := by
  let _ := globalSectionsAlgebra f
  exact Module.Finite.of_surjective (Algebra.linearMap k Γ(X, ⊤))
    (ConcreteCategory.bijective_of_isIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)).surjective

/-- **The injectivity half of Stacks Tag 0CDT.** Let `X` be a quasi-compact, quasi-separated
scheme over a field `k` with `H⁰(X, 𝒪_X) = k`, and let `k'/k` be a field extension. Then the
pullback map `Pic(X) → Pic(X_{k'})` is injective: `H⁰(X, 𝒪_X)` is then a field, hence
semi-local, and Tag 0CC5 applies. -/
@[stacks 0CDT "injectivity of `Pic(X) → Pic(X_{k'})`, proved from Tag 0CC5; the full \
identification is `bijOn_schemePullbackClass_galoisFixedClasses`"]
theorem injective_schemePullbackClass_of_globalSectionsIso {k k' : Type u} [Field k] [Field k']
    (φ : k →+* k') {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (hf : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) :
    Function.Injective (schemePullbackClass (pullback.fst f (Spec.map (CommRingCat.ofHom φ)))) :=
  injective_picardPullback_of_finiteDimensional X φ f (finiteDimensional_globalSections f hf)

end Stacks.Picard

end
