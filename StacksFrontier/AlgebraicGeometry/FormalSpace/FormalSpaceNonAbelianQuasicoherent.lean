module

public import Mathlib.CategoryTheory.Abelian.Transfer
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.Transfer
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules
public import StacksFrontier.Examples.Completion.CompleteModulesNotAbelian

/-!
# Non-abelianness of quasi-coherent modules, transported along an equivalence

Non-abelianness of a category is invariant under equivalence, and this file records the
transport together with the one instance of it that the category of quasi-coherent modules
on a category fibred in groupoids needs: if that category is equivalent to the category of
`I`-adically complete modules over a Noetherian domain which is complete for a principal
ideal with a non-zero non-unit generator, then it is not abelian.

The second statement is the closing step of the discussion in Stacks, Section 110.13, which
identifies the quasi-coherent modules on `Spf(ℤ_p)` with the `p`-adically complete abelian
groups and then quotes the non-abelianness of the latter. The non-abelianness of the latter is
`Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal`, Stacks 07JR.

## Main results

* `CategoryTheory.not_nonempty_abelian_of_equivalence`: a category equivalent to one carrying
  no abelian structure carries none either.
* `AlgebraicGeometry.FormalSpace.not_abelian_quasicoherentModules_of_equivalence`: the
  category of quasi-coherent modules on a category fibred in groupoids is not abelian as soon
  as it is equivalent to a category of adically complete modules of the kind Stacks 07JR rules
  out.

## Implementation notes

`CategoryTheory.abelianOfEquivalence` turns an abelian structure on a category into one on any
equivalent category, but it asks for the additive structure and the finite products of the
target as separate inputs. Both are themselves transported: the preadditive structure along
the fully faithful inverse functor by `CategoryTheory.Preadditive.ofFullyFaithful`, and the
finite products by `CategoryTheory.Adjunction.hasLimitsOfShape_of_equivalence`. Since
`CategoryTheory.Abelian` bundles its preadditive structure rather than taking it as a
parameter, the structure produced this way inhabits the same type that
`¬ Nonempty (Abelian _)` speaks about, so the two statements do contradict each other.

Non-abelianness is stated as `¬ Nonempty (Abelian _)`, which rules out every abelian structure
on the category rather than a preferred one; this matches the form of Stacks 07JR in
`StacksFrontier/Examples/Completion/CompleteModulesNotAbelian.lean`.

The category of quasi-coherent modules is `AlgebraicGeometry.FibredSite.quasicoherentModules`,
the registered site of Stacks 06WG. The variant
`AlgebraicGeometry.Stack.quasicoherentModules` is the same category — the two are equal by
`rfl` — so no separate statement is needed for it.

## References

* [Stacks Project, Tag 07JR](https://stacks.math.columbia.edu/tag/07JR)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- Carrying no abelian structure is invariant under equivalence of categories: if `M` admits
no abelian structure and `Q` is equivalent to `M`, then `Q` admits none either. -/
theorem not_nonempty_abelian_of_equivalence {Q : Type u₁} [Category.{v₁} Q]
    {M : Type u₂} [Category.{v₂} M] (e : Q ≌ M)
    (hM : ¬ Nonempty (Abelian M)) : ¬ Nonempty (Abelian Q) := by
  rintro ⟨hQ⟩
  let _ : Abelian Q := hQ
  let _ : Preadditive M := Preadditive.ofFullyFaithful e.fullyFaithfulInverse
  let _ : HasFiniteProducts M :=
    ⟨fun _ => Adjunction.hasLimitsOfShape_of_equivalence e.inverse⟩
  exact hM ⟨abelianOfEquivalence e.inverse⟩

end CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u v w m r s

/-- The category of quasi-coherent modules on a category fibred in groupoids over the schemes
over `S` is not abelian as soon as it is equivalent to the category of `I`-adically complete
`R`-modules for a Noetherian domain `R` which is complete for a principal ideal `I = (π)` whose
generator `π` is neither zero nor a unit.

This is the step by which Stacks, Section 110.13 concludes: the quasi-coherent modules on the
Noetherian affine formal algebraic space `Spf(ℤ_p)` are identified with the `p`-adically
complete abelian groups, and those do not form an abelian category by Stacks 07JR, which is
`Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal`.

The equivalence itself is an input here, not a conclusion: this statement does not exhibit a
formal algebraic space, and so it is not the lemma of Stacks 0ALG.

The universe of the complete modules is carried by an auxiliary module `E` with a linear
equivalence `E ≃ₗ[R] R`, exactly as in Stacks 07JR; see
`Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal`. -/
theorem not_abelian_quasicoherentModules_of_equivalence
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids)
    (R : Type r) [CommRing R] [IsNoetherianRing R] [NoZeroDivisors R]
    (I : Ideal R) (hR : IsAdicComplete I R) (π : R) (hIspan : I = Ideal.span {π})
    (hπ : π ≠ 0) (hπnonunit : ¬ IsUnit π)
    (E : Type s) [AddCommGroup E] [Module R E] (eER : E ≃ₗ[R] R)
    (e : FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp ≌
      Stacks.Examples.IAdicallyCompleteModuleCat.{s} R I) :
    ¬ Nonempty (Abelian (FibredSite.quasicoherentModules.{u, v, w, m} B S hS p hp)) :=
  not_nonempty_abelian_of_equivalence e
    (Stacks.Examples.not_abelian_iAdicallyCompleteModuleCat_of_principal R I hR π hIspan
      hπ hπnonunit E eER)

end AlgebraicGeometry.FormalSpace

end
