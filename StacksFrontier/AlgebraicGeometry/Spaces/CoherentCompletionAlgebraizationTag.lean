module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.CoherentCompletionExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionLeftExact
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08BB: the whole lemma

Let `F` be a Noetherian algebraic space over a scheme `S`, `𝓘 ⊆ 𝒪_F` a quasi-coherent sheaf of
ideals, `G` a coherent `𝒪_F`-module, `E` a coherent `𝓘`-adic system and `α : E ⟶ G^∧` a map whose
kernel and cokernel are annihilated by a power of `𝓘`.  Stacks 08BB asserts that there is a
unique, up to unique isomorphism, triple `(M, a, β)` of a coherent module `M`, a map `a : M ⟶ G`
whose kernel and cokernel are annihilated by a power of `𝓘`, and an isomorphism `β : E ≅ M^∧`
with `α = a^∧ ∘ β`.  This file states existence and uniqueness on one theorem.

## Main results

* `AlgebraicGeometry.Space.exists_algebraization_and_existsUnique_iso`: **Stacks 08BB**, the
  whole lemma.

## Implementation notes

The existence half is spelled exactly as `AlgebraicGeometry.Space.C1573.exists_algebraization`
states it, and the uniqueness half exactly as
`AlgebraicGeometry.Space.existsUnique_iso_of_algebraization_of_isNoetherian` states it: any two
such triples differ by a unique isomorphism compatible with the maps to `G` and with the comparison
isomorphisms. The `Fact` instance on the étale charts is the instance argument of the completion
functor of Stacks 08B4, implied by the Noetherian hypothesis.

## References

* [Stacks Project, Tag 08BB](https://stacks.math.columbia.edu/tag/08BB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    [Fact (HasEtaleLocalProperty B S hS F (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)

/-- **Stacks 08BB.**  Let `F` be a Noetherian algebraic space over `S` and `𝓘 ⊆ 𝒪_F` a
quasi-coherent sheaf of ideals.  Let `G` be a coherent `𝒪_F`-module, `E` an object of
`Coh(F, 𝓘)` and `α : E ⟶ G^∧` a map whose kernel and cokernel are annihilated by a power of `𝓘`.
Then there exists a triple `(M, a, β)` where

1. `M` is a coherent `𝒪_F`-module,
2. `a : M ⟶ G` is an `𝒪_F`-module map whose kernel and cokernel are annihilated by a power of
   `𝓘`,
3. `β : E ≅ M^∧` is an isomorphism, and
4. `α = a^∧ ∘ β`,

and it is unique up to unique isomorphism: for any two such triples `(M, a, β)` and
`(N, a', β')` there is exactly one isomorphism `e : M ≅ N` with `a' ∘ e = a` and
`e^∧ ∘ β = β'`. -/
@[stacks 08BB]
theorem exists_algebraization_and_existsUnique_iso
    (hZ : B.Contains (⊤_ Scheme.{u})) (hN : IsNoetherian B S hS hZ F)
    {G : CoherentModules.{u, u} B S hS F hF} {E : CoherentAdicSystems B S hS F hF 𝓘}
    (α : E ⟶ (completionFunctor B S hS F hF 𝓘 hI).obj G)
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α.hom) :
    (∃ (M : CoherentModules.{u, u} B S hS F hF) (a : M ⟶ G)
      (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M),
      IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a ∧
        α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a) ∧
    ∀ {M N : CoherentModules.{u, u} B S hS F hF} (a : M ⟶ G) (a' : N ⟶ G)
      (β : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj M)
      (β' : E ≅ (completionFunctor B S hS F hF 𝓘 hI).obj N),
      IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a →
      IsMapKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 a' →
      α = β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a →
      α = β'.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map a' →
      ∃! e : M ≅ N, e.hom ≫ a' = a ∧
        β.hom ≫ (completionFunctor B S hS F hF 𝓘 hI).map e.hom = β'.hom :=
  ⟨C1573.exists_algebraization B S hS F hF 𝓘 hI α hα,
    fun a a' β β' ha ha' hα₁ hα₂ =>
      existsUnique_iso_of_algebraization_of_isNoetherian B S hS F hF 𝓘 hI hZ hN α a a' β β'
        ha ha' hα₁ hα₂⟩

end AlgebraicGeometry.Space

end
