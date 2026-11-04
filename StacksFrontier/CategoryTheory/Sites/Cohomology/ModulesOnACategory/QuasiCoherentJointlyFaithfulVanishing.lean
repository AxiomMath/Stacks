module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions

/-!
# Vanishing of the cohomology of a cartesian object detected on a faithful family

Let `C` be a category, viewed as a site with the chaotic topology, let `O` be a presheaf of
rings on `C`, and let `K` be an object of `D(O)`. Suppose given an object `U` and a family of
arrows `U ⟶ V i` of `Cᵒᵖ` (that is, of maps `V i → U` of `C`) along which `K` is cartesian, i.e.
the canonical maps `RΓ(U, K) ⊗^L_{O(U)} O(V i) ⟶ RΓ(V i, K)` are isomorphisms, and such that
each extension of scalars `O(U) → O(V i)` is exact (for instance flat) and the family of them is
jointly faithful. If the degree `n` cohomology sheaf of `K` vanishes over every `V i`, then it
vanishes over `U`.

This is the commutative-algebra step behind the statement that an object of `QC(𝒳)` whose
restriction to the étale charts of the representing algebraic space vanishes is zero: étale
coverings of affine schemes are faithfully flat.

## Main results

* `Stacks.ModulesOnACategory.QuasiCoherentCohomology.isZero_homology_obj_of_jointlyFaithful`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.ModulesOnACategory.QuasiCoherentEquivalence

universe w u v r t

namespace Stacks.ModulesOnACategory.QuasiCoherentCohomology

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{r})

/-- **Vanishing of a cohomology sheaf is detected on a jointly faithful family of exact base
changes along which the object is cartesian.** If `K` in `D(O)` is cartesian along each arrow
`a i : U ⟶ V i` of `Cᵒᵖ`, each `E i` is an exact left adjoint of restriction of scalars along
`O(U) → O(V i)`, the family `E i` is jointly faithful on objects, and `Hⁿ(K)` vanishes over every
`V i`, then `Hⁿ(K)` vanishes over `U`. -/
theorem isZero_homology_obj_of_jointlyFaithful (bc : BaseChangeData.{w} O) (K : DMod.{w} O)
    {U : Cᵒᵖ} {ι : Type t} (V : ι → Cᵒᵖ) (a : ∀ i, U ⟶ V i)
    (E : ∀ i, ModuleCat.{max u v r w} (O.obj U) ⥤ ModuleCat.{max u v r w} (O.obj (V i)))
    [∀ i, (E i).Additive] [∀ i, PreservesFiniteLimits (E i)]
    [∀ i, PreservesFiniteColimits (E i)]
    (adj : ∀ i, E i ⊣ ModuleCat.restrictScalars.{max u v r w} (O.map (a i)).hom)
    (hE : ∀ M : ModuleCat.{max u v r w} (O.obj U), (∀ i, IsZero ((E i).obj M)) → IsZero M)
    (hK : ∀ i, IsIso (comparison.{w} bc (a i) K)) (n : ℤ)
    (hn : ∀ i, IsZero (((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max u v r w} O) n).obj K).obj (V i))) :
    IsZero (((DerivedCategory.homologyFunctor
      (PresheafOfModules.{max u v r w} O) n).obj K).obj U) := by
  refine hE _ fun i ↦ ?_
  have h := (isIso_comparison_iff O (a i) (adj i) bc K).mp (hK i) n
  exact (hn i).of_iso (@asIso _ _ _ _ ((sectionsBaseChange.{w} O (a i) (adj i)).app
    ((DerivedCategory.homologyFunctor (PresheafOfModules.{max u v r w} O) n).obj K)) h)

end Stacks.ModulesOnACategory.QuasiCoherentCohomology

end
