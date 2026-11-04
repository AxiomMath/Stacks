module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.NeighbourhoodSectionsComparison
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.PrincipalFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalFormalSections.SheafComparison

/-!
# Full faithfulness of the completion functor at a principal formal locus

Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A`, let `U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the open
subschemes of `U` containing `U ∩ V(f)`, ordered by reverse inclusion. [Stacks, Tag 0EKV] asserts
that if

1. `A` is complete with respect to the `f`-adic topology,
2. `f` is a nonzerodivisor, and
3. `H¹_𝔞(A/fA)` is a finite `A`-module,

then the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(U, f𝒪_U)`, `ℱ ↦ ℱ^∧`, is fully faithful on
the full subcategory of finite locally free objects.

This file proves it. The source's proof is two citations: by [Stacks, Tag 0EK2] it suffices to
know `colim_𝒱 Γ(V, 𝒪_V) = lim_n Γ(U, 𝒪_U / fⁿ 𝒪_U)`, and that is [Stacks, Tag 0EIH] at the
module `A`. Both halves are available:
`Stacks.Algebraization.isIso_comparisonMap_principalTilde` is [Stacks, Tag 0EIH] for the
comparison map of [Stacks, Tag 0EG2], and
`Stacks.Algebraization.NeighbourhoodCompletion.implications_among_conditions` is the chain
(1) ⇒ (2) ⇒ (3) ⇒ (4) of [Stacks, Tag 0EK2].

## Main results

* `Stacks.Algebraization.isIso_comparisonMap_unit_of_principal` — the comparison map of
  [Stacks, Tag 0EG2] is an isomorphism for `𝒪_U`, from the hypotheses of the source.
* `Stacks.Algebraization.isQuasiAffineComplete_principal` — condition (1) of [Stacks, Tag 0EK2]
  at the zero locus of `f` on `U`.
* `Stacks.Algebraization.completionFullyFaithfulComplete_principal` — **[Stacks, Tag 0EKV]**, in
  full: the comparison is bijective for a pair of finite locally free modules defined on an
  arbitrary member `V` of `𝒱`, which is what an object of `colim_𝒱 Coh(𝒪_V)` is.
* `Stacks.Algebraization.completionFullyFaithful_principal_finiteLocallyFree` — the same
  conclusion for a pair of modules defined on `U` itself, in the vocabulary of
  `Stacks.Algebraization.completionFunctor`, which is the form the consumers in
  `StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/` are stated with. It is a
  convenience for those consumers and carries no part of the tag on its own.

## Implementation notes

An object of `colim_𝒱 Coh(𝒪_V)` is a coherent module on *some* member of `𝒱`, and a finite
locally free module on a small `V` need not extend to `U`, so the tag is registered on
`Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`, condition (4)
of [Stacks, Tag 0EK2], which quantifies over every `V ∈ 𝒱` and all finite locally free
`𝒪_V`-modules and takes the colimit over the neighbourhoods inside `V`. Nothing in the proof asks
such a pair to extend: the implication (2) ⇒ (3) of that tag embeds a finite locally free module
on `V` into a finite direct sum of restrictions to `V` of high twists of the ample module `𝒪_U`,
and that is what carries the comparison from `U` down to `V`.

The hypotheses reach that chain through
`Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isIso_comparisonMap`: the comparison
map of [Stacks, Tag 0EG2] compares `colim_𝒱 Γ(V, 𝒪_V)` with the sections of the quotients
`𝒪_U / fⁿ 𝒪_U` on all of `U`, while condition (1) of [Stacks, Tag 0EK2] compares it with the
sections of the structure sheaves of the infinitesimal neighbourhoods of `U ∩ V(f)`; the two
agree by [Stacks, Tag 0EL1].

The narrower statement for modules defined on `U` itself, in the vocabulary of the completion
functor, is kept alongside the tag because
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` is the map the rest of this subtree —
and [Stacks, Tag 0EKU], whose conclusion is verbatim the same — is phrased with, and that map is
only defined for modules on `U`. It is not the tag and does not stand in for any part of it.

Hypothesis (2) is used as regularity of `f` on the module `A`, which is what "nonzerodivisor"
means there: `Stacks.Algebraization.isSMulRegular_self_of_mem_nonZeroDivisors` converts the two.
Hypothesis (3) is the finiteness of `H¹_𝔞` of `Stacks.Algebraization.FormalSections.Quot f A 1`,
which is `A / fA`.

## References

* [Stacks Project, Tag 0EKV](https://stacks.math.columbia.edu/tag/0EKV)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
* [Stacks Project, Tag 0EIH](https://stacks.math.columbia.edu/tag/0EIH)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.LocalCohomology

noncomputable section

universe u

namespace Stacks.Algebraization

open Stacks.Algebraization.FormalSections

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {a : Ideal A} {f : A}

omit [IsNoetherianRing A] in
/-- A nonzerodivisor of a commutative ring is regular on the ring itself. -/
public theorem isSMulRegular_self_of_mem_nonZeroDivisors (hf : f ∈ nonZeroDivisors A) :
    IsSMulRegular A f := by
  intro x y hxy
  have hxy' : f * x = f * y := hxy
  have h0 : (x - y) * f = 0 := by linear_combination hxy'
  exact sub_eq_zero.1 (hf.2 _ h0)

/-- **The theorem on formal functions for `𝒪_U`.** Under the hypotheses of [Stacks, Tag 0EKV]
the comparison map of [Stacks, Tag 0EG2] is an isomorphism for `𝒪_U`:
`colim_𝒱 Γ(V, 𝒪_V) = lim_n Γ(U, 𝒪_U / fⁿ 𝒪_U)`. This is the equality the source's proof of
[Stacks, Tag 0EKV] quotes, and it is the second clause of condition (1) of [Stacks, Tag 0EK2]
once the limit is read on the infinitesimal neighbourhoods.

This is [Stacks, Tag 0EIH] at the module `A`, read through the identification of `Ã|_U` with
`𝒪_U`. -/
public theorem isIso_comparisonMap_unit_of_principal (hf : f ∈ a)
    [IsAdicComplete (Ideal.span {f}) A] (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A
      (localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
        (Quot f (ModuleCat.of A A) 1) 1)) :
    IsIso (comparisonMap A (Ideal.span {f}) a
      (SheafOfModules.unit (complementZeroLocus A a : Scheme).ringCatSheaf)) :=
  isIso_comparisonMap_unit A a f
    (isIso_comparisonMap_principalTilde hf (ModuleCat.of A A)
      (isSMulRegular_self_of_mem_nonZeroDivisors hnzd) hH1)

/-- **Condition (1) of [Stacks, Tag 0EK2] at the zero locus of `f` on `U`.** Under the hypotheses
of [Stacks, Tag 0EKV] the scheme `U = Spec(A) ∖ V(𝔞)` is quasi-affine and the colimit of the
sections of `𝒪_U` over the open neighbourhoods of `U ∩ V(f)` is the limit of the sections of the
structure sheaves of the infinitesimal neighbourhoods of `U ∩ V(f)`.

The first clause is `Stacks.Algebraization.isQuasiAffine_complementZeroLocus`. The second is
`Stacks.Algebraization.isIso_comparisonMap_unit_of_principal`, which is [Stacks, Tag 0EIH] at the
module `A`, read through
`Stacks.Algebraization.isNeighbourhoodSectionsComplete_of_isIso_comparisonMap`: the comparison
map of [Stacks, Tag 0EG2] compares the same colimit with the sections of the quotients
`𝒪_U / fⁿ 𝒪_U` on all of `U`, and those are the sections on the infinitesimal neighbourhoods by
[Stacks, Tag 0EL1]. -/
public theorem isQuasiAffineComplete_principal (hf : f ∈ a)
    [IsAdicComplete (Ideal.span {f}) A] (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A
      (localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
        (Quot f (ModuleCat.of A A) 1) 1)) :
    NeighbourhoodCompletion.IsQuasiAffineComplete (principalFormalLocusι A a f) := by
  have : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.IsNoetherian.toIsLocallyNoetherian
  have hcoh : (SheafOfModules.unit
      (complementZeroLocus A a : Scheme).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent _
  have hqc : (SheafOfModules.unit
      (complementZeroLocus A a : Scheme).ringCatSheaf).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  refine ⟨isQuasiAffine_complementZeroLocus A a, ?_⟩
  exact (infTower_isSectionsComplete_iff (principalFormalLocusι A a f) _).2
    (isNeighbourhoodSectionsComplete_of_isIso_comparisonMap A (Ideal.span {f}) a _
      (isIso_comparisonMap_unit_of_principal hf hnzd hH1))

/-- **[Stacks, Tag 0EKV].** Let `A` be a Noetherian ring, let `f ∈ 𝔞 ⊆ A`, put
`U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the open subschemes of `U` containing `U ∩ V(f)`, ordered by
reverse inclusion. Assume

1. `A` is complete with respect to the `f`-adic topology,
2. `f` is a nonzerodivisor, and
3. `H¹_𝔞(A/fA)` is a finite `A`-module.

Then the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(U, f𝒪_U)`, `ℱ ↦ ℱ^∧`, is fully faithful on
the full subcategory of finite locally free objects.

An object of `colim_𝒱 Coh(𝒪_V)` is a coherent module on *some* `V ∈ 𝒱`, and a morphism between
two of them is an element of `colim_{W ⊆ V} Hom_{𝒪_W}(𝒢|_W, ℱ|_W)`; so the conclusion is
`Stacks.Algebraization.NeighbourhoodCompletion.CompletionFullyFaithfulComplete`, which quantifies
over every `V ∈ 𝒱` and all finite locally free `𝒪_V`-modules `𝒢`, `ℱ`, and asserts that
`colim_{W ⊆ V} Hom_{𝒪_W}(𝒢|_W, ℱ|_W) ⟶ lim_n Hom_{𝒪_{Y_n}}(𝒢|_{Y_n}, ℱ|_{Y_n})` is bijective.
The quantifier here is the tag's own — an arbitrary member `V` of `𝒱`, not the single member
`V = U` — which matters because a finite locally free module on a small `V` need not extend to
`U`. That is full faithfulness: an object of `Coh(U, f𝒪_U)` is an inverse system of coherent
modules,
`𝒢^∧` is the system `(𝒢|_{Y_n})` of restrictions to the infinitesimal neighbourhoods of
`U ∩ V(f)`, and a morphism `𝒢^∧ ⟶ ℱ^∧` is a compatible family of morphisms of the restrictions.

The source's proof is two citations: by [Stacks, Tag 0EK2] it suffices that
`colim_𝒱 Γ(V, 𝒪_V) = lim_n Γ(U, 𝒪_U / fⁿ 𝒪_U)`, which is [Stacks, Tag 0EIH] at the module `A`.
Both are available: the equality is `Stacks.Algebraization.isQuasiAffineComplete_principal`,
condition (1) of [Stacks, Tag 0EK2], and the chain (1) ⇒ (2) ⇒ (3) ⇒ (4) is
`Stacks.Algebraization.NeighbourhoodCompletion.implications_among_conditions`. No step of the
argument needs the pair `𝒢`, `ℱ` to extend from `V` to `U`: the implication (2) ⇒ (3) embeds a
finite locally free module on `V` into a finite direct sum of restrictions to `V` of high twists
of the ample module `𝒪_U`, which is what carries the comparison from `U` down to `V`. -/
@[stacks 0EKV]
public theorem completionFullyFaithfulComplete_principal (hf : f ∈ a)
    [IsAdicComplete (Ideal.span {f}) A] (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A
      (localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
        (Quot f (ModuleCat.of A A) 1) 1)) :
    NeighbourhoodCompletion.CompletionFullyFaithfulComplete (principalFormalLocusι A a f) :=
  have h := NeighbourhoodCompletion.implications_among_conditions (principalFormalLocusι A a f)
  h.2.2.1 (h.2.1 (h.1 (isQuasiAffineComplete_principal hf hnzd hH1)))

/-- **Full faithfulness for a pair of modules defined on `U` itself, in the vocabulary of the
completion functor.** Under the hypotheses of [Stacks, Tag 0EKV], for finite locally free
coherent `𝒢`, `ℱ` on `U = Spec(A) ∖ V(𝔞)` the canonical map
`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` from
`colim_{V ∈ 𝒱} Hom_V(𝒢|_V, ℱ|_V)` to `Hom_{Coh(U, f𝒪_U)}(𝒢^∧, ℱ^∧)` is bijective.

This is not the tag and carries no part of it: [Stacks, Tag 0EKV] is
`Stacks.Algebraization.completionFullyFaithfulComplete_principal`, which is the statement for an
object of `colim_𝒱 Coh(𝒪_V)` living on an arbitrary member of `𝒱`, and that general statement
does not follow from the present one, since a finite locally free module on a small `V` need not
extend to `U`. What is written here is the same conclusion for the single pair of modules on `U`,
read through `Stacks.Algebraization.completionFunctor`: the target is the hom-set
of the category of adic systems rather than the inverse limit of the hom-sets over the
infinitesimal neighbourhoods, which is the form the consumers in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/` are stated with.

By [Stacks, Tag 0EK2] it suffices that the comparison map of [Stacks, Tag 0EG2] be an isomorphism
for `𝒪_U`, which is [Stacks, Tag 0EIH] at the module `A`. -/
public theorem completionFullyFaithful_principal_finiteLocallyFree (hf : f ∈ a)
    [IsAdicComplete (Ideal.span {f}) A] (hnzd : f ∈ nonZeroDivisors A)
    (hH1 : Module.Finite A
      (localCohomologyModule A a (Ideal.fg_of_isNoetherianRing a)
        (Quot f (ModuleCat.of A A) 1) 1)) :
    ∀ G F : AlgebraicGeometry.SheafOfModules.CoherentModules
        (complementZeroLocus A a : Scheme).ringCatSheaf,
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree G.obj →
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree F.obj →
        Function.Bijective (NeighbourhoodHoms.nbhdHomComparison A (Ideal.span {f}) a G F) :=
  fun G F hG hF =>
    nbhdHomComparison_bijective_of_isIso_unit A (Ideal.span {f}) a
      (isIso_comparisonMap_unit_of_principal hf hnzd hH1) G F hG hF

end Stacks.Algebraization

end

end
