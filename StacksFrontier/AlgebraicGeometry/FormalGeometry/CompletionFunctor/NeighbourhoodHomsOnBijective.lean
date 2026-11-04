module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHomsOn
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHomsComplement
public import StacksFrontier.AlgebraicGeometry.InternalHomCoherent.RestrictOpenSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0EIV and Stacks 0EKU at a member `V` of `𝒱`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the
open subschemes of `U` containing `U ∩ V(I)`, ordered by reverse inclusion.

* `Stacks.Algebraization.nbhdHomComparisonOn_bijective` — for `V ∈ 𝒱` and coherent `𝒪_V`-modules
  `G`, `F`, the map `colim_{V' ≥ V} Hom_{V'}(G|_{V'}, F|_{V'}) ⟶ Hom_{Coh(V, I𝒪_V)}(G^∧, F^∧)` is
  bijective under the hypotheses of Stacks 0EIV.
* `Stacks.Algebraization.completionFullyFaithful_finiteLocallyFree_on` — **Stacks 0EKU**.

The proof is the source's: extend `G` and `F` coherently to `U`
(`AlgebraicGeometry.exists_isCoherent_extension_associatedPoints_subset`); condition (2) for `F`
on `V` gives condition (2) for the extension
(`associatedPointsClosureDimensionBound_of_restrictIso`, the condition being vacuous off `V`);
apply Stacks 0EIV at `U`
(`Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_dimensionBound`) and
transport back to `V` (`Stacks.Algebraization.nbhdHomComparisonOn_bijective_of_sectionsEquiv`).

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0EKU](https://stacks.math.columbia.edu/tag/0EKU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology Stacks.Algebraization.NeighbourhoodHoms

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I a : Ideal A}

/-- **The reduction of Stacks 0EIV from a member `V` of `𝒱` to `U`.** If the comparison map of
Stacks 0EIV at `U` is bijective for every pair of coherent modules on `U` whose target satisfies
condition (2), then the comparison map at every member `V` of `𝒱` is bijective for every pair of
coherent modules on `V` whose target satisfies condition (2). -/
theorem nbhdHomComparisonOn_bijective_of_forall
    (hU : ∀ G' F' : AlgebraicGeometry.SheafOfModules.CoherentModules
        (complementZeroLocus A a : Scheme).ringCatSheaf,
      AssociatedPointsClosureDimensionBound A I a F'.obj →
        Function.Bijective (nbhdHomComparison A I a G' F'))
    (V : OpensNearVanishing A I a)
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.openSet.toScheme.ringCatSheaf)
    (hdim : AssociatedPointsClosureDimensionBoundOn V F.obj) :
    Function.Bijective (nbhdHomComparisonOn V G F) := by
  have : IsNoetherian (complementZeroLocus A a : Scheme) := ⟨⟩
  obtain ⟨F', ⟨eF₀⟩, -, hF'⟩ := exists_extension_associatedPointsClosureDimensionBound V F.obj hdim
  obtain ⟨G₀, hG₀, ⟨eG₀⟩, -⟩ := exists_isCoherent_extension_associatedPoints_subset V.openSet G.obj
  let G' : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf := ⟨G₀, hG₀⟩
  let eG : restrictCoherentModules V.openSet.ι G' ≅ G := ObjectProperty.isoMk _ eG₀
  let eF : restrictCoherentModules V.openSet.ι F' ≅ F := ObjectProperty.isoMk _ eF₀
  refine nbhdHomComparisonOn_bijective_of_sectionsEquiv V G' F' G F eG eF
    (fun W => (internalHomRestrictOpenSectionsEquiv G₀ F'.obj V.openSet W.right.openSet
      W.hom.down).trans (transportSectionEquiv ((ObjectProperty.ι _).mapIso eG.symm)
        ((ObjectProperty.ι _).mapIso eF) (Under.preimageOpen V W))) ?_ ?_ (hU G' F' hF')
  · intro W₁ W₂ g s
    rfl
  · intro W s T hT y
    rfl

/-- **Stacks 0EIV.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, put `U = Spec(A) ∖ V(𝔞)` and
let `𝒱` be the set of open subschemes of `U` containing `U ∩ V(I)`, ordered by reverse inclusion.
Let `G`, `F` be coherent `𝒪_V`-modules for some `V ∈ 𝒱`. The map
`colim_{V' ≥ V} Hom_{V'}(G|_{V'}, F|_{V'}) ⟶ Hom_{Coh(V, I𝒪_V)}(G^∧, F^∧)` is bijective if

1. `A` is `I`-adically complete and has a dualizing complex, and
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`.

The target is the category of coherent adic systems on `V` along `I 𝒪_V`; restriction from `U`
to `V` identifies the morphisms of completions there with those in `Coh(U, I𝒪_U)`
(`Stacks.Algebraization.bijective_restrictCompletionHom`), the terms being supported in
`U ∩ V(I) ⊆ V`. -/
@[stacks 0EIV]
theorem nbhdHomComparisonOn_bijective (hIa : I ≤ a) (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (V : OpensNearVanishing A I a)
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.openSet.toScheme.ringCatSheaf)
    (hdim : AssociatedPointsClosureDimensionBoundOn V F.obj) :
    Function.Bijective (nbhdHomComparisonOn V G F) :=
  nbhdHomComparisonOn_bijective_of_forall
    (fun G' F' hF' => nbhdHomComparison_bijective_of_dimensionBound A I a hIa hcomplete
      hdualizing G' F' hF') V G F hdim

/-- **Stacks 0EKU.** Let `I ⊆ 𝔞 ⊆ A` be ideals of a Noetherian ring `A`, put
`U = Spec(A) ∖ V(𝔞)` and let `𝒱` be the set of open subschemes of `U` containing `U ∩ V(I)`,
ordered by reverse inclusion. Assume

1. `A` is `I`-adically complete and has a dualizing complex, and
2. for every associated prime `𝔭` of `A` with `I ⊄ 𝔭` and `V(𝔭) ∩ V(I) ⊄ V(𝔞)`, and every
   `𝔮 ∈ V(𝔭) ∩ V(𝔞)`, we have `dim((A/𝔭)_𝔮) > cd(A, I) + 1`.

Then the completion functor `colim_𝒱 Coh(𝒪_V) ⟶ Coh(U, I𝒪_U)` is fully faithful on the full
subcategory of finite locally free objects: for every `V ∈ 𝒱` and all finite locally free coherent
`𝒪_V`-modules `G`, `F`, the map
`colim_{V' ≥ V} Hom_{V'}(G|_{V'}, F|_{V'}) ⟶ Hom_{Coh(V, I𝒪_V)}(G^∧, F^∧)` is bijective.

Two objects of the colimit category given on members `V₁`, `V₂` of `𝒱` are compared on
`V₁ ∩ V₂ ∈ 𝒱`, so "for every `V`" is full faithfulness. The target `Coh(V, I𝒪_V)` is
`Coh(U, I𝒪_U)` on morphisms by `Stacks.Algebraization.bijective_restrictCompletionHom`.
The source's condition (2) on the associated primes of `A` gives condition (2) of Stacks 0EIV for
a finite locally free `F`, whose associated points are associated points of `V`
(`Stacks.Algebraization.associatedPointsClosureDimensionBoundOn_of_isFiniteLocallyFree`); the
finite local freeness of `G` is not needed. -/
@[stacks 0EKU]
theorem completionFullyFaithful_finiteLocallyFree_on (hIa : I ≤ a)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdim : ∀ p : PrimeSpectrum A, IsAssociatedPrimeStacks A A p.asIdeal →
      ¬ I ≤ p.asIdeal →
      (∃ y : PrimeSpectrum A, p.asIdeal ≤ y.asIdeal ∧ I ≤ y.asIdeal ∧ ¬ a ≤ y.asIdeal) →
      ∀ z : PrimeSpectrum A, p.asIdeal ≤ z.asIdeal → a ≤ z.asIdeal →
        ((cohomologicalDimension A I I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
          krullDimToEInt (closureLocalDimension A p z))
    (V : OpensNearVanishing A I a)
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules V.openSet.toScheme.ringCatSheaf)
    (_hG : Scheme.Modules.IsFiniteLocallyFree G.obj)
    (hF : Scheme.Modules.IsFiniteLocallyFree F.obj) :
    Function.Bijective (nbhdHomComparisonOn V G F) :=
  nbhdHomComparisonOn_bijective hIa hcomplete hdualizing V G F
    (associatedPointsClosureDimensionBoundOn_of_isFiniteLocallyFree V F.obj hF hdim)

end Stacks.Algebraization

end
