module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAlgebraizationII
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalSectionsAssociatedPointInduction

/-!
# Algebraization of formal sections: the global sections of a coherent module, Stacks 0EIG

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. Stacks 0EIG says that, under

1. `A` is `I`-adically complete and has a dualizing complex,
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`, and
3. `depth(F_x) ≥ 2` for every `x ∈ U` whose closure meets `V(I)` only inside `V(𝔞)`,

the arrow `H⁰(U, F) ⟶ lim H⁰(U, F / Iⁿ F)` is an isomorphism. This file proves it.

## Main results

* `Stacks.Algebraization.FormalSectionsII.isIso_globalToFormalSections_of_depthTwoOffFormalLocus`
  — **Stacks 0EIG**.

## The proof

The source's proof has two steps, and both are library results.

* By Stacks 0EG2,
  `Stacks.Algebraization.isIso_comparisonMap_of_associatedPointsClosureDimensionBound`,
  conditions (1) and (2) make the comparison map `colim_V H⁰(V, F) ⟶ lim H⁰(U, F / Iⁿ F)` an
  isomorphism, the colimit running over the opens `V ⊆ U` containing `U ∩ V(I)`.
* A point of `U` outside such a `V` has its closure meeting `V(I)` only inside `V(𝔞)`, so by
  condition (3) and Hartogs extension for coherent modules, Stacks 0E9I, every restriction
  `H⁰(U, F) ⟶ H⁰(V, F)` is an isomorphism and the colimit collapses onto its value at `U`
  (`Stacks.Algebraization.FormalSectionsII.isIso_sectionsNearVanishing_map_fromTop` and
  `Stacks.Algebraization.FormalSectionsII.isIso_colimit_ι_topNearVanishing`).

The arrow `Stacks.Algebraization.FormalSectionsII.globalToFormalSections` is the composite of the
colimit inclusion of `U` with the comparison map; its `n`-th component is reduction modulo `Iⁿ`
on `U` (`Stacks.Algebraization.FormalSectionsII.globalToFormalSections_proj`).

## References

* [Stacks Project, Tag 0EIG](https://stacks.math.columbia.edu/tag/0EIG)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization.FormalSectionsII

open Stacks.LocalCohomology

/-- **Stacks 0EIG.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and let `F` be a coherent
module on `U = Spec(A) ∖ V(𝔞)`. Assume

1. `A` is `I`-adically complete and has a dualizing complex,
2. whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`, and
3. `depth(F_x) ≥ 2` for every `x ∈ U` whose closure meets `V(I)` only inside `V(𝔞)`.

Then the arrow `H⁰(U, F) ⟶ lim H⁰(U, F / Iⁿ F)`, whose `n`-th component is reduction
modulo `Iⁿ`, is an isomorphism.

Conditions (1) and (2) make the comparison map of Stacks 0EG2 an isomorphism; condition (3) and
Stacks 0E9I identify `H⁰(V, F)` with `H⁰(U, F)` for every open `V ⊆ U` containing `U ∩ V(I)`. -/
@[stacks 0EIG]
theorem isIso_globalToFormalSections_of_depthTwoOffFormalLocus
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hIa : I ≤ a) (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (hdim : AssociatedPointsClosureDimensionBound A I a F)
    (hdepth : DepthTwoOffFormalLocus A I a F) :
    IsIso (globalToFormalSections A I a F) := by
  have hcmp : IsIso (comparisonMap A I a F) :=
    isIso_comparisonMap_of_associatedPointsClosureDimensionBound I a hIa hcomplete hdualizing F
      hdim
  have htop : IsIso (colimit.ι (sectionsNearVanishing A I a F) (topNearVanishing A I a)) :=
    isIso_colimit_ι_topNearVanishing A I a F
      (isIso_sectionsNearVanishing_map_fromTop A I a F hdepth)
  rw [globalToFormalSections]
  exact IsIso.comp_isIso' htop hcmp

end Stacks.Algebraization.FormalSectionsII

end
