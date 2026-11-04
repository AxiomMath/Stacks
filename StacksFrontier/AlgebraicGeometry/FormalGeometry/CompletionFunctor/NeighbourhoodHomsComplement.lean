module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.InternalHomAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AssociatedPointInductionSerreOne
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletedComplementDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHoms
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom

/-!
# Morphisms of completions come from morphisms near the formal locus, at `V = U`

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and `U = Spec(A) ∖ V(𝔞)`. For coherent modules
`𝒢`, `ℱ` on `U`, `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison` is the canonical
map from the germs of morphisms `𝒢|_V ⟶ ℱ|_V` on open neighbourhoods `V` of `U ∩ V(I)` to the
morphisms `𝒢^∧ ⟶ ℱ^∧` of the completions. This file proves it bijective under the hypotheses of
Stacks 0EIV, with no carried input; the two inputs the argument needs beyond those hypotheses
are supplied as follows:

* `Ass(SheafHom(𝒢, ℱ)) ⊆ Ass(ℱ)` is `AlgebraicGeometry.associatedPoints_internalHomOf_subset`,
  from Stacks 0EBC;
* Stacks 0EG2 for the internal hom is
  `Stacks.Algebraization.isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement`,
  whose induction runs over the middle clause of Stacks 0H48 and the splitting of Stacks 0DX3,
  both proved, and over Stacks 0EIF under condition (3)(a).

The shape of Stacks 0BLX on which Stacks 0EIF rests,
`Stacks.Algebraization.CompletedComplementIsFormalSections`, is the theorem
`Stacks.Algebraization.completedComplementIsFormalSections`, so nothing is carried.

## Main results

* `AlgebraicGeometry.associatedPoints_internalHomCoherent_subset` — the internal hom of two
  coherent modules has its associated points among those of the target.
* `Stacks.Algebraization.isIso_comparisonMap_of_bootstrapHypotheses` — Stacks 0EG2, with no
  carried input.
* `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_completedComplement` —
  the bijectivity at `V = U`, for any proof of `CompletedComplementIsFormalSections`.
* `Stacks.Algebraization.NeighbourhoodHoms.nbhdHomComparison_bijective_of_dimensionBound` — the
  bijectivity at `V = U`, with no carried input.

## References

* [Stacks Project, Tag 0EIV](https://stacks.math.columbia.edu/tag/0EIV)
* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0EBC](https://stacks.math.columbia.edu/tag/0EBC)
* [Stacks Project, Tag 0882](https://stacks.math.columbia.edu/tag/0882)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The internal hom of two coherent modules has its associated points among those of the
target**, for the coherent internal hom `Stacks.Algebraization.internalHomCoherent` used by the
completion functor. -/
public theorem associatedPoints_internalHomCoherent_subset {X : Scheme.{u}}
    [IsLocallyNoetherian X]
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) :
    Stacks.Divisors.associatedPoints (Stacks.Algebraization.internalHomCoherent X G F).obj ⊆
      Stacks.Divisors.associatedPoints F.obj := by
  have hG : _root_.SheafOfModules.IsCoherent G.obj := G.property
  have hF : _root_.SheafOfModules.IsCoherent F.obj := F.property
  have hH : _root_.SheafOfModules.IsCoherent
      (internalHomOf (Stacks.SheafOfModules.internalHomSheafHom X.sheaf G.obj F.obj)) :=
    (Stacks.Algebraization.internalHomCoherent X G F).property
  exact associatedPoints_internalHomOf_subset G.obj F.obj
    (Stacks.SheafOfModules.internalHomSheafHom X.sheaf G.obj F.obj)

end AlgebraicGeometry

namespace Stacks.Algebraization.NeighbourhoodHoms

open Stacks.Algebraization Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I a : Ideal A)

/-- **Stacks 0EIV at `V = U`, granted
`Stacks.Algebraization.CompletedComplementIsFormalSections`.**
Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, `U = Spec(A) ∖ V(𝔞)` and `𝒢`, `ℱ` coherent
modules on `U`. If `A` is `I`-adically complete and has a dualizing complex, and the associated
points of `ℱ` satisfy the dimension bound of condition (2), then the canonical map
`nbhdHomComparison` from the germs of morphisms `𝒢|_V ⟶ ℱ|_V` on open neighbourhoods `V` of
`U ∩ V(I)` to the morphisms `𝒢^∧ ⟶ ℱ^∧` of the completions is bijective.

The internal hom `ℋ = SheafHom(𝒢, ℱ)` has its associated points among those of `ℱ`
(`AlgebraicGeometry.associatedPoints_internalHomCoherent_subset`), so it satisfies condition (2)
too, and Stacks 0EG2 makes its comparison map an isomorphism; the remaining maps of
`nbhdHomComparison` are isomorphisms (the shift of the tower, global sections of a limit, and
Stacks 0882). -/
public theorem nbhdHomComparison_bijective_of_completedComplement
    (h0BLX : CompletedComplementIsFormalSections.{u}) (hIa : I ≤ a)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf)
    (hdim : AssociatedPointsClosureDimensionBound A I a F.obj) :
    Function.Bijective (nbhdHomComparison A I a G F) := by
  have _ : IsLocallyNoetherian (complementZeroLocus A a : Scheme) :=
    AlgebraicGeometry.isLocallyNoetherian_of_isOpenImmersion (complementZeroLocus A a).ι
  have hcoh : (internalHomNear A a G F).obj.IsCoherent := (internalHomNear A a G F).property
  have hboot : BootstrapHypotheses A I a (internalHomNear A a G F).obj :=
    ⟨hIa, hcomplete, hdualizing, fun x hx =>
      hdim x (associatedPoints_internalHomCoherent_subset G F hx)⟩
  have hiso : IsIso (comparisonMap A I a (internalHomNear A a G F).obj) :=
    isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement A I a h0BLX
      (internalHomNear A a G F).obj hboot
  have b1 : Function.Bijective
      (ConcreteCategory.hom (comparisonMap A I a (internalHomNear A a G F).obj)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 hiso
  have b2 : Function.Bijective (ConcreteCategory.hom (sectionsAbLimitIso
      (adicQuotientSystem (idealSheafNearVanishing A I a)
        (internalHomNear A a G F).obj)).inv) :=
    ConcreteCategory.bijective_of_isIso _
  have b3 : Function.Bijective (ConcreteCategory.hom
      ((sectionsAb (complementZeroLocus A a : Scheme)).map
        (adicCompletionLimitIso (idealSheafNearVanishing A I a)
          (internalHomNear A a G F)).hom)) :=
    ConcreteCategory.bijective_of_isIso _
  have b4 : Function.Bijective (ConcreteCategory.hom
      (globalSectionsLimitIso (idealSheafNearVanishing A I a)
        (internalHomNear A a G F)).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (Iso.isIso_hom _)
  exact (completionInternalHomEquiv (complementZeroLocus A a : Scheme)
    (idealSheafNearVanishing A I a) G F).bijective.comp (b4.comp (b3.comp (b2.comp b1)))

/-- **Stacks 0EIV at `V = U`.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`,
`U = Spec(A) ∖ V(𝔞)` and `𝒢`, `ℱ` coherent modules on `U`. Assume

1. `A` is `I`-adically complete and has a dualizing complex, and
2. whenever `x` is an associated point of `ℱ` outside `V(I)` whose closure meets `V(I)` outside
   `V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1`.

Then the canonical map `nbhdHomComparison` from the germs of morphisms `𝒢|_V ⟶ ℱ|_V` on open
neighbourhoods `V` of `U ∩ V(I)` to the morphisms `𝒢^∧ ⟶ ℱ^∧` of the completions is bijective.

This is `nbhdHomComparison_bijective_of_completedComplement` with Stacks 0BLX supplied by
`Stacks.Algebraization.completedComplementIsFormalSections`. -/
public theorem nbhdHomComparison_bijective_of_dimensionBound (hIa : I ≤ a)
    (hcomplete : IsAdicComplete I A)
    (hdualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K)
    (G F : AlgebraicGeometry.SheafOfModules.CoherentModules
      (complementZeroLocus A a : Scheme).ringCatSheaf)
    (hdim : AssociatedPointsClosureDimensionBound A I a F.obj) :
    Function.Bijective (nbhdHomComparison A I a G F) :=
  nbhdHomComparison_bijective_of_completedComplement A I a completedComplementIsFormalSections
    hIa hcomplete hdualizing G F hdim

end Stacks.Algebraization.NeighbourhoodHoms

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-- **Stacks 0EG2.** Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A` and `F` a coherent module on
`U = Spec(A) ∖ V(𝔞)`. Assume that `A` is `I`-adically complete and has a dualizing complex, and
that whenever `x` is an associated point of `F` outside `V(I)` whose closure meets `V(I)` outside
`V(𝔞)`, every `z ∈ closure {x} ∩ V(𝔞)` has `dim(𝒪_{closure {x}, z}) > cd(A, I) + 1` (these are
the fields of `Stacks.Algebraization.BootstrapHypotheses`, together with `I ⊆ 𝔞`). Then the
comparison map `Stacks.Algebraization.comparisonMap A I 𝔞 F`, from the sections of `F` on
arbitrarily small open neighbourhoods of `U ∩ V(I)` to the compatible families of sections of
`F / Iⁿ F` on `U`, is an isomorphism. -/
public theorem isIso_comparisonMap_of_bootstrapHypotheses (A : Type u) [CommRing A]
    [IsNoetherianRing A] (I a : Ideal A)
    (F : (complementZeroLocus A a : Scheme).Modules) [F.IsCoherent]
    (hF : BootstrapHypotheses A I a F) :
    IsIso (comparisonMap A I a F) :=
  isIso_comparisonMap_of_bootstrapHypotheses_of_completedComplement A I a
    completedComplementIsFormalSections F hF

end Stacks.Algebraization

end
