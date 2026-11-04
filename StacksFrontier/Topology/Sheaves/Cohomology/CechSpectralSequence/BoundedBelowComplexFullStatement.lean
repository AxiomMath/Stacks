module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.BoundedBelowComplexSpectralSequence
import StacksCore.Tactic.StacksAttribute

/-!
# Both halves of Tag 08BN at once

[Stacks, Tag 08BN] (Lemma 20.25.1) takes a ringed space `(X, O_X)`, an open covering
`U : X = ⋃_{i ∈ I} U_i` and a bounded below complex `F^•` of `O_X`-modules, and makes two
assertions about them together:

1. there is a canonical map `Tot(Č^•(U, F^•)) ⟶ RΓ(X, F^•)`, functorial in `F^•` and compatible
   with the two maps that Section 20.25 displays before the lemma — the augmentation
   `Γ(X, F^•) ⟶ Tot(Č^•(U, F^•))` of equation (20.25.0.1), which is [Stacks, Tag 07M9], and the
   refinement map `T_t : Tot(Č^•(U, F^•)) ⟶ Tot(Č^•(V, F^•))` of equation (20.25.0.2), which is
   [Stacks, Tag 08BM];
2. there is a spectral sequence with `E_2^{p,q} = H^p(Tot(Č^•(U, H^q(F^•))))` abutting to
   `H^{p+q}(X, F^•)`, where `H^q(F^•)` is the complex `n ↦ R^q i(F^n)` of cohomology presheaves
   of [Stacks, Tag 01ER].

The library states each half on its own, each for a wider class of inputs than the lemma needs:
`Stacks.Cech.cechToDerivedGlobalSections` gives the comparison simultaneously for every open
covering of `X`, and `Stacks.Cech.exists_cechSpectralSequence` gives the spectral sequence for
every covering and every bounded below complex. This file puts the two together into the single
conjunction the lemma asserts, taking in exactly the lemma's three inputs and nothing else.

## Main results

* `Stacks.Cech.exists_cechToDerivedComparison_and_cechSpectralSequence`: the conjunction of both
  assertions of [Stacks, Tag 08BN], over the ringed space, the open covering and the bounded
  below complex of the lemma.

## Implementation notes

The comparison of assertion 1 is the canonical one, `Stacks.Cech.cechToDerivedGlobalSections`,
named in the statement. Reading the assertion off it: the map itself is the field `map`, whose type
`cechDerivedFunctor X R U ⟶ derivedGlobalSectionsFunctor X R` is a morphism of functors on
bounded below complexes, so functoriality in `F^•` is carried by the type rather than by a
further equation; compatibility with (20.25.0.1) is spelled out at the lemma's own covering and
complex as the first component of the conjunction; and compatibility with (20.25.0.2) is spelled
out as the second, quantified over the refinements `t` that equation allows.

Both coordinates of the second page range over `ℤ`, which is the range the lemma states its
second page over and the range `(E.page 2).X` is indexed by.  In negative cohomological degree
both sides vanish, but the clause is only fully stated with that range included.

## References

* [The Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
* [The Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [The Stacks Project, Tag 08BM](https://stacks.math.columbia.edu/tag/08BM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace

namespace Stacks.Cech

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Tag 08BN.** Let `(X, O_X)` be a ringed space, let `U : X = ⋃_{i ∈ I} U_i` be an open
covering and let `F^•` be a bounded below complex of `O_X`-modules. Then

1. there is a canonical map `Tot(Č^•(U, F^•)) ⟶ RΓ(X, F^•)`, functorial in `F^•` -- it is a
   morphism of functors on bounded below complexes -- and compatible both with the augmentation
   of equation (20.25.0.1) ([Stacks, Tag 07M9]) and with the refinement map of equation
   (20.25.0.2) ([Stacks, Tag 08BM]); and
2. there is a cohomological spectral sequence with
   `E_2^{p,q} = H^p(Tot(Č^•(U, H^q(F^•))))` abutting to `H^{p+q}(X, F^•)`, where `H^q(F^•)` is
   the complex `n ↦ R^q i(F^n)` of cohomology presheaves of [Stacks, Tag 01ER].

Both halves are read off the library's wider statements: the comparison from the system of
comparisons for all coverings at once, `cechToDerivedGlobalSections`, and the spectral sequence
from `exists_cechSpectralSequence`. -/
@[stacks 08BN "the whole lemma: the canonical map `Tot(Č(U, F)) ⟶ RΓ(X, F)`, functorial in `F` \
and compatible with the augmentation of (20.25.0.1) = Tag 07M9 and the refinement map of \
(20.25.0.2) = Tag 08BM, together with the spectral sequence `E_2^{p,q} = H^p(Tot(Č(U, H^q(F))))` \
abutting to `H^{p+q}(X, F)` -- for a ringed space, an open covering of `X` and a bounded below \
complex of `O_X`-modules, which are the lemma's three inputs and all of them"]
theorem exists_cechToDerivedComparison_and_cechSpectralSequence
    {I : Type u} (U : I → Opens X) (hU : ⊤ = iSup U)
    (K : CochainComplex.Plus (SheafOfModules.{u} R)) :
    ((globalSectionsToCechDerived X R U).app K ≫
          ((cechToDerivedGlobalSections X R).map U hU).app K =
          globalSectionsToDerived X R K ∧
        ∀ (J : Type u) (V : J → Opens X) (hV : ⊤ = iSup V)
            (t : FormalCoproduct.mk J V ⟶ FormalCoproduct.mk I U),
          cechRefinementDerived X R U V t ≫ (cechToDerivedGlobalSections X R).map V hV =
            (cechToDerivedGlobalSections X R).map U hU) ∧
      ∃ E : CohomologicalSpectralSequence AddCommGrpCat.{u} 2,
        (∀ p q : ℤ,
          Nonempty ((E.page 2).X (p, q) ≅
            ((cechTotalComplexFunctor U).obj
              ((((underlyingPresheafFunctor X R).rightDerivedPlus q).mapHomologicalComplex
                (up ℤ)).obj K.1)).homology p)) ∧
          SpectralSequence.AbutsTo E (fun n =>
            (DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
              ((derivedGlobalSectionsFunctor X R).obj K)) :=
  ⟨⟨(cechToDerivedGlobalSections X R).globalSections U hU K,
      fun _ V hV t => (cechToDerivedGlobalSections X R).refinement U hU V hV t⟩,
    exists_cechSpectralSequence X R U hU K⟩

end Stacks.Cech

end
