module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.FiniteTypeCentre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BlowUpSquare.LongExactSequence

/-!
# The Mayer–Vietoris long exact sequence of a blowup square

Let `X` be a scheme and `Z ⊆ X` the closed subscheme cut out by a quasi-coherent ideal `I` of
finite type, with blowup square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
For `K ∈ D⁺(X_étale)` with torsion cohomology sheaves there is a long exact sequence
`H^p(X, K) ⟶ H^p(X', K|_{X'}) ⊕ H^p(Z, K|_Z) ⟶ H^p(E, K|_E) ⟶ H^{p+1}(X, K)`.
This is Stacks Tag 0EW3.

## Main results

* `AlgebraicGeometry.exists_longExactSequence_blowUp`: the long exact sequence (Stacks 0EW3).

## Implementation notes

Following the first proof of the source, this is
`Stacks.EtaleCohomology.exists_longExactSequence_of_isPullback_of_cohomologyCommutesWithBaseChange`
(the long exact sequence of the Mayer–Vietoris triangle of Stacks 0EW5, read through
`H^p(X, Rf_* N) = H^p(Y, N)`), applied to the blowup square: it is cartesian
(`AlgebraicGeometry.isPullback_exceptionalDivisor`), the blowup morphism is an isomorphism over
`X \ Z` (Stacks 02OS), and since `I` is of finite type the blowup morphism is proper, so
cohomology commutes with base change along it by the proper base change theorem
(`AlgebraicGeometry.cohomologyCommutesWithBaseChange_blowUpToBase_of_fg`, Stacks 0A3U).

## References

* [Stacks Project, Tag 0EW3](https://stacks.math.columbia.edu/tag/0EW3)
* [Stacks Project, Tag 0EW5](https://stacks.math.columbia.edu/tag/0EW5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0EW3.** Let `X` be a scheme, `K` an object of `D⁺(X_étale)` (a complex
of abelian sheaves on the small étale site, bounded below: `K.IsGE n`) with torsion cohomology
sheaves, and `Z ⊆ X` the closed subscheme cut out by a quasi-coherent ideal `I` of finite type
(finitely generated on every affine open). In the blowup square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
(`X'` the blowup of `X` in `I`, `E = b⁻¹(Z)` the exceptional divisor) there is a long exact
sequence
`H^p(X, K) ⟶ H^p(X', K|_{X'}) × H^p(Z, K|_Z) ⟶ H^p(E, K|_E) ⟶ H^{p+1}(X, K) ⟶ ⋯`
whose first map is `x ↦ (x|_{X'}, x|_Z)`, whose second map is `(x', z) ↦ x'|_E - z|_E` (the two
restrictions read in `H^p(E, K|_E)`, `K|_E = (j ≫ b)⁻¹ K`, through
`j⁻¹ b⁻¹ K ≅ K|_E ≅ π⁻¹ i⁻¹ K`), and whose third map is a connecting map `δ`, exact at all three
places for every `p`. Here `H^p(Y, M) = Hom(ℤ_Y[-p], M)` in `D(Y_étale)`
(`Stacks.EtaleCohomology.etaleDerivedCohomology`) and `K|_Y` is the derived inverse image. -/
@[stacks 0EW3]
public theorem exists_longExactSequence_blowUp {X : Scheme.{u}} (I : X.IdealSheafData)
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) (n : ℤ)
    (hK : K.IsGE n)
    (hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1} X.smallEtaleTopology K) :
    ∃ δ : ∀ p : ℤ, etaleDerivedCohomology.{u, 0} (exceptionalDivisor I) p
        ((etaleAbelianDerivedInverseImage.{u, 0}
          ((exceptionalIdeal I).subschemeι ≫ blowUpToBase I)).obj K) →+
      etaleDerivedCohomology.{u, 0} X (p + 1) K,
    ∀ p : ℤ,
      Function.Exact
        (fun x : etaleDerivedCohomology.{u, 0} X p K ↦
          (etaleDerivedCohomologyRestriction.{u, 0} (blowUpToBase I) p K x,
            etaleDerivedCohomologyRestriction.{u, 0} I.subschemeι p K x))
        (fun y : etaleDerivedCohomology.{u, 0} (blowUp I) p
              ((etaleAbelianDerivedInverseImage.{u, 0} (blowUpToBase I)).obj K) ×
            etaleDerivedCohomology.{u, 0} I.subscheme p
              ((etaleAbelianDerivedInverseImage.{u, 0} I.subschemeι).obj K) ↦
          etaleDerivedCohomologyRestriction.{u, 0} (exceptionalIdeal I).subschemeι p _ y.1 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalIdeal I).subschemeι
                (blowUpToBase I) _ rfl).inv.app K -
            etaleDerivedCohomologyRestriction.{u, 0} (exceptionalDivisorToCenter I) p _ y.2 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalDivisorToCenter I)
                I.subschemeι _ (isPullback_exceptionalDivisor I).w).inv.app K) ∧
      Function.Exact
        (fun y : etaleDerivedCohomology.{u, 0} (blowUp I) p
              ((etaleAbelianDerivedInverseImage.{u, 0} (blowUpToBase I)).obj K) ×
            etaleDerivedCohomology.{u, 0} I.subscheme p
              ((etaleAbelianDerivedInverseImage.{u, 0} I.subschemeι).obj K) ↦
          etaleDerivedCohomologyRestriction.{u, 0} (exceptionalIdeal I).subschemeι p _ y.1 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalIdeal I).subschemeι
                (blowUpToBase I) _ rfl).inv.app K -
            etaleDerivedCohomologyRestriction.{u, 0} (exceptionalDivisorToCenter I) p _ y.2 ≫
              (etaleAbelianDerivedInverseImageCompIso'.{u, 0} (exceptionalDivisorToCenter I)
                I.subschemeι _ (isPullback_exceptionalDivisor I).w).inv.app K)
        (δ p) ∧
      Function.Exact (δ p)
        (fun x : etaleDerivedCohomology.{u, 0} X (p + 1) K ↦
          (etaleDerivedCohomologyRestriction.{u, 0} (blowUpToBase I) (p + 1) K x,
            etaleDerivedCohomologyRestriction.{u, 0} I.subschemeι (p + 1) K x)) :=
  exists_longExactSequence_of_isPullback_of_cohomologyCommutesWithBaseChange.{u, 0}
    I.subschemeι (blowUpToBase I) (exceptionalIdeal I).subschemeι (exceptionalDivisorToCenter I)
    _ (isPullback_exceptionalDivisor I).w rfl (Scheme.Opens.ι I.support.compl)
    (range_subschemeι_compl_eq I) (isPullback_exceptionalDivisor I)
    _ _ (isPullback_blowUpToBase_restrict_compl_support I)
    (cohomologyCommutesWithBaseChange_blowUpToBase_of_fg I hI) K n hK hT

end AlgebraicGeometry

end
