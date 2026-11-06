module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.FppfHypercoveringDerivedDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDerivedPlusGlobalSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The étale cohomology spectral sequence of an fppf hypercovering

Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial algebraic space over `S`
and `a : U → X` an augmentation which is an fppf hypercovering of `X` (Section 0DH4). Let `𝓕` be
an abelian sheaf on `X_étale` and `𝓕_p` its pullback to `U_{p, étale}`. Then there is a canonical
spectral sequence

```
E_1^{p,q} = H^q_ét(U_p, 𝓕_p) ⇒ H^{p+q}_ét(X, 𝓕)
```

(Stacks 0DHA). It is the spectral sequence of Stacks 09WJ of `a⁻¹𝓕` on the small étale site
`U_étale` (`AlgebraicGeometry.Space.etaleSpectralSequence`), which converges to the cohomology of
`a⁻¹𝓕` on `U_étale`; and `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` for `K ∈ D⁺(X_étale)`, the content of
Stacks 0DH8, identifies the latter with `H^{p+q}_ét(X, 𝓕)`.

## Main results

* `AlgebraicGeometry.Space.IsFppfHypercovering.derivedPlusGlobalSectionsIso`:
  `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)`, naturally in `K ∈ D⁺(X_étale)`, for an fppf
  hypercovering; the isomorphism is `RΓ(X_étale, -)` of the unit `K → Ra_*a⁻¹K` followed by the
  factorization `RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` of Stacks 08J6.
* `AlgebraicGeometry.Space.IsFppfHypercovering.etaleSpectralSequence_pageOne_abutsTo`:
  **Stacks 0DHA**.

## Implementation notes

`X_étale` and `U_{p, étale}` are the spaces-étale sites, which Section 0DE7 identifies with the
small étale sites, and étale cohomology is `CategoryTheory.Sheaf.functorH`. The descent
isomorphism is stated in an arbitrary model of the bounded below derived categories; the statement
of Stacks 0DHA mentions no derived category, and its proof uses any model.

## References

* [Stacks Project, Tag 0DHA](https://stacks.math.columbia.edu/tag/0DHA)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 0DH7](https://stacks.math.columbia.edu/tag/0DH7)
* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Space

open SimplicialSiteSituation.Augmentation in
attribute [local instance] additive_totalInverseImageAb_etaleAugmentation
  preservesFiniteLimits_totalInverseImageAb_etaleAugmentation
  preservesFiniteColimits_totalInverseImageAb_etaleAugmentation
  additive_abelianTotalPushforward_etaleAugmentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

set_option synthInstance.maxHeartbeats 400000 in
/-- **`RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` for an fppf hypercovering** (the content of
Stacks 0DH8), naturally in `K ∈ D⁺(X_étale)`, in any model of the derived categories. Here
`a : Sh(U_étale) → Sh(X_étale)` is the morphism of topoi of Section 0DE7. The isomorphism is the
comparison
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedPlusGlobalSectionsComparison`:
`RΓ(X_étale, -)` of the unit `K → Ra_*a⁻¹K`, which is invertible
(`IsFppfHypercovering.isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app`), followed by
the factorization `RΓ(U_étale, -) = RΓ(X_étale, -) ∘ Ra_*` of Stacks 08J6. -/
def IsFppfHypercovering.derivedPlusGlobalSectionsIso (hA : IsFppfHypercovering A)
    [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (etaleSituation A).totalTopology AddCommGrpCat.{u + 1})]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    (Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ≅
      (SimplicialSiteSituation.Augmentation.totalInverseImageAb (etaleSituation A) _ _
          (etaleAugmentation A)).rightDerivedFunctorPlus ⋙
        (Sheaf.Γ (etaleSituation A).totalTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus :=
  have : ∀ K, IsIso ((SimplicialSiteSituation.Augmentation.derivedPlusGlobalSectionsComparison
      (etaleSituation A) _ _ (etaleAugmentation A)).app K) := fun K ↦
    have := hA.isIso_abelianTotalAdjunction_rightDerivedFunctorPlus_unit_app K
    SimplicialSiteSituation.Augmentation.isIso_derivedPlusGlobalSectionsComparison_app _ _ _ _ K
  have := NatIso.isIso_of_isIso_app
    (SimplicialSiteSituation.Augmentation.derivedPlusGlobalSectionsComparison
      (etaleSituation A) _ _ (etaleAugmentation A))
  asIso (SimplicialSiteSituation.Augmentation.derivedPlusGlobalSectionsComparison
    (etaleSituation A) _ _ (etaleAugmentation A))

set_option synthInstance.maxHeartbeats 400000 in
/-- The isomorphism `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` is the comparison
`derivedPlusGlobalSectionsComparison`. -/
theorem IsFppfHypercovering.derivedPlusGlobalSectionsIso_hom (hA : IsFppfHypercovering A)
    [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory (Sheaf (etaleSituation A).totalTopology AddCommGrpCat.{u + 1})]
    [HasDerivedCategory AddCommGrpCat.{u + 1}] :
    hA.derivedPlusGlobalSectionsIso.hom =
      SimplicialSiteSituation.Augmentation.derivedPlusGlobalSectionsComparison
        (etaleSituation A) _ _ (etaleAugmentation A) :=
  rfl

/-- **Stacks Project, Tag 0DHA.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a
simplicial algebraic space over `S` and `a : U → X` an augmentation. Let `𝓕` be an abelian sheaf
on `X_étale` and `𝓕_p` its pullback to `U_{p, étale}`. If `U` is an fppf hypercovering of `X`,
then the canonical spectral sequence `etaleSpectralSequence A` at `𝓕` has

`E_1^{p,q} = H^q_ét(U_p, 𝓕_p)`

(vanishing outside the first quadrant) and converges to `H^{p+q}_ét(X, 𝓕)`.

Here `X = A.right`, `U = A.left` and `a = A.hom`, the étale sites are the spaces-étale sites of
Section 0DE7, `𝓕_p` is the abelian inverse image along the morphism of topoi of Stacks 03G2 induced
by `a_p : U_p → X`, and `H^n_ét` is `CategoryTheory.Sheaf.functorH`; the first page is identified
naturally in `𝓕` by `AlgebraicGeometry.Space.etaleSpectralSequence_pageOneIso`, and the abutment is
zero in negative degrees. -/
@[stacks 0DHA]
theorem IsFppfHypercovering.etaleSpectralSequence_pageOne_abutsTo (hA : IsFppfHypercovering A)
    (F : Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}) :
    (∀ p q : ℕ, Nonempty ((((etaleSpectralSequence A).obj F).page 1 le_rfl).X ((p : ℤ), (q : ℤ)) ≅
      (Sheaf.functorH.{u + 1, u + 1} (SpacesEtale.topology B S hS (A.left.obj (op ⦋p⦌))) q).obj
        ((Sites.abelianInverseImage (EtaleComponent.baseChangeMorphism (A := A) ⦋p⦌)).obj F))) ∧
    (∀ p q : ℤ, p < 0 ∨ q < 0 → IsZero ((((etaleSpectralSequence A).obj F).page 1 le_rfl).X
      (p, q))) ∧
    SpectralSequence.AbutsTo ((etaleSpectralSequence A).obj F)
      (fun n => if 0 ≤ n then Sheaf.functorH.{u + 1, u + 1}
          (SpacesEtale.topology B S hS A.right) n.toNat |>.obj F
        else AddCommGrpCat.of PUnit) := by
  refine ⟨fun p q ↦ ⟨(etaleSpectralSequence_pageOneIso A p q).app F⟩,
    isZero_etaleSpectralSequence_pageOne A F, ?_⟩
  let := HasDerivedCategory.standard
    (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard
    (Sheaf (etaleSituation A).totalTopology AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  exact etaleSpectralSequence_abutsTo_of_derivedIso A hA.derivedPlusGlobalSectionsIso.hom F

end AlgebraicGeometry.Space

end
