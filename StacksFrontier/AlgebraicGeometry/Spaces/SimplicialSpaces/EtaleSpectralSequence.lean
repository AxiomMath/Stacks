module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponentInverseImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationDescentSpectralSequence

/-!
# The étale cohomology spectral sequence of an augmented simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`, with augmentations
`a_p : U_p → X`, and let `𝓕` be an abelian sheaf on `X_étale`, with pullbacks
`𝓕_p = a_p⁻¹𝓕` to `U_{p, étale}`. The small étale site `U_étale` of Section 0DE7 is a
simplicial site, and the spectral sequence of Stacks 09WJ of `a⁻¹𝓕` on it is a spectral
sequence, functorial in `𝓕`, with first page

```
E_1^{p,q} = H^q_ét(U_p, 𝓕_p).
```

If `a` satisfies cohomological descent in the form `RΓ(X_étale, K) = RΓ(U_étale, a⁻¹K)` -- which
Stacks 0DH8 asserts for an fppf hypercovering -- the spectral sequence converges to
`H^{p+q}_ét(X, 𝓕)`. This is the deduction of Stacks 0DHA from Stacks 0DH8 and 09WJ.

## Main definitions

* `AlgebraicGeometry.Space.etaleSpectralSequence`: the spectral sequence, as a functor of the
  abelian sheaf on `X_{spaces, étale}`.

## Main results

* `AlgebraicGeometry.Space.etaleSpectralSequence_pageOneIso`: `E_1^{p,q} = H^q_ét(U_p, 𝓕_p)`,
  naturally in `𝓕`, where `𝓕_p` is the abelian inverse image along the morphism of topoi of
  Stacks 03G2 induced by `a_p`.
* `AlgebraicGeometry.Space.isZero_etaleSpectralSequence_pageOne`: the first page vanishes
  outside the first quadrant.
* `AlgebraicGeometry.Space.etaleSpectralSequence_abutsTo_of_derivedIso`: if the comparison
  `RΓ(X_étale, -) ⟶ RΓ(U_étale, -) ∘ a⁻¹` is invertible at `𝓕[0]`, the spectral sequence of
  `𝓕` abuts to `H^{p+q}_ét(X, 𝓕)`.

## Implementation notes

The étale sites are the spaces-étale sites of Stacks 03G0, as in Section 0DE7, and étale
cohomology is Mathlib's `Sheaf.H`, the `Ext` groups out of the constant sheaf `ℤ`. The strict
model of `U_{p, spaces, étale}` that the simplicial site is built from is compared with
`U_{p, spaces, étale}` itself by
`AlgebraicGeometry.Space.EtaleComponent.componentInverseImageAbIso` and
`AlgebraicGeometry.Space.EtaleComponent.realizeCohomologyIso`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 0DHA](https://stacks.math.columbia.edu/tag/0DHA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

/-- **The étale cohomology spectral sequence of an augmented simplicial algebraic space**
`a : U → X`: the spectral sequence of Stacks 09WJ, on the small étale site `U_étale` of
Section 0DE7, of the inverse image `a⁻¹𝓕` of an abelian sheaf `𝓕` on `X_étale`, as a functor
of `𝓕`. -/
def etaleSpectralSequence :
    Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1} ⥤
      CohomologicalSpectralSequence AddCommGrpCat.{u + 1} 1 :=
  CategoryTheory.SimplicialSiteSituation.Augmentation.descentSpectralSequence
    (etaleSituation A) _ _ (etaleAugmentation A)

/-- **`E_1^{p,q} = H^q_ét(U_p, 𝓕_p)`**, naturally in the abelian sheaf `𝓕` on `X_étale`, where
`𝓕_p` is the pullback of `𝓕` along `a_p : U_p → X` (the abelian inverse image along the morphism
of topoi of Stacks 03G2 induced by `a_p`). -/
def etaleSpectralSequence_pageOneIso (p q : ℕ) :
    etaleSpectralSequence A ⋙
        CategoryTheory.SpectralSequence.pageFunctor AddCommGrpCat.{u + 1} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval AddCommGrpCat.{u + 1} _ ((p : ℤ), (q : ℤ)) ≅
      Sites.abelianInverseImage (EtaleComponent.baseChangeMorphism (A := A) ⦋p⦌) ⋙
        Sheaf.functorH.{u + 1, u + 1} (SpacesEtale.topology B S hS (A.left.obj (op ⦋p⦌))) q :=
  CategoryTheory.SimplicialSiteSituation.Augmentation.descentSpectralSequence_pageOneIso
      (etaleSituation A) _ _ (etaleAugmentation A) p q ≪≫
    Functor.isoWhiskerRight (EtaleComponent.componentInverseImageAbIso (A := A) ⦋p⦌)
      ((Sheaf.Γ ((etaleSituation A).componentTopology ⦋p⦌)
        AddCommGrpCat.{u + 1}).rightDerived q) ≪≫
    Functor.isoWhiskerLeft
      (Sites.abelianInverseImage (EtaleComponent.baseChangeMorphism (A := A) ⦋p⦌))
      (EtaleComponent.realizeCohomologyIso (A := A) ⦋p⦌ q)

/-- The first page of the étale cohomology spectral sequence of an augmented simplicial
algebraic space vanishes outside the first quadrant. -/
theorem isZero_etaleSpectralSequence_pageOne
    (F : Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}) (p q : ℤ)
    (h : p < 0 ∨ q < 0) :
    IsZero ((((etaleSpectralSequence A).obj F).page 1 le_rfl).X (p, q)) :=
  CategoryTheory.SimplicialSiteSituation.Augmentation.isZero_descentSpectralSequence_pageOne
    (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
    (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) F p q h

/-- Global sections of abelian sheaves on `X_{spaces, étale}` are additive, preserving binary
products. -/
local instance additive_sheafΓ_base :
    (Sheaf.Γ (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse image of abelian sheaves along the augmentation `a : Sh(U_étale) → Sh(X_étale)`
is additive. The general instance does not apply syntactically, the augmentation of Section 0DE7
being given in its continuous form. -/
local instance additive_etaleTotalInverseImageAb :
    (CategoryTheory.SimplicialSiteSituation.Augmentation.totalInverseImageAb
      (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).Additive :=
  CategoryTheory.SimplicialSiteSituation.Augmentation.additive_totalInverseImageAb _ _ _ _

/-- **Convergence under cohomological descent.** If the comparison
`φ : RΓ(X_étale, -) ⟶ RΓ(U_étale, -) ∘ a⁻¹` of bounded below derived functors is invertible at
`𝓕[0]`, the étale cohomology spectral sequence of `𝓕`, with first page
`E_1^{p,q} = H^q_ét(U_p, 𝓕_p)`, abuts to `H^{p+q}_ét(X, 𝓕)`. -/
theorem etaleSpectralSequence_abutsTo_of_derivedIso
    [HasDerivedCategory (Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory
      (Sheaf ((etaleSituation A).totalTopology) AddCommGrpCat.{u + 1})]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (φ : (Sheaf.Γ (SpacesEtale.topology B S hS A.right)
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus ⟶
      (CategoryTheory.SimplicialSiteSituation.Augmentation.totalInverseImageAb
          (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).rightDerivedFunctorPlus ⋙
        (Sheaf.Γ ((etaleSituation A).totalTopology)
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus)
    (F : Sheaf (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1})
    [IsIso (φ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj F))] :
    SpectralSequence.AbutsTo ((etaleSpectralSequence A).obj F)
      (fun n => if 0 ≤ n then Sheaf.functorH.{u + 1, u + 1}
          (SpacesEtale.topology B S hS A.right) n.toNat |>.obj F
        else AddCommGrpCat.of PUnit) := by
  have : (Sheaf.Γ (C := Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) AddCommGrpCat.{u + 1}).Additive :=
    Functor.additive_of_preserves_binary_products _
  refine (CategoryTheory.SimplicialSiteSituation.Augmentation.descentSpectralSequence_abutsTo
    (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
    (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) φ F).of_iso fun n => ?_
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn, ite_eq_left hn]
    exact (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u + 1, u + 1}
      (SpacesEtale.topology B S hS A.right) n.toNat).app F
  · rw [ite_eq_right hn, ite_eq_right hn]

end AlgebraicGeometry.Space

end
