module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationComponentInverseImageAb
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CohomologySpectralSequenceOfDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringCohomologicalDescent

/-!
# The spectral sequence of an augmentation satisfying cohomological descent

Let `S` be a simplicial-site situation (Stacks 09WE) with total site `C_total` and component
sites `C_p`, and let `a` be an augmentation of `S` towards a site `(D, K)` (Stacks 0D6Z), with
total augmentation `a : Sh(C_total) → Sh(D)` and component augmentations `a_p : Sh(C_p) → Sh(D)`
(Stacks 0D70). For an abelian sheaf `𝓕` on `D` write `𝓕_p = a_p⁻¹𝓕`.

Applying the spectral sequence of Stacks 09WJ to `a⁻¹𝓕` gives a spectral sequence, functorial
in `𝓕`, with

```
E_1^{p,q} = H^q(C_p, 𝓕_p),
```

because the restriction of `a⁻¹𝓕` to `C_p` is `a_p⁻¹𝓕` (Stacks 0D70, compatibility (b)). If the
augmentation satisfies cohomological descent in the form `RΓ(D, K) = RΓ(C_total, a⁻¹K)` for `K`
in `D⁺(D)` -- this is what Stacks 0DH8 asserts for an fppf hypercovering of an algebraic space,
and Stacks 09X9 for a hypercovering in a site -- then the spectral sequence converges to
`H^{p+q}(D, 𝓕)`. This is the argument of Stacks 0DHA: an immediate consequence of the descent
statement and Stacks 09WJ.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.Augmentation.descentSpectralSequence`: the spectral
  sequence of Stacks 09WJ of `a⁻¹𝓕`, as a functor of the abelian sheaf `𝓕` on `D`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.descentSpectralSequence_pageOneIso`:
  `E_1^{p,q} = H^q(C_p, a_p⁻¹𝓕)`, naturally in `𝓕`.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.isZero_descentSpectralSequence_pageOne`:
  the first page vanishes outside the first quadrant.
* `CategoryTheory.SimplicialSiteSituation.Augmentation.descentSpectralSequence_abutsTo`: if the
  comparison `RΓ(D, -) ⟶ RΓ(C_total, -) ∘ a⁻¹` is invertible at `𝓕[0]`, the spectral sequence
  of `𝓕` abuts to `H^{p+q}(D, 𝓕)`.

## Implementation notes

The cohomological descent hypothesis is a natural transformation `φ` of bounded below derived
functors together with its invertibility at `𝓕[0]`, in an arbitrary model of the derived
categories, so the result applies to a descent statement in whichever model it is proved. The
inverse image `a⁻¹` is exact (Stacks 04JC), so its bounded below derived functor is computed
degreewise and no derived inverse image appears in the spectral sequence itself.

## References

* [Stacks Project, Tag 09WJ](https://stacks.math.columbia.edu/tag/09WJ)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0DH8](https://stacks.math.columbia.edu/tag/0DH8)
* [Stacks Project, Tag 0DHA](https://stacks.math.columbia.edu/tag/0DHA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation.Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **The spectral sequence of an augmented simplicial site**: the spectral sequence of
Stacks 09WJ of the inverse image `a⁻¹𝓕` along the total augmentation, as a functor of the
abelian sheaf `𝓕` on the augmentation site. -/
def descentSpectralSequence : Sheaf K Ab.{u} ⥤ CohomologicalSpectralSequence Ab.{u} 1 :=
  totalInverseImageAb S D K a ⋙ S.cohomologySpectralSequence

/-- **`E_1^{p,q} = H^q(C_p, a_p⁻¹𝓕)`**, naturally in the abelian sheaf `𝓕` on the augmentation
site: the first page of Stacks 09WJ at `a⁻¹𝓕` is the cohomology of its restriction to `C_p`, and
that restriction is `a_p⁻¹𝓕` (Stacks 0D70, compatibility (b)). -/
def descentSpectralSequence_pageOneIso (p q : ℕ) :
    descentSpectralSequence S D K a ⋙
        CategoryTheory.SpectralSequence.pageFunctor Ab.{u} _ 1 1 le_rfl ⋙
          HomologicalComplex.eval Ab.{u} _ ((p : ℤ), (q : ℤ)) ≅
      componentInverseImageAb S D K a ⦋p⦌ ⋙
        (Sheaf.Γ (S.componentTopology ⦋p⦌) Ab.{u}).rightDerived q :=
  Functor.isoWhiskerLeft (totalInverseImageAb S D K a)
      (S.cohomologySpectralSequence_pageOneIso p q) ≪≫
    Functor.isoWhiskerRight (componentRestrictionAbInverseImageNatIso' S D K a ⦋p⦌)
      ((Sheaf.Γ (S.componentTopology ⦋p⦌) Ab.{u}).rightDerived q)

/-- The first page of the spectral sequence of an augmented simplicial site vanishes outside
the first quadrant. -/
theorem isZero_descentSpectralSequence_pageOne (F : Sheaf K Ab.{u}) (p q : ℤ)
    (h : p < 0 ∨ q < 0) :
    IsZero ((((descentSpectralSequence S D K a).obj F).page 1 le_rfl).X (p, q)) :=
  S.isZero_cohomologySpectralSequence_pageOne _ p q h

/-- **Convergence under cohomological descent.** If the comparison
`φ : RΓ(D, -) ⟶ RΓ(C_total, -) ∘ a⁻¹` of bounded below derived functors is invertible at
`𝓕[0]`, the spectral sequence of the augmented simplicial site at `𝓕`, whose first page is
`E_1^{p,q} = H^q(C_p, a_p⁻¹𝓕)`, abuts to `H^{p+q}(D, 𝓕)`. -/
theorem descentSpectralSequence_abutsTo
    [HasDerivedCategory (Sheaf K Ab.{u})] [HasDerivedCategory (Sheaf S.totalTopology Ab.{u})]
    [HasDerivedCategory Ab.{u}]
    [(Sheaf.Γ K Ab.{u}).Additive]
    (φ : (Sheaf.Γ K Ab.{u}).rightDerivedFunctorPlus ⟶
      (totalInverseImageAb S D K a).rightDerivedFunctorPlus ⋙
        (Sheaf.Γ S.totalTopology Ab.{u}).rightDerivedFunctorPlus)
    (F : Sheaf K Ab.{u})
    [IsIso (φ.app ((DerivedCategory.Plus.singleFunctor (Sheaf K Ab.{u}) 0).obj F))] :
    SpectralSequence.AbutsTo ((descentSpectralSequence S D K a).obj F)
      (fun n => if 0 ≤ n then ((Sheaf.Γ K Ab.{u}).rightDerived n.toNat).obj F
        else AddCommGrpCat.of PUnit) :=
  S.cohomologySpectralSequence_abutsTo_of_derivedIso (Sheaf.Γ K Ab.{u})
    (totalInverseImageAb S D K a) φ F

end CategoryTheory.SimplicialSiteSituation.Augmentation

end
