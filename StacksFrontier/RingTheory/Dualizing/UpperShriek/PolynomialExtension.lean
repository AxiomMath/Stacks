module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.Defs

/-!
# Derived base change along the polynomial algebra of a presentation

Let `p` be a polynomial presentation of `f : R →+* A`, with polynomial algebra `P`.  Since `P` is
flat over `R`, the derived base change `- ⊗_R^L P` carried by
`Dualizing.PolynomialPresentation.derivedExtension` is computed degreewise: its cohomology is the
extension of scalars of the cohomology.  Consequently it preserves cohomological boundedness on
either side, and preserves finiteness of the cohomology modules.

## Main definitions

There are no new definitions beyond the comparison isomorphism below.

## Main results

* `Dualizing.PolynomialPresentation.derivedExtensionHomologyIso` — the degreewise comparison
  `Hⁱ(K ⊗_R^L P) ≅ Hⁱ(K) ⊗_R P`.
* `Dualizing.PolynomialPresentation.derivedExtension_isBoundedBelow` and
  `Dualizing.PolynomialPresentation.derivedExtension_isBoundedAbove` — preservation of
  cohomological boundedness.
* `Dualizing.PolynomialPresentation.derivedExtension_derivedCategoryB`,
  `Dualizing.PolynomialPresentation.derivedExtension_derivedCategoryBPlus`,
  `Dualizing.PolynomialPresentation.derivedExtension_derivedCategoryBMinus` and
  `Dualizing.PolynomialPresentation.derivedExtension_derivedCategoryBBounded` — preservation of
  `D_Coh`, `D⁺_Coh`, `D⁻_Coh` and `D^b_Coh`.

## Implementation notes

Coherence is taken here to be `Module.Finite`, which is what coherence means for a module over a
Noetherian ring; the subcategories `D^?_Coh` are then the `DerivedCategoryB.derivedCategoryB?`
associated with that object property.  The preservation statements themselves need no Noetherian
hypothesis, since base change along any ring map carries finite modules to finite modules.

## References

* [Stacks Project, Tag 0BZK](https://stacks.math.columbia.edu/tag/0BZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing

namespace PolynomialPresentation

variable {R A : Type u} [CommRing R] [CommRing A] {f : R →+* A}

/-- Derived base change along the polynomial algebra `P` of a presentation is computed
degreewise: `Hⁱ(K ⊗_R^L P) ≅ Hⁱ(K) ⊗_R P`, because `P` is flat over `R`. -/
noncomputable def derivedExtensionHomologyIso (p : PolynomialPresentation f)
    (K : DerivedCategory (ModuleCat.{max v u} R)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.Poly) i).obj
        (p.derivedExtension.{u, v}.obj K) ≅
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj K) :=
  letI : PreservesFiniteLimits
      (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _ p.flat_C
  (StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)) i).app K

/-- Vanishing of the `i`-th cohomology is preserved by derived base change along `P`. -/
private theorem isZero_homology_derivedExtension (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)} {i : ℤ}
    (h : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} p.Poly) i).obj
      (p.derivedExtension.{u, v}.obj K)) :=
  ((ModuleCat.extendScalars.{u, u, max v u}
    (MvPolynomial.C : R →+* p.Poly)).map_isZero h).of_iso
      (p.derivedExtensionHomologyIso.{u, v} K i)

/-- Derived base change along the polynomial algebra of a presentation preserves cohomological
boundedness below. -/
theorem derivedExtension_isBoundedBelow (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.IsBoundedBelow K) :
    DerivedCategoryB.IsBoundedBelow (p.derivedExtension.{u, v}.obj K) := by
  exact hK.imp fun _ h i hi ↦ p.isZero_homology_derivedExtension.{u, v} (h i hi)

/-- Derived base change along the polynomial algebra of a presentation preserves cohomological
boundedness above. -/
theorem derivedExtension_isBoundedAbove (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.IsBoundedAbove K) :
    DerivedCategoryB.IsBoundedAbove (p.derivedExtension.{u, v}.obj K) := by
  exact hK.imp fun _ h i hi ↦ p.isZero_homology_derivedExtension.{u, v} (h i hi)

/-- Derived base change along the polynomial algebra of a presentation preserves coherence of
the cohomology modules: base change of a finite module is finite. -/
theorem derivedExtension_derivedCategoryB (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryB
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryB
      (fun M : ModuleCat.{max v u} p.Poly ↦ Module.Finite p.Poly M)
      (p.derivedExtension.{u, v}.obj K) := by
  intro i
  let : Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj K) := hK i
  have : Module.Finite p.Poly
      ((ModuleCat.extendScalars.{u, u, max v u} (MvPolynomial.C : R →+* p.Poly)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj K)) := by
    let : Algebra R p.Poly := (MvPolynomial.C : R →+* p.Poly).toAlgebra
    exact Module.Finite.base_change R p.Poly
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v u} R) i).obj K)
  exact Module.Finite.equiv (p.derivedExtensionHomologyIso.{u, v} K i).symm.toLinearEquiv

/-- Derived base change along the polynomial algebra of a presentation preserves bounded-below
complexes with coherent cohomology. -/
theorem derivedExtension_derivedCategoryBPlus (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBPlus
      (fun M : ModuleCat.{max v u} p.Poly ↦ Module.Finite p.Poly M)
      (p.derivedExtension.{u, v}.obj K) :=
  ⟨p.derivedExtension_isBoundedBelow.{u, v} hK.1, p.derivedExtension_derivedCategoryB.{u, v} hK.2⟩

/-- Derived base change along the polynomial algebra of a presentation preserves bounded-above
complexes with coherent cohomology. -/
theorem derivedExtension_derivedCategoryBMinus (p : PolynomialPresentation f)
    {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBMinus
      (fun M : ModuleCat.{max v u} p.Poly ↦ Module.Finite p.Poly M)
      (p.derivedExtension.{u, v}.obj K) :=
  ⟨p.derivedExtension_isBoundedAbove.{u, v} hK.1, p.derivedExtension_derivedCategoryB.{u, v} hK.2⟩

/-- Derived base change along the polynomial algebra of a presentation preserves bounded
complexes with coherent cohomology. -/
theorem derivedExtension_derivedCategoryBBounded
    (p : PolynomialPresentation f) {K : DerivedCategory (ModuleCat.{max v u} R)}
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{max v u} R ↦ Module.Finite R M) K) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun M : ModuleCat.{max v u} p.Poly ↦ Module.Finite p.Poly M)
      (p.derivedExtension.{u, v}.obj K) :=
  ⟨⟨p.derivedExtension_isBoundedBelow.{u, v} hK.1.1,
      p.derivedExtension_isBoundedAbove.{u, v} hK.1.2⟩,
    p.derivedExtension_derivedCategoryB.{u, v} hK.2⟩

end PolynomialPresentation

end Dualizing

end
