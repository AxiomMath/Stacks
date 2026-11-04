module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticProIsomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticDerivedPullbackLinear
public import StacksFrontier.CategoryTheory.Triangulated.LinearTriangulatedEquivalence

/-!
# The equivalence of Tag 0GZH as an equivalence of `R`-linear triangulated categories

Let `R` be a ring and let `(A_n)` and `(B_n)` be inverse systems of differential graded
`R`-algebras, with sheaves of differential graded algebras `𝒜` and `ℬ` on the chaotic site of
the index category. The functor `QC(𝒜) ⥤ QC(ℬ)` induced by a representative of a morphism of
pro-objects is the derived pullback along a functor of chaotic sites over the identity of the
constant sheaf of rings, restricted to the quasi-coherent objects; it commutes with the
translations, is triangulated and is `R`-linear. So when the morphism of pro-objects is an
isomorphism, the equivalence `QC(𝒜) ≌ QC(ℬ)` of Lemma 24.35.1 (Tag 0GZH) is an equivalence of
`R`-linear triangulated categories, the form in which Remark 0H1E chains it with the other
equivalences of the proof of Proposition 24.35.4 (Tag 0GZK).

## Main definitions

* `DifferentialGradedAlgebra.SystemProIso.qcLinearTriangulatedEquivalence`: the equivalence
  `QC(𝒜) ≌ QC(ℬ)` of a pro-isomorphism with on-the-nose composites, as an equivalence of
  `R`-linear triangulated categories.
* `DifferentialGradedAlgebra.SystemProHom.qcLinearTriangulatedEquivalence`: **the equivalence
  `QC(𝒜) ≌ QC(ℬ)` of Tag 0GZH, induced by a representative of an isomorphism of pro-objects, as an
  equivalence of `R`-linear triangulated categories.**

## References

* [Stacks Project, Lemma 24.35.1 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf

universe u

namespace DifferentialGradedAlgebra

open SheafOfModules.DifferentialGradedModule Stacks.ChaoticSite

variable {R : Type u} [CommRing R]

namespace SystemProIso

variable {ι : Type u} [Preorder ι] {A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- **The equivalence `QC(𝒜) ≌ QC(ℬ)` of a pro-isomorphism with on-the-nose composites, as an
equivalence of `R`-linear triangulated categories**: its functor, the derived pullback along the
representative `A_{F₁ i} → B_i`, commutes with the translations, is triangulated and is
`R`-linear. -/
def qcLinearTriangulatedEquivalence (e : SystemProIso A B) :
    LinearTriangulatedEquivalence R (Chaotic.QC (systemSheaf A)).FullSubcategory
      (Chaotic.QC (systemSheaf B)).FullSubcategory where
  equivalence := e.qcEquivalence
  commShift := chaoticQCPullback_commShift (systemInverseImageHom e.F₁ e.hom)
  isTriangulated := chaoticQCPullback_isTriangulated (systemInverseImageHom e.F₁ e.hom)
  linear := chaoticQCPullback_linear (systemInverseImageHom e.F₁ e.hom)

/-- The underlying equivalence of `qcLinearTriangulatedEquivalence` is `qcEquivalence`. -/
theorem qcLinearTriangulatedEquivalence_equivalence (e : SystemProIso A B) :
    e.qcLinearTriangulatedEquivalence.equivalence = e.qcEquivalence :=
  rfl

end SystemProIso

namespace SystemProHom

variable {ι : Type u} [LinearOrder ι] [LocallyFiniteOrderBot ι]
  {A B : ιᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R}

/-- **The equivalence `QC(𝒜) ≌ QC(ℬ)` of Tag 0GZH, as an equivalence of `R`-linear triangulated
categories.** Its functor is the functor `QC(𝒜) ⥤ QC(ℬ)` induced by a representative `φ` of an
isomorphism of pro-objects, an equivalence by Tag 0GZH; it is the derived pullback along `φ` on
quasi-coherent objects, which commutes with the translations, is triangulated and is
`R`-linear. -/
def qcLinearTriangulatedEquivalence (φ : SystemProHom A B) (hφ : φ.IsProIso) :
    LinearTriangulatedEquivalence R (Chaotic.QC (systemSheaf A)).FullSubcategory
      (Chaotic.QC (systemSheaf B)).FullSubcategory where
  equivalence :=
    haveI := φ.isEquivalence_qcPullback hφ
    φ.qcPullback.asEquivalence
  commShift := chaoticQCPullback_commShift (systemInverseImageHom φ.F φ.hom)
  isTriangulated := chaoticQCPullback_isTriangulated (systemInverseImageHom φ.F φ.hom)
  linear := chaoticQCPullback_linear (systemInverseImageHom φ.F φ.hom)

/-- The functor of `qcLinearTriangulatedEquivalence` is the functor `QC(𝒜) ⥤ QC(ℬ)` induced by
the representative. -/
theorem qcLinearTriangulatedEquivalence_functor (φ : SystemProHom A B) (hφ : φ.IsProIso) :
    (φ.qcLinearTriangulatedEquivalence hφ).equivalence.functor = φ.qcPullback :=
  rfl

end SystemProHom

end DifferentialGradedAlgebra
