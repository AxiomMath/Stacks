module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.TwoGeneratorSquare

/-!
# `Spec` of a quotient ring as a closed subscheme

For an ideal `I` of a commutative ring `A`, the morphism `Spec (A ⧸ I) ⟶ Spec A` is a closed
immersion, and this file identifies it, as an arrow, with the closed subscheme of `Spec A` cut
out by the quasi-coherent ideal sheaf attached to `I`.

The statement is proved in that generality and then specialized to the lower horizontal arrow of
the two-generator almost blowup square of
`StacksFrontier/AlgebraicGeometry/TwoGeneratorSquare.lean`, whose center is
`Spec (A ⧸ (f₁, f₂)) ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.arrowIsoKerSubschemeι`: a closed immersion is, as an arrow, the
  closed subscheme cut out by its kernel.
* `AlgebraicGeometry.ker_appTop_Spec_map`: the kernel of the global-sections map of `Spec φ` is
  the kernel of `φ` read through the counit `Γ(Spec A, ⊤) ≅ A`.
* `AlgebraicGeometry.Spec.arrowIsoQuotientSubschemeι`: `Spec (A ⧸ I) ⟶ Spec A` is the closed
  subscheme of `Spec A` cut out by `I`.
* `Stacks.AlmostBlowUp.twoGenerator_center`: the lower-left corner of the two-generator square
  is the closed subscheme of `Spec A` defined by `(f₁, f₂)`.

## Implementation notes

Mathlib already knows that `Spec` of a surjection is a closed immersion
(`AlgebraicGeometry.IsClosedImmersion.spec_of_quotient_mk`), that the scheme-theoretic image of
a closed immersion is the whole domain (the `IsIso f.toImage` instance), that the subscheme cut
out by `f.ker` *is* the scheme-theoretic image, and that `f.ker` is computed on an affine target
by `AlgebraicGeometry.Scheme.ker_of_isAffine`. What is missing is only the
assembly of those four facts into a comparison of arrows, together with the computation of
`RingHom.ker (Spec.map φ).appTop.hom`; the latter is the naturality square of the counit
`Γ(Spec ·, ⊤) ≅ ·` plus the fact that a ring isomorphism turns `Ideal.comap` into `Ideal.map`
along its inverse.

`Stacks.AlmostBlowUp.twoGenerator_center` records the identification as a
`Nonempty (Arrow.mk _ ≅ Arrow.mk _)`; the underlying isomorphism is produced here as data, so
clients that need the comparison morphisms themselves can use
`AlgebraicGeometry.Spec.arrowIsoQuotientSubschemeι` directly. The statement of Tag 0EVH, which
uses the identification over `Spec A`, is
`Stacks.AlmostBlowUp.isAlmostBlowUpSquare_twoGeneratorSquare`.

## References

* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- For an isomorphism `e` of commutative rings, pulling an ideal back along `e` is the same as
pushing it forward along `e⁻¹`. -/
theorem Ideal.comap_hom_eq_map_inv {A B : CommRingCat.{u}} (e : A ≅ B) (J : Ideal B) :
    Ideal.comap e.hom.hom J = Ideal.map e.inv.hom J := by
  exact Ideal.comap_symm e.symm.commRingCatIsoToRingEquiv

/-- **A closed immersion is the closed subscheme cut out by its kernel.** The comparison is the
morphism to the scheme-theoretic image, which is an isomorphism precisely because `f` is a closed
immersion. -/
def Scheme.Hom.arrowIsoKerSubschemeι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    Arrow.mk f ≅ Arrow.mk f.ker.subschemeι :=
  Arrow.isoMk (asIso f.toImage) (Iso.refl _) (by simp)

/-- The kernel of the map on global sections induced by `Spec φ` is the kernel of `φ`, transported
along the inverse of the counit `Γ(Spec A, ⊤) ≅ A`. -/
theorem ker_appTop_Spec_map {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    RingHom.ker (Spec.map φ).appTop.hom =
      Ideal.map (Scheme.ΓSpecIso A).inv.hom (RingHom.ker φ.hom) := by
  have h : (Spec.map φ).appTop = (Scheme.ΓSpecIso A).hom ≫ φ ≫ (Scheme.ΓSpecIso B).inv := by
    rw [← Category.assoc]
    exact (Iso.eq_comp_inv _).mpr (Scheme.ΓSpecIso_naturality φ)
  have hinj : Function.Injective (Scheme.ΓSpecIso B).inv.hom :=
    (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective
  rw [h]
  change RingHom.ker (((Scheme.ΓSpecIso B).inv.hom.comp φ.hom).comp
    (Scheme.ΓSpecIso A).hom.hom) = _
  rw [RingHom.comp_assoc, RingHom.ker_comp_of_injective _ hinj, ← RingHom.comap_ker,
    Ideal.comap_hom_eq_map_inv]

/-- The kernel ideal sheaf of `Spec (A ⧸ I) ⟶ Spec A` is the quasi-coherent ideal sheaf attached
to `I`. -/
theorem ker_Spec_map_quotient_mk {A : Type u} [CommRing A] (I : Ideal A) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker =
      Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I) := by
  rw [Scheme.ker_of_isAffine, ker_appTop_Spec_map]
  simp

/-- **`Spec` of a quotient ring is a closed subscheme.** For an ideal `I` of `A`, the morphism
`Spec (A ⧸ I) ⟶ Spec A` is isomorphic, as an arrow, to the closed subscheme of `Spec A` cut out
by the quasi-coherent ideal sheaf attached to `I`. -/
def Spec.arrowIsoQuotientSubschemeι {A : Type u} [CommRing A] (I : Ideal A) :
    Arrow.mk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ≅
      Arrow.mk (Scheme.IdealSheafData.ofIdealTop
        (Ideal.map (Scheme.ΓSpecIso (.of A)).inv.hom I)).subschemeι :=
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).arrowIsoKerSubschemeι ≪≫
    eqToIso (by rw [ker_Spec_map_quotient_mk])

end AlgebraicGeometry

namespace Stacks.AlmostBlowUp

open AlgebraicGeometry

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- The lower-left corner is the closed subscheme defined by `(f₁,f₂)`. -/
theorem twoGenerator_center :
    Nonempty (Arrow.mk (centerToBase A f₁ f₂) ≅
      Arrow.mk (centerIdealSheaf A f₁ f₂).subschemeι) :=
  ⟨Spec.arrowIsoQuotientSubschemeι (centerIdeal A f₁ f₂)⟩

end Stacks.AlmostBlowUp

end
