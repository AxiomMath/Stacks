module

public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality
public import StacksCore.Algebra.Homology.SpectralSequence.PageInfinity

/-!
# Transporting the infinity page along an equality of spectral sequences

The spectral sequence of a filtered complex depends on the family of subobjects cutting out the
filtration, and the *same* family can be presented in more than one way: the filtration of the
total complex of a double complex by the second coordinate is presented both as
`HomologicalComplex₂.stepSubobject` and as `CochainComplex.filtrationSubobject` of
`HomologicalComplex₂.totalFiltration₂`.  `HomologicalComplex₂.spectralSequence_congr` says that
the two presentations give the *same* spectral sequence, as a propositional equality. This file
identifies the infinity pages of equal spectral sequences, compatibly with morphisms, and proves
the companion of `HomologicalComplex₂.spectralSequence_congr` on morphisms.

## Main definitions

* `CategoryTheory.SpectralSequence.pageInfinityEqToIso`: equal spectral sequences have the same
  infinity page.

## Main results

* `CategoryTheory.SpectralSequence.mapPageInfinity_pageInfinityEqToIso`: two morphisms of spectral
  sequences conjugate to one another by those identifications induce the same map on the infinity
  pages, up to the same identifications.
* `FilteredComplexSpectralSequence.spectralSequenceMap_filtration_congr`: the morphism of spectral
  sequences induced by a morphism of filtered complexes depends only on the families of subobjects
  cutting out the two filtrations, not on their presentations, stated as the conjugation by the
  `eqToHom`s of `HomologicalComplex₂.spectralSequence_congr`.

## References

* [Stacks Project, Tag 012O](https://stacks.math.columbia.edu/tag/012O)
* [Stacks Project, Tag 0130](https://stacks.math.columbia.edu/tag/0130)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex FilteredComplexSpectralSequence

namespace CategoryTheory.SpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ℤ → ComplexShape ι} {r₀ : ℤ}

/-- The isomorphism between the infinity pages at `pq` of two equal spectral sequences. -/
def pageInfinityEqToIso {E E' : SpectralSequence C c r₀} (h : E = E') (pq : ι)
    [E.HasPageInfinityAt pq] [E'.HasPageInfinityAt pq] :
    E.pageInfinity pq ≅ E'.pageInfinity pq :=
  eqToIso (by subst h; rfl)

/-- If two morphisms `f` and `f'` of spectral sequences are conjugate,
`f ≫ eqToHom h₂ = eqToHom h₁ ≫ f'`, then the maps they induce on the infinity pages are conjugate
by `pageInfinityEqToIso`. -/
theorem mapPageInfinity_pageInfinityEqToIso {E₁ E₂ E₁' E₂' : SpectralSequence C c r₀}
    (h₁ : E₁ = E₁') (h₂ : E₂ = E₂') (f : E₁ ⟶ E₂) (f' : E₁' ⟶ E₂')
    (hf : f ≫ eqToHom h₂ = eqToHom h₁ ≫ f') (pq : ι)
    [E₁.HasPageInfinityAt pq] [E₂.HasPageInfinityAt pq]
    [E₁'.HasPageInfinityAt pq] [E₂'.HasPageInfinityAt pq] :
    Hom.mapPageInfinity f pq ≫ (pageInfinityEqToIso h₂ pq).hom =
      (pageInfinityEqToIso h₁ pq).hom ≫ Hom.mapPageInfinity f' pq := by
  subst h₁ h₂
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp] at hf
  subst hf
  simp [pageInfinityEqToIso]

end CategoryTheory.SpectralSequence

namespace FilteredComplexSpectralSequence

variable {A : Type u} [Category.{v} A] [Abelian A] {K L : CochainComplex A ℤ}

/-- The morphism of spectral sequences induced by a morphism of filtered complexes depends only on
the families of subobjects cutting out the two filtrations: for equal families `FK = FK'` and
`FL = FL'`, the two induced morphisms are conjugate by the `eqToHom`s of
`HomologicalComplex₂.spectralSequence_congr`. -/
theorem spectralSequenceMap_filtration_congr (φ : K ⟶ L)
    {FK FK' : ℤ → ∀ n : ℤ, Subobject (K.X n)} {FL FL' : ℤ → ∀ n : ℤ, Subobject (L.X n)}
    (hK : FK = FK') (hL : FL = FL')
    (hφ : ∀ p n : ℤ, (Subobject.«exists» (φ.f n)).obj (FK p n) ≤ FL p n)
    (hφ' : ∀ p n : ℤ, (Subobject.«exists» (φ.f n)).obj (FK' p n) ≤ FL' p n)
    (hantiK : ∀ p p' n : ℤ, p ≤ p' → FK p' n ≤ FK p n)
    (hantiK' : ∀ p p' n : ℤ, p ≤ p' → FK' p' n ≤ FK' p n)
    (hantiL : ∀ p p' n : ℤ, p ≤ p' → FL p' n ≤ FL p n)
    (hantiL' : ∀ p p' n : ℤ, p ≤ p' → FL' p' n ≤ FL' p n) :
    spectralSequenceMap φ hφ hantiK hantiL ≫
        eqToHom (HomologicalComplex₂.spectralSequence_congr hL hantiL hantiL') =
      eqToHom (HomologicalComplex₂.spectralSequence_congr hK hantiK hantiK') ≫
        spectralSequenceMap φ hφ' hantiK' hantiL' := by
  subst hK hL
  simp

end FilteredComplexSpectralSequence

end
