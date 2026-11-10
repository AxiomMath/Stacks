module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.Scheme.Reduction
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.BlowupFibreDimension

/-!
# Ideal sheaves on the spectrum of a ring

On an affine scheme the quasi-coherent ideal sheaves are the ideals of the ring of global
sections, by `AlgebraicGeometry.Scheme.IdealSheafData.equivOfIsAffine`. This file turns that
bijection into a dictionary between `Ideal A` and `(Spec A).IdealSheafData`, so that a statement
about a chain of closed subschemes of `Spec A` — a stratification, say — can be read as a
statement about a chain of ideals of `A`, and conversely.

Every entry of the dictionary is an equivalence, so it may be used in either direction:

* the order structure — `AlgebraicGeometry.specIdealSheaf_le_iff`, with
  `AlgebraicGeometry.specIdealSheafOrderIso` the bijection itself;
* the support — `Stacks.LocalCohomology.coe_support_specIdealSheaf`, the zero locus of the ideal;
* finite type — `AlgebraicGeometry.isFiniteType_specIdealSheaf_iff`, finite generation;
* emptiness of the closed subscheme — `AlgebraicGeometry.specIdealSheaf_eq_top_iff`, the
  improper ideal;
* the closed subscheme itself — `AlgebraicGeometry.exists_subschemeIso_specIdealSheaf`, the
  spectrum of the quotient, with its inclusion the spectrum of the quotient map;
* thickenings — `AlgebraicGeometry.isThickening_subschemeι_specIdealSheaf_iff`, the ideal lying
  in the nilradical.

## Main results

* `Stacks.LocalCohomology.specIdealSheaf`: the ideal sheaf on `Spec A` cut out by an ideal of `A`.
* `AlgebraicGeometry.specIdealSheafOrderIso`: the ideals of `A` and the quasi-coherent ideal
  sheaves on `Spec A` are the same ordered set; its two halves are
  `AlgebraicGeometry.specIdealSheaf_le_iff` and
  `AlgebraicGeometry.exists_eq_specIdealSheaf`.
* `AlgebraicGeometry.ker_specMap_quotientMk`: that ideal sheaf is the kernel of the spectrum of
  the quotient map.
* `AlgebraicGeometry.exists_subschemeIso_specIdealSheaf`: the closed subscheme cut out by `I` is
  `Spec (A ⧸ I)`, by an isomorphism that takes its inclusion to the spectrum of `A → A ⧸ I`.
* `AlgebraicGeometry.isFiniteType_specIdealSheaf_iff`,
  `AlgebraicGeometry.specIdealSheaf_eq_top_iff` and
  `AlgebraicGeometry.isThickening_subschemeι_specIdealSheaf_iff`: the three side conditions a
  stratification of `Spec A` imposes on its ideal sheaves, read on the ideals.

## Implementation notes

`Γ(Spec A, ⊤)` is not `A` but a ring isomorphic to it through
`AlgebraicGeometry.Scheme.ΓSpecIso`, so `Stacks.LocalCohomology.specIdealSheaf` pushes the ideal
forward along that isomorphism before applying
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop`. Pushing an ideal forward along an
isomorphism is injective and order reflecting, which is what makes every entry of the dictionary
an equivalence rather than an implication.

The closed subscheme is identified with the spectrum of the quotient through
`AlgebraicGeometry.IsClosedImmersion.Spec_iff`: the inclusion of the subscheme is a closed
immersion into an affine scheme, hence the spectrum of a quotient map, and the ideal of that
quotient is the one it started from because the kernel ideal sheaf of the inclusion is the ideal
sheaf itself. The statement is an existential rather than a named isomorphism because that
classification offers no canonical choice.
-/

@[expose] public section

open CategoryTheory
open Stacks.LocalCohomology (specIdealSheaf coe_support_specIdealSheaf)

universe u

namespace AlgebraicGeometry

/-- The ideal of global sections of the ideal sheaf cut out by `I` is the ideal `I` pushed
forward along `A ≅ Γ(Spec A, ⊤)`. -/
theorem ideal_specIdealSheaf_top {A : Type u} [CommRing A] (I : Ideal A) :
    (specIdealSheaf A I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom := by
  simp [specIdealSheaf]

/-- The inverse of `AlgebraicGeometry.Scheme.ΓSpecIso` is injective, being an isomorphism. -/
private theorem injective_ΓSpecIso_inv (A : Type u) [CommRing A] :
    Function.Injective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).1

private theorem surjective_ΓSpecIso_inv (A : Type u) [CommRing A] :
    Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2

/-- Pushing an ideal of `A` forward to `Γ(Spec A, ⊤)` and pulling it back again gives it
back. -/
private theorem map_ΓSpecIso_hom_map_inv {A : Type u} [CommRing A] (I : Ideal A) :
    (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).map
        (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom = I := by
  rw [Ideal.map_map]
  refine (congrArg (Ideal.map · I) ?_).trans (Ideal.map_id I)
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id A
  rw [← CommRingCat.hom_comp, (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id]
  rfl

/-- **The dictionary is order reflecting.** -/
@[simp]
theorem specIdealSheaf_le_iff {A : Type u} [CommRing A] {I J : Ideal A} :
    specIdealSheaf A I ≤ specIdealSheaf A J ↔ I ≤ J := by
  refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.le_of_isAffine ?_⟩
  · have h' := h ⟨⊤, isAffineOpen_top _⟩
    rw [ideal_specIdealSheaf_top, ideal_specIdealSheaf_top] at h'
    rw [← map_ΓSpecIso_hom_map_inv I, ← map_ΓSpecIso_hom_map_inv J]
    exact Ideal.map_mono h'
  · rw [ideal_specIdealSheaf_top, ideal_specIdealSheaf_top]
    exact Ideal.map_mono h

/-- Distinct ideals of `A` cut out distinct quasi-coherent ideal sheaves on `Spec A`. -/
theorem specIdealSheaf_injective (A : Type u) [CommRing A] :
    Function.Injective (specIdealSheaf A) := fun _ _ h =>
  le_antisymm (specIdealSheaf_le_iff.mp h.le) (specIdealSheaf_le_iff.mp h.ge)

/-- **Every quasi-coherent ideal sheaf on `Spec A` is cut out by an ideal of `A`.** -/
theorem exists_eq_specIdealSheaf (A : Type u) [CommRing A]
    (J : (Spec (CommRingCat.of A)).IdealSheafData) :
    ∃ I : Ideal A, J = specIdealSheaf A I := by
  refine ⟨(J.ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [ideal_specIdealSheaf_top, Ideal.map_map]
  refine Eq.symm ((congrArg (Ideal.map · (J.ideal ⟨⊤, isAffineOpen_top _⟩)) ?_).trans
    (Ideal.map_id _))
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom = RingHom.id _
  rw [← CommRingCat.hom_comp, (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id]
  rfl

/-- **The ideals of `A` and the quasi-coherent ideal sheaves on `Spec A` are the same ordered
set.** -/
noncomputable def specIdealSheafOrderIso (A : Type u) [CommRing A] :
    Ideal A ≃o (Spec (CommRingCat.of A)).IdealSheafData :=
  RelIso.ofSurjective ⟨⟨specIdealSheaf A, specIdealSheaf_injective A⟩, specIdealSheaf_le_iff⟩
    fun J => (exists_eq_specIdealSheaf A J).imp fun _ h => h.symm

/-- The order isomorphism `AlgebraicGeometry.specIdealSheafOrderIso` sends an ideal `I` of `A`
to the ideal sheaf cut out by `I`. -/
@[simp]
theorem specIdealSheafOrderIso_apply {A : Type u} [CommRing A] (I : Ideal A) :
    specIdealSheafOrderIso A I = specIdealSheaf A I := rfl

/-- The zero ideal of `A` cuts out the zero ideal sheaf on `Spec A`. -/
@[simp]
theorem specIdealSheaf_bot (A : Type u) [CommRing A] :
    specIdealSheaf A (⊥ : Ideal A) = ⊥ := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [ideal_specIdealSheaf_top]
  simp

/-- The unit ideal of `A` cuts out the unit ideal sheaf on `Spec A`. -/
@[simp]
theorem specIdealSheaf_top (A : Type u) [CommRing A] :
    specIdealSheaf A (⊤ : Ideal A) = ⊤ := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  rw [ideal_specIdealSheaf_top]
  simpa using Ideal.map_top (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- **The closed subscheme cut out by `I` is empty exactly when `I` is the improper ideal.** -/
theorem specIdealSheaf_eq_top_iff {A : Type u} [CommRing A] {I : Ideal A} :
    specIdealSheaf A I = ⊤ ↔ I = ⊤ :=
  ⟨fun h => specIdealSheaf_injective A (h.trans (specIdealSheaf_top A).symm),
    fun h => h ▸ specIdealSheaf_top A⟩

/-- **The ideal sheaf cut out by `I` is of finite type exactly when `I` is finitely
generated.** -/
theorem isFiniteType_specIdealSheaf_iff {A : Type u} [CommRing A] {I : Ideal A} :
    (specIdealSheaf A I).IsFiniteType ↔ I.FG := by
  refine ⟨fun h => ?_, fun h U => ?_⟩
  · have hmap := h ⟨⊤, isAffineOpen_top _⟩
    rw [ideal_specIdealSheaf_top] at hmap
    exact map_ΓSpecIso_hom_map_inv I ▸ hmap.map _
  · rw [specIdealSheaf, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map]
    exact h.map _

/-- **The inclusion of the closed subscheme cut out by `I` is a thickening exactly when `I` is
contained in the nilradical.** -/
theorem isThickening_subschemeι_specIdealSheaf_iff {A : Type u} [CommRing A] {I : Ideal A} :
    Stacks.Thickenings.IsThickening (specIdealSheaf A I).subschemeι ↔ I ≤ nilradical A := by
  rw [Scheme.IdealSheafData.isThickening_subschemeι_iff, ← SetLike.coe_set_eq,
    TopologicalSpace.Closeds.coe_top, coe_support_specIdealSheaf]
  exact (PrimeSpectrum.zeroLocus_eq_univ_iff (I : Set A)).trans SetLike.coe_subset_coe

/-- Pulling an ideal of `A` back along `Γ(Spec A, ⊤) ≅ A` is pushing it forward along the
inverse isomorphism. -/
private theorem comap_ΓSpecIso_hom {A : Type u} [CommRing A] (I : Ideal A) :
    I.comap (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
      I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom :=
  (Ideal.map_symm (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv).symm

/-- **The ideal sheaf cut out by `I` is the kernel of the spectrum of the quotient map.** -/
theorem ker_specMap_quotientMk {A : Type u} [CommRing A] (I : Ideal A) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker = specIdealSheaf A I := by
  rw [Scheme.ker_of_isAffine, specIdealSheaf]
  congr 1
  have happ : (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
        CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv := by
    simp
  rw [happ]
  change RingHom.ker ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv.hom.comp
    ((Ideal.Quotient.mk I).comp (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)) = _
  rw [RingHom.ker_comp_of_injective _ (injective_ΓSpecIso_inv (A ⧸ I)),
    ← RingHom.comap_ker, Ideal.mk_ker, comap_ΓSpecIso_hom]

/-- **The closed subscheme cut out by `I` is the spectrum of `A ⧸ I`.** The inclusion of the
closed subscheme into `Spec A` becomes the spectrum of the quotient map `A → A ⧸ I`. -/
theorem exists_subschemeIso_specIdealSheaf {A : Type u} [CommRing A] (I : Ideal A) :
    ∃ e : (specIdealSheaf A I).subscheme ≅ Spec (CommRingCat.of (A ⧸ I)),
      (specIdealSheaf A I).subschemeι =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  obtain ⟨J, e, he⟩ :=
    IsClosedImmersion.Spec_iff.mp
      (inferInstance : IsClosedImmersion (specIdealSheaf A I).subschemeι)
  have hJ : J = I := by
    refine specIdealSheaf_injective A ?_
    rw [← ker_specMap_quotientMk J, ← Scheme.Hom.ker_comp_of_isIso e.hom, ← he,
      Scheme.IdealSheafData.ker_subschemeι]
  subst hJ
  exact ⟨e, he⟩

end AlgebraicGeometry

end
