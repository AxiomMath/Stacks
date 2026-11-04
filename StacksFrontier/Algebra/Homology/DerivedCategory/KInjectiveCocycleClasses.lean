module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology

/-!
# Morphisms into a K-injective complex as cocycles modulo coboundaries

Let `L` be a K-injective cochain complex.  The morphisms `K ⟶ L` of the derived category are the
degree `0` cocycles of the complex of morphisms `Hom^•(K, L)` modulo the coboundaries, and the
morphisms `K ⟶ L[-1]` are its degree `-1` cohomology.  This file records the three consequences
of `CochainComplex.IsKInjective.Qh_map_bijective` in the form in which a sheaf-theoretic
argument on the complexes `U ↦ Hom^•(K|_U, L|_U)` consumes them:

* every morphism of the derived category is the image of a morphism of complexes, that is of a
  degree `0` cocycle;
* two degree `0` cocycles have the same image exactly when they differ by a coboundary;
* if `Hom(K, L[-1]) = 0` in the derived category, every degree `-1` cocycle is a coboundary.

## Main results

* `CochainComplex.IsKInjective.Qh_map_quotient_map_surjective`
* `CochainComplex.IsKInjective.Qh_map_quotient_map_homOf_eq_iff`
* `CochainComplex.IsKInjective.exists_δ_eq_of_subsingleton`

## References

* [Stacks Project, Tag 0D66](https://stacks.math.columbia.edu/tag/0D66)
-/

@[expose] public section

universe v u

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKInjective

open HomComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- **Every morphism of the derived category into a K-injective complex is the image of a
morphism of complexes.** -/
theorem Qh_map_quotient_map_surjective {K L : CochainComplex C ℤ} [L.IsKInjective]
    (φ : Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
      Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)) :
    ∃ f : K ⟶ L, Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) = φ := by
  obtain ⟨g, rfl⟩ := (Qh_map_bijective _ L).surjective φ
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective g
  exact ⟨f, rfl⟩

/-- **Two degree `0` cocycles into a K-injective complex have the same image in the derived
category exactly when they differ by a coboundary.** -/
theorem Qh_map_quotient_map_homOf_eq_iff {K L : CochainComplex C ℤ} [L.IsKInjective]
    (z z' : Cocycle K L 0) :
    Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (Cocycle.homOf z)) =
        Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map (Cocycle.homOf z')) ↔
      ∃ c : Cochain K L (-1), δ (-1) 0 c = (z : Cochain K L 0) - z' := by
  rw [(Qh_map_bijective _ L).injective.eq_iff]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := Cochain.equivHomotopy _ _ (HomotopyCategory.homotopyOfEq _ _ h)
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.cochain_ofHom_homOf_eq_coe] at hc
    exact ⟨c, by rw [hc, add_sub_cancel_right]⟩
  · rintro ⟨c, hc⟩
    refine HomotopyCategory.eq_of_homotopy _ _ ((Cochain.equivHomotopy _ _).symm ⟨c, ?_⟩)
    rw [Cocycle.cochain_ofHom_homOf_eq_coe, Cocycle.cochain_ofHom_homOf_eq_coe, hc,
      sub_add_cancel]

/-- **If `Hom(K, L[-1])` vanishes in the derived category, every degree `-1` cocycle of
`Hom^•(K, L)` is a coboundary**, for `L` K-injective. -/
theorem exists_δ_eq_of_subsingleton {K L : CochainComplex C ℤ} [L.IsKInjective]
    (h : Subsingleton (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
      (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L))⟦(-1 : ℤ)⟧))
    (z : Cochain K L (-1)) (hz : δ (-1) 0 z = 0) :
    ∃ e : Cochain K L (-2), δ (-2) (-1) e = z := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let e' : Qh.obj (q.obj (L⟦(-1 : ℤ)⟧)) ≅ (Qh.obj (q.obj L))⟦(-1 : ℤ)⟧ :=
    Qh.mapIso ((q.commShiftIso (-1 : ℤ)).app L) ≪≫ (Qh.commShiftIso (-1 : ℤ)).app (q.obj L)
  have hsub : Subsingleton (q.obj K ⟶ q.obj (L⟦(-1 : ℤ)⟧)) :=
    ⟨fun a b => (Qh_map_bijective _ (L⟦(-1 : ℤ)⟧)).injective
      ((cancel_mono e'.hom).1 (h.elim _ _))⟩
  let z' : Cocycle K L (-1) := Cocycle.mk z 0 (by simp) hz
  have h0 : CohomologyClass.toHom (CohomologyClass.mk z') = 0 := hsub.elim _ _
  rwa [CohomologyClass.toHom_mk_eq_zero_iff, mem_coboundaries_iff z' (-2) (by simp)] at h0

end CochainComplex.IsKInjective

end
