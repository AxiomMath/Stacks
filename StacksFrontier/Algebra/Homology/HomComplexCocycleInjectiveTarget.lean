module

public import StacksFrontier.Algebra.Homology.DerivedCategory.InjectiveRepresents
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Cocycles into a K-injective resolution of an injective object

Let `𝒜` be an abelian category, `W` an injective object, and `ι : W[-d] ⟶ L` a quasi-isomorphism
into a K-injective complex (an injective resolution of `W` placed in degree `d`). A cocycle
`z ∈ Z^d(Hom^•(K, L))` is a morphism of complexes `z̃ : K ⟶ L[d]`. If `z̃` induces zero on `H^0`,
then `z` is a coboundary (`CochainComplex.HomComplex.mem_coboundaries_of_homologyMap_eq_zero`):
in the derived category `z̃` is a morphism `K ⟶ W[0]`, determined by its effect on `H^0` because
`W` is injective (`DerivedCategory.bijective_homologyToSingle_of_injective`), and maps into a
K-injective complex are determined in the derived category.

This is the injectivity half of `H^d(Hom^•(K, L)) ≅ Hom(H^0(K), W)`, read on cocycles; it is
used to identify the degree-`d` cohomology of the internal Hom complex into the trace target with
the dual of `H^0` in the base case of the derived Poincaré duality of Tag 03VM.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **A cocycle of degree `d` into a K-injective resolution of an injective object `W[-d]` is a
coboundary as soon as it induces zero on `H^0`.** -/
theorem mem_coboundaries_of_homologyMap_eq_zero {K L : CochainComplex C ℤ} (W : C) [Injective W]
    (d : ℤ) (ι : (CochainComplex.singleFunctor C d).obj W ⟶ L) [QuasiIso ι] [(L⟦d⟧).IsKInjective]
    (z : Cocycle K L d)
    (hz : HomologicalComplex.homologyMap (Cocycle.equivHomShift.symm z) 0 = 0) :
    z ∈ coboundaries K L d := by
  let z' : K ⟶ L⟦d⟧ := Cocycle.equivHomShift.symm z
  let ι' : (CochainComplex.singleFunctor C 0).obj W ⟶ L⟦d⟧ :=
    ((CochainComplex.singleFunctors C).shiftIso d 0 d (by omega)).inv.app W ≫ ι⟦d⟧'
  have : QuasiIso (ι⟦d⟧') := (CochainComplex.quasiIso_shift_iff ι d).2 inferInstance
  have : QuasiIso ι' := by
    have h2 : QuasiIso (((CochainComplex.singleFunctors C).shiftIso d 0 d (by omega)).inv.app W) :=
      quasiIso_of_isIso _
    exact quasiIso_comp (hφ := h2) _ _
  let f : DerivedCategory.Q.obj K ⟶ (DerivedCategory.singleFunctor C 0).obj W :=
    DerivedCategory.Q.map z' ≫ inv (DerivedCategory.Q.map ι') ≫
      (DerivedCategory.singleFunctorIsoCompQ C 0).inv.app W
  have hH : (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Q.map z') = 0 :=
    (cancel_mono _).1 ((DerivedCategory.homologyFunctorFactors_hom_naturality z' 0).trans
      ((congrArg (_ ≫ ·) hz).trans (comp_zero.trans zero_comp.symm)))
  have hf : f = 0 := by
    apply (DerivedCategory.bijective_homologyToSingle_of_injective _ W 0).1
    rw [map_zero, DerivedCategory.homologyToSingle_apply]
    simp only [f, Functor.map_comp, hH, zero_comp]
  have hQ : DerivedCategory.Q.map z' = 0 := by
    simpa [f] using congrArg (· ≫ (DerivedCategory.singleFunctorIsoCompQ C 0).hom.app W ≫
      DerivedCategory.Q.map ι') hf
  have hq : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map z' = 0 := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C _).obj K) (L⟦d⟧)).1
    rw [Functor.map_zero]
    have h := (DerivedCategory.quotientCompQhIso C).hom.naturality z'
    rw [hQ, comp_zero] at h
    change (HomotopyCategory.quotient C _ ⋙ DerivedCategory.Qh).map z' = 0
    exact (cancel_mono _).1 (h.trans zero_comp.symm)
  rwa [← CohomologyClass.toHom_mk_eq_zero_iff, CohomologyClass.toHom_mk]

end CochainComplex.HomComplex
