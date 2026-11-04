module

public import StacksFrontier.Algebra.Homology.KFlat

/-!
# K-flatness transports along an isomorphism of complexes

A cochain complex of `R`-modules isomorphic to a K-flat one is K-flat.

## Main results

* `CochainComplex.KFlat.of_iso`: K-flatness transports along an isomorphism of complexes.

## References

* [Stacks Project, Tag 06XZ](https://stacks.math.columbia.edu/tag/06XZ)
-/
open CategoryTheory

@[expose] public section

universe u v

/-- If `K ≅ L` is an isomorphism of cochain complexes of `R`-modules and `K` is K-flat, then `L`
is K-flat. -/
theorem CochainComplex.KFlat.of_iso {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{max u v} R) ℤ} (e : K ≅ L)
    (hK : CochainComplex.KFlat.{u, v} K) : CochainComplex.KFlat.{u, v} L := by
  let _ := ModuleCat.liftedModuleMonoidalStruct.{u, v} (R := R)
  let _ := ModuleCat.liftedModuleMonoidal.{u, v} (R := R)
  exact fun M hM ↦ HomologicalComplex.Acyclic.of_iso
    (((((MonoidalCategory.curriedTensor (ModuleCat.{max u v} R)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj M) ⋙
      HomologicalComplex₂.totalFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso e) (hK M hM)

end
