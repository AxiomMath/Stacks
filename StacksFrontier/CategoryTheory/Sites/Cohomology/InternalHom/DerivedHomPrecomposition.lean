module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomTriangulated
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrying
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison

/-!
# Precomposition with a map inverted by derived internal Hom

Let `(𝒞, 𝒪)` be a ringed site and `Y` an object of `D(𝒪)`. If a map `t : A ⟶ B` of `D(𝒪)` is
inverted by `R𝑆heafHom_𝒪(-, Y)`, then precomposition with `t` is a bijection
`Hom(B, Y) ≃ Hom(A, Y)`.

## Main results

* `AlgebraicGeometry.RingedSite.subsingleton_hom_of_isZero_derivedSheafHom`: `Hom(Z, Y)` is
  trivial when `R𝑆heafHom_𝒪(Z, Y)` is zero.
* `AlgebraicGeometry.RingedSite.bijective_precomp_of_isIso_derivedSheafHom_map`: the statement
  above.

## Implementation notes

Morphisms `Z ⟶ Y` are recovered from `R𝑆heafHom_𝒪(Z, Y)` by the tensor–internal-Hom bijection
of [Stacks, Tag 08J8] at the unit `𝒪`, together with the left unit constraint of the derived
tensor product, rather than through global sections, so that no property of derived global
sections is used. The passage from one map to a bijection is the triangulated structure: the
contravariant half of [Stacks, Tag 08JC]
(`AlgebraicGeometry.RingedSite.exists_distinguished_derivedSheafHom`) applied to a triangle on
`t` and to its inverse rotation.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JC](https://stacks.math.columbia.edu/tag/08JC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Pretriangulated

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **A vanishing derived internal Hom leaves no non-zero morphism.** If
`R𝑆heafHom_𝒪(Z, Y) = 0` then `Z ⟶ Y` has at most one element: by [Stacks, Tag 08J8] the
morphisms `𝒪 ⊗^𝐋_𝒪 Z ⟶ Y` are the morphisms `𝒪 ⟶ R𝑆heafHom_𝒪(Z, Y)`, and `𝒪 ⊗^𝐋_𝒪 Z ≅ Z`. -/
theorem subsingleton_hom_of_isZero_derivedSheafHom
    (Z Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : IsZero (((derivedSheafHomBifunctor X).obj (op Z)).obj Y)) :
    Subsingleton (Z ⟶ Y) := by
  refine ⟨fun a b => ?_⟩
  have hs : Subsingleton (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
      (Stacks.DerivedTensor.RingedSite.unitObject X)).obj Z ⟶ Y) :=
    ⟨fun _ _ => (derivedCurryHomEquiv X _ Z Y).symm.injective (h.eq_of_tgt _ _)⟩
  exact (cancel_epi ((derivedTensorProductDatumOfSite X
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)).leftUnitIso X Z).hom).mp
    (hs.elim _ _)

/-- **Precomposition with a map is bijective on morphisms into `Y` once `R𝑆heafHom(-, Y)`
inverts it.** Complete `t : A ⟶ B` to a distinguished triangle `A ⟶ B ⟶ C ⟶ A⟦1⟧`. By
[Stacks, Tag 08JC] in the contravariant variable `R𝑆heafHom(-, Y)` carries it and its inverse
rotation to distinguished triangles in which `R𝑆heafHom(t, Y)` is one of the maps, so
`R𝑆heafHom(C, Y)` and `R𝑆heafHom(C⟦-1⟧, Y)` vanish. Hence `C ⟶ Y` and `C⟦-1⟧ ⟶ Y` are trivial,
and the two exact sequences of morphism groups attached to the triangles make precomposition
with `t` injective and surjective. -/
theorem bijective_precomp_of_isIso_derivedSheafHom_map
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (t : A ⟶ B)
    (Y : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (ht : IsIso (((derivedSheafHomBifunctor X).map t.op).app Y)) :
    Function.Bijective (fun g : B ⟶ Y => t ≫ g) := by
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle t
  obtain ⟨δ, hδ⟩ := exists_distinguished_derivedSheafHom X Y _ hT
  have hC : IsZero (((derivedSheafHomBifunctor X).obj (op C)).obj Y) :=
    (Triangle.isZero₁_iff_isIso₂ _ hδ).mpr ht
  have hT' := inv_rot_of_distTriang _ hT
  obtain ⟨δ', hδ'⟩ := exists_distinguished_derivedSheafHom X Y _ hT'
  have hC' : IsZero (((derivedSheafHomBifunctor X).obj (op (C⟦(-1 : ℤ)⟧))).obj Y) :=
    (Triangle.isZero₃_iff_isIso₁ _ hδ').mpr ht
  have sC := subsingleton_hom_of_isZero_derivedSheafHom X C Y hC
  have sC' := subsingleton_hom_of_isZero_derivedSheafHom X _ Y hC'
  refine ⟨fun g₁ g₂ hg => ?_, fun a => ?_⟩
  · obtain ⟨c, hc⟩ := Triangle.yoneda_exact₂ _ hT (g₁ - g₂)
      ((Preadditive.comp_sub _ _ _).trans (sub_eq_zero.mpr hg))
    rw [sC.elim c 0, comp_zero] at hc
    exact sub_eq_zero.mp hc
  · obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ hT' a (sC'.elim _ _)
    exact ⟨g, hg.symm⟩

end AlgebraicGeometry.RingedSite

end
