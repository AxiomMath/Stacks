module

public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.Basic
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.Uniqueness

/-!
# The third term of the localization triangle is a derived tensor product

Let `J = (f₁, …, f_r)` be a finitely generated ideal of a commutative ring `A` and let `V` be
`Spec A ∖ V(J)`. Local cohomology `RΓ_{V(J)}` is the derived tensor product with the extended
alternating Čech complex `C(f)` of the ring (Stacks 0A6R,
`Stacks.LocalCohomology.CechFormula.localCohomologyCechIso`). This file records the companion
statement for the third term of the localization triangle of Stacks 0DWR: derived sections on `V`
are, as a functor of the module, the derived tensor product with one fixed object `C'` of `D(A)`,
a cone of the Čech augmentation `C(f) ⟶ A`.

## Main results

* `Stacks.LocalCohomology.exists_complementIso_tensor` — for every
  `Stacks.LocalCohomology.LocalizationTriangleData` `D` of `J` there is an object `C'` of `D(A)`
  with `D.complement ≅ (- [0]) ⋙ (C' ⊗ᴸ -)`.

## Implementation notes

Complete the Čech augmentation `ε : C(f) ⟶ A` to a distinguished triangle
`C(f) ⟶ A ⟶ C' ⟶ C(f)[1]`. Tensoring with `M[0]` is exact in the first variable, so
`C(f) ⊗ᴸ M ⟶ A ⊗ᴸ M ⟶ C' ⊗ᴸ M ⟶` is distinguished, and the normalization of the Čech formula
identifies its first map with the counit `RΓ_{V(J)}(M) ⟶ M[0]`. The third terms of two
distinguished triangles on the same first map are isomorphic; the isomorphism is pinned down by
its composite with the restriction, because the third term of a localization triangle is
`J`-local (`Stacks.LocalCohomology.hom_ext_of_restriction_comp`), and that is what makes the
pointwise isomorphisms natural.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.LocalCohomology

variable {A : Type u} [CommRing A] {J : Ideal A} {hJ : J.FG}

/-- **Derived sections on `Spec A ∖ V(J)` are a derived tensor product.** For a localization
triangle datum `D` of `J = (f₁, …, f_r)` there is an object `C'` of `D(A)` — a cone of the Čech
augmentation `C(f) ⟶ A` — such that `D.complement` is naturally isomorphic to
`M ↦ C' ⊗ᴸ M[0]`. -/
theorem exists_complementIso_tensor {r : ℕ} (f : Fin r → A)
    (hf : Ideal.span (Set.range f) = J) (D : LocalizationTriangleData.{u, u} A J hJ) :
    ∃ C : DerivedCategory (ModuleCat.{u} A),
      Nonempty (D.complement ≅ DerivedCategory.singleFunctor (ModuleCat.{u} A) 0 ⋙
        (canonicalDerivedTensorProduct A).tensor.obj C) := by
  obtain ⟨C, g, h, hdist⟩ := distinguished_cocone_triangle (CechFormula.cechAugmentation A f)
  have key : ∀ M : ModuleCat.{u} A, ∃ c : D.complement.obj M ≅
      ((canonicalDerivedTensorProduct A).tensor.obj C).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M),
      D.restriction.app M ≫ c.hom =
        (CechFormula.derivedTensorLeftUnitor A).inv.app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≫
          ((canonicalDerivedTensorProduct A).tensor.map g).app
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) := by
    intro M
    let X := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
    let Φ := (canonicalDerivedTensorProduct A).tensor.flip.obj X
    let := (canonicalDerivedTensorProduct A).commShift_left X
    have := (canonicalDerivedTensorProduct A).exact_left X
    have hmap := Φ.map_distinguished _ hdist
    have hcounit := congrArg (fun φ => φ.app X)
      (CechFormula.localCohomologyCechIso_comp_augmentation A J hJ f hf)
    simp only [CechFormula.cechTensorToId, NatTrans.comp_app] at hcounit
    let T₀ := Φ.mapTriangle.obj (Triangle.mk (CechFormula.cechAugmentation A f) g h)
    have comm : (D.triangle M).mor₁ ≫ (CechFormula.derivedTensorLeftUnitor A).inv.app X =
        (CechFormula.localCohomologyCechIso A J hJ f hf).hom.app X ≫ T₀.mor₁ := by
      change (Dualizing.localCohomologyAdjunction A J hJ).counit.app X ≫ _ = _
      refine ((CechFormula.derivedTensorLeftUnitor A).app X).comp_inv_eq.2 ?_
      exact hcounit.symm.trans (Category.assoc _ _ _).symm
    obtain ⟨c, hc₁, hc₂⟩ := complete_distinguished_triangle_morphism (D.triangle M) T₀
      (D.distinguished M) hmap _ _ comm
    have hiso : IsIso c := isIso₃_of_isIso₁₂
      (Triangle.homMk (D.triangle M) T₀ _ _ c comm hc₁ hc₂) (D.distinguished M) hmap
      (inferInstanceAs (IsIso ((CechFormula.localCohomologyCechIso A J hJ f hf).hom.app X)))
      (inferInstanceAs (IsIso ((CechFormula.derivedTensorLeftUnitor A).inv.app X)))
    exact ⟨@asIso _ _ _ _ c hiso, hc₁⟩
  choose c hc using key
  have hZ : ∀ N : ModuleCat.{u} A, (Dualizing.derivedPowerTorsionProperty A J hJ).rightOrthogonal
      (((canonicalDerivedTensorProduct A).tensor.obj C).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)) := fun N W φ hW => by
    rw [← Category.comp_id φ, ← (c N).inv_hom_id, ← Category.assoc,
      rightOrthogonal_complement D N (φ ≫ (c N).inv) hW, zero_comp]
  refine ⟨C, ⟨NatIso.ofComponents c fun {M N} φ => ?_⟩⟩
  refine hom_ext_of_restriction_comp D M (hZ N) ?_
  rw [← Category.assoc, ← D.restriction.naturality φ, Category.assoc, hc N,
    ← Category.assoc (D.restriction.app M), hc M]
  have h₁ := (CechFormula.derivedTensorLeftUnitor A).inv.naturality
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map φ)
  have h₂ := ((canonicalDerivedTensorProduct A).tensor.map g).naturality
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map φ)
  simp only [Functor.id_obj, Functor.id_map] at h₁ h₂
  simp only [Functor.comp_map, Category.assoc]
  rw [← h₂, reassoc_of% h₁]

end Stacks.LocalCohomology

end
