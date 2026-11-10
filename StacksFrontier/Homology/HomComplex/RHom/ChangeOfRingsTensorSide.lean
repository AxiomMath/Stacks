module

public import StacksFrontier.Homology.ExtendScalars.Monoidal
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange

/-!
# The tensor side of the Hom-complex change-of-rings comparison

`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry` compares the Hom-side
change-of-rings map `Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap` along a ring
homomorphism `f : R → A` with the comparison
`Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso` of the two tensor products.  That
comparison is constructed by `CategoryTheory.Adjunction.leftAdjointUniq`, so on its own it names
the tensor side only up to the uniqueness of a left adjoint.

This file identifies it with the monoidality isomorphism
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of degreewise extension of scalars, the
chain-level map underlying the derived monoidality isomorphism
`CochainComplex.ExtendScalars.derivedMonoidalIso`.

## Main results

* `Stacks.DerivedHom.BaseChangeIso.eq_extendScalarsMonoidalIso_inv` — the summand
  characterization of the inverse monoidality isomorphism: a map
  `A ⊗_R (P ⊗_R K) ⟶ (A ⊗_R P) ⊗_A (A ⊗_R K)` of complexes that is `δ` followed by the inclusion
  of the summand on the base change of every antidiagonal inclusion *is* that inverse.
* `Stacks.DerivedHom.BaseChangeIso.extendScalars_map_ι_comp_tensorExtendScalarsIso` — the
  tensor-side comparison satisfies that characterization.
* `Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso_hom_app_eq_monoidalIso_inv` — **the
  identification**: the component of the tensor-side comparison at `P` is the inverse of the
  monoidality isomorphism of degreewise extension of scalars at `(P, K)`.
* `Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry_monoidalIso` — the
  chain-level Hom-side-versus-tensor-side comparison with the tensor side written as that
  monoidality isomorphism.

## References

* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open scoped TensorProduct

universe u

namespace Stacks.DerivedHom.BaseChangeIso

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

/-- Extension of scalars along `f` is an additive functor. -/
local instance extendScalarsAdditive : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The summand characterization of the inverse monoidality isomorphism.**  A map of complexes
`ψ : A ⊗_R (P ⊗_R K) ⟶ (A ⊗_R P) ⊗_A (A ⊗_R K)` whose composite with the base change of every
antidiagonal inclusion `P^i ⊗_R K^j ⟶ (P ⊗_R K)^n` is the module-level oplax comparison `δ` of
extension of scalars followed by the inclusion of the corresponding summand is the inverse of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso`. -/
theorem eq_extendScalarsMonoidalIso_inv
    (P K : CochainComplex (ModuleCat.{u} R) ℤ)
    (ψ : (mapCochainComplex f).obj (P ⊗ K) ⟶
      (mapCochainComplex f).obj P ⊗ (mapCochainComplex f).obj K)
    (hψ : ∀ (i j n : ℤ) (h : i + j = n),
      (ModuleCat.extendScalars.{u, u, u} f).map (HomologicalComplex.ιTensorObj P K i j n h) ≫
          ψ.f n =
        Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u} f) (P.X i) (K.X j) ≫
          HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj P)
            ((mapCochainComplex f).obj K) i j n h) :
    ψ = (extendScalarsMonoidalIso f P K).inv := by
  refine (cancel_epi (extendScalarsMonoidalIso f P K).hom).1 ?_
  rw [Iso.hom_inv_id]
  ext n : 1
  refine HomologicalComplex.mapBifunctor.hom_ext fun i j hij ↦ ?_
  change i + j = n at hij
  rw [HomologicalComplex.comp_f, ← Category.assoc,
    ι_extendScalarsMonoidalIso_hom f P K n i j hij, Category.assoc, hψ i j n hij,
    ← Category.assoc, Functor.Monoidal.μ_δ, HomologicalComplex.id_f]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **The tensor-side comparison on the base change of an antidiagonal summand.**  Extending the
inclusion `P^i ⊗_R K^j ⟶ (P ⊗_R K)^n` and following it by
`Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso` gives the module-level oplax comparison
`δ : A ⊗_R (P^i ⊗_R K^j) ⟶ (A ⊗_R P^i) ⊗_A (A ⊗_R K^j)` of extension of scalars, followed by the
inclusion of the corresponding summand of `(A ⊗_R P) ⊗_A (A ⊗_R K)`. -/
theorem extendScalars_map_ι_comp_tensorExtendScalarsIso
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (i j n : ℤ) (h : i + j = n) :
    (ModuleCat.extendScalars.{u, u, u} f).map
          (HomologicalComplex.ιTensorObj P K i j n h) ≫
        ((tensorExtendScalarsIso f K).hom.app P).f n =
      Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u} f) (P.X i) (K.X j) ≫
        HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj K) i j n h := by
  let := f.toAlgebra
  apply ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (((tensorExtendScalarsIso f K).hom.app P).f n).hom
        ((1 : A) ⊗ₜ[R] (HomologicalComplex.ιTensorObj P K i j n h).hom (x ⊗ₜ[R] y)) =
      (HomologicalComplex.ιTensorObj ((mapCochainComplex f).obj P)
          ((mapCochainComplex f).obj K) i j n h).hom
        (((1 : A) ⊗ₜ[R] x) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] y))
  exact tensorExtendScalarsIso_hom_app_f_one_tmul f P K i j n h x y

/-- **The tensor-side comparison is the monoidality isomorphism of degreewise extension of
scalars.**  The component at `P` of
`Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso` is the inverse of
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` at `(P, K)`. -/
theorem tensorExtendScalarsIso_hom_app_eq_monoidalIso_inv
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (tensorExtendScalarsIso f K).hom.app P = (extendScalarsMonoidalIso f P K).inv :=
  eq_extendScalarsMonoidalIso_inv f P K _ (extendScalars_map_ι_comp_tensorExtendScalarsIso f P K)

/-- **The chain-level Hom-side-versus-tensor-side change-of-rings comparison, with the canonical
tensor side.**  This is
`Stacks.DerivedHom.BaseChangeIso.homComplexChangeOfRingsMap_uncurry` with the tensor-side
comparison rewritten, by
`Stacks.DerivedHom.BaseChangeIso.tensorExtendScalarsIso_hom_app_eq_monoidalIso_inv`, as the
inverse monoidality isomorphism of degreewise extension of scalars. -/
theorem homComplexChangeOfRingsMap_uncurry_monoidalIso
    (P K : CochainComplex (ModuleCat.{u} R) ℤ) (J : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (q : (CochainComplex.restrictScalarsLarge.{u, u, u} f).obj J ⟶ I)
    (s : (CochainComplex.extendScalarsLarge.{u, u, u} f).obj P ⟶
      CochainComplex.HomComplexR A
        ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) :
    ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).homEquiv (P ⊗ K) J
          ((extendScalarsMonoidalIso f P K).inv ≫
            StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry s) ≫ q =
      StacksDraft.DerivedHom.DerivedInternalHom.Model.uncurry
        (((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).homEquiv P
            (CochainComplex.HomComplexR A
              ((CochainComplex.extendScalarsLarge.{u, u, u} f).obj K) J) s ≫
          Stacks.DerivedHom.BaseChange.homComplexChangeOfRingsMap f K J I q) := by
  rw [← tensorExtendScalarsIso_hom_app_eq_monoidalIso_inv f P K]
  exact homComplexChangeOfRingsMap_uncurry f P K J I q s

end Stacks.DerivedHom.BaseChangeIso

end
