module

public import StacksFrontier.Homology.ExtendScalars.Monoidal
public import StacksFrontier.Homology.Tor.BaseChangeTensorIso

/-!
# The tensor base-change isomorphism of [stacks 068I] is the monoidality isomorphism

Two chain-level comparisons of the two tensor products across degreewise extension of scalars
along `f : R →+* A` occur in this library.

* `CochainComplex.DerivedTensor.IsTensorBaseChangeIso` is the *property* of an isomorphism
  `(A ⊗_R K) ⊗_A (A ⊗_R L) ≅ A ⊗_R (K ⊗_R L)` of total complexes of being the standard one:
  on every antidiagonal summand it is the inverse of
  `TensorProduct.AlgebraTensorModule.distribBaseChange`.  It is the shape in which the
  monoidality isomorphism of [stacks 068I] is presented by
  `CochainComplex.DerivedTensor.DerivedExtensionScalarsTensorIso.comparison`, hence by
  `Dualizing.tensorBaseChangeMor_comp_eq_q_obj`, which evaluates the [stacks 068I] candidate for
  the lax monoidal structure map of derived base change at a pair of K-flat complexes.
* `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` is the monoidality isomorphism of
  degreewise extension of scalars, characterized on the antidiagonal summand of bidegree `(i, j)`
  by `CochainComplex.ExtendScalars.ι_extendScalarsMonoidalIso_hom` as the module-level lax
  comparison `μ` of `ModuleCat.extendScalars` followed by the base change of the inclusion of the
  summand.  It is the comparison the *Hom* side of the keystone is written in: it is the tensor
  factor of `Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap`, the closed form
  of the chain-level map underlying the change-of-rings isomorphism of [stacks 0E1W].

This file identifies them.  The two summand characterizations differ only in naming the
module-level comparison: `TensorProduct.AlgebraTensorModule.distribBaseChange R A M N` inverted
against `Functor.LaxMonoidal.μ (ModuleCat.extendScalars f) M N`.  Both are the map
`(a ⊗ x) ⊗ (b ⊗ y) ↦ ab ⊗ (x ⊗ y)`, and the identification is settled on pure tensors through the
oplax comparison `δ`, whose value `ModuleCat.extendScalars_δ_tmul` is `1 ⊗ (x ⊗ y) ↦ (1 ⊗ x) ⊗
(1 ⊗ y)`.

Since the summand formula determines the comparison, this makes the [stacks 068I] chain-level
tensor base change *equal* to the monoidality isomorphism rather than merely isomorphic to it, so
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_naturality` — naturality of the
monoidality isomorphism in both complexes — becomes available about the [stacks 068I] side.

**What is not done here.**  The keystone equation of
`Dualizing.tensorBaseChangeMor_eq_iff` is not proved and no caveat is lifted: this removes a
vocabulary gap on the tensor side only.

## Main results

* `CochainComplex.DerivedTensor.extendScalars_delta_eq` and
  `CochainComplex.DerivedTensor.extendScalars_mu_eq` — the oplax and lax module-level
  comparisons of `ModuleCat.extendScalars` are
  `TensorProduct.AlgebraTensorModule.distribBaseChange` and its inverse.
* `CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq` — **the summand formula determines
  the comparison**: two isomorphisms of total complexes that are both standard are equal.  This
  holds at independent universes for the two rings.
* `CochainComplex.DerivedTensor.isTensorBaseChangeIso_extendScalarsMonoidalIso` — **the
  monoidality isomorphism is standard**.
* `CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom` —
  **the identification**: every standard tensor base-change isomorphism of total complexes is the
  monoidality isomorphism of degreewise extension of scalars.

## Implementation notes

`CochainComplex.ExtendScalars.extendScalarsMonoidalIso` is stated for two rings in *one*
universe, with their modules in that universe too, so the identification is available only there.
That is not a restriction where it is wanted: the Hom side of the keystone lives in the
scalar-lift world of [stacks 0E1W], where `ULift R` and `ULift A` and all their modules share one
universe.  The uniqueness statement `CochainComplex.DerivedTensor.IsTensorBaseChangeIso.hom_eq`
needs no monoidality isomorphism and is therefore stated at independent universes, which is where
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` produces its comparison.

`TensorProduct.AlgebraTensorModule.distribBaseChange` asks for an `Algebra R A`, which the
definition of `CochainComplex.DerivedTensor.IsTensorBaseChangeIso` supplies from the ring
homomorphism by `RingHom.toAlgebra`; the two element-level statements therefore carry that
instance in a `letI` in their statements, exactly as that definition does.

No `@[stacks]` attribute is placed here: this is an identification of two constructions, and
covers no tag.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.ExtendScalars
open scoped TensorProduct

universe u

namespace CochainComplex.DerivedTensor

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)

local instance extendScalarsAdditive' : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
  (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).left_adjoint_additive

/-- **The oplax comparison of extension of scalars is `distribBaseChange`.**  The map
`δ : A ⊗_R (M ⊗_R N) ⟶ (A ⊗_R M) ⊗_A (A ⊗_R N)` of `ModuleCat.extendScalars` is the base-change
distributivity isomorphism of `TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
theorem extendScalars_delta_eq (M N : ModuleCat.{u} R) :
    letI := f.toAlgebra
    Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u} f) M N =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).toModuleIso.hom := by
  let := f.toAlgebra
  exact ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).homEquiv _ _).injective
    (ModuleCat.hom_ext (TensorProduct.ext' (ModuleCat.extendScalars_δ_tmul f M N)))

/-- **The lax comparison of extension of scalars is the inverse of `distribBaseChange`.**  The
map `μ : (A ⊗_R M) ⊗_A (A ⊗_R N) ⟶ A ⊗_R (M ⊗_R N)` of `ModuleCat.extendScalars` is the inverse
of the base-change distributivity isomorphism. -/
theorem extendScalars_mu_eq (M N : ModuleCat.{u} R) :
    letI := f.toAlgebra
    Functor.LaxMonoidal.μ (ModuleCat.extendScalars.{u, u, u} f) M N =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toModuleIso.hom := by
  let := f.toAlgebra
  refine (cancel_mono (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars.{u, u, u} f) M N)).mp
    ((Functor.Monoidal.μ_δ _ _ _).trans ?_)
  rw [extendScalars_delta_eq f M N]
  exact ModuleCat.hom_ext (LinearMap.ext fun z =>
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).apply_symm_apply z).symm)

section Uniqueness

universe uR uA v

/-- **The summand formula determines the comparison.**  Two isomorphisms of total complexes
`(A ⊗_R K) ⊗_A (A ⊗_R L) ≅ A ⊗_R (K ⊗_R L)` that are both the standard tensor base change in the
sense of `CochainComplex.DerivedTensor.IsTensorBaseChangeIso` are equal. -/
theorem IsTensorBaseChangeIso.hom_eq {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    (g : R →+* A) (K L : CochainComplex (ModuleCat.{max uR uA v} R) ℤ)
    {e e' : tensorComplex.{uA, max uR v} ((extensionOfScalarsCochain.{uR, uA, v} g).obj K)
        ((extensionOfScalarsCochain.{uR, uA, v} g).obj L) ≅
      (extensionOfScalarsCochain.{uR, uA, v} g).obj (tensorComplex.{uR, max uA v} K L)}
    (he : IsTensorBaseChangeIso.{uR, uA, v} g K L e)
    (he' : IsTensorBaseChangeIso.{uR, uA, v} g K L e') :
    e.hom = e'.hom := by
  refine HomologicalComplex.hom_ext _ _ fun n => HomologicalComplex.mapBifunctor.hom_ext ?_
  intro p q h
  rw [he p q n h, he' p q n h]

end Uniqueness

/-- **The monoidality isomorphism of degreewise extension of scalars is the standard tensor
base-change isomorphism**, in the sense of
`CochainComplex.DerivedTensor.IsTensorBaseChangeIso`. -/
theorem isTensorBaseChangeIso_extendScalarsMonoidalIso
    (K L : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsTensorBaseChangeIso.{u, u, u} f K L (extendScalarsMonoidalIso f K L) := by
  intro p q n h
  rw [← extendScalars_mu_eq f (K.X p) (L.X q)]
  exact ι_extendScalarsMonoidalIso_hom f K L n p q h

/-- **The identification of the two chain-level tensor comparisons.**  Every standard tensor
base-change isomorphism of total complexes — in particular the one
`CochainComplex.DerivedTensor.DerivedExtensionScalarsTensorIso.comparison` supplies to
`Dualizing.tensorBaseChangeMor_comp_eq_q_obj` for the [stacks 068I] candidate — is the
monoidality isomorphism `CochainComplex.ExtendScalars.extendScalarsMonoidalIso` of degreewise
extension of scalars, which is the comparison the chain-level formula
`Stacks.DerivedHom.BaseChangeIso.uncurry_homComplexChangeOfRingsMap` of the Hom side of
[stacks 0E1W] is written in.

Being an equality of morphisms and not an isomorphism of the two, it makes
`CochainComplex.ExtendScalars.extendScalarsMonoidalIso_naturality` available about the
[stacks 068I] side. -/
theorem IsTensorBaseChangeIso.hom_eq_extendScalarsMonoidalIso_hom
    (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    {e : tensorComplex.{u, u} ((extensionOfScalarsCochain.{u, u, u} f).obj K)
        ((extensionOfScalarsCochain.{u, u, u} f).obj L) ≅
      (extensionOfScalarsCochain.{u, u, u} f).obj (tensorComplex.{u, u} K L)}
    (he : IsTensorBaseChangeIso.{u, u, u} f K L e) :
    e.hom = (extendScalarsMonoidalIso f K L).hom :=
  IsTensorBaseChangeIso.hom_eq.{u, u, u} f K L he
    (isTensorBaseChangeIso_extendScalarsMonoidalIso f K L)

end CochainComplex.DerivedTensor

end
