module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensor

/-!
# Vanishing of a derived tensor product from the action of a scalar

Let `A` be a commutative ring and let `x : A`. If `x` acts invertibly on an object `K` of the
derived category of `A`-modules and acts as zero on an object `L`, then `K ⊗^L_A L = 0`: the
scalar acts on the derived tensor product both invertibly and as zero.

The application is the vanishing of `N ⊗^L_A A/I` for an `A`-module `N` on which some element of
`I` acts invertibly — a localization `N_x` with `x ∈ I`, for instance. Every `Tor_i^A(N, A/I)`
then vanishes, not only the ordinary tensor product.

## Main results

* `Stacks.DerivedTensor.map_smul_id_right`, `Stacks.DerivedTensor.map_smul_id_left`: a scalar
  multiple of the identity is carried to the same scalar multiple of the identity by the derived
  tensor product in either variable.
* `Stacks.DerivedTensor.isZero_derivedTensor_of_isIso_smul`: the vanishing criterion in the
  derived category.
* `Stacks.DerivedTensor.isZero_derivedTensor_single_quotient_of_isUnit`: for modules, the
  vanishing of `N[0] ⊗^L_A (A ⧸ I)[0]` when some element of `I` acts invertibly on `N`.

## Implementation notes

Linearity in the second variable is read off the characterization of the canonical derived tensor
product of [Stacks, Tag 0BYI] on K-flat representatives, where the tensor product of the identity
with a scalar multiple of the identity is computed termwise. Linearity in the first variable is
then obtained from the commutativity isomorphism, which is central for the scalar action because
the derived category of `A`-modules is `A`-linear.

An object on which some endomorphism is simultaneously invertible and zero is a zero object,
since then the zero endomorphism is an isomorphism and the identity is zero.

## References

* [Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.DerivedTensor

universe u

namespace Stacks.DerivedTensor

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- Scalars act on a derived tensor product through the second variable as they act on the
object. -/
theorem map_smul_id_right (K L : DerivedCategory (ModuleCat.{u} A)) (a : A) :
    ((canonicalDerivedTensorProductFunctor A).obj K).map (a • 𝟙 L) =
      a • 𝟙 (((canonicalDerivedTensorProductFunctor A).obj K).obj L) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative K
  obtain ⟨Q, hQ, ⟨eQ⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative L
  let T := canonicalDerivedTensorProduct A
  change (T.tensor.obj K).map (a • 𝟙 L) = a • 𝟙 ((T.tensor.obj K).obj L)
  have hPQ : (T.tensor.obj (DerivedCategory.Q.obj P)).map
      (a • 𝟙 (DerivedCategory.Q.obj Q)) =
        a • 𝟙 ((T.tensor.obj (DerivedCategory.Q.obj P)).obj (DerivedCategory.Q.obj Q)) := by
    have h := T.comparison_naturality (𝟙 P) (a • 𝟙 Q) hP hP hQ hQ
    simp only [Functor.map_smul, DerivedCategory.Q.map_id, T.tensor.map_id, NatTrans.id_app,
      Category.id_comp] at h
    rw [← cancel_mono (T.comparison P Q hP hQ).hom, h]
    have ht : HomologicalComplex.tensorHom (𝟙 P) (a • 𝟙 Q) =
        a • 𝟙 (MonoidalCategory.tensorObj P Q) := by
      ext1 n
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro i j hij
      simp only [curriedTensor_obj_obj, HomologicalComplex.ι_mapBifunctorMap,
        HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
        HomologicalComplex.smul_f_apply, curriedTensor_obj_map,
        MonoidalLinear.whiskerLeft_smul, whiskerLeft_id, Linear.smul_comp, Category.id_comp,
        Linear.comp_smul]
      exact (Category.comp_id _).symm
    rw [ht, Functor.map_smul, DerivedCategory.Q.map_id]
    simp
  have hQ' : (T.tensor.obj (DerivedCategory.Q.obj P)).map (a • 𝟙 L) =
      a • 𝟙 ((T.tensor.obj (DerivedCategory.Q.obj P)).obj L) := by
    rw [← cancel_epi ((T.tensor.obj (DerivedCategory.Q.obj P)).map eQ.hom),
      ← Functor.map_comp]
    simp only [Linear.comp_smul, Category.comp_id]
    rw [show a • eQ.hom = (a • 𝟙 _) ≫ eQ.hom by simp, Functor.map_comp, hPQ]
    simp
  have hnat := (T.tensor.map eP.hom).naturality (a • 𝟙 L)
  rw [← cancel_epi ((T.tensor.mapIso eP).app L).hom]
  dsimp
  rw [← hnat, hQ']
  simp

/-- Scalars act on a derived tensor product through the first variable as they act on the
object. -/
theorem map_smul_id_left (K L : DerivedCategory (ModuleCat.{u} A)) (a : A) :
    ((canonicalDerivedTensorProductFunctor A).map (a • 𝟙 K)).app L =
      a • 𝟙 (((canonicalDerivedTensorProductFunctor A).obj K).obj L) := by
  have hnat := NatTrans.congr_app
    ((derivedTensorProductKoszulBraiding A).iso.hom.naturality (a • 𝟙 K)) L
  simp only [NatTrans.comp_app] at hnat
  rw [show ((canonicalDerivedTensorProductFunctor A).flip.map (a • 𝟙 K)).app L =
      ((canonicalDerivedTensorProductFunctor A).obj L).map (a • 𝟙 K) from rfl,
    map_smul_id_right A L K a] at hnat
  refine (cancel_mono (((derivedTensorProductKoszulBraiding A).iso.hom.app K).app L)).mp ?_
  rw [hnat]
  simp

/-- An object carrying an endomorphism which is both an isomorphism and zero is a zero object. -/
theorem isZero_of_isIso_zero {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {X : C} {f : X ⟶ X} (hiso : IsIso f) (hzero : f = 0) : IsZero X := by
  have h : (0 : X ⟶ X) ≫ @inv _ _ _ _ f hiso = 𝟙 X := by
    rw [← hzero]
    exact IsIso.hom_inv_id f
  rw [IsZero.iff_id_eq_zero, ← h, zero_comp]

/-- A derived tensor product on which a scalar acts both invertibly and as zero vanishes:
if `x : A` acts invertibly on `K` and as zero on `L`, then `K ⊗^L_A L = 0`. -/
theorem isZero_derivedTensor_of_isIso_smul (x : A) (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : IsIso (x • 𝟙 K)) (hL : x • 𝟙 L = 0) :
    IsZero (((canonicalDerivedTensorProductFunctor A).obj K).obj L) := by
  refine isZero_of_isIso_zero (f := x • 𝟙 (((canonicalDerivedTensorProductFunctor A).obj K).obj L))
    ?_ ?_
  · rw [← map_smul_id_left A K L x]
    infer_instance
  · rw [← map_smul_id_right A K L x, hL, Functor.map_zero]

/-- Multiplication by a scalar whose image is a unit of an `A`-algebra is an isomorphism of the
algebra viewed as an `A`-module. -/
theorem isIso_smul_id_of_isUnit_algebraMap (B : Type u) [CommRing B] [Algebra A B] {x : A}
    (hx : IsUnit (algebraMap A B x)) : IsIso (x • 𝟙 (ModuleCat.of A B)) := by
  obtain ⟨v, hv⟩ := hx
  refine ⟨ModuleCat.ofHom (LinearMap.mulLeft A (↑v⁻¹ : B)), ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext b
    change (↑v⁻¹ : B) * (x • b) = b
    rw [Algebra.smul_def, ← hv, ← mul_assoc, v.inv_mul, one_mul]
  · apply ModuleCat.hom_ext
    ext b
    change x • ((↑v⁻¹ : B) * b) = b
    rw [Algebra.smul_def, ← hv, ← mul_assoc, v.mul_inv, one_mul]

/-- A scalar multiple of the identity of a module placed in degree zero is the image of the
scalar multiple of the identity of the module. -/
private theorem smul_id_single_obj (M : ModuleCat.{u} A) (x : A) :
    x • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (x • 𝟙 M) := by
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]

/-- A scalar annihilating a module acts as zero on the module placed in degree zero of the
derived category. -/
theorem smul_id_single_eq_zero (M : ModuleCat.{u} A) {x : A} (hx : ∀ m : M, x • m = 0) :
    x • 𝟙 ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) = 0 := by
  have hM : x • 𝟙 M = 0 := by
    ext m
    exact hx m
  rw [smul_id_single_obj, hM, CategoryTheory.Functor.map_zero]

/-- The derived tensor product of a module with the quotient by an ideal vanishes as soon as
some element of the ideal acts invertibly on the module. Every `Tor_i^A(N, A ⧸ I)` vanishes, not
only the ordinary tensor product. -/
theorem isZero_derivedTensor_single_quotient_of_isUnit (I : Ideal A) (N : ModuleCat.{u} A) {x : A}
    (hxI : x ∈ I) (hx : IsIso (x • 𝟙 N)) :
    IsZero (((canonicalDerivedTensorProductFunctor A).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj N)).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ I)))) := by
  refine isZero_derivedTensor_of_isIso_smul A x _ _ ?_ ?_
  · rw [smul_id_single_obj]
    infer_instance
  · refine smul_id_single_eq_zero A _ fun m => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    exact (Submodule.Quotient.eq _).mpr (by simpa using I.mul_mem_right y hxI)

end Stacks.DerivedTensor

end
