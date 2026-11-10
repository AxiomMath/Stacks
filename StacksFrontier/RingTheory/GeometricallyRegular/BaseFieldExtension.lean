module

import Mathlib.FieldTheory.PurelyInseparable.Tower
import Mathlib.Data.Finset.Functor
import Mathlib.RingTheory.RingHom.Etale

public import StacksFrontier.RingTheory.GeometricallyRegular.Smooth
public import StacksFrontier.RingTheory.GeometricallyRegular.Colimit
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v w

/-!
# Geometric regularity is insensitive to a separable algebraic base field

Let `k'/k` be a separable algebraic field extension and let `A` be a `k'`-algebra, viewed as a
`k`-algebra by restriction of scalars. Then `A` is geometrically regular over `k` if and only if
it is geometrically regular over `k'`.

## Main results

* `Stacks.GeometricallyRegular.SeparableBase.isRegularRing_tensorProduct`: if `A` is
  geometrically regular over `k`, then `R ⊗[k] A` is a regular ring for every essentially finite
  type `k`-algebra `R` which is a field, in any universe.
* `Stacks.GeometricallyRegular.SeparableBase.isGeometricallyRegular_tensorProduct`: geometric
  regularity is preserved by base change to a finitely generated extension field.
* `Algebra.isGeometricallyRegular_iff_tower_top_of_isSeparable`: for a separable algebraic
  extension `k'/k` and a `k'`-algebra `A`, geometric regularity of `A` over `k` is equivalent to
  geometric regularity of `A` over `k'`.
* `Stacks.FormalFibres.exists_tensorProduct_ringEquiv` and
  `Stacks.FormalFibres.exists_fiber_ringEquiv`: tensor products and fibres at a prime are carried
  along compatible ring isomorphisms.

## References

* [StacksProject 07QH](https://stacks.math.columbia.edu/tag/07QH)
* [StacksProject 0382](https://stacks.math.columbia.edu/tag/0382)
* [StacksProject 0381](https://stacks.math.columbia.edu/tag/0381)
* [StacksProject 07QG](https://stacks.math.columbia.edu/tag/07QG)
* [StacksProject 07QF](https://stacks.math.columbia.edu/tag/07QF)
* [StacksProject 00U2](https://stacks.math.columbia.edu/tag/00U2)
-/

namespace Stacks.GeometricallyRegular.SeparableBase



open scoped TensorProduct

/-- The tensor product over `k` of a separable algebraic extension `k'/k` and a purely inseparable
extension `L/k` is a field. -/
@[ega "IV 6.7.4.1" "special case", ega "IV 6.7.6" "special case", sga "1 XIII 2.0.2" "special case"]
private theorem isField_tensorProduct (k : Type u) (k' : Type v) (L : Type w) [Field k] [Field k']
    [Field L] [Algebra k k'] [Algebra k L] [Algebra.IsSeparable k k']
    [IsPurelyInseparable k L] : IsField (k' ⊗[k] L) := by
  refine IntermediateField.LinearDisjoint.isField_of_forall k k' L fun K _ _ fa fb ↦ ?_
  have : Algebra.IsSeparable k ↥fa.fieldRange := AlgEquiv.Algebra.isSeparable fa.equivFieldRange
  have : IsPurelyInseparable k ↥fb.fieldRange := fb.equivFieldRange.isPurelyInseparable
  exact IntermediateField.linearDisjoint_of_isPurelyInseparable_of_isSeparable _ _

/-- A finite separable field extension is étale. -/
private theorem etale_of_isSeparable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K] [Module.Finite k K] : Algebra.Etale k K := by
  rw [Algebra.etale_iff]
  exact ⟨Algebra.FormallyEtale.of_isSeparable k K,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- If `S` is an étale `R`-algebra and `A` is an `S`-algebra, the map `S ⊗[R] A → A`,
`s ⊗ a ↦ s • a`, is étale. -/
private theorem etale_productMap (R : Type u) (S : Type v) (A : Type w) [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra R A] [Algebra S A] [IsScalarTower R S A]
    [Algebra.Etale R S] :
    RingHom.Etale (Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R S A)
      (AlgHom.id R A)).toRingHom := by
  let mul : (S ⊗[R] A) →ₐ[R] A :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom R S A) (AlgHom.id R A)
  let _algRight : Algebra A (S ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _algMul : Algebra (S ⊗[R] A) A := mul.toRingHom.toAlgebra
  have : Algebra.Etale A (S ⊗[R] A) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofRingEquiv
      (f := (Algebra.TensorProduct.comm R A S).toRingEquiv)
      (fun a ↦ by change (Algebra.TensorProduct.comm R A S) (a ⊗ₜ 1) = 1 ⊗ₜ a; simp))
  have : IsScalarTower A (S ⊗[R] A) A := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change x = mul (1 ⊗ₜ x)
    simp [mul]
  exact Algebra.Etale.of_restrictScalars A (S ⊗[R] A) A

/-- If `A` is geometrically regular over `k`, then `R ⊗[k] A` is a regular ring for every
essentially finite type `k`-algebra `R` which is a field, in any universe. -/
@[ega "0 22.5.8" "b) ⇒ b')"]
theorem isRegularRing_tensorProduct (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.IsGeometricallyRegular k A] (R : Type w) [CommRing R] [Algebra k R]
    [Algebra.EssFiniteType k R] (hR : IsField R) : IsRegularRing (R ⊗[k] A) := by
  let _fieldR : Field R := hR.toField
  refine (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
    k A).mpr (fun L _ _ _ _ ↦ ?_) R
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  let f : L →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  have : Module.Finite k ↥f.fieldRange := Module.Finite.equiv f.equivFieldRange.toLinearEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.congr f.equivFieldRange.symm AlgEquiv.refl).toRingEquiv

/-- If `A` is geometrically regular over `k` and `k'/k` is a finitely generated field extension,
then `k' ⊗[k] A` is geometrically regular over `k'`. -/
theorem isGeometricallyRegular_tensorProduct (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A]
    [Algebra.EssFiniteType k k'] [Algebra.IsGeometricallyRegular k A] :
    Algebra.IsGeometricallyRegular k' (k' ⊗[k] A) := by
  refine ⟨fun K _ _ _ ↦ ?_⟩
  let _algKK : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq' rfl
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k k' K
  have := isRegularRing_tensorProduct k A K (Field.toIsField K)
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange k k' k' K A).symm.toRingEquiv

/-- If `k → k'` is étale and `A` is a `k'`-algebra which is geometrically regular over `k`, then
it is geometrically regular over `k'`. -/
private theorem isGeometricallyRegular_tower_top_of_etale (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A] [Algebra k' A]
    [IsScalarTower k k' A] [Algebra.Etale k k'] [Algebra.IsGeometricallyRegular k A] :
    Algebra.IsGeometricallyRegular k' A := by
  let mul : (k' ⊗[k] A) →ₐ[k] A :=
    Algebra.TensorProduct.productMap (IsScalarTower.toAlgHom k k' A) (AlgHom.id k A)
  let _algMul : Algebra (k' ⊗[k] A) A := mul.toRingHom.toAlgebra
  have : Algebra.Etale (k' ⊗[k] A) A := etale_productMap k k' A
  have : IsScalarTower k' (k' ⊗[k] A) A := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change algebraMap k' A x = mul (x ⊗ₜ 1)
    simp [mul]
  have : Algebra.IsGeometricallyRegular k' (k' ⊗[k] A) :=
    isGeometricallyRegular_tensorProduct k k' A
  exact Algebra.IsGeometricallyRegular.of_smooth (k' ⊗[k] A)

/-- If `A` is a `k'`-algebra which is geometrically regular over `k`, with `k'/k` separable, then
`A` is geometrically regular over every intermediate field `F` of `k'/k` which is finite over `k`,
viewed as a subfield of `k'`. -/
private theorem isGeometricallyRegular_toSubfield (k : Type u) (k' : Type v) (A : Type w) [Field k]
    [Field k'] [CommRing A] [Algebra k k'] [Algebra k A] [Algebra k' A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] [Algebra.IsGeometricallyRegular k A] (F : IntermediateField k k')
    [Module.Finite k F] : Algebra.IsGeometricallyRegular ↥F.toSubfield A := by
  let _algF : Algebra k ↥F.toSubfield := inferInstanceAs (Algebra k ↥F)
  have : Module.Finite k ↥F.toSubfield := inferInstanceAs (Module.Finite k ↥F)
  have : Algebra.IsSeparable k ↥F.toSubfield := inferInstanceAs (Algebra.IsSeparable k ↥F)
  have : IsScalarTower k ↥F.toSubfield A := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    change algebraMap k A x = algebraMap k' A (algebraMap k k' x)
    rw [← IsScalarTower.algebraMap_apply]
  have := etale_of_isSeparable k ↥F.toSubfield
  exact isGeometricallyRegular_tower_top_of_etale k _ A

/-- If `k'/k` is separable algebraic and `A` is a `k'`-algebra which is geometrically regular over
`k`, then `A` is geometrically regular over `k'`. -/
private theorem isGeometricallyRegular_tower_top (k : Type u) (k' : Type v) (A : Type w) [Field k]
    [Field k'] [CommRing A] [Algebra k k'] [Algebra k A] [Algebra k' A] [IsScalarTower k k' A]
    [Algebra.IsSeparable k k'] [Algebra.IsGeometricallyRegular k A] :
    Algebra.IsGeometricallyRegular k' A := by
  classical
  have hmono : Monotone fun S : Finset k' ↦
      (IntermediateField.adjoin k (S : Set k')).toSubfield :=
    fun _ _ hST _ hx ↦ IntermediateField.adjoin.mono k _ _ (Finset.coe_subset.mpr hST) hx
  have : ∀ S : Finset k', Algebra.IsGeometricallyRegular
      ↥((IntermediateField.adjoin k (S : Set k')).toSubfield) A := fun S ↦ by
    have : Module.Finite k ↥(IntermediateField.adjoin k (S : Set k')) :=
      IntermediateField.finiteDimensional_adjoin
        fun x _ ↦ (Algebra.IsSeparable.isSeparable k x).isIntegral
    exact isGeometricallyRegular_toSubfield k k' A _
  exact Algebra.IsGeometricallyRegular.of_directed_of_iSup_eq_top _ hmono.directed_le
    (eq_top_iff.mpr fun x _ ↦
      le_iSup (fun S : Finset k' ↦ (IntermediateField.adjoin k (S : Set k')).toSubfield)
        ({x} : Finset k') (IntermediateField.subset_adjoin k _ (by simp)))

/-- If `k'/k` is separable algebraic and `A` is a `k'`-algebra which is geometrically regular over
`k'`, then `A` is geometrically regular over `k`. -/
@[ega "IV 6.7.6" "special case"]
private theorem isGeometricallyRegular_of_tower_top (k : Type u) (k' : Type v) (A : Type w)
    [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A] [Algebra k' A]
    [IsScalarTower k k' A] [Algebra.IsSeparable k k']
    [Algebra.IsGeometricallyRegular k' A] : Algebra.IsGeometricallyRegular k A := by
  refine ⟨fun K _ _ _ ↦
    (Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
      k A).mpr (fun L _ _ _ _ ↦ ?_) K⟩
  have := isRegularRing_tensorProduct k' A (k' ⊗[k] L) (isField_tensorProduct k k' L)
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.comm k' (k' ⊗[k] L) A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange k k' k' A L).toRingEquiv.trans
        (Algebra.TensorProduct.comm k A L).toRingEquiv))

/-- For a separable algebraic extension `k'/k` and a `k'`-algebra `A`, geometric regularity of `A`
over `k` is equivalent to geometric regularity of `A` over `k'`. -/
public theorem solution (k : Type u) (k' : Type v) (A : Type w) [Field k] [Field k'] [CommRing A]
    [Algebra k k'] [Algebra k A] [Algebra k' A] [IsScalarTower k k' A] [Algebra.IsSeparable k k'] :
    Algebra.IsGeometricallyRegular k A ↔ Algebra.IsGeometricallyRegular k' A :=
  ⟨fun _ ↦ isGeometricallyRegular_tower_top k k' A,
    fun _ ↦ isGeometricallyRegular_of_tower_top k k' A⟩

end Stacks.GeometricallyRegular.SeparableBase

@[expose] public section



namespace Algebra

/-- Let `k'/k` be a separable algebraic field extension and let `A` be a `k'`-algebra, viewed as a
`k`-algebra by restriction of scalars. Then `A` is geometrically regular over `k` if and only if
it is geometrically regular over `k'`. -/
@[stacks 07QH "The source's separable algebraic extension `k'/k` is `Algebra.IsSeparable k k'`, \
  which already contains algebraicity (`Algebra.IsSeparable.isAlgebraic`); no finiteness is \
  assumed, the reduction to the finite case being internal to the proof (Lemma 07QG). `A` being \
  an algebra over `k'` and over `k` at once is `IsScalarTower k k' A`, which pins the \
  `k`-structure to be the restriction of the `k'`-structure. Geometric regularity is \
  `Algebra.IsGeometricallyRegular` (Definition 0382), which already implies the Noetherianness \
  Definition 0382 assumes. Named after Mathlib's `Algebra.isSeparable_tower_top_of_isSeparable`, \
  `tower_top` naming the right-hand side. See the module docstring."]
public theorem isGeometricallyRegular_iff_tower_top_of_isSeparable (k : Type u) (k' : Type v)
    (A : Type w) [Field k] [Field k'] [CommRing A] [Algebra k k'] [Algebra k A] [Algebra k' A]
    [IsScalarTower k k' A] [Algebra.IsSeparable k k'] :
    IsGeometricallyRegular k A ↔ IsGeometricallyRegular k' A :=
  Stacks.GeometricallyRegular.SeparableBase.solution k k' A

end Algebra

end

/-! ### Transport of tensor products and of fibres along ring isomorphisms

A tensor product and a fibre at a prime are carried along by compatible isomorphisms of the rings
involved.
-/

section

open scoped TensorProduct

@[expose] public section

namespace Stacks.FormalFibres

/-- An isomorphism of base rings together with compatible isomorphisms of two algebras over
them induces an isomorphism of the tensor products, sending `a ⊗ₜ k` to `f a ⊗ₜ g k`. -/
public lemma exists_tensorProduct_ringEquiv
    {R A K S B L : Type*}
    [CommRing R] [CommRing A] [CommRing K] [CommRing S] [CommRing B] [CommRing L]
    [Algebra R A] [Algebra R K] [Algebra S B] [Algebra S L]
    (e : R ≃+* S) (f : A ≃+* B) (g : K ≃+* L)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (hg : ∀ r, g (algebraMap R K r) = algebraMap S L (e r)) :
    ∃ E : A ⊗[R] K ≃+* B ⊗[S] L,
      ∀ a k, E (a ⊗ₜ[R] k) = f a ⊗ₜ[S] g k := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let : Algebra R B := ((algebraMap S B).comp e.toRingHom).toAlgebra
  let : Algebra R L := ((algebraMap S L).comp e.toRingHom).toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S L := IsScalarTower.of_algebraMap_eq' rfl
  let F : A ≃ₐ[R] B := { f with commutes' := hf }
  let G : K ≃ₐ[R] L := { g with commutes' := hg }
  let : TensorProduct.CompatibleSMul R S B L := by
    constructor
    intro s b l
    obtain ⟨r, rfl⟩ := e.surjective s
    simp only [Algebra.smul_def]
    change (algebraMap R B r * b) ⊗ₜ[R] l = b ⊗ₜ[R] (algebraMap R L r * l)
    exact TensorProduct.smul_tmul r b l
  exact ⟨(Algebra.TensorProduct.congr F G).toRingEquiv.trans
    (Algebra.TensorProduct.equivOfCompatibleSMul R S S B L).symm.toRingEquiv, fun _ _ ↦ rfl⟩

/-- An isomorphism of rings compatible with isomorphic algebras over them induces an isomorphism
of the fibres over corresponding primes, compatible with the induced isomorphism of residue
fields. -/
public lemma exists_fiber_ringEquiv
    {R A S B : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing B]
    [Algebra R A] [Algebra S B] (e : R ≃+* S) (f : A ≃+* B)
    (hf : ∀ r, f (algebraMap R A r) = algebraMap S B (e r))
    (q : Ideal S) [q.IsPrime] :
    let p := q.comap e.toRingHom
    ∃ E : p.Fiber A ≃+* q.Fiber B,
      ∀ a, E (algebraMap p.ResidueField (p.Fiber A) a) =
        algebraMap q.ResidueField (q.Fiber B)
          (Ideal.residueFieldRingEquiv p q e rfl a) := by
  dsimp only
  let p := q.comap e.toRingHom
  let ek := Ideal.residueFieldRingEquiv p q e rfl
  obtain ⟨E, hE⟩ := exists_tensorProduct_ringEquiv e ek f
    (fun r ↦ Ideal.ResidueField.map_algebraMap p q e.toRingHom rfl r) hf
  refine ⟨E, fun a ↦ ?_⟩
  change E (a ⊗ₜ[R] (1 : A)) = ek a ⊗ₜ[S] (1 : B)
  rw [hE, map_one]

end Stacks.FormalFibres

end

end
