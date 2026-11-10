module

public import StacksFrontier.Deformation.FlatAlgebraLiftCompletionRelative
public import StacksFrontier.Deformation.FlatModuleLiftLocalization
public import StacksFrontier.Deformation.FlatModuleLiftTransport
public import StacksFrontier.Homology.HomComplex.RHom.HomModuleBaseChange

/-!
# Stacks 0DZ2 at an abstract pair of thickenings

Stacks 0DZ2 is proved in `StacksFrontier.Deformation.FlatModuleLiftLocalization` with the two
lower rings written as the literal base changes `P = P' ⊗_{A'} A` and `Q = Q' ⊗_{A'} A`, and
with the module lifts written as isomorphisms out of `ModuleCat.extendScalars`. The proof of
Stacks 0DZ3 produces and consumes a different shape: `P` and `Q` are abstract rings carrying
the kernel identities `ker(P' → P) = ker(A' → A)·P'` and `ker(Q' → Q) = ker(A' → A)·Q'`, and a
lift of `M` is a linear equivalence `P ⊗_{P'} M' ≅ M`. That shape is
`Deformation.FlatModuleLiftBaseChangeStatementAt`.

This file transports the proved form into that shape, and so discharges the hypothesis `h0DZ2`
of Stacks 0DZ3 whenever the kernel of `A' → A` has square zero — which is the case of a small
extension of Artinian bases, the only case Stacks 0DZ5 needs. Nothing here touches the
dévissage from a nilpotent kernel to a square-zero one: the proved form of Stacks 0DZ2 already
allows the kernel of `A' → A` to be nilpotent provided the two *thickenings* `P' → P` and
`Q' → Q` are square-zero, and a square-zero kernel makes them so, the kernel of a thickening
being the extension of the kernel of `A' → A`.

The consumers that take `P` to be the literal base change `P' ⊗_{A'} A` and leave only `Q`
abstract — the proofs of Stacks 0DZ7 and Stacks 0DZB, which present the algebra over
`P' ⊗_{A'} A` rather than over an abstract thickening — are served by
`Deformation.exists_flatModuleLift_iff_baseChange_of_sqZero`, the same comparison at that
special pair, proved with the transport dictionary of
`StacksFrontier.Deformation.FlatModuleLiftTransport`.

## Main definitions

* `Deformation.tensorEquivOfRingEquiv`: a base change `S ⊗_R X` carried along ring isomorphisms
  `R ≃ R₀`, `S ≃ S₀` and a semilinear isomorphism `X ≃ X₀`.
* `Deformation.ringEquivTensorBaseChange`: the identification of an abstract thickening with
  the literal base change, as a ring isomorphism.
* `Deformation.tensorBaseChangeAlgebra`: the base change along `A' → A` of a map `P' → Q'`.
* `Deformation.ringEquivLocalizationTensorBaseChange`: the identification of the two
  localizations of a thickening at an element.

## Main results

* `Deformation.nonempty_extendScalars_iso_iff`: a module lift written in `ModuleCat` is one
  written as a linear equivalence out of a tensor product.
* `Deformation.nonempty_linearEquiv_congr_semilinear`: a linear isomorphism carried along a
  ring isomorphism by two semilinear isomorphisms.
* `Deformation.exists_flatModuleLift_iff_tensorBaseChange`: the lifting problem over an
  abstract thickening is the lifting problem over the literal base change.
* `Deformation.flat_tensorBaseChangeAlgebra`: the base change of a flat ring map is flat.
* `Deformation.bijective_quotientMap_of_ker_map`: the quotient identity `R/J = S/JS` passes to
  a thickening of both sides.
* `Deformation.exists_flatModuleLift_iff_baseChange_of_sq_zero`: **Stacks 0DZ2 at an abstract
  pair of thickenings**, for a square-zero kernel and a finite module.
* `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`: the same, packaged as the
  hypothesis `h0DZ2` of the proof of Stacks 0DZ3.
* `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_sq_zero`: **the second
  implication of Stacks 0DZ3, unconditionally, for a square-zero kernel**.
* `Deformation.hasFlatAlgebraLift_adicCompletion_iff_of_sq_zero`: **Stacks 0DZ3,
  unconditionally, for a square-zero kernel**.
* `Deformation.exists_flatModuleLift_iff_baseChange_of_sqZero`: **Stacks 0DZ2** at
  `P = P' ⊗_{A'} A` and `Q = P ⊗_{P'} Q'`, for a square-zero kernel and a finite module.

## Implementation notes

The transport is all carried by one construction. `Deformation.tensorMapOfRingEquiv` sends
`s ⊗ x` to `eS s ⊗ fX x`; it is balanced because `fX` is semilinear over `eR`, and with its
inverse it gives `Deformation.tensorEquivOfRingEquiv`, an additive isomorphism semilinear over
`eS`. Every comparison below — of the two lifting problems, of the base change `Q ⊗_P M`, and
of the localized lifting problem at `g` — is an instance of it followed by
`Deformation.nonempty_linearEquiv_congr_semilinear`.

The module structures over the literal base changes are restrictions of scalars along the
identification, installed with `Module.compHom`;
`Deformation.isScalarTower_of_smul_algebraMap` and
`Deformation.isScalarTower_base_of_smul_algebraMap` turn such a restriction into the scalar
towers the proved form asks for, and finiteness transports because the identification is
surjective.

Flatness of the base change `P' ⊗_{A'} A → Q' ⊗_{A'} A` is *not* transported: it is obtained
directly from flatness of `P' → Q'`, by cancelling the base change to identify
`(P' ⊗_{A'} A) ⊗_{P'} Q'` with `Q' ⊗_{A'} A`. That identification is a priori only `P'`-linear,
but `P' → P' ⊗_{A'} A` is surjective, so a `P'`-algebra map between `P' ⊗_{A'} A`-algebras is
automatically one of `P' ⊗_{A'} A`-algebras.

The quotient identity needs one genuinely arithmetic step,
`Deformation.exists_mem_and_sub_algebraMap_mem_map`: an element of the extension of an ideal
`I` is congruent modulo `JS` to the image of an element of `I`, because each coefficient can
itself be moved across `R/J = S/JS`.

`Deformation.exists_flatModuleLift_iff_baseChange_of_sqZero`, in the final section, runs the
same transport at `P = P' ⊗_{A'} A` and `Q = P ⊗_{P'} Q'` out of
`StacksFrontier.Deformation.FlatModuleLiftTransport` instead: there `P` needs no identification at
all, and the one comparison left is `Q ≅ Q' ⊗_{A'} A`, the two being quotients of `Q'` by the
same ideal.

## References

* [Stacks Project, Tag 0DZ2](https://stacks.math.columbia.edu/tag/0DZ2)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Deformation

/-- A flat module lift written as an isomorphism in `ModuleCat` out of an extension of scalars
is the same thing as one written as a linear equivalence out of a tensor product. -/
theorem nonempty_extendScalars_iso_iff (P' P : Type u) [CommRing P'] [CommRing P]
    [Algebra P' P] (M' : Type u) [AddCommGroup M'] [Module P' M']
    (Z : Type u) [AddCommGroup Z] [Module P Z] :
    Nonempty ((ModuleCat.extendScalars.{u, u, u} (algebraMap P' P)).obj
        (ModuleCat.of P' M') ≅ ModuleCat.of P Z) ↔
      Nonempty ((P ⊗[P'] M') ≃ₗ[P] Z) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨(StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
      (A := P) (ModuleCat.of P' M')).symm.trans i.toLinearEquiv⟩
  · rintro ⟨e⟩
    exact ⟨((StacksDraft.DerivedHom.HomModuleBaseChange.extendScalarsObjTensorEquiv
      (A := P) (ModuleCat.of P' M')).trans e).toModuleIso⟩

/-- The complex with a single module in degree zero is bounded above. -/
theorem minus_q_single (R : Type u) [CommRing R] (X : Type u) [AddCommGroup X] [Module R X] :
    (DerivedCategory.TStructure.t (C := ModuleCat.{u} R)).minus
      (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R X))) :=
  ⟨0, inferInstance⟩

/-! ### Transporting a base change along ring isomorphisms -/

section TensorCongr

variable {R R₀ S S₀ X X₀ : Type u} [CommRing R] [CommRing R₀] [CommRing S] [CommRing S₀]
  [Algebra R S] [Algebra R₀ S₀] [AddCommGroup X] [Module R X] [AddCommGroup X₀] [Module R₀ X₀]

/-- The additive map `S ⊗_R X → S₀ ⊗_{R₀} X₀` carrying `s ⊗ x` to `eS s ⊗ fX x`, for a pair of
ring isomorphisms `eR : R ≃ R₀`, `eS : S ≃ S₀` over which the structure maps correspond and an
`eR`-semilinear isomorphism `fX : X ≃ X₀`. -/
def tensorMapOfRingEquiv (eR : R ≃+* R₀) (eS : S ≃+* S₀)
    (hcomm : ∀ r : R, eS (algebraMap R S r) = algebraMap R₀ S₀ (eR r))
    (fX : X ≃+ X₀) (hfX : ∀ (r : R) (x : X), fX (r • x) = eR r • fX x) :
    (S ⊗[R] X) →+ (S₀ ⊗[R₀] X₀) :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk'
      (fun s => AddMonoidHom.mk' (fun x => (eS s) ⊗ₜ[R₀] (fX x))
        (fun x y => by rw [map_add, TensorProduct.tmul_add]))
      (fun s t => AddMonoidHom.ext fun x => by
        change (eS (s + t)) ⊗ₜ[R₀] (fX x) = (eS s) ⊗ₜ[R₀] (fX x) + (eS t) ⊗ₜ[R₀] (fX x)
        rw [map_add, TensorProduct.add_tmul]))
    (fun r s x => by
      change (eS (r • s)) ⊗ₜ[R₀] (fX x) = (eS s) ⊗ₜ[R₀] (fX (r • x))
      rw [hfX r x, ← TensorProduct.smul_tmul, Algebra.smul_def, map_mul, hcomm,
        ← Algebra.smul_def])

/-- `Deformation.tensorMapOfRingEquiv` sends `s ⊗ x` to `eS s ⊗ fX x`. -/
theorem tensorMapOfRingEquiv_tmul (eR : R ≃+* R₀) (eS : S ≃+* S₀)
    (hcomm : ∀ r : R, eS (algebraMap R S r) = algebraMap R₀ S₀ (eR r))
    (fX : X ≃+ X₀) (hfX : ∀ (r : R) (x : X), fX (r • x) = eR r • fX x) (s : S) (x : X) :
    tensorMapOfRingEquiv eR eS hcomm fX hfX (s ⊗ₜ[R] x) = (eS s) ⊗ₜ[R₀] (fX x) := rfl

end TensorCongr

/-! ### Semilinear isomorphisms over a ring isomorphism -/

section Semilinear

variable {S S₀ : Type u} [CommRing S] [CommRing S₀] (eS : S ≃+* S₀)
  {W W₀ Y Y₀ : Type u} [AddCommGroup W] [Module S W] [AddCommGroup W₀] [Module S₀ W₀]
  [AddCommGroup Y] [Module S Y] [AddCommGroup Y₀] [Module S₀ Y₀]

/-- The inverse of an `eS`-semilinear additive isomorphism is `eS.symm`-semilinear. -/
theorem semilinear_symm (u : W ≃+ W₀) (hu : ∀ (s : S) (w : W), u (s • w) = eS s • u w)
    (s₀ : S₀) (w₀ : W₀) : u.symm (s₀ • w₀) = eS.symm s₀ • u.symm w₀ := by
  refine u.injective ?_
  rw [u.apply_symm_apply, hu, u.apply_symm_apply, eS.apply_symm_apply]

/-- **Transport of a linear isomorphism along a ring isomorphism.** If `W ≅ W₀` and `Y ≅ Y₀` are
additive isomorphisms semilinear over a ring isomorphism `eS : S ≃ S₀`, then an `S`-linear
isomorphism `W ≅ Y` gives an `S₀`-linear isomorphism `W₀ ≅ Y₀`. -/
theorem nonempty_linearEquiv_of_semilinear
    (u : W ≃+ W₀) (hu : ∀ (s : S) (w : W), u (s • w) = eS s • u w)
    (v : Y ≃+ Y₀) (hv : ∀ (s : S) (y : Y), v (s • y) = eS s • v y)
    (h : Nonempty (W ≃ₗ[S] Y)) : Nonempty (W₀ ≃ₗ[S₀] Y₀) := by
  obtain ⟨f⟩ := h
  refine ⟨{ u.symm.trans (f.toAddEquiv.trans v) with map_smul' := fun s₀ w₀ => ?_ }⟩
  change v (f (u.symm (s₀ • w₀))) = s₀ • v (f (u.symm w₀))
  rw [semilinear_symm eS u hu, f.map_smul, hv, eS.apply_symm_apply]

/-- `Deformation.nonempty_linearEquiv_of_semilinear` read as an equivalence. -/
theorem nonempty_linearEquiv_congr_semilinear
    (u : W ≃+ W₀) (hu : ∀ (s : S) (w : W), u (s • w) = eS s • u w)
    (v : Y ≃+ Y₀) (hv : ∀ (s : S) (y : Y), v (s • y) = eS s • v y) :
    Nonempty (W ≃ₗ[S] Y) ↔ Nonempty (W₀ ≃ₗ[S₀] Y₀) :=
  ⟨nonempty_linearEquiv_of_semilinear eS u hu v hv,
    nonempty_linearEquiv_of_semilinear eS.symm u.symm (semilinear_symm eS u hu)
      v.symm (semilinear_symm eS v hv)⟩

end Semilinear

section TensorEquiv

variable {R R₀ S S₀ X X₀ : Type u} [CommRing R] [CommRing R₀] [CommRing S] [CommRing S₀]
  [Algebra R S] [Algebra R₀ S₀] [AddCommGroup X] [Module R X] [AddCommGroup X₀] [Module R₀ X₀]

/-- The structure maps still correspond under the inverse ring isomorphisms. -/
theorem algebraMap_comm_symm {eR : R ≃+* R₀} {eS : S ≃+* S₀}
    (hcomm : ∀ r : R, eS (algebraMap R S r) = algebraMap R₀ S₀ (eR r)) (r₀ : R₀) :
    eS.symm (algebraMap R₀ S₀ r₀) = algebraMap R S (eR.symm r₀) := by
  refine eS.injective ?_
  rw [eS.apply_symm_apply, hcomm, eR.apply_symm_apply]

/-- **Transport of a base change along ring isomorphisms.** For ring isomorphisms
`eR : R ≃ R₀` and `eS : S ≃ S₀` over which the structure maps correspond and an
`eR`-semilinear additive isomorphism `fX : X ≃ X₀`, the base changes `S ⊗_R X` and
`S₀ ⊗_{R₀} X₀` are isomorphic, `eS`-semilinearly. -/
def tensorEquivOfRingEquiv (eR : R ≃+* R₀) (eS : S ≃+* S₀)
    (hcomm : ∀ r : R, eS (algebraMap R S r) = algebraMap R₀ S₀ (eR r))
    (fX : X ≃+ X₀) (hfX : ∀ (r : R) (x : X), fX (r • x) = eR r • fX x) :
    (S ⊗[R] X) ≃+ (S₀ ⊗[R₀] X₀) where
  toFun := tensorMapOfRingEquiv eR eS hcomm fX hfX
  invFun := tensorMapOfRingEquiv eR.symm eS.symm (algebraMap_comm_symm hcomm) fX.symm
    (fun r₀ x₀ => semilinear_symm eR fX hfX r₀ x₀)
  map_add' _ _ := map_add _ _ _
  left_inv w := by
    induction w using TensorProduct.inductionOn with
    | tmul s x =>
        rw [tensorMapOfRingEquiv_tmul, tensorMapOfRingEquiv_tmul, eS.symm_apply_apply,
          fX.symm_apply_apply]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']
  right_inv w₀ := by
    induction w₀ using TensorProduct.inductionOn with
    | tmul s₀ x₀ =>
        rw [tensorMapOfRingEquiv_tmul, tensorMapOfRingEquiv_tmul, eS.apply_symm_apply,
          fX.apply_symm_apply]
    | add w w' hw hw' => rw [map_add, map_add, hw, hw']

/-- `Deformation.tensorEquivOfRingEquiv` is semilinear over `eS`. -/
theorem tensorEquivOfRingEquiv_smul (eR : R ≃+* R₀) (eS : S ≃+* S₀)
    (hcomm : ∀ r : R, eS (algebraMap R S r) = algebraMap R₀ S₀ (eR r))
    (fX : X ≃+ X₀) (hfX : ∀ (r : R) (x : X), fX (r • x) = eR r • fX x)
    (s : S) (w : S ⊗[R] X) :
    tensorEquivOfRingEquiv eR eS hcomm fX hfX (s • w) =
      eS s • tensorEquivOfRingEquiv eR eS hcomm fX hfX w := by
  induction w using TensorProduct.inductionOn with
  | tmul t x =>
      change tensorMapOfRingEquiv eR eS hcomm fX hfX (s • (t ⊗ₜ[R] x)) =
        eS s • tensorMapOfRingEquiv eR eS hcomm fX hfX (t ⊗ₜ[R] x)
      rw [TensorProduct.smul_tmul', tensorMapOfRingEquiv_tmul, tensorMapOfRingEquiv_tmul,
        smul_eq_mul, map_mul, ← smul_eq_mul, TensorProduct.smul_tmul']
  | add w w' hw hw' => rw [smul_add, map_add, map_add, hw, hw', smul_add]

/-- A linear equivalence out of the transported base change exists iff one out of the original
base change does, when the target is carried along `eS`-semilinearly. -/
private theorem nonempty_tensor_linearEquiv_congr {Y Y₀ : Type u} [AddCommGroup Y] [Module S Y]
    [AddCommGroup Y₀] [Module S₀ Y₀] (eR : R ≃+* R₀) (eS : S ≃+* S₀)
    (hcomm : ∀ r : R, eS (algebraMap R S r) = algebraMap R₀ S₀ (eR r))
    (fX : X ≃+ X₀) (hfX : ∀ (r : R) (x : X), fX (r • x) = eR r • fX x)
    (v : Y ≃+ Y₀) (hv : ∀ (s : S) (y : Y), v (s • y) = eS s • v y) :
    Nonempty ((S ⊗[R] X) ≃ₗ[S] Y) ↔ Nonempty ((S₀ ⊗[R₀] X₀) ≃ₗ[S₀] Y₀) :=
  nonempty_linearEquiv_congr_semilinear eS (tensorEquivOfRingEquiv eR eS hcomm fX hfX)
    (tensorEquivOfRingEquiv_smul eR eS hcomm fX hfX) v hv

end TensorEquiv

/-! ### Modules carried along a ring isomorphism -/

section Restrict

/-- A module structure given by restriction along an algebra map is a scalar tower. -/
theorem isScalarTower_of_smul_algebraMap {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {M : Type u} [AddCommGroup M] [Module S M] [Module T M]
    (hsmul : ∀ (x : S) (m : M), x • m = algebraMap S T x • m) : IsScalarTower S T M :=
  ⟨fun x y z => by rw [hsmul, Algebra.smul_def, mul_smul]⟩

/-- A module structure given by restriction along an algebra map `S → T` is a scalar tower over
a base `A` of both, as soon as the two structure maps out of `A` agree. -/
theorem isScalarTower_base_of_smul_algebraMap {A S T : Type u} [CommRing A] [CommRing S]
    [CommRing T] [Algebra A S] [Algebra A T] [Algebra S T] {M : Type u} [AddCommGroup M]
    [Module A M] [Module S M] [Module T M] [IsScalarTower A T M]
    (hcompat : ∀ a : A, algebraMap S T (algebraMap A S a) = algebraMap A T a)
    (hsmul : ∀ (x : S) (m : M), x • m = algebraMap S T x • m) : IsScalarTower A S M :=
  ⟨fun a x m => by
    rw [hsmul, Algebra.smul_def, map_mul, hcompat, mul_smul, hsmul x m,
      IsScalarTower.algebraMap_smul]⟩

end Restrict

/-! ### The base change of the top ring map -/

section BaseChangeAlgebra

variable (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
  [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The base change along `A' → A` of a map `P' → Q'` of `A'`-algebras. -/
abbrev tensorBaseChangeAlgebra :
    Algebra (TensorProduct A' P' A) (TensorProduct A' Q' A) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' P' Q')
    (AlgHom.id A' A)).toRingHom.toAlgebra

/-- The base change of `P' → Q'` sends `x ⊗ a` to the image of `x` in `Q'` tensored with `a`. -/
theorem tensorBaseChangeAlgebra_tmul (x : P') (a : A) :
    letI := tensorBaseChangeAlgebra A' A P' Q'
    algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A) (x ⊗ₜ[A'] a) =
      (algebraMap P' Q' x) ⊗ₜ[A'] a := by
  let := tensorBaseChangeAlgebra A' A P' Q'
  change Algebra.TensorProduct.map (IsScalarTower.toAlgHom A' P' Q') (AlgHom.id A' A)
    (x ⊗ₜ[A'] a) = _
  rw [Algebra.TensorProduct.map_tmul]
  rfl

/-- The base change of `P' → Q'` restricts along `P' → P' ⊗_{A'} A` to the composite
`P' → Q' → Q' ⊗_{A'} A`. -/
theorem tensorBaseChangeAlgebra_algebraMap (x : P') :
    letI := tensorBaseChangeAlgebra A' A P' Q'
    algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)
        (algebraMap P' (TensorProduct A' P' A) x) =
      algebraMap Q' (TensorProduct A' Q' A) (algebraMap P' Q' x) := by
  let := tensorBaseChangeAlgebra A' A P' Q'
  have h : algebraMap P' (TensorProduct A' P' A) x = x ⊗ₜ[A'] (1 : A) := rfl
  rw [h, tensorBaseChangeAlgebra_tmul]
  rfl

/-- **The base change of the top ring map is the base change of `Q'` along `P' → P' ⊗ A`.**
Cancelling the base change identifies `(P' ⊗_{A'} A) ⊗_{P'} Q'` with `Q' ⊗_{A'} A`, as
algebras over `P' ⊗_{A'} A`. -/
def linearEquivTensorBaseChangeTop :
    letI := tensorBaseChangeAlgebra A' A P' Q'
    ((TensorProduct A' P' A) ⊗[P'] Q') ≃ₗ[TensorProduct A' P' A] (TensorProduct A' Q' A) := by
  letI := tensorBaseChangeAlgebra A' A P' Q'
  set φ : ((TensorProduct A' P' A) ⊗[P'] Q') ≃ₐ[P'] (TensorProduct A' Q' A) :=
    (Algebra.TensorProduct.comm P' (TensorProduct A' P' A) Q').trans
      (Algebra.TensorProduct.cancelBaseChange A' P' P' Q' A) with hφ
  have hbase : ∀ y : TensorProduct A' P' A,
      φ (algebraMap (TensorProduct A' P' A) ((TensorProduct A' P' A) ⊗[P'] Q') y) =
        algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A) y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
    | tmul x a =>
        have h1 : algebraMap (TensorProduct A' P' A) ((TensorProduct A' P' A) ⊗[P'] Q')
            (x ⊗ₜ[A'] a) = (x ⊗ₜ[A'] a) ⊗ₜ[P'] (1 : Q') := rfl
        rw [h1, hφ, AlgEquiv.trans_apply, Algebra.TensorProduct.comm_tmul,
          Algebra.TensorProduct.cancelBaseChange_tmul, tensorBaseChangeAlgebra_tmul,
          Algebra.smul_def, mul_one]
  exact { φ.toLinearEquiv.toAddEquiv with
    map_smul' := fun y w => by
      change φ (y • w) = y • φ w
      rw [Algebra.smul_def, map_mul, hbase, Algebra.smul_def] }

/-- The base change of a flat ring map is flat. -/
theorem flat_tensorBaseChangeAlgebra [Module.Flat P' Q'] :
    letI := tensorBaseChangeAlgebra A' A P' Q'
    Module.Flat (TensorProduct A' P' A) (TensorProduct A' Q' A) := by
  let := tensorBaseChangeAlgebra A' A P' Q'
  have : Module.Flat (TensorProduct A' P' A) ((TensorProduct A' P' A) ⊗[P'] Q') :=
    Module.Flat.baseChange P' (TensorProduct A' P' A) Q'
  exact Module.Flat.of_linearEquiv (linearEquivTensorBaseChangeTop A' A P' Q').symm

end BaseChangeAlgebra

/-! ### One thickening, carried to the literal base change -/

section Thickening

variable (A' A P' P : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [Algebra A' A] [Algebra A' P'] [Algebra A' P] [Algebra A P] [Algebra P' P]
  [IsScalarTower A' A P] [IsScalarTower A' P' P] [Module.Flat A' P']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The square-zero thickening of the literal base change, from a square-zero kernel. -/
theorem sq_ker_algebraMap_tensorProduct_eq_bot
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    RingHom.ker (algebraMap P' (TensorProduct A' P' A)) ^ 2 = ⊥ := by
  rw [Algebra.ker_algebraMap_tensorProduct_left A' P' A, ← Ideal.map_pow, hzeroA,
    Ideal.map_bot]

variable (hsurjA : Function.Surjective (algebraMap A' A))
  (hsurjP : Function.Surjective (algebraMap P' P))
  (hkerP : RingHom.ker (algebraMap P' P) =
    (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))

/-- The identification of an abstract thickening with the literal base change, as a ring
isomorphism. -/
abbrev ringEquivTensorBaseChange : P ≃+* TensorProduct A' P' A :=
  (algEquivTensorBaseChangeOfKer A' A P' P hsurjA hsurjP hkerP).toRingEquiv

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- The identification `P ≃ P' ⊗_{A'} A` commutes with the structure maps out of `P'`. -/
theorem ringEquivTensorBaseChange_algebraMap (x : P') :
    ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP (algebraMap P' P x) =
      algebraMap P' (TensorProduct A' P' A) x :=
  (algEquivTensorBaseChangeOfKer A' A P' P hsurjA hsurjP hkerP).commutes x

/-- The identification `P ≃ P' ⊗_{A'} A` commutes with the structure maps out of `A`. -/
theorem ringEquivTensorBaseChange_algebraMap_base (a : A) :
    ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP (algebraMap A P a) =
      algebraMap A (TensorProduct A' P' A) a :=
  algEquivTensorBaseChangeOfKer_algebraMap_base A' A P' P hsurjA hsurjP hkerP a

/-- The `P`-algebra structure on `P` through the identification with the literal base change. -/
abbrev algebraTensorBaseChange : Algebra (TensorProduct A' P' A) P :=
  ((ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm : _ →+* P).toAlgebra

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- Wrapping a module in `ULift` is semilinear over the identification of the thickening with
the literal base change. -/
theorem ulift_up_semilinear
    (M : Type u) [AddCommGroup M] [Module P M] [Module (TensorProduct A' P' A) M]
    (hsmul : ∀ (x : TensorProduct A' P' A) (m : M),
      x • m = (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm x • m)
    (p : P) (m : M) :
    (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm.toAddEquiv (p • m) =
      ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP p •
        (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm.toAddEquiv m := by
  set e := ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP
  have hp : p • m = e p • m := by rw [hsmul, e.symm_apply_apply]
  change (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm (p • m) =
    e p • (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm m
  rw [hp, LinearEquiv.map_smul]

/-- A module over `P` and `A`, restricted to the literal base change through its identification
with `P`, is a scalar tower over `A`. -/
private theorem isScalarTower_base_tensorBaseChange
    (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
    [Module (TensorProduct A' P' A) M]
    (hsmul : ∀ (x : TensorProduct A' P' A) (m : M),
      x • m = (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm x • m) :
    IsScalarTower A (TensorProduct A' P' A) M := by
  let : Algebra (TensorProduct A' P' A) P :=
    algebraTensorBaseChange A' A P' P hsurjA hsurjP hkerP
  refine isScalarTower_base_of_smul_algebraMap (T := P) (fun a => ?_) hsmul
  change (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm
    (algebraMap A (TensorProduct A' P' A) a) = algebraMap A P a
  rw [← ringEquivTensorBaseChange_algebraMap_base A' A P' P hsurjA hsurjP hkerP a,
    RingEquiv.symm_apply_apply]

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- **A flat module lift over an abstract thickening is one over the literal base change.** For
a `P`-module `M` on which the base change `P' ⊗_{A'} A` acts through the identification with
`P`, the two readings of "`M'` is a `P'`-module lift of `M`" agree. -/
theorem nonempty_tensorLift_congr
    (M' : Type u) [AddCommGroup M'] [Module P' M']
    (M : Type u) [AddCommGroup M] [Module P M] [Module (TensorProduct A' P' A) M]
    (hsmul : ∀ (x : TensorProduct A' P' A) (m : M),
      x • m = (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm x • m) :
    Nonempty ((P ⊗[P'] M') ≃ₗ[P] M) ↔
      Nonempty (((TensorProduct A' P' A) ⊗[P'] M')
        ≃ₗ[TensorProduct A' P' A] ULift.{u} M) := by
  set e := ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP
  have hcomm : ∀ r : P', e (algebraMap P' P r) =
      algebraMap P' (TensorProduct A' P' A) ((RingEquiv.refl P') r) :=
    ringEquivTensorBaseChange_algebraMap A' A P' P hsurjA hsurjP hkerP
  have hfX : ∀ (r : P') (x : M'), (AddEquiv.refl M') (r • x) =
      (RingEquiv.refl P') r • (AddEquiv.refl M') x := fun _ _ => rfl
  exact nonempty_tensor_linearEquiv_congr (RingEquiv.refl P') e hcomm (AddEquiv.refl M') hfX
    (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm.toAddEquiv
    (ulift_up_semilinear A' A P' P hsurjA hsurjP hkerP M hsmul)

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- **The lifting problem over an abstract thickening is the lifting problem over the literal
base change.** The two existential statements of Stacks 0DZ2 — one in the shape the proof of
Stacks 0DZ3 produces, one in the shape the obstruction calculus proves — are equivalent. -/
theorem exists_flatModuleLift_iff_tensorBaseChange
    (M : Type u) [AddCommGroup M] [Module P M] [Module (TensorProduct A' P' A) M]
    (hsmul : ∀ (x : TensorProduct A' P' A) (m : M),
      x • m = (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm x • m) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
      (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap P' (TensorProduct A' P' A))).obj (ModuleCat.of P' M') ≅
          ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M))) := by
  constructor
  · rintro ⟨M', _, _, _, _, hflat, hlift⟩
    exact ⟨M', inferInstance, inferInstance, inferInstance, inferInstance, hflat,
      (nonempty_extendScalars_iso_iff P' (TensorProduct A' P' A) M' (ULift.{u} M)).mpr
        ((nonempty_tensorLift_congr A' A P' P hsurjA hsurjP hkerP M' M hsmul).mp hlift)⟩
  · rintro ⟨M', _, _, _, _, hflat, hlift⟩
    exact ⟨M', inferInstance, inferInstance, inferInstance, inferInstance, hflat,
      (nonempty_tensorLift_congr A' A P' P hsurjA hsurjP hkerP M' M hsmul).mpr
        ((nonempty_extendScalars_iso_iff P' (TensorProduct A' P' A) M' (ULift.{u} M)).mp hlift)⟩

/-! #### The localization of the thickening at an element -/

include hsurjA hsurjP hkerP in
omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- The identification of the thickening with the literal base change carries the powers of the
image of `g` to the powers of the image of `g`. -/
theorem map_powers_ringEquivTensorBaseChange (g : P') :
    Submonoid.map
        (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).toMonoidHom
        (Submonoid.powers (algebraMap P' P g)) =
      Submonoid.powers (algebraMap P' (TensorProduct A' P' A) g) := by
  rw [Submonoid.map_powers]
  congr 1
  exact ringEquivTensorBaseChange_algebraMap A' A P' P hsurjA hsurjP hkerP g

omit [Module.Flat A' P'] in
/-- The literal base change of `(P')_g` is a localization of the literal base change of `P'`. -/
theorem isLocalization_away_tensorBaseChange (g : P') :
    letI := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
    IsLocalization.Away (algebraMap P' (TensorProduct A' P' A) g)
      (TensorProduct A' (Localization.Away g) A) := by
  let := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
  exact IsLocalization.Away.tensorBaseChange A' A P' (Localization.Away g) g
    (tensorBaseChangeAlgebra_tmul A' A P' (Localization.Away g))

include hsurjA hsurjP hkerP in
/-- **The two localizations of the thickening at `g` agree.** The localization of the abstract
thickening `P` at the image of `g` and the localization `(P')_g ⊗_{A'} A` of the literal base
change are both localizations of corresponding elements, hence isomorphic. -/
def ringEquivLocalizationTensorBaseChange (g : P') :
    letI := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
    Localization.Away (algebraMap P' P g) ≃+*
      TensorProduct A' (Localization.Away g) A :=
  letI := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
  haveI := isLocalization_away_tensorBaseChange A' A P' g
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (algebraMap P' P g))
    (S := Localization.Away (algebraMap P' P g))
    (T := Submonoid.powers (algebraMap P' (TensorProduct A' P' A) g))
    (Q := TensorProduct A' (Localization.Away g) A)
    (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP)
    (map_powers_ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP g)

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- On `P`, the identification of the two localizations at `g` is the identification
`P ≃ P' ⊗_{A'} A` followed by the structure map to `(P')_g ⊗_{A'} A`. -/
theorem ringEquivLocalizationTensorBaseChange_algebraMap (g : P') (p : P) :
    letI := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
    ringEquivLocalizationTensorBaseChange A' A P' P hsurjA hsurjP hkerP g
        (algebraMap P (Localization.Away (algebraMap P' P g)) p) =
      algebraMap (TensorProduct A' P' A) (TensorProduct A' (Localization.Away g) A)
        (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP p) := by
  let := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
  have := isLocalization_away_tensorBaseChange A' A P' g
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (map_powers_ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP g) p

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- The identification of the two localizations is a map of algebras over `(P')_g`. -/
theorem ringEquivLocalizationTensorBaseChange_algebraMap_away (g : P')
    (r : Localization.Away g) :
    letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
      (Localization.awayMap (algebraMap P' P) g).toAlgebra
    letI := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
    ringEquivLocalizationTensorBaseChange A' A P' P hsurjA hsurjP hkerP g
        (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g)) r) =
      algebraMap (Localization.Away g) (TensorProduct A' (Localization.Away g) A) r := by
  let : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
    (Localization.awayMap (algebraMap P' P) g).toAlgebra
  let := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
  set eg := ringEquivLocalizationTensorBaseChange A' A P' P hsurjA hsurjP hkerP g with heg
  suffices h : (eg : Localization.Away (algebraMap P' P g) →+* _).comp
      (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))) =
      algebraMap (Localization.Away g) (TensorProduct A' (Localization.Away g) A) from
    RingHom.congr_fun h r
  refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun x => ?_)
  have hl : algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))
      (algebraMap P' (Localization.Away g) x) =
      algebraMap P (Localization.Away (algebraMap P' P g)) (algebraMap P' P x) :=
    RingHom.congr_fun (IsLocalization.map_comp
      (M := Submonoid.powers g) (S := Localization.Away g)
      (g := algebraMap P' P) (T := Submonoid.powers (algebraMap P' P g))
      (Q := Localization.Away (algebraMap P' P g))
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _))) x
  change eg (algebraMap (Localization.Away g) (Localization.Away (algebraMap P' P g))
      (algebraMap P' (Localization.Away g) x)) = _
  rw [hl, heg, ringEquivLocalizationTensorBaseChange_algebraMap,
    ringEquivTensorBaseChange_algebraMap, tensorBaseChangeAlgebra_algebraMap]
  rfl

omit [Algebra A' P] [Algebra A P] [IsScalarTower A' A P] [IsScalarTower A' P' P] in
/-- **A local lift over the abstract thickening is one over the literal base change.** An
isomorphism `P_g ⊗_{(P')_g} L ≅ P_g ⊗_P M` gives the extension of scalars of `L` to
`(P')_g ⊗_{A'} A` as the base change of `M` along `P' ⊗_{A'} A → (P')_g ⊗_{A'} A`. -/
private theorem nonempty_extendScalars_iso_of_localization (g : P')
    (M : Type u) [AddCommGroup M] [Module P M] [Module (TensorProduct A' P' A) M]
    (hsmul : ∀ (x : TensorProduct A' P' A) (m : M),
      x • m = (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm x • m)
    (L : Type u) [AddCommGroup L] [Module (Localization.Away g) L] :
    letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
      (Localization.awayMap (algebraMap P' P) g).toAlgebra
    letI := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
    Nonempty ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
        ≃ₗ[Localization.Away (algebraMap P' P g)]
          (Localization.Away (algebraMap P' P g) ⊗[P] M)) →
      Nonempty ((ModuleCat.extendScalars.{u, u, u} (algebraMap (Localization.Away g)
          (TensorProduct A' (Localization.Away g) A))).obj
            (ModuleCat.of (Localization.Away g) L) ≅
        ModuleCat.of (TensorProduct A' (Localization.Away g) A)
          (ULift.{u} (TensorProduct (TensorProduct A' P' A)
            (TensorProduct A' (Localization.Away g) A) (ULift.{u} M)))) := by
  let : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
    (Localization.awayMap (algebraMap P' P) g).toAlgebra
  let := tensorBaseChangeAlgebra A' A P' (Localization.Away g)
  intro hLiso
  rw [nonempty_extendScalars_iso_iff]
  have hcommg := ringEquivLocalizationTensorBaseChange_algebraMap_away A' A P' P hsurjA
    hsurjP hkerP g
  have hcommPg := ringEquivLocalizationTensorBaseChange_algebraMap A' A P' P hsurjA hsurjP
    hkerP g
  set t := tensorEquivOfRingEquiv
    (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP)
    (ringEquivLocalizationTensorBaseChange A' A P' P hsurjA hsurjP hkerP g) hcommPg
    (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm.toAddEquiv
    (ulift_up_semilinear A' A P' P hsurjA hsurjP hkerP M hsmul)
  have hts := tensorEquivOfRingEquiv_smul
    (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP)
    (ringEquivLocalizationTensorBaseChange A' A P' P hsurjA hsurjP hkerP g) hcommPg
    (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm.toAddEquiv
    (ulift_up_semilinear A' A P' P hsurjA hsurjP hkerP M hsmul)
  refine (nonempty_tensor_linearEquiv_congr (RingEquiv.refl (Localization.Away g))
      (ringEquivLocalizationTensorBaseChange A' A P' P hsurjA hsurjP hkerP g) hcommg
      (AddEquiv.refl L) (fun _ _ => rfl)
    (t.trans (ULift.moduleEquiv
      (R := TensorProduct A' (Localization.Away g) A)
      (M := TensorProduct (TensorProduct A' P' A)
        (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))).symm.toAddEquiv)
    (fun s y => ?_)).mp hLiso
  change (ULift.moduleEquiv (R := TensorProduct A' (Localization.Away g) A)
    (M := TensorProduct (TensorProduct A' P' A)
      (TensorProduct A' (Localization.Away g) A) (ULift.{u} M))).symm (t (s • y)) = _
  rw [hts]
  rfl

end Thickening


/-! ### The quotient identity passes to the base changes -/

section QuotientIdentity

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- A bijection `R/J ≅ S/JS` makes every element of `S` congruent to one coming from `R`. -/
theorem exists_sub_mem_map_of_bijective_quotientMap (J : Ideal R)
    (hquot : Function.Bijective (Ideal.quotientMap (J.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map)) (s : S) :
    ∃ r : R, s - algebraMap R S r ∈ J.map (algebraMap R S) := by
  obtain ⟨y, hy⟩ := hquot.2 (Ideal.Quotient.mk _ s)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.quotientMap_mk] at hy
  exact ⟨r, (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hy.symm⟩

/-- A bijection `R/J ≅ S/JS` detects membership in `J`. -/
theorem mem_of_algebraMap_mem_map_of_bijective_quotientMap (J : Ideal R)
    (hquot : Function.Bijective (Ideal.quotientMap (J.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map)) {r : R} (hr : algebraMap R S r ∈ J.map (algebraMap R S)) : r ∈ J := by
  refine Ideal.Quotient.eq_zero_iff_mem.mp (hquot.1 ?_)
  rwa [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]

/-- **Moving a coefficient across the quotient identity.** If every element of `S` is congruent
modulo `JS` to one coming from `R`, then every element of the extension of an ideal `I` is
congruent modulo `JS` to the image of an element of `I`. -/
theorem exists_mem_and_sub_algebraMap_mem_map (J I : Ideal R)
    (hsurj : ∀ s : S, ∃ r : R, s - algebraMap R S r ∈ J.map (algebraMap R S))
    {x : S} (hx : x ∈ I.map (algebraMap R S)) :
    ∃ b ∈ I, x - algebraMap R S b ∈ J.map (algebraMap R S) := by
  rw [Ideal.map, Ideal.span] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨b, hb, by simp⟩
  | zero => exact ⟨0, I.zero_mem, by simp⟩
  | add y z _ _ ihy ihz =>
      obtain ⟨b₁, hb₁, h₁⟩ := ihy
      obtain ⟨b₂, hb₂, h₂⟩ := ihz
      refine ⟨b₁ + b₂, I.add_mem hb₁ hb₂, ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ h₁ h₂
  | smul s y _ ih =>
      obtain ⟨b, hb, h⟩ := ih
      obtain ⟨r, hr⟩ := hsurj s
      refine ⟨r * b, I.mul_mem_left _ hb, ?_⟩
      have hrw : s • y - algebraMap R S (r * b) =
          s * (y - algebraMap R S b) + (s - algebraMap R S r) * algebraMap R S b := by
        rw [map_mul, smul_eq_mul]; ring
      rw [hrw]
      exact Submodule.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ hr)

/-- **The quotient identity `R/J = S/JS` passes to a thickening.** Let `R → R₀` and `S → S₀` be
surjections over a flat map `R → S`, with the kernel of `S → S₀` the extension of the kernel of
`R → R₀`. If `R/J → S/JS` is bijective then so is `R₀/JR₀ → S₀/JS₀`. -/
theorem bijective_quotientMap_of_ker_map {R₀ S₀ : Type u} [CommRing R₀] [CommRing S₀]
    [Algebra R R₀] [Algebra S S₀] [Algebra R₀ S₀]
    (hcompat : ∀ r : R,
      algebraMap R₀ S₀ (algebraMap R R₀ r) = algebraMap S S₀ (algebraMap R S r))
    (hsurjS : Function.Surjective (algebraMap S S₀))
    (hsurjR : Function.Surjective (algebraMap R R₀))
    (hkerS : RingHom.ker (algebraMap S S₀) =
      (RingHom.ker (algebraMap R R₀)).map (algebraMap R S))
    (J : Ideal R)
    (hquot : Function.Bijective (Ideal.quotientMap (J.map (algebraMap R S)) (algebraMap R S)
      Ideal.le_comap_map)) :
    Function.Bijective (Ideal.quotientMap ((J.map (algebraMap R R₀)).map (algebraMap R₀ S₀))
      (algebraMap R₀ S₀) Ideal.le_comap_map) := by
  have hcomp : (algebraMap R₀ S₀).comp (algebraMap R R₀) =
      (algebraMap S S₀).comp (algebraMap R S) := RingHom.ext hcompat
  have hJS₀ : (J.map (algebraMap R R₀)).map (algebraMap R₀ S₀) =
      (J.map (algebraMap R S)).map (algebraMap S S₀) := by
    rw [Ideal.map_map, Ideal.map_map, hcomp]
  have hsurjmod := exists_sub_mem_map_of_bijective_quotientMap J hquot
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y₀ hy₀
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y₀
    obtain ⟨r, rfl⟩ := hsurjR y
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem, hJS₀, hcompat] at hy₀
    have hmem : algebraMap R S r ∈ Ideal.comap (algebraMap S S₀)
        ((J.map (algebraMap R S)).map (algebraMap S S₀)) := hy₀
    rw [Ideal.comap_map_of_surjective _ hsurjS, ← RingHom.ker_eq_comap_bot, hkerS,
      Submodule.mem_sup] at hmem
    obtain ⟨j, hj, x, hx, hsum⟩ := hmem
    obtain ⟨b, hb, hbx⟩ := exists_mem_and_sub_algebraMap_mem_map J
      (RingHom.ker (algebraMap R R₀)) hsurjmod hx
    have hrb : algebraMap R S (r - b) ∈ J.map (algebraMap R S) := by
      rw [show algebraMap R S (r - b) = j + (x - algebraMap R S b) by
        rw [map_sub, ← hsum]
        ring]
      exact Submodule.add_mem _ hj hbx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hval : algebraMap R R₀ r = algebraMap R R₀ (r - b) := by
      rw [map_sub, RingHom.mem_ker.mp hb, sub_zero]
    rw [hval]
    exact Ideal.mem_map_of_mem _
      (mem_of_algebraMap_mem_map_of_bijective_quotientMap J hquot hrb)
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, rfl⟩ := hsurjS w
    obtain ⟨r, hr⟩ := hsurjmod s
    refine ⟨Ideal.Quotient.mk _ (algebraMap R R₀ r), ?_⟩
    rw [Ideal.quotientMap_mk, hcompat, Ideal.Quotient.mk_eq_mk_iff_sub_mem, hJS₀]
    refine (Submodule.neg_mem_iff _).mp ?_
    rw [neg_sub, ← map_sub]
    exact Ideal.mem_map_of_mem _ hr

end QuotientIdentity

/-! ### Stacks 0DZ2 for an abstract pair of thickenings -/

section TwoThickenings

variable (A' A P' P Q' Q : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing P]
  [CommRing Q'] [CommRing Q]
  [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra A' P] [Algebra A' Q]
  [Algebra A P] [Algebra A Q] [Algebra P' P] [Algebra P' Q'] [Algebra P' Q]
  [Algebra P Q] [Algebra Q' Q]
  [IsScalarTower A' A P] [IsScalarTower A' A Q] [IsScalarTower A' P' P]
  [IsScalarTower A' P' Q'] [IsScalarTower A' Q' Q] [IsScalarTower A P Q]
  [IsScalarTower P' P Q] [IsScalarTower P' Q' Q] [Module.Flat A' P'] [Module.Flat A' Q']
  (hsurjA : Function.Surjective (algebraMap A' A))
  (hsurjP : Function.Surjective (algebraMap P' P))
  (hkerP : RingHom.ker (algebraMap P' P) =
    (RingHom.ker (algebraMap A' A)).map (algebraMap A' P'))
  (hsurjQ : Function.Surjective (algebraMap Q' Q))
  (hkerQ : RingHom.ker (algebraMap Q' Q) =
    (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q'))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

include hsurjA hsurjP hkerP hsurjQ hkerQ in
omit [IsScalarTower A P Q] [Algebra A' P] [Algebra A' Q] [Algebra A P] [Algebra A Q]
  [IsScalarTower A' A P] [IsScalarTower A' A Q] [IsScalarTower A' P' P] [IsScalarTower A' Q' Q] in
/-- The two identifications with the literal base changes intertwine the top ring map with its
base change. -/
theorem ringEquivTensorBaseChange_algebraMap_top (p : P) :
    letI := tensorBaseChangeAlgebra A' A P' Q'
    ringEquivTensorBaseChange A' A Q' Q hsurjA hsurjQ hkerQ (algebraMap P Q p) =
      algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A)
        (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP p) := by
  let := tensorBaseChangeAlgebra A' A P' Q'
  obtain ⟨x, rfl⟩ := hsurjP p
  rw [← IsScalarTower.algebraMap_apply P' P Q, IsScalarTower.algebraMap_apply P' Q' Q,
    ringEquivTensorBaseChange_algebraMap, ringEquivTensorBaseChange_algebraMap,
    tensorBaseChangeAlgebra_algebraMap]

/-- The kernel of the upper thickening is the extension of the kernel of the lower one. -/
theorem ker_algebraMap_tensorProduct_map :
    RingHom.ker (algebraMap Q' (TensorProduct A' Q' A)) =
      (RingHom.ker (algebraMap P' (TensorProduct A' P' A))).map (algebraMap P' Q') := by
  rw [Algebra.ker_algebraMap_tensorProduct_left A' Q' A,
    Algebra.ker_algebraMap_tensorProduct_left A' P' A, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

omit [IsScalarTower A P Q] [Algebra A' P] [Algebra A' Q] [Algebra A P] [Algebra A Q]
  [IsScalarTower A' A P] [IsScalarTower A' A Q] [IsScalarTower A' P' P] [IsScalarTower A' Q' Q] in
/-- **The base change `Q ⊗_P M` over the literal base changes.** An isomorphism
`Q ⊗_P M ≅ N` gives the extension of scalars of `M` along `P' ⊗_{A'} A → Q' ⊗_{A'} A` as `N`,
both modules restricted to the literal base changes through their identifications. -/
private theorem nonempty_extendScalars_iso_tensorBaseChange
    (M : Type u) [AddCommGroup M] [Module P M] [Module (TensorProduct A' P' A) M]
    (hsmulM : ∀ (x : TensorProduct A' P' A) (m : M),
      x • m = (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm x • m)
    (N : Type u) [AddCommGroup N] [Module Q N] [Module (TensorProduct A' Q' A) N]
    (hsmulN : ∀ (x : TensorProduct A' Q' A) (n : N),
      x • n = (ringEquivTensorBaseChange A' A Q' Q hsurjA hsurjQ hkerQ).symm x • n)
    (hMN : Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N)) :
    letI := tensorBaseChangeAlgebra A' A P' Q'
    Nonempty ((ModuleCat.extendScalars.{u, u, u}
      (algebraMap (TensorProduct A' P' A) (TensorProduct A' Q' A))).obj
        (ModuleCat.of (TensorProduct A' P' A) (ULift.{u} M)) ≅
      ModuleCat.of (TensorProduct A' Q' A) (ULift.{u} N)) := by
  let := tensorBaseChangeAlgebra A' A P' Q'
  have hcommPQ := ringEquivTensorBaseChange_algebraMap_top A' A P' P Q' Q hsurjA hsurjP hkerP
    hsurjQ hkerQ
  rw [nonempty_extendScalars_iso_iff]
  exact (nonempty_tensor_linearEquiv_congr
    (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP)
    (ringEquivTensorBaseChange A' A Q' Q hsurjA hsurjQ hkerQ) hcommPQ
    (ULift.moduleEquiv (R := TensorProduct A' P' A) (M := M)).symm.toAddEquiv
    (ulift_up_semilinear A' A P' P hsurjA hsurjP hkerP M hsmulM)
    (ULift.moduleEquiv (R := TensorProduct A' Q' A) (M := N)).symm.toAddEquiv
    (ulift_up_semilinear A' A Q' Q hsurjA hsurjQ hkerQ N hsmulN)).mp hMN

include hsurjA hsurjP hkerP hsurjQ hkerQ in
/-- **Stacks 0DZ2 at an abstract pair of thickenings, for a square-zero kernel.** This is the
statement of Stacks 0DZ2 in the shape the proof of Stacks 0DZ3 produces — `P` and `Q` abstract
rings carrying the kernel identities rather than the literal base changes `P' ⊗_{A'} A` and
`Q' ⊗_{A'} A` — for a kernel of `A' → A` of square zero, and for `M` finite over `P`.

The two restrictions are exactly the two the proved form carries. `M` finite is what the
`Ext` base change of Stacks 0A6A needs. Square-zero kernel is what makes the two thickenings
`P' → P` and `Q' → Q` square-zero, which is what the obstruction calculus of Stacks 0DYR
needs; the form of Stacks 0DZ2 proved in
`StacksFrontier.Deformation.FlatModuleLiftLocalization` already allows the kernel of `A' → A` to
be merely nilpotent provided the two thickenings are square-zero, and it is that form which is
used here. -/
theorem exists_flatModuleLift_iff_baseChange_of_sq_zero
    [IsNoetherianRing P] [Module.Flat P' Q'] [Module.Flat P Q]
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map))
    (M : Type u) [AddCommGroup M] [Module P M] [Module A M] [IsScalarTower A P M]
      [Module.Finite P M] [Module.Flat A M] (N : Type u) [AddCommGroup N] [Module Q N]
    (hMN : Nonempty ((Q ⊗[P] M) ≃ₗ[Q] N))
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g) (Localization.Away (algebraMap P' P g)) :=
        (Localization.awayMap (algebraMap P' P) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' P g) ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' P g)]
              (Localization.Away (algebraMap P' P g) ⊗[P] M))) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((P ⊗[P'] M') ≃ₗ[P] M)) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty ((Q ⊗[Q'] N') ≃ₗ[Q] N)) := by
  classical
  let := tensorBaseChangeAlgebra A' A P' Q'
  let : Algebra (TensorProduct A' P' A) P :=
    algebraTensorBaseChange A' A P' P hsurjA hsurjP hkerP
  let : Algebra (TensorProduct A' Q' A) Q :=
    algebraTensorBaseChange A' A Q' Q hsurjA hsurjQ hkerQ
  let : Module (TensorProduct A' P' A) M :=
    Module.compHom M (algebraMap (TensorProduct A' P' A) P)
  let : Module (TensorProduct A' Q' A) N :=
    Module.compHom N (algebraMap (TensorProduct A' Q' A) Q)
  let : Module A N := Module.compHom N (algebraMap A Q)
  have : IsNoetherianRing (TensorProduct A' P' A) :=
    isNoetherianRing_of_ringEquiv P (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP)
  have : IsScalarTower (TensorProduct A' P' A) P M :=
    isScalarTower_of_smul_algebraMap (fun _ _ => rfl)
  have : IsScalarTower (TensorProduct A' Q' A) Q N :=
    isScalarTower_of_smul_algebraMap (fun _ _ => rfl)
  have : IsScalarTower A Q N := isScalarTower_of_smul_algebraMap (fun _ _ => rfl)
  have : Module.Finite (TensorProduct A' P' A) M := by
    rw [Module.finite_def]
    exact (Module.Finite.fg_top (R := P) (M := M)).restrictScalars_of_surjective
      (ringEquivTensorBaseChange A' A P' P hsurjA hsurjP hkerP).symm.surjective
  have := isScalarTower_base_tensorBaseChange A' A P' P hsurjA hsurjP hkerP M fun _ _ => rfl
  have := isScalarTower_base_tensorBaseChange A' A Q' Q hsurjA hsurjQ hkerQ N fun _ _ => rfl
  have : Module.Flat A N := flat_base_of_baseChangeEquiv A P Q M N hMN.some
  have hquot₀ := bijective_quotientMap_of_ker_map (R := P') (S := Q')
    (R₀ := TensorProduct A' P' A) (S₀ := TensorProduct A' Q' A)
    (tensorBaseChangeAlgebra_algebraMap A' A P' Q') (surjective_tmul_one A' A hsurjA Q')
    (surjective_tmul_one A' A hsurjA P') (ker_algebraMap_tensorProduct_map A' A P' Q') J' hquot
  -- Stacks 0DZ2 over the literal base changes
  rw [exists_flatModuleLift_iff_tensorBaseChange A' A P' P hsurjA hsurjP hkerP M
      (fun _ _ => rfl),
    exists_flatModuleLift_iff_tensorBaseChange A' A Q' Q hsurjA hsurjQ hkerQ N
      (fun _ _ => rfl)]
  exact exists_flat_lift_iff_exists_flat_lift_baseChange_of_localizationLift_of_isNilpotent_ker
    A' A P' Q' hsurjA ⟨2, hzeroA⟩ (sq_ker_algebraMap_tensorProduct_eq_bot A' A P' hzeroA)
    (RingHom.ext (tensorBaseChangeAlgebra_algebraMap A' A P' Q'))
    (flat_tensorBaseChangeAlgebra A' A P' Q') J' hquot₀ M N
    (nonempty_extendScalars_iso_tensorBaseChange A' A P' P Q' Q hsurjA hsurjP hkerP hsurjQ
      hkerQ M (fun _ _ => rfl) N (fun _ _ => rfl) hMN) _ (minus_q_single _ _) (Iso.refl _)
    fun g hg => by
      obtain ⟨L, _, _, _, _, hLflat, hLiso⟩ := hloc g hg
      exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, hLflat,
        nonempty_extendScalars_iso_of_localization A' A P' P hsurjA hsurjP hkerP g M
          (fun _ _ => rfl) L hLiso⟩

end TwoThickenings

/-! ### Stacks 0DZ3 at a square-zero kernel -/

/-- **Stacks 0DZ2 as the proof of Stacks 0DZ3 consumes it, for a square-zero kernel.** The
hypothesis `h0DZ2` that `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_at`
carries, discharged whenever the kernel of `A' → A` has square zero. -/
theorem flatModuleLiftBaseChangeStatementAt_of_sq_zero (A' A : Type u) [CommRing A']
    [CommRing A] [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥) :
    FlatModuleLiftBaseChangeStatementAt.{u} A' A := by
  intro P' P Q' Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _hsurjA _hnilA hsurjP hkerP
    hsurjQ hkerQ _ _ _ _ J' hquot M _ _ _ _ _ _ N _ _ hMN hloc
  have : IsScalarTower A' A Q := by
    refine IsScalarTower.of_algebraMap_eq fun a' => ?_
    rw [IsScalarTower.algebraMap_apply A P Q, ← IsScalarTower.algebraMap_apply A' A P,
      IsScalarTower.algebraMap_apply A' P' P, ← IsScalarTower.algebraMap_apply P' P Q,
      IsScalarTower.algebraMap_apply P' Q' Q, ← IsScalarTower.algebraMap_apply A' P' Q',
      ← IsScalarTower.algebraMap_apply A' Q' Q]
  exact exists_flatModuleLift_iff_baseChange_of_sq_zero A' A P' P Q' Q hsurjA hsurjP hkerP
    hsurjQ hkerQ hzeroA J' hquot M N hMN hloc

/-- **The second implication of Stacks 0DZ3, unconditionally, for a square-zero kernel.** For a
surjection `A' → A` of Noetherian rings whose kernel has square zero and a finite type flat
`A`-algebra `B` with `A → B_h` syntomic for every `h` in an ideal `𝔟`, a flat lift of the
`𝔟`-adic completion of `B` to `A'` gives one of `B`.

This is `Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_at` with its
hypothesis `h0DZ2` discharged by
`Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`. -/
theorem hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_sq_zero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A (AdicCompletion b B) → HasFlatAlgebraLift A' A B :=
  hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_at A' A B
    (flatModuleLiftBaseChangeStatementAt_of_sq_zero A' A hsurjA hzeroA) hsurjA ⟨2, hzeroA⟩ b
    hsyn

/-- **Stacks 0DZ3 at a square-zero kernel, unconditionally.** For a surjection `A' → A` of
Noetherian rings whose kernel has square zero and a finite type flat `A`-algebra `B` with
`A → B_h` syntomic for every `h` in an ideal `𝔟`, flat lifts of `B` to `A'` exist exactly when
flat lifts of the `𝔟`-adic completion of `B` do.

This is `Deformation.hasFlatAlgebraLift_adicCompletion_iff_at` with its hypothesis `h0DZ2`
discharged by `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`. -/
theorem hasFlatAlgebraLift_adicCompletion_iff_of_sq_zero
    (A' A B : Type u) [CommRing A'] [CommRing A] [CommRing B]
    [IsNoetherianRing A'] [IsNoetherianRing A] [Algebra A' A] [Algebra A B]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)
    [Algebra.FiniteType A B] [Module.Flat A B] (b : Ideal B)
    (hsyn : ∀ h ∈ b, Algebra.Syntomic A (Localization.Away h)) :
    HasFlatAlgebraLift A' A B ↔ HasFlatAlgebraLift A' A (AdicCompletion b B) :=
  hasFlatAlgebraLift_adicCompletion_iff_at A' A B
    (flatModuleLiftBaseChangeStatementAt_of_sq_zero A' A hsurjA hzeroA) hsurjA ⟨2, hzeroA⟩ b
    hsyn

/-! ### Stacks 0DZ2 at the literal base change of the presentation -/

section AbstractTarget

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Stacks 0DZ2 in the shape its consumers use, for a square-zero kernel.** Let `A' → A` be
a surjection with square-zero kernel, let `P'` be a flat `A'`-algebra, let `Q'` be a flat
`P'`-algebra, let `P = P' ⊗_{A'} A` and `Q = P ⊗_{P'} Q'`, let `J'` be an ideal of `P'` with
`P'/J' = Q'/J'Q'`, and let `M` be an `A`-flat finite `P`-module whose localizations at the
elements of `J'` have `A'`-flat lifts over the localizations of `P'`. Then `M` has an `A'`-flat
`P'`-module lift if and only if a `Q`-module `N` isomorphic to `Q ⊗_P M` has an `A'`-flat
`Q'`-module lift. -/
theorem exists_flatModuleLift_iff_baseChange_of_sqZero
    (A' A P' Q' : Type u) [CommRing A'] [CommRing A] [CommRing P'] [CommRing Q']
    [Algebra A' A] [Algebra A' P'] [Algebra A' Q'] [Algebra P' Q'] [IsScalarTower A' P' Q']
    [Module.Flat A' P'] [Module.Flat P' Q']
    [IsNoetherianRing (TensorProduct A' P' A)]
    (hsurjA : Function.Surjective (algebraMap A' A))
    (hzeroA : (RingHom.ker (algebraMap A' A)) ^ 2 = ⊥)
    (J' : Ideal P')
    (hquot : Function.Bijective (Ideal.quotientMap (J'.map (algebraMap P' Q'))
      (algebraMap P' Q') Ideal.le_comap_map))
    (M : Type u) [AddCommGroup M] [Module (TensorProduct A' P' A) M] [Module A M]
      [IsScalarTower A (TensorProduct A' P' A) M]
      [Module.Finite (TensorProduct A' P' A) M] [Module.Flat A M]
    (N : Type u) [AddCommGroup N]
      [Module (TensorProduct A' P' A ⊗[P'] Q') N]
    (hN : Nonempty (((TensorProduct A' P' A ⊗[P'] Q') ⊗[TensorProduct A' P' A] M)
      ≃ₗ[TensorProduct A' P' A ⊗[P'] Q'] N))
    (hloc : ∀ g ∈ J',
      letI : Algebra (Localization.Away g)
          (Localization.Away (algebraMap P' (TensorProduct A' P' A) g)) :=
        (Localization.awayMap (algebraMap P' (TensorProduct A' P' A)) g).toAlgebra
      ∃ (L : Type u) (_ : AddCommGroup L) (_ : Module (Localization.Away g) L)
        (_ : Module A' L) (_ : IsScalarTower A' (Localization.Away g) L),
        Module.Flat A' L ∧ Nonempty
          ((Localization.Away (algebraMap P' (TensorProduct A' P' A) g)
              ⊗[Localization.Away g] L)
            ≃ₗ[Localization.Away (algebraMap P' (TensorProduct A' P' A) g)]
              (Localization.Away (algebraMap P' (TensorProduct A' P' A) g)
                ⊗[TensorProduct A' P' A] M))) :
    (∃ (M' : Type u) (_ : AddCommGroup M') (_ : Module P' M') (_ : Module A' M')
        (_ : IsScalarTower A' P' M'), Module.Flat A' M' ∧
        Nonempty ((TensorProduct A' P' A ⊗[P'] M') ≃ₗ[TensorProduct A' P' A] M)) ↔
      (∃ (N' : Type u) (_ : AddCommGroup N') (_ : Module Q' N') (_ : Module A' N')
        (_ : IsScalarTower A' Q' N'), Module.Flat A' N' ∧
        Nonempty (((TensorProduct A' P' A ⊗[P'] Q') ⊗[Q'] N')
          ≃ₗ[TensorProduct A' P' A ⊗[P'] Q'] N)) := by
  have hsurjP : Function.Surjective (algebraMap P' (TensorProduct A' P' A)) :=
    surjective_tmul_one A' A hsurjA P'
  have hkerP : RingHom.ker (algebraMap P' (TensorProduct A' P' A)) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' P') :=
    Algebra.ker_algebraMap_tensorProduct_left A' P' A
  have : Module.Flat A' Q' := Module.Flat.trans A' P' Q'
  have hkerQ : RingHom.ker (algebraMap Q' (TensorProduct A' P' A ⊗[P'] Q')) =
      (RingHom.ker (algebraMap A' A)).map (algebraMap A' Q') := by
    have h := ker_includeRight P' (TensorProduct A' P' A) Q' hsurjP
    rwa [hkerP, Ideal.map_map, ← IsScalarTower.algebraMap_eq] at h
  have : IsScalarTower A' Q' (TensorProduct A' P' A ⊗[P'] Q') :=
    IsScalarTower.of_algebraMap_eq fun a' => by
      rw [show algebraMap A' (TensorProduct A' P' A ⊗[P'] Q') a' =
          (algebraMap A' (TensorProduct A' P' A) a') ⊗ₜ[P'] (1 : Q') from rfl,
        show algebraMap Q' (TensorProduct A' P' A ⊗[P'] Q') (algebraMap A' Q' a') =
          (1 : TensorProduct A' P' A) ⊗ₜ[P'] (algebraMap A' Q' a') from rfl,
        IsScalarTower.algebraMap_apply A' P' (TensorProduct A' P' A),
        IsScalarTower.algebraMap_apply A' P' Q',
        Algebra.algebraMap_eq_smul_one (R := P') (A := TensorProduct A' P' A),
        Algebra.algebraMap_eq_smul_one (R := P') (A := Q'), TensorProduct.smul_tmul]
  -- Stacks 0DZ2, through its form at an abstract pair of thickenings
  exact exists_flatModuleLift_iff_baseChange_of_sq_zero A' A P' (TensorProduct A' P' A) Q'
    (TensorProduct A' P' A ⊗[P'] Q') hsurjA hsurjP hkerP
    (surjective_includeRight P' (TensorProduct A' P' A) Q' hsurjP) hkerQ hzeroA J' hquot M N
    hN hloc

end AbstractTarget

end Deformation

end
