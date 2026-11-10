module

public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.PolynomialPresentation
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Basic
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.SetIndexed
public import StacksFrontier.RingTheory.DividedPowers.Polynomial.Stages

/-!
# Base change of a presentation of a divided power envelope

Let `(B, I, γ)` be a divided power ring and let `J = I + (f t : t ∈ T)` be an ideal of `B`
generated over `I` by a family of elements.  The divided power envelope `D` of `J` is then a
quotient of the divided power polynomial algebra `B⟨x_t⟩` on the generating family, by the kernel
`K` of the presentation.

Extending the coefficients along a ring map `B → B'` carries that presentation to a presentation
of `D ⊗_B B'` by the divided power polynomial algebra `B'⟨x_t⟩`, modulo the extension of `K`
along the coefficient-change map.  The resulting isomorphism sends the class of `ψ(p) ⊗ b'` to
the class of `b'` times the coefficient-change of `p`.

## Main results

* `Crystalline.dividedPowerEnvelope_tensor_equiv_quotient` gives that base-changed quotient
  presentation, together with the formula for the isomorphism on pure tensors.

## Implementation notes

The relation ideal is taken to be the kernel of the surjective presentation map rather than a
chosen list of generators, so no description of the relations is needed; its extension along the
coefficient-change map of divided power polynomial algebras is then exactly the ideal generated
by the images of the original relations.

## References

* [Stacks Project, Tag 07HF](https://stacks.math.columbia.edu/tag/07HF)
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Crystalline

open DividedPowers

universe u v w

/-- Extension of coefficients of a divided power polynomial algebra: `B' ⊗[B] B⟨x_t⟩ ≃ B'⟨x_t⟩`
as `B'`-algebras. -/
private noncomputable def dividedPowerPolynomialBaseChangeEquiv
    (B : DividedPowerRing.{u}) (T : Type w)
    (B' : Type v) [CommRing B'] [Algebra B B'] :
    (B' ⊗[B] setIndexedDividedPowerPolynomialAlgebra B T) ≃ₐ[B']
      setIndexedDividedPowerPolynomialAlgebra B' T := by
  let F := setIndexedDividedPowerPolynomialAlgebra B T
  let F' := setIndexedDividedPowerPolynomialAlgebra B' T
  let φ : F →ₐ[B] F' :=
    DividedPowerAlgebra.map B'
      (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B'))
  let lift : B' ⊗[B] F →ₐ[B'] F' :=
    Algebra.TensorProduct.lift (Algebra.ofId B' F') φ (fun _ _ ↦ Commute.all _ _)
  let b := DividedPowers.dividedPowerPolynomialMonomialBasis B T
  let b' := DividedPowers.dividedPowerPolynomialMonomialBasis B' T
  have hlin : lift.toLinearMap = (b.baseChange B').equiv b' (Equiv.refl _) := by
    refine (b.baseChange B').ext fun n => ?_
    change lift.toLinearMap ((b.baseChange B') n) =
      ((b.baseChange B').equiv b' (Equiv.refl _)) ((b.baseChange B') n)
    rw [Module.Basis.equiv_apply (b.baseChange B') n b' (Equiv.refl _), Equiv.refl_apply,
      Module.Basis.baseChange_apply]
    change lift (1 ⊗ₜ[B] b n) = b' n
    rw [Algebra.TensorProduct.lift_tmul]
    simp only [map_one, one_mul]
    rw [DividedPowers.dividedPowerPolynomialMonomialBasis_apply,
      DividedPowers.dividedPowerPolynomialMonomialBasis_apply]
    change φ (DividedPowers.dividedPowerPolynomialMonomial B n) =
      DividedPowers.dividedPowerPolynomialMonomial B' n
    simp only [φ, DividedPowers.dividedPowerPolynomialMonomial, Finsupp.prod, map_prod]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [DividedPowerAlgebra.map_apply_dp]
    congr 1
    ext y
    simp [Finsupp.mapRange.linearMap_apply, Algebra.linearMap_apply]
  have hb : Function.Bijective lift.toLinearMap := by
    rw [hlin]
    exact ((b.baseChange B').equiv b' (Equiv.refl _)).bijective
  exact AlgEquiv.ofBijective lift hb

private lemma dividedPowerPolynomialBaseChangeEquiv_tmul
    (B : DividedPowerRing.{u}) (T : Type w) (B' : Type v) [CommRing B'] [Algebra B B']
    (b' : B') (p : setIndexedDividedPowerPolynomialAlgebra B T) :
    dividedPowerPolynomialBaseChangeEquiv B T B' (b' ⊗ₜ[B] p) =
      algebraMap B' _ b' *
        DividedPowerAlgebra.map B'
          (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B')) p := by
  change Algebra.TensorProduct.lift (Algebra.ofId B' _)
      (DividedPowerAlgebra.map B'
        (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B')))
      (fun _ _ ↦ Commute.all _ _) (b' ⊗ₜ[B] p) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

/-- A surjection `ψ : F → A` of `B`-algebras and an identification `B' ⊗[B] F ≃ F'` restricting
to `φ` on `F` present `A ⊗[B] B'` as the quotient of `F'` by the extension of `ker ψ` along `φ`. -/
private theorem exists_tensor_ringEquiv_quotient_map_ker {B A F F' B' : Type*} [CommRing B]
    [CommRing A] [CommRing F] [CommRing F'] [CommRing B'] [Algebra B A] [Algebra B F]
    [Algebra B B'] [Algebra B' F'] (ψ : F →ₐ[B] A) (hψ : Function.Surjective ψ)
    (eF : B' ⊗[B] F ≃ₐ[B'] F') (φ : F →+* F')
    (heF : ∀ b' p, eF (b' ⊗ₜ[B] p) = algebraMap B' F' b' * φ p) :
    ∃ e : A ⊗[B] B' ≃+* F' ⧸ (RingHom.ker ψ).map φ,
      ∀ p b', e (ψ p ⊗ₜ[B] b') = Ideal.Quotient.mk _ (φ p * algebraMap B' F' b') := by
  let I : Ideal F := RingHom.ker ψ
  let K' : Ideal F' := I.map φ
  let q := Ideal.quotientKerAlgEquivOfSurjective hψ
  let e₁ : A ⊗[B] B' ≃ₐ[B] (F ⧸ I) ⊗[B] B' :=
    Algebra.TensorProduct.congr q.symm AlgEquiv.refl
  let e₂ := (Algebra.TensorProduct.comm B (F ⧸ I) B').toRingEquiv
  let e₃ := Algebra.TensorProduct.tensorQuotientEquiv (R := B) B' F B' I
  let I' : Ideal (B' ⊗[B] F) :=
    I.map (Algebra.TensorProduct.includeRight : F →ₐ[B] B' ⊗[B] F).toRingHom
  have hbase : eF.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight : F →ₐ[B] B' ⊗[B] F).toRingHom = φ :=
    RingHom.ext fun p => by
      change eF (1 ⊗ₜ[B] p) = φ p
      simpa using heF 1 p
  have hI : K' = Ideal.map eF.toRingEquiv.toRingHom I' := by
    rw [Ideal.map_map, hbase]
  let e₄ := Ideal.quotientEquiv I' K' eF.toRingEquiv hI
  refine ⟨e₁.toRingEquiv.trans (e₂.trans (e₃.toRingEquiv.trans e₄)), fun p b' => ?_⟩
  have hq : q.symm (ψ p) = Ideal.Quotient.mk I p :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hψ p
  have he₁ : e₁ (ψ p ⊗ₜ[B] b') = Ideal.Quotient.mk I p ⊗ₜ[B] b' := by
    change (Algebra.TensorProduct.congr q.symm AlgEquiv.refl) (ψ p ⊗ₜ[B] b') = _
    rw [Algebra.TensorProduct.congr_apply]
    simp [Algebra.TensorProduct.map_tmul, hq]
  have he₂ : e₂ (Ideal.Quotient.mk I p ⊗ₜ[B] b') = b' ⊗ₜ[B] Ideal.Quotient.mk I p :=
    Algebra.TensorProduct.comm_tmul B (Ideal.Quotient.mk I p) b'
  have he₃ : e₃ (b' ⊗ₜ[B] Ideal.Quotient.mk I p) = Ideal.Quotient.mk I' (b' ⊗ₜ[B] p) := by
    change Algebra.TensorProduct.tensorQuotientEquiv (R := B) B' F B' I
      (b' ⊗ₜ[B] Ideal.Quotient.mk I p) = _
    rw [Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul (R := B) B' F B' I]
    rfl
  have he₄ : e₄ (Ideal.Quotient.mk I' (b' ⊗ₜ[B] p)) =
      Ideal.Quotient.mk K' (eF (b' ⊗ₜ[B] p)) :=
    Ideal.quotientEquiv_mk I' K' eF.toRingEquiv hI (b' ⊗ₜ[B] p)
  change e₄ (e₃ (e₂ (e₁ (ψ p ⊗ₜ[B] b')))) = _
  rw [he₁, he₂, he₃, he₄, heF]
  exact congrArg (Ideal.Quotient.mk K') (mul_comm _ _)

/-- The quotient presentation of a divided power envelope after extension of its
coefficient ring. The formula on pure tensors identifies the displayed equivalence
with the canonical base-change map. -/
@[stacks 07HF]
public theorem dividedPowerEnvelope_tensor_equiv_quotient
    (B : DividedPowerRing.{u}) (T : Type w)
    (J : Ideal B) (hJ : B.ideal.map (RingHom.id B) ≤ J)
    (f : T → B) (hf : J = B.ideal ⊔ Ideal.span (Set.range f))
    (D : DividedPowerEnvelope B (RingHom.id B) J hJ)
    (B' : Type v) [CommRing B'] [Algebra B B'] :
    letI : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
    let ψ := (surjectiveDividedPowerPolynomialMap B T J hJ f hf D).1
    let F := setIndexedDividedPowerPolynomialAlgebra B T
    let F' := setIndexedDividedPowerPolynomialAlgebra B' T
    let baseChange : F →+* F' :=
      (DividedPowerAlgebra.map B'
        (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B'))).toRingHom
    let K' : Ideal F' := (RingHom.ker ψ.toRingHom).map baseChange
    ∃ e : (D.object ⊗[B] B') ≃+* (F' ⧸ K'),
      ∀ (p : F) (b' : B'),
        e (TensorProduct.tmul B (ψ p) b') =
          Ideal.Quotient.mk K' (baseChange p * algebraMap B' F' b') := by
  classical
  let : Algebra B D.object := D.algebraMap.toRingHom.toAlgebra
  let surj := surjectiveDividedPowerPolynomialMap B T J hJ f hf D
  let ψ := surj.1
  let F := setIndexedDividedPowerPolynomialAlgebra B T
  let F' := setIndexedDividedPowerPolynomialAlgebra B' T
  let baseChange : F →+* F' :=
    (DividedPowerAlgebra.map B'
      (Finsupp.mapRange.linearMap (α := T) (Algebra.linearMap B B'))).toRingHom
  have hcompat : ψ.toRingHom.comp (algebraMap B F) = algebraMap B D.object := by
    have hcoeff :
        (setIndexedDividedPowerPolynomialCoefficientDPMorphism B T).toRingHom =
          algebraMap B F := rfl
    have hstruct' : D.algebraMap.toRingHom = D.structureMap.toRingHom := by
      simpa using D.algebraMap_comp
    rw [← hcoeff, ← show D.structureMap.toRingHom = algebraMap B D.object from hstruct'.symm,
      ← DividedPowers.DPMorphism.comp_toRingHom]
    exact congrArg DividedPowers.DPMorphism.toRingHom surj.property.1
  let ψAlg : F →ₐ[B] D.object :=
    { toRingHom := ψ.toRingHom
      commutes' := RingHom.congr_fun hcompat }
  exact exists_tensor_ringEquiv_quotient_map_ker ψAlg surj.property.2.2
    (dividedPowerPolynomialBaseChangeEquiv B T B') baseChange
    (dividedPowerPolynomialBaseChangeEquiv_tmul B T B')

end Crystalline

end

end
