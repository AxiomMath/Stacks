module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The fibre of a base change is the base change of the fibre

Let `R → S` be a ring map, let `R → R'` be any ring map and let `S'` be the base change
`R' ⊗_R S`, presented as a pushout square `Algebra.IsPushout R R' S S'`. Let `p ⊆ R` and
`p' ⊆ R'` be primes with `κ(p) → κ(p')` an extension of residue fields over `R`. This file
compares the two fibres: `κ(p') ⊗_{R'} S'` is the base change of `κ(p) ⊗_R S` along
`κ(p) → κ(p')`.

## Main results

* `Ideal.Fiber.baseChangeAlgEquiv`: the comparison
  `κ(p') ⊗_{κ(p)} (κ(p) ⊗_R S) ≃ κ(p') ⊗_{R'} S'`.
* `Ideal.Fiber.isPushout_baseChange`: the square of fibres is a pushout square.

## Implementation notes

The base change is the abstract one, `Algebra.IsPushout R R' S S'`; the model `R' ⊗_R S` is a
witness by `TensorProduct.isPushout`. The residue field extension is a hypothesis,
`[Algebra p.ResidueField p'.ResidueField]` with `[IsScalarTower R p.ResidueField p'.ResidueField]`,
and `p'.LiesOver p` is not assumed.

The algebra structure `Algebra.TensorProduct.rightAlgebra` of the fibre over its second factor is
a local instance here, as in Mathlib's files about fibres. The algebra structure
`Ideal.Fiber.baseChangeAlgebra` and the scalar tower `Ideal.Fiber.isScalarTower_baseChange` depend
on the chosen pushout square and are not global instances; they must be introduced with `let` and
`have` before `Ideal.Fiber.isPushout_baseChange` is used.

## References

* [Stacks Project, Tag 02UQ](https://stacks.math.columbia.edu/tag/02UQ), smoothness at a prime
  under extension of the base field.
* [Stacks Project, Tag 00SI](https://stacks.math.columbia.edu/tag/00SI), the
  complete-intersection condition under extension of the base field.
* [Stacks Project, Tag 00RJ](https://stacks.math.columbia.edu/tag/00RJ), Cohen–Macaulayness under
  extension of the base field.
-/

@[expose] public section

open Algebra TensorProduct

namespace Ideal.Fiber

variable (R R' S S' : Type*) [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
  [Algebra R R'] [Algebra R S] [Algebra R S'] [Algebra R' S'] [Algebra S S']
  [IsScalarTower R R' S'] [IsScalarTower R S S'] [Algebra.IsPushout R R' S S']
  (p : Ideal R) [p.IsPrime] (p' : Ideal R') [p'.IsPrime]

section

variable [Algebra p.ResidueField p'.ResidueField]
  [IsScalarTower R p.ResidueField p'.ResidueField]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The fibre commutes with base change.** For `S' = R' ⊗_R S` and primes `p' ⊆ R'` over
`p ⊆ R`, the fibre `κ(p') ⊗_{R'} S'` of `S'/R'` over `p'` is the base change along
`κ(p) → κ(p')` of the fibre `κ(p) ⊗_R S` of `S/R` over `p`. -/
noncomputable def baseChangeAlgEquiv :
    p'.ResidueField ⊗[p.ResidueField] (p.Fiber S) ≃ₐ[p'.ResidueField] p'.Fiber S' :=
  haveI : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  AlgEquiv.ofRingEquiv (f :=
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField p'.ResidueField
        p'.ResidueField S).toRingEquiv.trans
      ((Algebra.TensorProduct.comm R p'.ResidueField S).toRingEquiv.trans
        ((Algebra.IsPushout.cancelBaseChangeAlg R S R' S' p'.ResidueField).symm.toRingEquiv.trans
          (Algebra.TensorProduct.comm R' S' p'.ResidueField).toRingEquiv)))
    (fun x ↦ by
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.comm_tmul,
        Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul, Algebra.TensorProduct.one_def,
        Algebra.TensorProduct.cancelBaseChange_tmul])

/-- The comparison `Ideal.Fiber.baseChangeAlgEquiv` on generators: it is `x ⊗ s ↦ x ⊗ s`. -/
theorem baseChangeAlgEquiv_tmul_tmul (y : p'.ResidueField) (x : p.ResidueField) (s : S) :
    baseChangeAlgEquiv R R' S S' p p' (y ⊗ₜ[p.ResidueField] (x ⊗ₜ[R] s))
      = (x • y) ⊗ₜ[R'] algebraMap S S' s := by
  simp [baseChangeAlgEquiv, Algebra.TensorProduct.comm_tmul,
    Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- The `κ(p) ⊗_R S`-algebra structure on `κ(p') ⊗_{R'} S'` given by the base change of the
fibre: the map `z ↦ 1 ⊗ z` read through `Ideal.Fiber.baseChangeAlgEquiv`. -/
@[instance_reducible]
noncomputable def baseChangeAlgebra : Algebra (p.Fiber S) (p'.Fiber S') :=
  ((baseChangeAlgEquiv R R' S S' p p' :
      p'.ResidueField ⊗[p.ResidueField] (p.Fiber S) →+* p'.Fiber S').comp
    (algebraMap (p.Fiber S) (p'.ResidueField ⊗[p.ResidueField] (p.Fiber S)))).toAlgebra

attribute [local instance] baseChangeAlgebra

/-- The map of fibres of `Ideal.Fiber.baseChangeAlgebra` is a map of `κ(p)`-algebras. -/
theorem isScalarTower_baseChange :
    IsScalarTower p.ResidueField (p.Fiber S) (p'.Fiber S') :=
  .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply p.ResidueField p'.ResidueField (p'.Fiber S') x]
    change _ = baseChangeAlgEquiv R R' S S' p p' (1 ⊗ₜ[p.ResidueField] _)
    simp [baseChangeAlgEquiv_tmul_tmul, Algebra.TensorProduct.algebraMap_apply,
      Algebra.smul_def]

attribute [local instance] isScalarTower_baseChange

/-- The map of fibres of `Ideal.Fiber.baseChangeAlgebra` extends `S → S'`: the square with sides
`S → S'` and `κ(p) ⊗_R S → κ(p') ⊗_{R'} S'` commutes. -/
theorem algebraMap_baseChange_comp_includeRight :
    (algebraMap (p.Fiber S) (p'.Fiber S')).comp
        (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom
      = (Algebra.TensorProduct.includeRight : S' →ₐ[R'] p'.Fiber S').toRingHom.comp
          (algebraMap S S') := by
  ext s
  change baseChangeAlgEquiv R R' S S' p p' (1 ⊗ₜ[p.ResidueField] (1 ⊗ₜ[R] s)) = _
  simp [baseChangeAlgEquiv_tmul_tmul]

/-- The map of fibres of `Ideal.Fiber.baseChangeAlgebra` on an element of `S`: the pointwise form
of `Ideal.Fiber.algebraMap_baseChange_comp_includeRight`. -/
theorem algebraMap_baseChange_includeRight (s : S) :
    algebraMap (p.Fiber S) (p'.Fiber S')
        ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) s)
      = (Algebra.TensorProduct.includeRight : S' →ₐ[R'] p'.Fiber S') (algebraMap S S' s) :=
  RingHom.congr_fun (algebraMap_baseChange_comp_includeRight R R' S S' p p') s

/-- **The square of fibres is a pushout square.** For `S' = R' ⊗_R S` and primes `p' ⊆ R'` over
`p ⊆ R`, the fibre of `S'/R'` over `p'` is the base change of the fibre of `S/R` over `p` along
the residue field extension `κ(p) → κ(p')`. -/
theorem isPushout_baseChange :
    Algebra.IsPushout p.ResidueField p'.ResidueField (p.Fiber S) (p'.Fiber S') :=
  Algebra.IsPushout.of_equiv (baseChangeAlgEquiv R R' S S' p p') rfl

end

end Ideal.Fiber

end
