module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition

import StacksCore.Tactic.StacksAttribute

/-!
# Base change of essentially finite ring maps

Essential finite type is already stable under arbitrary base change in Mathlib.  For essential
finite presentation, write the target as a localization `M⁻¹A` of a finitely presented
algebra.  After base change, `S ⊗[R] M⁻¹A` is the localization of `S ⊗[R] A` at the image
of `M`, while finite presentation of `A` base changes to finite presentation of `S ⊗[R] A`.

## Main results

* `RingHom.EssentiallyOfFinitePresentation.baseChange_algebraMap`: for an `R`-algebra `T` given by
  an ambient `Algebra R T` instance, `S → S ⊗[R] T` is essentially of finite presentation when
  `R → T` is.
* `RingHom.EssentiallyOfFinitePresentation.baseChange`: the same statement for a bare ring map
  `R → T`, read through `RingHom.toAlgebra`.
-/

@[expose] public section

open scoped TensorProduct

add_to_stacks 0AUF "(1)" RingHom.EssFiniteType.isStableUnderBaseChange
add_to_ega "IV 1.3.9" RingHom.EssFiniteType.isStableUnderBaseChange

namespace RingHom.EssentiallyOfFinitePresentation

universe u v w

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **Essential finite presentation is preserved by base change**, for an `R`-algebra `T` given
by an ambient instance: `S → S ⊗[R] T` is essentially of finite presentation as soon as
`R → T` is.

Writing `T = M⁻¹A` with `A` of finite presentation over `R`, the base change `S ⊗[R] T` is the
localization of `S ⊗[R] A` at the image of `M`
(`IsLocalization.tensorProduct_tensorProduct_right`, applied along the map
`S ⊗[R] A → S ⊗[R] T` induced by `A → T`), and `S ⊗[R] A` is of finite presentation over `S`
(`Algebra.FinitePresentation.baseChange`). -/
theorem baseChange_algebraMap {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (h : (algebraMap R T).EssentiallyOfFinitePresentation) :
    (algebraMap S (S ⊗[R] T)).EssentiallyOfFinitePresentation := by
  obtain ⟨A, instA, algRA, algAT, towerRAT, fpRA, M, locMT⟩ := h
  let := instA
  let := algRA
  let := algAT
  let := fpRA
  -- `towerRAT` is stated for the algebra structure `(algebraMap R T).toAlgebra`; read it as the
  -- equality of structure maps, which is the same for the ambient structure.
  have towerRAT' : IsScalarTower R A T := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    let : Algebra R T := (algebraMap R T).toAlgebra
    exact IsScalarTower.algebraMap_eq R A T
  let φ : (S ⊗[R] A) →ₐ[R] (S ⊗[R] T) :=
    Algebra.TensorProduct.map (AlgHom.id R S) (IsScalarTower.toAlgHom R A T)
  let algBaseChange : Algebra (S ⊗[R] A) (S ⊗[R] T) := φ.toRingHom.toAlgebra
  have towerBaseChange : IsScalarTower S (S ⊗[R] A) (S ⊗[R] T) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      show _ = φ (algebraMap S (S ⊗[R] A) x)
      simp [φ, Algebra.TensorProduct.algebraMap_apply]
  have : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) (S ⊗[R] T) :=
    IsLocalization.tensorProduct_tensorProduct_right R S M T (by
      ext x
      simp [φ, RingHom.algebraMap_toAlgebra])
  have : Algebra.FinitePresentation S (S ⊗[R] A) :=
    Algebra.FinitePresentation.baseChange S
  exact RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := S ⊗[R] A)
    (M.map (Algebra.TensorProduct.includeRight (R := R) (A := S)))

/-- **Essential finite presentation is preserved by base change.**  The target is written in the
canonical tensor-product model of the pushout; invariance under isomorphism identifies this with
any other model of the base change. -/
@[stacks 0AUF "(2)"]
theorem baseChange {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (f : R →+* T) (h : f.EssentiallyOfFinitePresentation) :
    letI := f.toAlgebra
    ((Algebra.TensorProduct.includeLeft (R := R) (S := S) (A := S) (B := T)).toRingHom)
      |>.EssentiallyOfFinitePresentation := by
  let : Algebra R T := f.toAlgebra
  exact baseChange_algebraMap (S := S) h

end RingHom.EssentiallyOfFinitePresentation

end
