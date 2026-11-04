module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeRightExact
public import StacksFrontier.Deformation.SquareZero.ConormalTorsion

/-!
# Base change of the conormal cokernel in its coefficients

Let `R → S` be a flat map of commutative rings, let `d : M → P` be a map of finitely presented
`R`-modules and let `N` be an `R`-module.  The cokernel

`coker( Hom_R(P, N) ⟶ Hom_R(M, N) )`

of precomposition with `d` commutes with base change along `R → S`: its base change to `S` is
the same cokernel taken with coefficients `S ⊗_R N`.  Both `Hom`'s commute with base change
because `M` and `P` are finitely presented and `S` is flat, and cokernels commute with base
change for formal reasons.

For a finite type algebra `B` over a field and a flat `B`-algebra `Bʰ` this says that
`Ext¹_B(NL_{B/k}, Bʰ ⊗_B N)` is `Ext¹_B(NL_{B/k}, N) ⊗_B Bʰ`, which is the flat base change
input of Stacks 0DZC.

## Main definitions

* `Deformation.Examples.lcompBaseChange`: precomposition with `d` on maps into an `S`-module,
  which is `S`-linear and not merely `R`-linear.

## Main results

* `Deformation.Examples.isBaseChange_compRight`: for a finitely presented `M` and a flat `S`,
  `Hom_R(M, S ⊗_R N)` is the base change of `Hom_R(M, N)`.
* `Deformation.Examples.homCokernelBaseChangeEquiv`: the cokernel of precomposition with `d`
  commutes with base change.
* `Deformation.Examples.extOneCokernelBaseChangeEquiv`: hence
  `Ext¹_B(NL_{B/k}, Bʰ ⊗_B N) ≅ Ext¹_B(NL_{B/k}, N) ⊗_B Bʰ`.

## Implementation notes

The coefficient module of the base-changed cokernel is `S ⊗_R N`, so the cokernel is a quotient
of `Hom_R(M, S ⊗_R N)` — an `S`-module — by the image of an `R`-linear map.  `IsBaseChange` asks
its target to be an `S`-module, and a quotient by an `R`-submodule carries no `S`-action, so the
cokernel is formed over `S` instead, by `Deformation.Examples.lcompBaseChange`, and
`Submodule.Quotient.restrictScalarsEquiv` identifies the two quotients: they are quotients of one
module by one subset, read over the two rings.

`Hom_R(M, S ⊗_R N)` is reached from `Module.FinitePresentation.isBaseChange_map`, which states the
base change property for `S ⊗_R M →ₗ[S] S ⊗_R N`, by `LinearMap.liftBaseChangeEquiv` and
`IsBaseChange.iff_of_equiv_comm`.  `Mathlib`'s `IsBaseChange.linearMapRight` is the same statement
but for a finite *free* `M`, which the conormal module is not.

`Stacks.Deformation.extOneCokernel` is built on the canonical presentation, whose conormal module
is not finitely presented; as in `Deformation.Examples.exists_pow_smul_eq_zero_extOneCokernel` the
statement is proved at `Algebra.Presentation.ofFinitePresentation` and transported by
`Deformation.Examples.conormalCokernelEquiv`.

## References

* [Stacks Project, Tag 0DZC](https://stacks.math.columbia.edu/tag/0DZC)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe uk uB uN

namespace Deformation.Examples

open Stacks.Deformation

section Hom

variable {R : Type*} [CommRing R] {M P N : Type*}
  [AddCommGroup M] [AddCommGroup P] [AddCommGroup N] [Module R M] [Module R P] [Module R N]
  (S : Type*) [CommRing S] [Algebra R S] (d : M →ₗ[R] P)

/-- Precomposition with `d` on maps into the `S`-module `S ⊗_R N`.  This is
`LinearMap.lcomp` with its `S`-linearity recorded, which is what forms the cokernel as a
quotient by an `S`-submodule. -/
def lcompBaseChange : (P →ₗ[R] S ⊗[R] N) →ₗ[S] (M →ₗ[R] S ⊗[R] N) where
  toFun t := t.comp d
  map_add' t t' := by ext x; simp
  map_smul' s t := by ext x; simp

/-- `Deformation.Examples.lcompBaseChange S d` sends `t` to `t.comp d`. -/
@[simp]
lemma lcompBaseChange_apply (t : P →ₗ[R] S ⊗[R] N) :
    lcompBaseChange S (N := N) d t = t.comp d := rfl

/-- The `S`-submodule of maps factoring through `d` and the `R`-submodule of such maps have the
same elements: `Deformation.Examples.lcompBaseChange` and `LinearMap.lcomp` are the same map. -/
lemma restrictScalars_range_lcompBaseChange :
    Submodule.restrictScalars R (LinearMap.range (lcompBaseChange S (N := N) d)) =
      LinearMap.range (LinearMap.lcomp R (S ⊗[R] N) d) :=
  Submodule.ext fun _ ↦ Iff.rfl

/-- **`Hom_R(M, S ⊗_R N)` is the base change of `Hom_R(M, N)`** for a finitely presented `M` and
a flat `S`.  This is `Module.FinitePresentation.isBaseChange_map` read through the identification
of `Hom_R(M, S ⊗_R N)` with `Hom_S(S ⊗_R M, S ⊗_R N)`. -/
theorem isBaseChange_compRight [Module.FinitePresentation R M] [Module.Flat R S] :
    IsBaseChange S (LinearMap.compRight R (M := M) ((TensorProduct.mk R S N) 1)) := by
  refine (IsBaseChange.iff_of_equiv_comm (LinearEquiv.refl R (M →ₗ[R] N))
    (LinearMap.liftBaseChangeEquiv S) ?_).mpr
    (Module.FinitePresentation.isBaseChange_map R M N S)
  ext t x
  simp

/-- Postcomposition with `n ↦ 1 ⊗ n`, read on the cokernels of precomposition with `d`, with the
target divided by the `S`-submodule of maps factoring through `d`.  It is the map whose
invertibility after base change is `Deformation.Examples.isBaseChange_homCokernelPush`. -/
def homCokernelPush :
    ((M →ₗ[R] N) ⧸ LinearMap.range (LinearMap.lcomp R N d)) →ₗ[R]
      ((M →ₗ[R] S ⊗[R] N) ⧸ LinearMap.range (lcompBaseChange S (N := N) d)) :=
  Submodule.liftQ _
    ((Submodule.mkQ (LinearMap.range (lcompBaseChange S (N := N) d))).restrictScalars R ∘ₗ
      LinearMap.compRight R (M := M) ((TensorProduct.mk R S N) 1)) (by
    rintro _ ⟨t, rfl⟩
    exact (Submodule.Quotient.mk_eq_zero _).2
      ⟨LinearMap.compRight R (M := P) ((TensorProduct.mk R S N) 1) t, rfl⟩)

/-- `Deformation.Examples.homCokernelPush S d` sends the class of `δ : M →ₗ[R] N` to the class
of its postcomposition with `n ↦ 1 ⊗ n`. -/
@[simp]
lemma homCokernelPush_mk (δ : M →ₗ[R] N) :
    homCokernelPush S d (Submodule.Quotient.mk δ) =
      Submodule.Quotient.mk (LinearMap.compRight R ((TensorProduct.mk R S N) 1) δ) := rfl

variable [Module.FinitePresentation R M] [Module.FinitePresentation R P] [Module.Flat R S]

/-- **The cokernel of precomposition with `d` over `S ⊗_R N` is the base change of the cokernel
over `N`.**  Both `Hom`'s commute with the base change, by
`Deformation.Examples.isBaseChange_compRight`, so the right-exactness shape of
`IsBaseChange.of_right_exact` carries it to the cokernels. -/
theorem isBaseChange_homCokernelPush :
    IsBaseChange S (homCokernelPush S d (N := N)) :=
  IsBaseChange.of_right_exact S
    (LinearMap.compRight R (M := P) ((TensorProduct.mk R S N) 1))
    (LinearMap.compRight R (M := M) ((TensorProduct.mk R S N) 1)) _
    (by ext t x; simp) (Submodule.liftQ_mkQ _ _ _)
    (isBaseChange_compRight S) (isBaseChange_compRight S)
    (LinearMap.exact_map_mkQ_range _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_map_mkQ_range _) (Submodule.mkQ_surjective _)

/-- **The cokernel of precomposition with `d` commutes with base change.** -/
def homCokernelBaseChangeEquiv :
    ((M →ₗ[R] S ⊗[R] N) ⧸ LinearMap.range (LinearMap.lcomp R (S ⊗[R] N) d)) ≃ₗ[R]
      S ⊗[R] ((M →ₗ[R] N) ⧸ LinearMap.range (LinearMap.lcomp R N d)) :=
  ((Submodule.quotEquivOfEq _ _
      (restrictScalars_range_lcompBaseChange S (N := N) d).symm).trans
    (Submodule.Quotient.restrictScalarsEquiv R
      (LinearMap.range (lcompBaseChange S (N := N) d)))).trans
      ((isBaseChange_homCokernelPush S d (N := N)).equiv.restrictScalars R).symm

/-- **The base-change comparison undoes pushing the coefficients forward**: the class of
`(1 ⊗ -) ∘ δ` goes to `1 ⊗ [δ]`.  This is what identifies postcomposition with `n ↦ 1 ⊗ n` on
the cokernels with the canonical scalar extension of the cokernel over `N`. -/
theorem homCokernelBaseChangeEquiv_compRight (δ : M →ₗ[R] N) :
    homCokernelBaseChangeEquiv S d
        (Submodule.Quotient.mk (LinearMap.compRight R ((TensorProduct.mk R S N) 1) δ))
      = (1 : S) ⊗ₜ[R] (Submodule.Quotient.mk δ) := by
  simp only [homCokernelBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq,
    LinearEquiv.restrictScalars_apply]
  rw [(isBaseChange_homCokernelPush S d (N := N)).equiv_tmul, one_smul, homCokernelPush_mk]
  rfl

end Hom

section ExtOne

variable (k : Type uk) (B : Type uB) [Field k] [CommRing B] [Algebra k B]
  [Algebra.FiniteType k B] (N : Type uN) [AddCommGroup N] [Module B N]
  (Bh : Type uB) [CommRing Bh] [Algebra B Bh] [Module.Flat B Bh]

/-- **Flat base change of `Ext¹_B(NL_{B/k}, N)` in the coefficients.**  For a finite type algebra
`B` over a field and a flat `B`-algebra `Bʰ`,

`Ext¹_B(NL_{B/k}, Bʰ ⊗_B N) ≅ Ext¹_B(NL_{B/k}, N) ⊗_B Bʰ`.

The conormal module of a finite presentation of `B` is finite, hence finitely presented because
`B` is Noetherian, and the cotangent space is finite projective; so both `Hom`'s commute with the
base change and therefore so does their cokernel. -/
def extOneCokernelBaseChangeEquiv :
    extOneCokernel k B (Bh ⊗[B] N) ≃+ (extOneCokernel k B N) ⊗[B] Bh := by
  let : Algebra.FinitePresentation k B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  let P₀ := Algebra.Presentation.ofFinitePresentation k B
  let Q := P₀.reindex (Equiv.ulift.{uB}) (Equiv.refl _)
  let : Module.Finite B Q.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite Q.fg_ker
  let : Module.FinitePresentation B Q.toExtension.Cotangent :=
    Module.finitePresentation_of_finite B Q.toExtension.Cotangent
  let : Module.Finite B Q.toExtension.CotangentSpace :=
    Module.Finite.of_basis Q.toGenerators.cotangentSpaceBasis
  let : Module.FinitePresentation B Q.toExtension.CotangentSpace :=
    Module.finitePresentation_of_projective B Q.toExtension.CotangentSpace
  let eN : conormalCokernelAt Q.toExtension N ≃ₗ[B] extOneCokernel k B N :=
    conormalCokernelEquiv
      (Algebra.Generators.defaultHom (Algebra.Generators.self k B) Q.toGenerators).toExtensionHom
      (Algebra.Generators.defaultHom Q.toGenerators
        (Algebra.Generators.self k B)).toExtensionHom N
  let eBN : conormalCokernelAt Q.toExtension (Bh ⊗[B] N) ≃ₗ[B] extOneCokernel k B (Bh ⊗[B] N) :=
    conormalCokernelEquiv
      (Algebra.Generators.defaultHom (Algebra.Generators.self k B) Q.toGenerators).toExtensionHom
      (Algebra.Generators.defaultHom Q.toGenerators
        (Algebra.Generators.self k B)).toExtensionHom (Bh ⊗[B] N)
  exact (eBN.symm.trans ((homCokernelBaseChangeEquiv Bh
      Q.toExtension.cotangentComplex).trans
    ((TensorProduct.congr (LinearEquiv.refl B Bh) eN).trans
      (TensorProduct.comm B Bh (extOneCokernel k B N))))).toAddEquiv

end ExtOne

end Deformation.Examples

end
