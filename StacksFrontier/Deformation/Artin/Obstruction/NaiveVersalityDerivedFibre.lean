module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.ZeroDegree
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersality
public import StacksFrontier.RingTheory.NaiveCotangent.DerivedSquareZeroExtension

/-!
# Condition (2) of Stacks 07YM, as an `Ext` condition

Let `ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` and let `k` be a field which is an
`A`-algebra; in Stacks 07YM, `k` is the residue field of a finite type point `u₀` of
`Spec A`. Condition (2) of that tag asks that `ξ` induce a surjection on `H^{-1}` and an
injection on `H^0` after derived base change to `k`.

This file states both halves of that condition as conditions on `Ext` groups, in the
presentation of the derived fibre that the tag itself uses: a chosen derived tensor product
`Deformation.Artin.DerivedTensorProduct`, supplied as data. The two halves are already
available for the other presentation of the derived fibre, the total derived extension of
scalars, in `StacksFrontier.Deformation.Artin.Obstruction.NaiveVersality`; what this file adds is
their composition with the comparison of the two presentations, which until now was sealed
inside the file proving Stacks 07YL.

## Main results

* `Deformation.Artin.surjective_derivedTensorFibre_neg_one_iff_injective_extOne` — condition
  (2) in degree `-1`: the surjectivity of `H^{-1}(ξ ⊗ᴸ_A k)` is the injectivity of
  `Ext¹_A(NL_{A/Λ}, k) ⟶ Ext¹_A(E, k)`, that is of precomposition with `ξ`.
* `Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_extZero` — condition
  (2) in degree `0`: the injectivity of `H^0(ξ ⊗ᴸ_A k)` is the surjectivity of
  `Ext⁰_A(NL_{A/Λ}, k) ⟶ Ext⁰_A(E, k)`.
* `Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_comp` — the same
  condition with the degree-zero `Ext` groups written as morphism groups of the derived
  category, which is the form the tangent-space description of versality is stated in.

These are the two forms in which condition (2) is used in the proof of Stacks 07YM. In the
direction `(1) ⇒ (2)` the first is what turns a failure of surjectivity into a nonzero class
of `Ext¹_A(NL_{A/Λ}, k)` killed by `ξ`, which is the input of Stacks 07YL, and the second is
what identifies the dual of `H^0(ξ ⊗ᴸ_A k)` with the map `Der_Λ(A, k) ⟶ T_x(k)` on tangent
spaces, whose surjectivity is what versality provides. In the direction `(2) ⇒ (1)` the first
is what forces an obstruction class to vanish.

## Implementation notes

The coefficient module of the `Ext` groups is `ULift k`, read as an `A`-module by restriction
of scalars along the structure map, because `Ext` is formed in a module universe above that of
the ring; this is the shape the duality of Stacks 07YK is stated in. The map
`Ext^i_A(NL_{A/Λ}, k) ⟶ Ext^i_A(E, k)` is precomposition with `ξ`, written out rather than
named.

The field `k` is an arbitrary `A`-algebra which is a field, not specifically the residue field
of a point of `Spec A`: neither half of the condition uses anything else, and the statements
are applied at a residue field by instantiation.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 07YK](https://stacks.math.columbia.edu/tag/07YK)
* [Stacks Project, Tag 07YL](https://stacks.math.columbia.edu/tag/07YL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

variable {Λ A k : Type u} [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]

/-- **Stacks 07YM, condition (2) in degree `-1`.** For a morphism `ξ : E ⟶ NL_{A/Λ}` of
`D⁻(A)` and a field `k` which is an `A`-algebra, the map
`H^{-1}(E ⊗ᴸ_A k) ⟶ H^{-1}(NL_{A/Λ} ⊗ᴸ_A k)`, formed through a chosen derived tensor product,
is surjective exactly when precomposition with `ξ` is injective on
`Ext¹_A(−, k)`, that is when `Ext¹_A(NL_{A/Λ}, k) ⟶ Ext¹_A(E, k)` is injective.

This is `Deformation.Artin.surjective_derivedFibre_neg_one_iff_injective_extOne`, which proves
the same statement for the total derived extension of scalars, composed with the comparison
`Deformation.Artin.surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars` of
the two presentations of the derived fibre. -/
@[stacks 07YM "condition (2) in degree -1, through a chosen derived tensor product"]
public theorem surjective_derivedTensorFibre_neg_one_iff_injective_extOne
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) :
    Function.Surjective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
          ((T.tensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A k))).map ξ)) ↔
      Function.Injective
        (fun α : DerivedCategory.Ext (derivedNaiveCotangentComplex Λ A)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars (algebraMap A k)).obj
                (ModuleCat.of k (ULift.{u} k)))) 1 =>
          ξ ≫ α) :=
  (surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars T ξ (-1)).trans
    (surjective_derivedFibre_neg_one_iff_injective_extOne (algebraMap A k) E hE ξ)

/-- **Stacks 07YM, condition (2) in degree `0`.** For a morphism `ξ : E ⟶ NL_{A/Λ}` of
`D⁻(A)` and a field `k` which is an `A`-algebra, the map
`H^0(E ⊗ᴸ_A k) ⟶ H^0(NL_{A/Λ} ⊗ᴸ_A k)`, formed through a chosen derived tensor product, is
injective exactly when precomposition with `ξ` is surjective on `Ext⁰_A(−, k)`, that is when
`Ext⁰_A(NL_{A/Λ}, k) ⟶ Ext⁰_A(E, k)` is surjective.

This is `Deformation.Artin.injective_derivedFibre_zero_iff_surjective_extZero` composed with
the comparison
`Deformation.Artin.injective_derivedTensorFibre_iff_injective_derivedExtensionScalars` of the
two presentations of the derived fibre. -/
@[stacks 07YM "condition (2) in degree 0, through a chosen derived tensor product"]
public theorem injective_derivedTensorFibre_zero_iff_surjective_extZero
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) :
    Function.Injective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((T.tensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A k))).map ξ)) ↔
      Function.Surjective
        (fun α : DerivedCategory.Ext (derivedNaiveCotangentComplex Λ A)
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars (algebraMap A k)).obj
                (ModuleCat.of k (ULift.{u} k)))) 0 =>
          ξ ≫ α) :=
  (injective_derivedTensorFibre_iff_injective_derivedExtensionScalars T ξ 0).trans
    (injective_derivedFibre_zero_iff_surjective_extZero (algebraMap A k) E hE ξ)

/-- **Stacks 07YM, condition (2) in degree `0`, as a condition on morphisms.** The injectivity
of `H^0(ξ ⊗ᴸ_A k)` is the surjectivity of precomposition with `ξ` on morphisms
`NL_{A/Λ} ⟶ k[0]` of `D(A)`.

This is `Deformation.Artin.injective_derivedTensorFibre_zero_iff_surjective_extZero` followed
by `DerivedCategory.surjective_extZero_comp_iff_surjective_comp`: in degree `0` an `Ext` class
*is* a morphism. It is the form in which condition (2) meets the tangent-space description of
versality, whose statements are about morphisms of the derived category. -/
@[stacks 07YM "condition (2) in degree 0, as a condition on morphisms"]
public theorem injective_derivedTensorFibre_zero_iff_surjective_comp
    (T : DerivedTensorProduct A) (E : DerivedCategory (ModuleCat.{u} A))
    (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
    (ξ : E ⟶ derivedNaiveCotangentComplex Λ A) :
    Function.Injective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((T.tensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              (ModuleCat.of A k))).map ξ)) ↔
      Function.Surjective
        (fun f : derivedNaiveCotangentComplex Λ A ⟶
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
              ((ModuleCat.restrictScalars (algebraMap A k)).obj
                (ModuleCat.of k (ULift.{u} k))) =>
          ξ ≫ f) :=
  (injective_derivedTensorFibre_zero_iff_surjective_extZero T E hE ξ).trans
    (DerivedCategory.surjective_extZero_comp_iff_surjective_comp ξ _)

end Deformation.Artin
