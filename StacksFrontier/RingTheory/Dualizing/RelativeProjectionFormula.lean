module

public import StacksFrontier.RingTheory.Dualizing.RelativeUniqueness

/-!
# The unrestricted projection formula at the diagonal

Let `R → A` be a flat ring map, put `B = A ⊗[R] A`, write `p₁ : A → B` for the left
coprojection and `Δ : B → A` for the multiplication map.  This file proves, in `D(B)`,

> `A_B ⊗ᴸ_B p₁^*M ≅ Δ_*M`,

where `A_B = Δ_*A` is `Dualizing.diagonalObject` and `Δ_*` is restriction of scalars along the
multiplication map.  `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness` had only the
`p₁`-restricted consequence
`Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso`; this isomorphism is
the first of the two inputs that the module documentation of
`StacksFrontier.RingTheory.Dualizing.RelativeUniquenessDuality` records the duality route to
[stacks 0E2D] as wanting, and the one place it is wanted is the currying isomorphism of
[stacks 0A65], which has to be fed `A_B ⊗ᴸ_B p₁^*M` as an object of `D(B)`.

## The shape of the proof

Nothing is special about the diagonal: the statement holds for any ring map `φ : A → B` with a
retraction `ψ : B → A`, and that is how it is proved.  On a K-flat representative `P` of `M` the
chain-level isomorphism is a single application of the projection formula of [stacks 06Y1],
`baseChangeTensorIso`, read **along the retraction** rather than along `φ`:

`ψ_*(1 ⊗_A ψ^*φ^*P) ≅ ψ_*(1) ⊗_B φ^*P`.

Its left-hand side is `ψ_*P` because `ψ^*φ^* = (ψ ∘ φ)^* = id^*` and `1 ⊗_A -` is the identity,
and its right-hand side is the left-hand side of the projection formula because `ψ_*(1)` is the
single complex on the target ring.  So the only inputs are the projection formula of
[stacks 06Y1], the composition and unit isomorphisms of extension of scalars, and the left
unitor; no flatness, no perfection and no boundedness hypothesis is used, and the existing
restricted form is strictly weaker.

## Main definitions

* `Dualizing.extendScalarsRetractionComplexIso` — extension of scalars along `φ` and then along
  a retraction `ψ` of `φ` returns the complex.
* `Dualizing.singleTargetRestrictScalarsUnitIso` — the single complex on the target ring of `ψ`
  is the restriction along `ψ` of the tensor unit.
* `Dualizing.singleTargetTensorExtendScalarsIso` — **the chain-level unrestricted projection
  formula** `ψ_*(A)[0] ⊗_B φ^*P ≅ ψ_*P`.

## Main results

* `Dualizing.nonempty_tensor_diagonalObject_iso_restrictScalars_lmul` — **the unrestricted
  projection formula in `D(B)`**: `A_B ⊗ᴸ_B p₁^*M ≅ Δ_*M`.  Restricting it along `p₁` and using
  that `Δ ∘ p₁` is the identity returns
  `Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso` of
  `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`, so this is the stronger statement; that
  deduction is not carried out here, the restricted form already being in the library with its
  own proof.  It is **pointwise**: for the duality route's enriched adjunction the same formula is
  needed as an isomorphism of functors of the tensor factor, which is
  `Dualizing.diagonalProjectionNatIso` of
  `StacksFrontier.RingTheory.Dualizing.RelativeProjectionFormulaNatural`.

## References

* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

noncomputable section

section Retraction

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Extension of scalars along `φ : A →+* B` followed by extension of scalars along a retraction
`ψ` of `φ` returns the complex: `ψ^*φ^*P = (ψ ∘ φ)^*P = id^*P = P`. -/
def extendScalarsRetractionComplexIso (φ : A →+* B) (ψ : B →+* A)
    (h : ψ.comp φ = RingHom.id A) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (CochainComplex.extendScalars ψ).obj ((CochainComplex.extendScalars φ).obj P) ≅ P := by
  have e := (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp.{u, u} φ ψ)
    (ComplexShape.up ℤ)).app P
  rw [h] at e
  exact e.symm ≪≫ (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsId.{u, u} A)
    (ComplexShape.up ℤ)).app P

/-- The single complex on the target ring of `ψ : B →+* A`, read as a complex of `B`-modules, is
the restriction of scalars along `ψ` of the tensor unit of the complexes of `A`-modules. -/
def singleTargetRestrictScalarsUnitIso (ψ : B →+* A) :
    (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (targetAsModule.{u, u} ψ) ≅
      (CochainComplex.restrictScalars ψ).obj (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ)) :=
  (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).mapIso
      ((ModuleCat.restrictScalars.{u} ψ).mapIso
        (ULift.moduleEquiv.{u, u, u} (R := A) (M := A)).toModuleIso) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars.{u} ψ)
      (ComplexShape.up ℤ) 0).app (ModuleCat.of A A)).symm

/-- **The chain-level unrestricted projection formula.**  For `φ : A →+* B` with a retraction
`ψ : B →+* A`, the target ring in degree zero tensored over `B` with the base change of `P` along
`φ` is the restriction of `P` along `ψ`:

`ψ_*(A)[0] ⊗_B φ^*P ≅ ψ_*P`.

This is the projection formula of [stacks 06Y1] read along `ψ` rather than along `φ`; the
right-hand side of that formula is the left-hand side here because `ψ_*` of the tensor unit is
the single complex on the target ring, and its left-hand side is `ψ_*P` because `ψ^*φ^*` is the
identity and the left unitor removes the remaining tensor unit. -/
def singleTargetTensorExtendScalarsIso (φ : A →+* B) (ψ : B →+* A)
    (h : ψ.comp φ = RingHom.id A) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (targetAsModule.{u, u} ψ) ⊗
        (CochainComplex.extendScalars φ).obj P ≅
      (CochainComplex.restrictScalars ψ).obj P :=
  (MonoidalCategory.tensorRight ((CochainComplex.extendScalars φ).obj P)).mapIso
      (singleTargetRestrictScalarsUnitIso ψ) ≪≫
    (baseChangeTensorIso ψ ((CochainComplex.extendScalars φ).obj P)
      (𝟙_ (CochainComplex (ModuleCat.{u} A) ℤ))).symm ≪≫
    (CochainComplex.restrictScalars ψ).mapIso
      (λ_ _ ≪≫ extendScalarsRetractionComplexIso φ ψ h P)

end Retraction

/-- **The unrestricted projection formula at the diagonal.**  Let `R → A` be flat, put
`B = A ⊗[R] A` and let `Δ : B → A` be the multiplication map.  Derived tensoring the diagonal
`A_B` with the derived base change of `M` along the left coprojection returns the restriction of
`M` along `Δ`:

`A_B ⊗ᴸ_B p₁^*M ≅ Δ_*M`   in `D(B)`.

Restricting further along `p₁` gives
`Dualizing.nonempty_restrictScalars_includeLeft_tensor_diagonalObject_iso`, which is therefore a
consequence; this is the form the duality route to [stacks 0E2D] needs, where the currying
isomorphism of [stacks 0A65] has to be fed `A_B ⊗ᴸ_B p₁^*M` as an object of `D(B)` and not after
a restriction.

The proof takes a K-flat representative `P` of `M`, whose base change along `p₁` is K-flat over
`B` by [stacks 06Y1] and so computes both the derived base change and the derived tensor
product, and applies the chain-level formula
`Dualizing.singleTargetTensorExtendScalarsIso` at the retraction
`Dualizing.lmul'_comp_includeLeftRingHom`. -/
theorem nonempty_tensor_diagonalObject_iso_restrictScalars_lmul (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] [Module.Flat R A] (M : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).obj
          (diagonalObject R A, (diagonalDerivedExtension R A).obj M) ≅
        (ModuleCat.restrictScalars.{u}
            (Algebra.TensorProduct.lmul' R :
              A ⊗[R] A →ₐ[R] A).toRingHom).mapDerivedCategory.obj M) := by
  classical
  obtain ⟨P, hP, -, ⟨eP⟩⟩ := StacksDraft.Perfect.exists_kFlat_representative.{u, u} M
  set p₁ : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom with hp₁
  set Δ : A ⊗[R] A →+* A :=
    (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom with hΔ
  have hEP : ((CochainComplex.extendScalars p₁).obj P).KFlat := kFlat_baseChange p₁ P hP
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} p₁
  have hcomp : IsIso (D.comparison.app P) := D.comparison_isIso_of_kFlat P hP
  let eE : (diagonalDerivedExtension R A).obj M ≅
      DerivedCategory.Q.obj ((CochainComplex.extendScalars p₁).obj P) :=
    ((diagonalDerivedExtensionIsoTotalDerived R A).app M).symm ≪≫
      D.functor.mapIso eP ≪≫ @asIso _ _ _ _ (D.comparison.app P) hcomp
  let eA : diagonalObject R A ≅
      DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
          (targetAsModule.{u, u} Δ)) :=
    sourceSingleRestrictScalarsIsoQ.{u} Δ
  refine ⟨(StacksDraft.DerivedHom.DerivedInternalHom.Model.tensor (A ⊗[R] A)).mapIso
      (eA.prod eE) ≪≫
    (StacksDraft.DerivedHom.DerivedInternalHom.Model.adjunction (A ⊗[R] A)).tensorIso _ _ hEP ≪≫
    DerivedCategory.Q.mapIso
      (singleTargetTensorExtendScalarsIso p₁ Δ (lmul'_comp_includeLeftRingHom R A) P) ≪≫
    ((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategoryFactors.app P).symm ≪≫
    (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory.mapIso eP.symm⟩

end

end Dualizing

end
