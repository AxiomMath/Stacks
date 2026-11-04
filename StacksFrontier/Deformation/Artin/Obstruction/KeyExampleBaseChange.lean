module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.KeyExample
public import StacksFrontier.RingTheory.NaiveCotangent.ExtCokernelLinear

/-!
# The obstruction group of the key example after base change

Let `Λ` be a ring, let `R = Λ[x_1, …, x_n]/J` and let `𝒳 = (Sch/X)_{fppf}` with `X = Spec R`.
For a deformation situation `(x, A' → A)` of the key example the source of Stacks 07YI writes
the obstruction group in two ways,
```
Ext¹_R(NL_{R/Λ}, I) = Ext¹_A(NL_{R/Λ} ⊗_R A, I),
```
and this file proves that identification.

The two-term complex `NL_{R/Λ}` of the presentation `Λ[x_1, …, x_n] → R` is `J/J² → ⊕_i R dx_i`
with free degree-`0` term, and `NL_{R/Λ} ⊗_R A` is its termwise base change
`A ⊗_R J/J² → A ⊗_R (⊕_i R dx_i)`, again with free degree-`0` term. Both first extension groups
are therefore computed by `Stacks 0GPU` as cokernels of the dual differential, and the
identification is the tensor-hom adjunction
`Hom_R(U, M) = Hom_A(A ⊗_R U, M)` for an `A`-module `M`, which carries one cokernel
presentation onto the other.

## Main definitions

* `Deformation.Artin.KeyExample.dualCokernelBaseChange` — the tensor-hom adjunction on the
  cokernel of the dual of a map of modules.
* `Deformation.Artin.KeyExample.baseChangedObstructionModule` — the obstruction module computed
  from the base-changed two-term complex,
  `Hom_A(A ⊗_R J/J², M)/Hom_A(A ⊗_R R^{⊕n}, M)`.

## Main results

* `Deformation.Artin.KeyExample.extOneBaseChange` and
  `Deformation.Artin.KeyExample.extOneBaseChange_extOneClass`: for a two-term complex of
  `R`-modules with free degree-`0` term and an `A`-module `M`, the first extension group over
  `R` of the complex is the first extension group over `A` of its termwise base change, by an
  equivalence carrying the class of a functional `f` to the class of `f` extended to `A`.
* `Deformation.Artin.KeyExample.extOneNaiveCotangentBaseChange`:
  `Ext¹_R(NL_{R/Λ}, M) = Ext¹_A(NL_{R/Λ} ⊗_R A, M)`.
* `Deformation.Artin.KeyExample.obstructionModuleBaseChange`: the same identification read on
  the cokernel presentations of the two groups.

## Implementation notes

The two extension groups are modules over different rings, so the comparison is an equivalence
of additive groups; that is what the source's equality of groups asserts. It is not an
unidentified additive equivalence, though:
`extOneBaseChange_extOneClass` computes it on the explicit extension class of a conormal
functional, which by `Stacks 0GPU`
(`NaiveCotangent.ExtCokernelLinear.extOneTwoTermLinearEquiv`) is enough to pin it down.

## References

* [Stacks Project, Tag 07YI](https://stacks.math.columbia.edu/tag/07YI)
* [Stacks Project, Tag 0GPU](https://stacks.math.columbia.edu/tag/0GPU)
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Deformation.Artin.KeyExample

/-! ### Base change of the cokernel of a dual differential -/

section DualCokernel

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {U V M : Type u} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- The tensor-hom adjunction turns precomposition with `d` into precomposition with the base
change of `d`. -/
theorem liftBaseChangeEquiv_comp (d : U →ₗ[R] V) (f : V →ₗ[R] M) :
    LinearMap.liftBaseChangeEquiv A (f ∘ₗ d) =
      (LinearMap.liftBaseChangeEquiv A f) ∘ₗ d.baseChange A := by
  ext a
  simp [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul]

/-- The tensor-hom adjunction carries the functionals factoring through `d` onto those
factoring through the base change of `d`. -/
theorem map_toAddSubgroup_range_lcomp (d : U →ₗ[R] V) :
    AddSubgroup.map
        (LinearMap.liftBaseChangeEquiv A (R := R) (M := U)
          (N := M)).toAddEquiv.toAddMonoidHom
        (LinearMap.range (LinearMap.lcomp R M d)).toAddSubgroup =
      (LinearMap.range (LinearMap.lcomp A M (d.baseChange A))).toAddSubgroup := by
  ext f
  constructor
  · rintro ⟨-, ⟨h, rfl⟩, rfl⟩
    exact ⟨LinearMap.liftBaseChangeEquiv A h, (liftBaseChangeEquiv_comp (A := A) d h).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨LinearMap.lcomp R M d ((LinearMap.liftBaseChangeEquiv A).symm g),
      ⟨(LinearMap.liftBaseChangeEquiv A).symm g, rfl⟩, ?_⟩
    show LinearMap.liftBaseChangeEquiv A
      (((LinearMap.liftBaseChangeEquiv A).symm g) ∘ₗ d) = g ∘ₗ d.baseChange A
    simpa only [LinearEquiv.apply_symm_apply] using
      liftBaseChangeEquiv_comp (A := A) d ((LinearMap.liftBaseChangeEquiv A).symm g)

/-- **The tensor-hom adjunction on dual cokernels.** For a map `d : U → V` of `R`-modules and an
`A`-module `M`, the cokernel of precomposition with `d` on `R`-linear functionals is the
cokernel of precomposition with the base change of `d` on `A`-linear functionals. -/
def dualCokernelBaseChange (d : U →ₗ[R] V) :
    ((U →ₗ[R] M) ⧸ LinearMap.range (LinearMap.lcomp R M d)) ≃+
      ((A ⊗[R] U →ₗ[A] M) ⧸ LinearMap.range (LinearMap.lcomp A M (d.baseChange A))) :=
  QuotientAddGroup.congr _ _ (LinearMap.liftBaseChangeEquiv A).toAddEquiv
    (map_toAddSubgroup_range_lcomp d)

/-- The adjunction sends the class of a functional `f` to the class of its extension to `A`. -/
@[simp]
theorem dualCokernelBaseChange_mk (d : U →ₗ[R] V) (f : U →ₗ[R] M) :
    dualCokernelBaseChange (A := A) d (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (f.liftBaseChange A) :=
  rfl

end DualCokernel

/-! ### Base change of the first extension group of a two-term complex -/

section ExtOne

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {U V M : Type u} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
  [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Free R V]

/-- **Base change of the first extension group of a two-term complex.** For a map
`d : U → V` of `R`-modules with `V` free and an `A`-module `M`, the first extension group over
`R` of the two-term complex `[U → V]` with coefficients in `M` is the first extension group
over `A` of its termwise base change `[A ⊗_R U → A ⊗_R V]`. Both are computed as cokernels of
the dual differential by `Stacks 0GPU`, and the comparison between those cokernels is the
tensor-hom adjunction. -/
def extOneBaseChange (d : U →ₗ[R] V) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
          (NaiveCotangent.ExtCokernelLinear.singleMap (ModuleCat.ofHom d))))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R M)) 1 ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
          (NaiveCotangent.ExtCokernelLinear.singleMap
            (ModuleCat.ofHom (d.baseChange A)))))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) 1 :=
  ((NaiveCotangent.ExtCokernelLinear.extOneTwoTermLinearEquiv
        (Nc := M) d).toAddEquiv.trans (dualCokernelBaseChange (A := A) d)).trans
    (NaiveCotangent.ExtCokernelLinear.extOneTwoTermLinearEquiv
      (Nc := M) (d.baseChange A)).toAddEquiv.symm

/-- **The comparison, on an explicit class.** The extension class of a conormal functional `f`
goes to the extension class of the functional `f` extends to over `A`. This characterises
`extOneBaseChange`, since every class is the class of a functional. -/
theorem extOneBaseChange_extOneClass (d : U →ₗ[R] V) (f : U →ₗ[R] M) :
    extOneBaseChange (A := A) d
        (NaiveCotangent.ExtCokernelLinear.extOneClass (ModuleCat.ofHom d)
          (ModuleCat.ofHom f)) =
      NaiveCotangent.ExtCokernelLinear.extOneClass (ModuleCat.ofHom (d.baseChange A))
        (ModuleCat.ofHom (f.liftBaseChange A)) := by
  rw [extOneBaseChange, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.symm_apply_eq]
  exact (congrArg _ (NaiveCotangent.ExtCokernelLinear.extOneTwoTermLinearEquiv_extOneClass
    (Nc := M) d (ModuleCat.ofHom f))).trans
    (NaiveCotangent.ExtCokernelLinear.extOneTwoTermLinearEquiv_extOneClass
      (Nc := M) (d.baseChange A) (ModuleCat.ofHom (f.liftBaseChange A))).symm

end ExtOne

/-! ### The obstruction group of the key example after base change -/

section Presentation

variable {Λ R : Type u} [CommRing Λ] [CommRing R] [Algebra Λ R] {n : ℕ}
  (P : Algebra.Generators Λ R (Fin n)) (A : Type u) [CommRing A] [Algebra R A]
  (M : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- **The obstruction module of Stacks 07YI computed after base change**, the cokernel
`Hom_A(A ⊗_R J/J², M)/Hom_A(A ⊗_R R^{⊕n}, M)` of the dual of the differential of
`NL_{R/Λ} ⊗_R A`. -/
@[stacks 07YI "the obstruction module computed from NL_{R/Λ} ⊗_R A"]
abbrev baseChangedObstructionModule :=
  ((A ⊗[R] P.toExtension.Cotangent) →ₗ[A] M) ⧸
    LinearMap.range ((LinearMap.lcomp A M
      ((NaiveCotangent.NL P).d.baseChange A)) :
      ((A ⊗[R] P.toExtension.CotangentSpace) →ₗ[A] M) →ₗ[A]
        ((A ⊗[R] P.toExtension.Cotangent) →ₗ[A] M))

/-- **Stacks 07YI.** The obstruction module `Hom_R(J/J², M)/Hom_R(R^{⊕n}, M)` of the key
example agrees with the obstruction module computed from `NL_{R/Λ} ⊗_R A`: the tensor-hom
adjunction carries one cokernel presentation onto the other. -/
@[stacks 07YI "Hom_R(J/J², M)/Hom_R(R^{⊕n}, M) = Hom_A(A ⊗ J/J², M)/Hom_A(A ⊗ R^{⊕n}, M)"]
def obstructionModuleBaseChange :
    obstructionModule P M ≃+ baseChangedObstructionModule P A M :=
  dualCokernelBaseChange (A := A) (NaiveCotangent.NL P).d

/-- The comparison of obstruction modules sends the class of a map `J/J² → M` to the class of
its extension to `A ⊗_R J/J² → M`. -/
theorem obstructionModuleBaseChange_mk (f : P.toExtension.Cotangent →ₗ[R] M) :
    obstructionModuleBaseChange P A M (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (f.liftBaseChange A) :=
  rfl

/-- **Stacks 07YI: `Ext¹_R(NL_{R/Λ}, M) = Ext¹_A(NL_{R/Λ} ⊗_R A, M)`.** The first extension
group of the naive cotangent complex of `R` over `Λ` with coefficients in an `A`-module `M` is
the first extension group over `A` of the base change `NL_{R/Λ} ⊗_R A`. Both complexes are
realized as the mapping cone of their differential, so that the conormal module lies in degree
`-1`. -/
@[stacks 07YI "Ext¹_R(NL_{R/Λ}, I) = Ext¹_A(NL_{R/Λ} ⊗_R A, I)"]
def extOneNaiveCotangentBaseChange :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
          (NaiveCotangent.ExtCokernelLinear.singleMap
            (ModuleCat.ofHom P.toExtension.cotangentComplex))))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R M)) 1 ≃+
      DerivedCategory.Ext
        (DerivedCategory.Q.obj (HomologicalComplex.homotopyCofiber
          (NaiveCotangent.ExtCokernelLinear.singleMap
            (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A)))))
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A M)) 1 :=
  extOneBaseChange (A := A) P.toExtension.cotangentComplex

/-- The identification of the two extension groups sends the class of a conormal functional
`f : J/J² → M` to the class of its extension `A ⊗_R J/J² → M`. -/
theorem extOneNaiveCotangentBaseChange_extOneClass
    (f : P.toExtension.Cotangent →ₗ[R] M) :
    extOneNaiveCotangentBaseChange P A M
        (NaiveCotangent.ExtCokernelLinear.extOneClass
          (ModuleCat.ofHom P.toExtension.cotangentComplex) (ModuleCat.ofHom f)) =
      NaiveCotangent.ExtCokernelLinear.extOneClass
        (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A))
        (ModuleCat.ofHom (f.liftBaseChange A)) :=
  extOneBaseChange_extOneClass P.toExtension.cotangentComplex f

end Presentation

end Deformation.Artin.KeyExample

end
