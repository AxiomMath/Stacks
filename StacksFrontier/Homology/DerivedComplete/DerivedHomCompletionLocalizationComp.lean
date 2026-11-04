module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat

/-!
# Iterated derived Hom from principal localizations

Let `A` be a commutative ring and let `f, g ∈ A`. For any object `K` of the derived category
of `A`-modules, first taking derived Hom from `A_g` and then from `A_f` is canonically
isomorphic to taking derived Hom from `A_{fg}`.

## Main results

* `DerivedHomLocalization.derivedHom_localization_comp` identifies the iterated derived Hom
  with derived Hom from the localization at the product.

## Implementation notes

The derived-Hom bifunctor is `StacksDraft.DerivedHom.derivedHomAdjunction`, and principal
localizations are represented by `Localization.Away` placed in cohomological degree zero.
The equality in the source is expressed as a canonical isomorphism in the derived category.
Each localized ring is regarded as an `A`-module and then as a complex concentrated in degree
zero.

## References

* [The Stacks Project, Tag 0A6C](https://stacks.math.columbia.edu/tag/0A6C)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace DerivedHomLocalization

/-- **Stacks 0A6C.** For `f, g ∈ A` and `K ∈ D(A)`, there is a canonical isomorphism
`RHom_A(A_f, RHom_A(A_g, K)) ≅ RHom_A(A_{fg}, K)`. -/
@[stacks 0A6C]
public noncomputable def derivedHom_localization_comp {A : Type u} [CommRing A]
    [HasDerivedCategory (ModuleCat A)] (f g : A) (K : DerivedCategory (ModuleCat A)) :
    let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
    let away (a : A) := DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (ModuleCat A) 0).obj
        (ModuleCat.of A (Localization.Away a)))
    D.hom.obj (Opposite.op (away f), D.hom.obj (Opposite.op (away g), K)) ≅
      D.hom.obj (Opposite.op (away (f * g)), K) := by
  let D := StacksDraft.DerivedHom.derivedHomAdjunction (R := A)
  let sf := (CochainComplex.singleFunctor (ModuleCat A) 0).obj
    (ModuleCat.of A (Localization.Away f))
  let sg := (CochainComplex.singleFunctor (ModuleCat A) 0).obj
    (ModuleCat.of A (Localization.Away g))
  let sfg := (CochainComplex.singleFunctor (ModuleCat A) 0).obj
    (ModuleCat.of A (Localization.Away (f * g)))
  letI : ∀ n : ℤ, Module.Flat A (sg.X n) := fun n => by
    by_cases h : n = 0
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0
          (ModuleCat.of A (Localization.Away g)) n h).toLinearEquiv
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (ModuleCat.of A (Localization.Away g)) n h).isoZero.toLinearEquiv
  have hg : sg.KFlat :=
    (CochainComplex.KFlat.kFlat_of_flat sg 0)
  let e₁ := StacksDraft.TorAmplitude.FaithfullyFlat.singleTensorLeftMapHomologicalComplexIso
    (ModuleCat.of A (Localization.Away f)) sg
  let e₂ := (CategoryTheory.Functor.mapCochainComplexSingleFunctor
    (tensorLeft (ModuleCat.of A (Localization.Away f))) 0).app
      (ModuleCat.of A (Localization.Away g))
  letI : IsLocalization.Away (f * g)
      (TensorProduct A (Localization.Away f) (Localization.Away g)) := by
    let : IsLocalization.Away (algebraMap A (Localization.Away f) g)
        (TensorProduct A (Localization.Away f) (Localization.Away g)) :=
      IsLocalization.Away.tensor (R := A) (S := Localization.Away f) g
        (Localization.Away g)
    apply IsLocalization.Away.mul' (Localization.Away f) _ f g
  let em : (ModuleCat.of A (Localization.Away f) ⊗
      ModuleCat.of A (Localization.Away g)) ≅
      ModuleCat.of A (Localization.Away (f * g)) :=
    LinearEquiv.toModuleIso
      ((IsLocalization.algEquiv (Submonoid.powers (f * g))
        (TensorProduct A (Localization.Away f) (Localization.Away g))
        (Localization.Away (f * g))).toLinearEquiv)
  let ec : sf ⊗ sg ≅ sfg := e₁ ≪≫ e₂ ≪≫
    (CochainComplex.singleFunctor (ModuleCat A) 0).mapIso em
  let ed : D.tensor.obj (DerivedCategory.Q.obj sf, DerivedCategory.Q.obj sg) ≅
      DerivedCategory.Q.obj sfg :=
    D.tensorIso sf sg hg ≪≫ DerivedCategory.Q.mapIso ec
  exact (StacksDraft.DerivedHom.derivedHomCurrying.iso _ _ K) ≪≫
    D.hom.mapIso (Iso.prod ed.symm.op (Iso.refl K))

end DerivedHomLocalization

end
