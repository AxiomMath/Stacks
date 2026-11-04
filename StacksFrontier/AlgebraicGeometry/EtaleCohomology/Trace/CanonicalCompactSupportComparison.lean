module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.InducedCompactification
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CanonicalCompactSupportFrobenius
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportCompactification

/-!
# The two presentations of `RΓ_c(X_k̄, K)` agree

Let `j : X ⟶ X̄` be a compactification of `X` over a field `k` and `k̄` an extension of `k`. This
file identifies `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})`
(`Stacks.EtaleCohomology.compactSupportFrobeniusCohomology`), on which the canonical Frobenius
acts, with the cohomology with compact support of [Stacks, Tag 0GJZ] taken through the
base-changed compactification `j_k̄ : X_k̄ ⟶ X̄_k̄`
(`Stacks.EtaleCohomology.geometricCompactSupportCohomology`), which is
`RΓ(X̄_k̄, Rj_{k̄!}(K|_{X_k̄}))`. The two agree because the square

```
X_k̄ --j_k̄--> X̄_k̄
 |pr            |pr̄
 X  ----j---->  X̄
```

is cartesian, so that extension by zero commutes with inverse image ([Stacks, Tag 03S6]), and
because extension by zero is exact.

## Main results

* `Stacks.EtaleCohomology.isPullback_compactificationFieldBaseChange`: the square is cartesian.
* `Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIso`: the comparison
  `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄}) ≅ RΓ_c(X_k̄, K|_{X_k̄})`.
* `Stacks.EtaleCohomology.isPerfect_compactSupportFrobeniusCohomology_iff`: perfectness can
  be checked on either presentation.

## References

* [Stacks Project, Tag 03S6](https://stacks.math.columbia.edu/tag/03S6)
* [Stacks Project, Tag 03UI](https://stacks.math.columbia.edu/tag/03UI)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section Square

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The base change of a compactification is a cartesian square**: `X_k̄` is the inverse image
of `X` in `X̄_k̄`. -/
public theorem isPullback_compactificationFieldBaseChange :
    IsPullback (pullback.fst f (specAlgebraMap k kbar))
      (compactificationFieldBaseChangeImmersion f j kbar) j.immersion
      (pullback.fst j.toBase (specAlgebraMap k kbar)) := by
  have hf : j.immersion ≫ j.toBase = f := Over.w j.obj.hom
  have s : IsPullback (compactificationFieldBaseChangeImmersion f j kbar ≫
      pullback.snd j.toBase (specAlgebraMap k kbar)) (pullback.fst f (specAlgebraMap k kbar))
      (specAlgebraMap k kbar) (j.immersion ≫ j.toBase) := by
    rw [compactificationFieldBaseChange_immersion_comp_snd, hf]
    exact (IsPullback.of_hasPullback f (specAlgebraMap k kbar)).flip
  exact (IsPullback.of_right s
    (compactificationFieldBaseChange_immersion_comp_fst f j kbar)
    (IsPullback.of_hasPullback j.toBase (specAlgebraMap k kbar)).flip).flip

end Square

section Comparison

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- [Stacks, Tag 03S6] for the base-changed compactification:
`j_{k̄!}(pr^{-1} -) ≅ pr̄^{-1}(j_! -)` on sheaves of `Λ`-modules. -/
public def compactificationFieldBaseChangeExtensionByZeroIso :
    etaleModuleInverseImage.{u, r} Λ (pullback.fst f (specAlgebraMap k kbar)) ⋙
        etaleModuleExtensionByZero.{u, r} Λ (compactificationFieldBaseChangeImmersion f j kbar) ≅
      etaleModuleExtensionByZero.{u, r} Λ j.immersion ⋙
        etaleModuleInverseImage.{u, r} Λ (pullback.fst j.toBase (specAlgebraMap k kbar)) :=
  etaleModuleInverseImageExtensionByZeroIso.{u, r} Λ
    (isPullback_compactificationFieldBaseChange f j kbar)

/-- The derived extension by zero along `j_k̄` of a complex is its degreewise extension by
zero. -/
public def compactificationFieldBaseChangeDerivedExtensionByZeroIso
    (C : CochainComplex.Plus (EtaleModules.{u, r} Λ (pullback f (specAlgebraMap k kbar)))) :
    DerivedCategory.Plus.Q.obj ((etaleModuleExtensionByZero.{u, r} Λ
        (compactificationFieldBaseChangeImmersion f j kbar)).mapCochainComplexPlus.obj C) ≅
      (etaleModuleDerivedExtensionByZero.{u, r} Λ
        (compactificationFieldBaseChangeImmersion f j kbar)).obj (DerivedCategory.Plus.Q.obj C) :=
  haveI : IsIso (etaleModuleExtensionByZero.{u, r} Λ
      (compactificationFieldBaseChangeImmersion f j kbar)).rightDerivedFunctorPlusUnit :=
    Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology _
  haveI : IsIso ((Functor.mapCochainComplexPlusDerivedUnit (etaleModuleExtensionByZero.{u, r} Λ
      (compactificationFieldBaseChangeImmersion f j kbar))).app C) := by
    rw [Functor.mapCochainComplexPlusDerivedUnit_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
      (@IsIso.comp_isIso _ _ _ _ _ _ _
        (NatIso.isIso_app_of_isIso _ _) inferInstance)
  asIso ((Functor.mapCochainComplexPlusDerivedUnit (etaleModuleExtensionByZero.{u, r} Λ
      (compactificationFieldBaseChangeImmersion f j kbar))).app C)

/-- The coefficient comparison `Rj_{k̄!}(K|_{X_k̄}) ≅ (j_! K)|_{X̄_k̄}` in `D⁺(X̄_k̄)`. -/
public def compactificationFieldBaseChangeCoefficientIso
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (etaleModuleDerivedExtensionByZero.{u, r} Λ
        (compactificationFieldBaseChangeImmersion f j kbar)).obj
        (fieldBaseChangeRestriction.{u, r} Λ (Over.mk f) kbar K) ≅
      fieldBaseChangeRestriction.{u, r} Λ (Over.mk j.toBase) kbar
        ((etaleModuleExtensionByZero.{u, r} Λ j.immersion).mapCochainComplexPlus.obj K) :=
  (compactificationFieldBaseChangeDerivedExtensionByZeroIso.{u, r} Λ f j kbar _).symm ≪≫
    DerivedCategory.Plus.Q.mapIso (ObjectProperty.isoMk _
      ((NatIso.mapHomologicalComplex
        (compactificationFieldBaseChangeExtensionByZeroIso.{u, r} Λ f j kbar)
          (ComplexShape.up ℤ)).app K.obj))

/-- **The two presentations of `RΓ_c(X_k̄, K)` agree**: `RΓ(X̄_k̄, (j_! K)|_{X̄_k̄})` is isomorphic
to the cohomology with compact support of [Stacks, Tag 0GJZ] of `K|_{X_k̄}` through the
base-changed compactification. -/
public def compactSupportFrobeniusCohomologyIso
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    (geometricCompactSupportCohomology.{u, r} f j kbar Λ).obj
        (fieldBaseChangeRestriction.{u, r} Λ (Over.mk f) kbar K) ≅
      compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K :=
  (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of kbar))).mapIso
    ((etaleModuleDerivedDirectImage.{u, r} Λ
        (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
      (compactificationFieldBaseChangeCoefficientIso.{u, r} Λ f j kbar K))

omit [Fintype k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- Perfectness of `RΓ_c(X_k̄, K)` can be checked on either presentation. -/
public theorem isPerfect_compactSupportFrobeniusCohomology_iff
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    StacksDraft.Perfect.IsPerfect
        (DerivedCategory.Plus.ι.obj (compactSupportFrobeniusCohomology.{u, r} Λ f j kbar K)) ↔
      StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
        ((geometricCompactSupportCohomology.{u, r} f j kbar Λ).obj
          (fieldBaseChangeRestriction.{u, r} Λ (Over.mk f) kbar K))) :=
  ⟨StacksDraft.Perfect.isPerfect_of_iso
      (DerivedCategory.Plus.ι.mapIso (compactSupportFrobeniusCohomologyIso.{u, r} Λ f j kbar K)),
    StacksDraft.Perfect.isPerfect_of_iso
      (DerivedCategory.Plus.ι.mapIso
        (compactSupportFrobeniusCohomologyIso.{u, r} Λ f j kbar K)).symm⟩

end Comparison

end Stacks.EtaleCohomology

end
