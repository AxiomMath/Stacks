module

public import StacksFrontier.RingTheory.Dualizing.CoextendScalarsProjective
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityBundlePerfect
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityInvertibleKernelPerfect
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor

/-!
# `RHom_R(B, -)` is `- ⊗_R^L B` for a self-dual finite projective algebra

Let `f : R →+* B` make `B` a finite projective `R`-module which is its own `R`-linear dual,
`Hom_R(B, R) ≅ B` as `B`-modules.  Then derived coextension of scalars along `f` is derived base
change:

`RHom_R(B, -) ≅ - ⊗_R^L B : D(R) ⥤ D(B)`.

This is [Stacks, Tag 0BZE] read at a self-dual finite projective algebra, and it is the step by
which the source's proof of [Stacks, Tag 0C0G] turns the finite case into the surjective one: the
self-duality of a monogenic finite free algebra is the generator `δ_{d-1}` of
`Dualizing.adjoinRootSelfDualIso`.

## Main results

* `Dualizing.nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual` — the isomorphism
  above, for a bare ring homomorphism with the three inputs carried explicitly.
* `Dualizing.nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual_algebra` — the same for
  an `Algebra R B` with `B` finite free over `R`, the perfectness and projectivity discharged.

## Implementation notes

Stacks 0BZE identifies `RHom_R(B, -)` with derived tensoring over `R` by *the value*
`RHom_R(B, R)`, not by `B`: that is
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect`, which is unconditional
beyond the perfectness of `B` over `R`.  What the self-duality adds is the identification of that
value with `B` in degree zero, and it is used in exactly one place, as the hypothesis `hL` of
that theorem.  The value is computed by
`Dualizing.derivedHomObjSingleIso`: `B` being projective over `R`, coextension of scalars is
exact, so `RHom_R(B, R)` is concentrated in degree zero and is `Hom_R(B, R)` there.

The projectivity and perfectness hypotheses are taken at the `R`-module structure on `B` that
restriction of scalars along `f` builds, and at the one `RingHom.toAlgebra` builds; the two have
the same `SMul` field and all other fields of `Module` are propositions, so they are the same
instance up to definitional equality.  For an honest `Algebra R B` the actions agree only by
`Algebra.smul_def`, which is why
`Dualizing.projective_restrictScalars_algebraMap_of_projective` transports across a
`LinearEquiv`.

## References

* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.DerivedTensor

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {R B : Type u} [CommRing R] [CommRing B]

/-- **Derived coextension of scalars along a self-dual finite projective algebra is derived base
change.**  Let `f : R →+* B` make `B` a perfect `R`-module which is projective as an `R`-module
and self-dual, `B ≅ Hom_R(B, R)` as `B`-modules.  Then

`RHom_R(B, -) ≅ - ⊗_R^L B : D(R) ⥤ D(B)`.

This is [Stacks, Tag 0BZE] in the derived change-of-rings shape, whose tensor factor is the value
`RHom_R(B, R)`, together with the computation of that value: `B` is projective over `R`, so
coextension of scalars is exact and the value is `Hom_R(B, R)` in degree zero, which the
self-duality identifies with `B`. -/
theorem nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual (f : R →+* B)
    (hperf : letI := f.toAlgebra
      StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) B)
    (hproj : Module.Projective R
      ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of B B)))
    (hself : ModuleCat.of B B ≅
      (ModuleCat.coextendScalars.{u, u, u} f).obj (ModuleCat.of R R)) :
    Nonempty (derivedHom.{u, u, u} f ≅
      derivedTensorProductOver.{u, u} f
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) := by
  refine nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect f hperf _ ?_
  refine ⟨(DerivedCategory.quotientCompQhIso (ModuleCat.{u} B)).symm.app _ ≪≫
    DerivedCategory.Qh.objObjPreimageIso _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso hself ≪≫
    (derivedHomObjSingleIso f hproj (ModuleCat.of R R)).symm⟩

/-- The `R`-module structure `RingHom.toAlgebra` puts on `B` through `algebraMap R B` is the
original one.  The two `SMul` fields agree only by `Algebra.smul_def`, which is a theorem, so the
equality of the instances is recorded here once and used to read a statement about `B` as an
`R`-module at either of them. -/
theorem algebraMap_toAlgebra_toModule_eq [i : Algebra R B] :
    @Algebra.toModule R B _ _ ((algebraMap R B).toAlgebra) = @Algebra.toModule R B _ _ i :=
  Module.ext' _ _ fun r b => (Algebra.smul_def r b).symm

/-- **A finite projective algebra is a perfect module at the `RingHom.toAlgebra` structure.**
This is `StacksDraft.Perfect.isPerfectModule_of_finite_projective` read at the `R`-module
structure `RingHom.toAlgebra` builds from `algebraMap R B`, which is the one
`Dualizing.nonempty_derivedHom_iso_canonicalDerivedTensor_of_perfect` is stated at. -/
theorem isPerfectModule_toAlgebra_of_finite_projective [Algebra R B]
    [Module.Finite R B] [Module.Projective R B] :
    letI := (algebraMap R B).toAlgebra
    StacksDraft.Perfect.IsPerfectModule.{u, u, u + 1} (R := R) B := by
  show @StacksDraft.Perfect.IsPerfectModule R _ B _
    (@Algebra.toModule R B _ _ ((algebraMap R B).toAlgebra)) _
  rw [algebraMap_toAlgebra_toModule_eq (R := R) (B := B)]
  exact StacksDraft.Perfect.isPerfectModule_of_finite_projective.{u, u} B

/-- **Derived coextension of scalars along a self-dual finite free algebra is derived base
change.**  Let `B` be an `R`-algebra, finite and free as an `R`-module, which is its own
`R`-linear dual.  Then `RHom_R(B, -) ≅ - ⊗_R^L B`.

This is `Dualizing.nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual` with its
perfectness and projectivity hypotheses discharged: a finite free module is finite projective,
hence perfect by `StacksDraft.Perfect.isPerfectModule_of_finite_projective`. -/
theorem nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual_algebra [Algebra R B]
    [Module.Finite R B] [Module.Free R B]
    (hself : ModuleCat.of B B ≅
      (ModuleCat.coextendScalars.{u, u, u} (algebraMap R B)).obj (ModuleCat.of R R)) :
    Nonempty (derivedHom.{u, u, u} (algebraMap R B) ≅
      derivedTensorProductOver.{u, u} (algebraMap R B)
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))) :=
  nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual (algebraMap R B)
    isPerfectModule_toAlgebra_of_finite_projective
    projective_restrictScalars_algebraMap_of_projective hself

end Dualizing

end
