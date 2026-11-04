module

public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Ext
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.RelativeDualizingSerre

/-!
# The zeroth cohomology of derived Hom into the base ring is the dual

Let `f : R →+* A` be a homomorphism of commutative rings and let `RHom_R(A, -) : D(R) ⥤ D(A)` be
derived coextension of scalars, [Stacks, Tag 0A70].  This file identifies

`H^0(RHom_R(A, R)) ≅ Hom_R(A, R)`

`R`-linearly, where the left-hand side is read as an `R`-module through `f`.

Two identifications compose.  The cohomology of derived coextension is Ext,
[Stacks, Tag 0A71], which this library has as
`Dualizing.derivedCoextendScalarsHomologyLinearEquivExt`; it gives
`H^q(RHom_R(A, K)) ≅ Ext^q_R(A[0], K)` for every `K` of `D(R)` and every `q`.  And an `Ext` in
degree `0` between two complexes concentrated in degree `0` is a module of homomorphisms, which
is [Stacks, Tag 06XS] at `n = a = a' = b = 0`, available `R`-linearly as
`Dualizing.extremalExtLinearEquiv`.  Taking `K = R[0]` and `q = 0` and composing gives the
statement.

## Main definitions

* `Dualizing.extZeroSingleLinearEquiv` — `Ext^0_R(M[0], N[0]) ≅ Hom_R(M, N)`, the degree-`0`
  edge case of [Stacks, Tag 06XS].
* `Dualizing.derivedHomHomologyLinearEquivExtStandard` — [Stacks, Tag 0A71] at the derived Hom
  functor `Dualizing.derivedHom` itself: `H^q(RHom_R(A, K)) ≅ Ext^q_R(A[0], K)`.
* `Dualizing.uliftRestrictLinearEquiv` — the universe lift `ULift A`, read over `R` through
  `algebraMap R A`, is `A`.
* `Dualizing.derivedHomHomologyZeroLinearEquivDual` — `H^0(RHom_R(A, R)) ≅ Hom_R(A, R)`.

## Implementation notes

The module universe is pinned to the universe of the two rings.  `Dualizing.extremalExtLinearEquiv`
is stated for `ModuleCat.{u} A` with `A : Type u`, so that is where the composite lives; a
statement at `ModuleCat.{max v u}` would need that lemma restated.  Nothing below needs the extra
room: the consumer is a statement about `R`-modules and `A`-modules, both of them in `Type u`.

The `ULift` appears because the free rank-one module naming the `Ext` of [Stacks, Tag 0A71] is
`ULift A`, and because the relative dualizing complex is `RHom_R(A, -)` evaluated at the single
complex on `ULift R`.  `Dualizing.uliftRestrictLinearEquiv` strips it on the source side and
`ULift.moduleEquiv` on the target side.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **`Ext^0` between two complexes concentrated in degree `0` is a module of homomorphisms.**
For `R`-modules `M` and `N`,

`Ext^0_R(M[0], N[0]) ≅ Hom_R(M, N)` .

This is [Stacks, Tag 06XS] at `n = 0`, `a = a' = b = 0`: `M[0]` lies in `D^{≤ 0}(R)` and `N[0]`
lies in `D^{≥ 0}(R)`, so taking cohomology in degree `0` is a bijection on `Ext^0`, and it is
`R`-linear by `Dualizing.extremalExtLinearEquiv`. -/
noncomputable def extZeroSingleLinearEquiv {R : Type u} [CommRing R] (M N : ModuleCat.{u} R) :
    DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) 0 ≃ₗ[R] (M →ₗ[R] N) :=
  (extremalExtLinearEquiv ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) 0 0 0 0 (by norm_num)
      le_rfl).trans
    (LinearEquiv.arrowCongr
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
        M).toLinearEquiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} R) 0).app
        N).toLinearEquiv)

/-- **[Stacks, Tag 0A71] at `Dualizing.derivedHom`.**  For `f : R →+* A` and `K` in `D(R)`,
restriction of scalars along `f` identifies

`H^q(RHom_R(A, K)) ≅ Ext^q_R(A[0], K)` .

`Dualizing.derivedCoextendScalarsHomologyLinearEquivExt` proves this for an arbitrary right
derived functor of coextension of scalars presented by its structural transformation; this is
that statement at the functor `Dualizing.derivedHom` and its total-derived unit, for which
`Dualizing.derivedHom_isRightDerivedFunctor` supplies the universal property. -/
noncomputable def derivedHomHomologyLinearEquivExtStandard {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (K : DerivedCategory (ModuleCat.{u} R)) (q : ℤ) :
    ((ModuleCat.restrictScalars.{u} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((derivedHom.{u, u, u} f).obj K))) ≃ₗ[R]
      DerivedCategory.Ext ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        ((ModuleCat.restrictScalars.{u} f).obj (ModuleCat.of A (ULift.{u} A)))) K q :=
  (derivedCoextendScalarsHomologyLinearEquivExt f (derivedHom.{u, u, u} f)
    ((coextendScalarsToDerivedCategory f).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)))).linearEquiv K q

/-- **The universe lift of `A`, read over `R`, is `A`.**  For an `R`-algebra `A`, the `R`-module
obtained from the free rank-one `A`-module `ULift A` by restriction of scalars along
`algebraMap R A` is `A` itself: the two actions of `r` are `algebraMap R A r * -` either way. -/
noncomputable def uliftRestrictLinearEquiv {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] :
    ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj
      (ModuleCat.of A (ULift.{u} A))) ≃ₗ[R] A where
  toFun x := x.down
  map_add' _ _ := rfl
  map_smul' r x := (Algebra.smul_def r x.down).symm
  invFun a := ULift.up a
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The zeroth cohomology of `RHom_R(A, R)` is the `R`-dual of `A`.**  For an `R`-algebra `A`,

`H^0(RHom_R(A, R)) ≅ Hom_R(A, R)`

as `R`-modules, the left-hand side being read over `R` through `algebraMap R A`.

The cohomology of derived coextension is `Ext`, [Stacks, Tag 0A71]
(`Dualizing.derivedHomHomologyLinearEquivExtStandard`), and an `Ext^0` between complexes
concentrated in degree `0` is a module of homomorphisms, [Stacks, Tag 06XS]
(`Dualizing.extZeroSingleLinearEquiv`).  No hypothesis on `A` or on `f` is needed: the
identification holds for every homomorphism of commutative rings. -/
noncomputable def derivedHomHomologyZeroLinearEquivDual {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] :
    ((ModuleCat.restrictScalars.{u} (algebraMap R A)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((derivedHom.{u, u, u} (algebraMap R A)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
              (ModuleCat.of R (ULift.{u} R)))))) ≃ₗ[R] (A →ₗ[R] R) :=
  ((derivedHomHomologyLinearEquivExtStandard (algebraMap R A) _ 0).trans
      (extZeroSingleLinearEquiv _ _)).trans
    (LinearEquiv.arrowCongr uliftRestrictLinearEquiv ULift.moduleEquiv)

end Dualizing

end
