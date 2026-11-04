module

public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.BLinear
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeCorepresented
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangePushout

/-!
# The base-changed representatives of [stacks 0E1U] at the diagonal square

With the notation of `StacksFrontier/RingTheory/Dualizing/RelativeBaseChangeTorIndependence.lean` —
`R → A` flat, `R → R'` arbitrary, `A' = A ⊗[R] R'`, `B = A ⊗[R] A`, `B' = A' ⊗[R'] A'`, and
`Δ : B → A`, `Δ' : B' → A'` the two multiplication maps — the proof of [stacks 0E2F] (2) applies
[stacks 0E1U] at the flat ring map `R → B`, to the diagonal `A` and to `X = K ⊗ᴸ_A B`.  That
produces two representatives: `P^•`, bounded above with finite free `B`-modules, with
`P^• ≅ A[0]` in `D(B)`, and `F^•`, bounded with `R`-flat `B`-modules, with `F^• ≅ X` in `D(B)`;
and it produces them *compatibly with base change along `R → R'`*, the base change being termwise
extension of scalars along the map of diagonals `Dualizing.diagonalBaseChangeMap`.

This file identifies the two base-changed representatives, which is what the degreewise argument
of [stacks 0E2F] (2) needs above the chase:

* `P^• ⊗_B B' ≅ A'[0]` in `D(B')`, and
* `F^• ⊗_B B' ≅ (K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'` in `D(B')`.

Together — `Dualizing.nonempty_homAddEquiv_restrictedUnitSingle` — they say that the morphism
groups `Hom_{D(B')}(P^• ⊗_B B', (F^• ⊗_B B')⟦j⟧)` that the representability clause of
[stacks 0E1U] computes are the groups `Hom_{D(B')}(A'[0], Y⟦j⟧)` that the hypotheses of
`Dualizing.isRelativeDualizingComplex_baseChange_of_hom` are read on.

## Main definitions

* `Dualizing.diagonalBaseChangeExtendScalarsIso` — termwise extension of scalars along the map of
  diagonals carries `Dualizing.diagonalModule` to `A'` as a `B'`-module through `Δ'`.
* `Dualizing.diagonalBaseChangeSingleIso` — **`A ⊗ᴸ_B B' = A'`**: the derived base change along
  the map of diagonals of the diagonal module placed in degree zero is `A'[0]`.

## Main results

* `Dualizing.nonempty_restrictedUnitSingle_iso_extendScalars` — **the first identification**: the
  termwise base change of any K-flat representative of `A[0]` represents `A'[0]`.
* `Dualizing.nonempty_diagonalDerivedExtension_baseChange_iso` — derived base change along the map
  of diagonals of `K ⊗ᴸ_A B` is `(K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'`: the diagonal of the base change is the
  base change of the diagonal, derived.
* `Dualizing.nonempty_diagonalBaseChangeTarget_iso_extendScalars` — **the second
  identification**: the termwise base change of a bounded above representative of `K ⊗ᴸ_A B` with
  `R`-flat terms represents `(K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'`.
* `Dualizing.nonempty_homAddEquiv_restrictedUnitSingle` — the two identifications on the morphism
  groups.

## Implementation notes

*The first identification is pure transport.*  Both halves of `A ⊗ᴸ_B B' = A'` are proved:
the vanishing of the higher Tor modules is
`Dualizing.isIso_comparison_diagonalBaseChange_single` and the naive identification is
`Dualizing.diagonalBaseChangePushoutEquiv`, an isomorphism of `B'`-algebras.  What is done here is
to read the second as a statement about the *termwise* functor
`CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`.  That functor is built
from `ModuleCat.extendScalars` of a ring hom, so no `Algebra` instance enters its statement and
the scalar-action diamond discussed in the module documentation of
`StacksFrontier/RingTheory/Dualizing/RelativeBaseChangePushout.lean` does not recur; only the proof
needs the actions seated, which is why the local instances of that file are reinstated in the
first section.

*The asymmetry between the two representatives.*  `F^•` is bounded *above* with `R`-flat terms,
hence K-flat over `R` by [stacks 064K], `CochainComplex.KFlat.kFlat_of_flat`, and therefore
computes its own derived base change along `B → B'` by Tor independence —
`Dualizing.isIso_comparison_diagonalBaseChange_of_flat`.  The complex `E^•` of [stacks 0E1U] is
bounded *below* with `R`-flat terms and is for that reason not K-flat, which is why no such
identification is available for it and why the source argues degreewise instead; see the module
documentation of `StacksFrontier/RingTheory/Dualizing/RelativeBaseChange.lean`.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

section Transport

attribute [local instance 10000] diagonalBaseChangeAlgebra smulDiagonalBaseChange
  moduleDiagonalBaseChange

attribute [local instance] isScalarTower_diagonalBaseChange isPushout_diagonalBaseChange
  diagonalAlgebraSelf diagonalAlgebraBaseChange
  isScalarTower_diagonal_diagonalBaseChange isScalarTower_base_diagonalBaseChange
  isPushout_diagonalBaseChange_diagonal

variable [Module.Flat R A]

/-- **`B' ⊗_B A = A'` for the termwise extension-of-scalars functor.**  Extension of scalars
along the map of diagonals `Dualizing.diagonalBaseChangeMap` carries the diagonal module
`Dualizing.diagonalModule` to `A'`, viewed as a `B'`-module through the multiplication map `Δ'`.

This is `Dualizing.diagonalBaseChangePushoutEquiv` read as a morphism of `ModuleCat B'`:
`ModuleCat.extendScalars` is taken along a ring hom, so the `B`-module structures on `B'` and on
the diagonal are the ones that equivalence is linear for. -/
def diagonalBaseChangeExtendScalarsIso :
    (ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')).obj
        (diagonalModule R A) ≅
      (ModuleCat.restrictScalars.{u}
        (Algebra.TensorProduct.lmul' R' :
          (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom).obj
        (ModuleCat.of (A ⊗[R] R') (A ⊗[R] R')) :=
  LinearEquiv.toModuleIso (diagonalBaseChangePushoutEquiv R A R').toLinearEquiv

end Transport

variable [Module.Flat R A]

/-- **`A ⊗ᴸ_B B' = A'[0]`.**  The derived base change along the map of diagonals `B → B'` of the
diagonal module placed in degree zero is `A'`, viewed as a `B'`-module through `Δ'` and placed in
degree zero.

Both halves are already proved: `Dualizing.isIso_comparison_diagonalBaseChange_single` says the
comparison from derived to termwise extension of scalars is invertible there, which is the
vanishing of the higher Tor modules, and `Dualizing.diagonalBaseChangeExtendScalarsIso` evaluates
the termwise functor.  This is the identification the proof of [stacks 0E2F] (2) gets from Tor
independence (More on Algebra, Lemma 15.62.2). -/
def diagonalBaseChangeSingleIso :
    (totalDerivedExtensionScalars.{u, u, u} (diagonalBaseChangeMap R A R')).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
          (diagonalModule R A)) ≅
      restrictedUnitSingle
        (Algebra.TensorProduct.lmul' R' :
          (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 := by
  let C := ModuleCat.{u} (A ⊗[R] A)
  let C' := ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
  let D := totalDerivedExtensionScalars.{u, u, u} (diagonalBaseChangeMap R A R')
  let F := ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')
  let M : C := diagonalModule R A
  let P := (CochainComplex.singleFunctor C 0).obj M
  exact D.functor.mapIso ((DerivedCategory.singleFunctorIsoCompQ C 0).app M) ≪≫
    @asIso _ _ _ _ (D.comparison.app P) (isIso_comparison_diagonalBaseChange_single R A R') ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C' 0).app (F.obj M)).symm ≪≫
    (DerivedCategory.singleFunctor C' 0).mapIso (diagonalBaseChangeExtendScalarsIso R A R')

/-- **The first identification above the degreewise chase of [stacks 0E2F] (2): `P^• ⊗_B B'`
represents `A'[0]`.**  Let `P^•` be a K-flat complex of `B`-modules representing the diagonal
module placed in degree zero — the representative [stacks 0E1U] produces is bounded above with
finite free terms, hence K-flat by [stacks 064K].  Then the termwise extension of scalars of `P^•`
along the map of diagonals represents `A'`, viewed as a `B'`-module through `Δ'` and placed in
degree zero.

K-flatness makes the comparison invertible at `P^•`, and `Dualizing.diagonalBaseChangeSingleIso`
evaluates the derived functor on `A[0]`. -/
theorem nonempty_restrictedUnitSingle_iso_extendScalars
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A)) :
    Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) ≅
      restrictedUnitSingle
        (Algebra.TensorProduct.lmul' R' :
          (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0) := by
  let D := totalDerivedExtensionScalars.{u, u, u} (diagonalBaseChangeMap R A R')
  exact ⟨(@asIso _ _ _ _ (D.comparison.app P) (D.comparison_isIso_of_kFlat P hP)).symm ≪≫
    D.functor.mapIso eP ≪≫
    diagonalBaseChangeSingleIso R A R'⟩

/-- **The diagonal of the base change is the base change of the diagonal, derived.**  For `K` an
object of `D(A)`, the derived base change along the map of diagonals `B → B'` of `K ⊗ᴸ_A B` is
`(K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'`.

The route is the one of `Dualizing.diagonalDerivedExtensionBaseChangeIso`: both sides are derived
extension of scalars along a composite of two ring maps, and the two composites agree by
`Dualizing.diagonalBaseChangeMap_comp_includeLeft`, so
`StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso` identifies them. -/
theorem nonempty_diagonalDerivedExtension_baseChange_iso
    (K : DerivedCategory (ModuleCat.{u} A)) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    Nonempty
      ((totalDerivedExtensionScalars.{u, u, u}
            (diagonalBaseChangeMap R A R')).functor.obj
          ((diagonalDerivedExtension R A).obj K) ≅
        (diagonalDerivedExtension R' (A ⊗[R] R')).obj
          ((totalDerivedExtensionScalars.{u, u, u}
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  refine ⟨(totalDerivedExtensionScalars.{u, u, u}
      (diagonalBaseChangeMap R A R')).functor.mapIso
        (((diagonalDerivedExtensionIsoTotalDerived R A).app K).symm) ≪≫ ?_⟩
  refine (StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
    (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] A)
    (diagonalBaseChangeMap R A R')).app K ≪≫ ?_
  rw [diagonalBaseChangeMap_comp_includeLeft]
  exact ((StacksDraft.DerivedExtensionScalarsComp.derivedExtensionScalarsCompIso
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')
      (Algebra.TensorProduct.includeLeftRingHom :
        (A ⊗[R] R') →+* (A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))).app K).symm ≪≫
    (diagonalDerivedExtensionIsoTotalDerived R' (A ⊗[R] R')).app _

/-- **The second identification above the degreewise chase of [stacks 0E2F] (2): `F^• ⊗_B B'`
represents `(K ⊗ᴸ_A A') ⊗ᴸ_{A'} B'`.**  Let `F^•` be a complex of `B`-modules, bounded above and
with terms flat over `R`, representing `K ⊗ᴸ_A B` — which is the second representative
[stacks 0E1U] produces.  Then the termwise extension of scalars of `F^•` along the map of
diagonals represents the object `Y` of `D(B')` whose derived Hom from the diagonal clause (2)
computes.

Boundedness *above* with `R`-flat terms makes `F^•` K-flat over `R` ([stacks 064K]), hence makes
the comparison invertible at `F^•` by Tor independence
(`Dualizing.isIso_comparison_diagonalBaseChange_of_flat`);
`Dualizing.nonempty_diagonalDerivedExtension_baseChange_iso` then evaluates the derived
functor. -/
theorem nonempty_diagonalBaseChangeTarget_iso_extendScalars
    (K : DerivedCategory (ModuleCat.{u} A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    Nonempty (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, u, u} (diagonalBaseChangeMap R A R')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F) ≅
      (diagonalDerivedExtension R' (A ⊗[R] R')).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let D := totalDerivedExtensionScalars.{u, u, u} (diagonalBaseChangeMap R A R')
  exact ⟨(@asIso _ _ _ _ (D.comparison.app F)
      (isIso_comparison_diagonalBaseChange_of_flat R A R' F d hflat)).symm ≪≫
    D.functor.mapIso eF ≪≫
    (nonempty_diagonalDerivedExtension_baseChange_iso R A R' K).some⟩

/-- **The two identifications, on the morphism groups.**  The morphism groups
`Hom_{D(B')}(P^• ⊗_B B', (F^• ⊗_B B')⟦j⟧)` — the groups the representability clause of
[stacks 0E1U] computes after base change — are the groups `Hom_{D(B')}(A'[0], Y⟦j⟧)` on which the
hypotheses of `Dualizing.isRelativeDualizingComplex_baseChange_of_hom` are read.

The two identifications enter as precomposition and postcomposition; the degree-zero group
carries an `A'`-action through its source (`Dualizing.smulHomRestrictedUnitSingle`) which this
additive statement says nothing about. -/
theorem nonempty_homAddEquiv_restrictedUnitSingle
    (K : DerivedCategory (ModuleCat.{u} A))
    (P : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (hP : CochainComplex.KFlat.{u, u} P)
    (eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj (diagonalModule R A))
    (F : CochainComplex (ModuleCat.{u} (A ⊗[R] A)) ℤ) (d : ℤ) [F.IsStrictlyLE d]
    (hflat : ∀ i : ℤ, Module.Flat R
      ((ModuleCat.restrictScalars (algebraMap R (A ⊗[R] A))).obj (F.X i)))
    (eF : DerivedCategory.Q.obj F ≅ (diagonalDerivedExtension R A).obj K) (j : ℤ) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    Nonempty
      ((DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, u, u}
              (diagonalBaseChangeMap R A R')).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
          (CategoryTheory.shiftFunctor
              (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.extendScalars.{u, u, u}
                (diagonalBaseChangeMap R A R')).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj F))) ≃+
        (restrictedUnitSingle
            (Algebra.TensorProduct.lmul' R' :
              (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') →ₐ[R'] (A ⊗[R] R')).toRingHom 0 ⟶
          (CategoryTheory.shiftFunctor
              (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).obj
            ((diagonalDerivedExtension R' (A ⊗[R] R')).obj
              ((totalDerivedExtensionScalars.{u, u, u}
                (Algebra.TensorProduct.includeLeftRingHom :
                  A →+* A ⊗[R] R')).functor.obj K)))) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  obtain ⟨e₂⟩ := nonempty_restrictedUnitSingle_iso_extendScalars R A R' P hP eP
  obtain ⟨e₃⟩ := nonempty_diagonalBaseChangeTarget_iso_extendScalars R A R' K F d hflat eF
  exact ⟨(precompAddEquiv e₂.symm _).trans
    (postcompAddEquiv _ ((CategoryTheory.shiftFunctor
      (DerivedCategory (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R')))) j).mapIso e₃))⟩

end

end Dualizing

end
