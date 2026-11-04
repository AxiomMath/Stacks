module

public import StacksFrontier.Homology.PseudoCoherent.BaseChange
public import StacksFrontier.Homology.TorAmplitude.NilpotentCertified
public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.MateSquare
import all StacksFrontier.Homology.TorAmplitude.NilpotentCertified

/-!
# The finite-Tor-dimension case of Stacks 0BZM

Let `R → A` and `R → R'` be Tor-independent ring maps and `A' = A ⊗_R R'`. Stacks 0BZM asserts
that the base-change morphism of Stacks 0E29 is invertible at every bounded-below object of
`D(R)` when `A` is pseudo-coherent over `R` and `R'` has *finite Tor dimension* over `R`. The
reduction of Stacks 0E2A, carried out in
`StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.BridgeA.MateSquare`, brings that assertion
down to one commuting square plus invertibility of the derived-Hom base-change morphism of
Stacks 0E1X at the algebra, and the latter is supplied by Stacks 0A6A. Of the four cases of
Stacks 0A6A, the one Stacks 0BZM needs is case (4): finite Tor dimension of the base change,
pseudo-coherence of the first argument, boundedness below of the second.

This file instantiates case (4), and relates the hypotheses as Stacks 0BZM states them to the
hypotheses as Stacks 0A6A reads them. Stacks 0A6A reads both conditions on the algebra in the
common module universe that the three rings force, with the ring moved into that universe by
`ULift`; Stacks 0BZM states them for `A` and `R'` in their own universes. So:

* pseudo-coherence of `A` as an `R`-module is carried up to pseudo-coherence of the degree-zero
  complex on `ULift A` by `StacksDraft.PseudoCoherence.ulift_preserves_pseudoCoherent`, after
  the two `R`-module structures on `ULift A` — universe lift of the algebra, and restriction of
  scalars of `ULift A` over `A` — are identified;
* finite Tor dimension of `R'` over `R`, read off an arbitrary
  `StacksDraft.TorAmplitude.CertifiedDerivedTensoring` as in Stacks 0652, is carried to the
  canonical derived tensor product of the lifted ring, which is the form Stacks 0A6A case (4) is
  stated in.

## Main definitions

* `Dualizing.uliftAlgebraRestrictScalarsIso` — the universe lift of an algebra, as a module over
  the base ring, is the restriction of scalars of the universe lift of the algebra over itself.

## Main results

* `Dualizing.isPseudoCoherent_singleULiftAlgebra` — a pseudo-coherent module stays
  pseudo-coherent after the universe lift, in the spelling Stacks 0A6A uses.
* `Dualizing.exists_isZero_canonTensor_of_moduleHasFiniteTorDimension` — finite Tor dimension of
  a module, read off an arbitrary certified derived tensor product, gives the Tor-amplitude
  bound of Stacks 0A6A case (4) at the lifted ring.
* `Dualizing.isIso_derivedHomBaseChangeAtAlgebra_of_finiteTorDimension` — **Stacks 0A6A (4)** at
  the arguments of Stacks 0E2A: the derived-Hom base-change morphism of Stacks 0E1X out of the
  algebra is invertible when `R'` has finite Tor dimension over `R`, `A` is pseudo-coherent over
  `R` and `K` is bounded below.
* `Dualizing.isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_mateSquare` — **Stacks
  0BZM**, with the comparison square of Stacks 0E2A as its only remaining hypothesis and with the
  hypotheses on `A` and on `K` exactly as Stacks 0BZM states them.

## Implementation notes

The derived extension functors and the morphisms exhibiting their universal properties are
arguments, exactly as in `Dualizing.derivedHomBaseChange`, so nothing here depends on a choice of
model for unbounded derived extension of scalars.

Finite Tor dimension is read at the module universe that the three rings force, rather than at
the universe of `R'` alone. The two are different propositions and the second does not imply the
first: Tor amplitude at a larger module universe is tested against more modules, and the only
route from the smaller condition to the larger one is the flat-representative characterisation of
Stacks 0654, whose proof needs enough projectives in the module category — that is, it needs the
module universe to contain the ring's.

## References

* [Stacks Project, Tag 0BZM](https://stacks.math.columbia.edu/tag/0BZM)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 064Q](https://stacks.math.columbia.edu/tag/064Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open StacksDraft.PseudoCoherence StacksDraft.TorAmplitude Stacks.DerivedHom.BaseChangeIso
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp v

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

attribute [local instance] extendScalarsAdditiveOfRingHom

/-- The universe lift of an algebra `A`, viewed as a module over the base ring `R`, is the
restriction of scalars along `R → A` of the universe lift of `A` as a module over itself. Both
carriers are `ULift A`, and the identity map is `R`-linear by `Algebra.smul_def`. -/
noncomputable def uliftAlgebraRestrictScalarsIso
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A] :
    (ModuleCat.uliftFunctor.{max v uR uA, uA} R).obj (ModuleCat.of R A) ≅
      (ModuleCat.restrictScalars (algebraMap R A)).obj
        (ModuleCat.of A (ULift.{max v uR uA, uA} A)) where
  hom := ConcreteCategory.ofHom (C := ModuleCat R)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => ULift.ext _ _ (Algebra.smul_def r x.down) }
  inv := ConcreteCategory.ofHom (C := ModuleCat R)
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => ULift.ext _ _ (Algebra.smul_def r x.down).symm }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- Pseudo-coherence of `A` as an `R`-module, in the spelling of Stacks 064Q (4), gives
pseudo-coherence of the degree-zero complex on `ULift A` in the larger module universe, in the
spelling Stacks 0A6A uses for the algebra. -/
theorem isPseudoCoherent_singleULiftAlgebra
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
    (hA : IsModulePseudoCoherent (R := R) A) :
    IsPseudoCoherent
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA, uA} A)))) := by
  obtain ⟨E, hE, ⟨e⟩⟩ :=
    (ulift_preserves_pseudoCoherent.{uA, max v uR uA, uR} (R := R)
      ((DerivedCategory.singleFunctor (ModuleCat.{uA} R) 0).obj (ModuleCat.of R A))).2 hA
  exact ⟨E, hE, ⟨e ≪≫
    ((ModuleCat.uliftFunctor.{max v uR uA, uA} R).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of R A) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{max v uR uA} R) 0).mapIso
        uliftAlgebraRestrictScalarsIso.{uR, uA, v}⟩⟩

/-- Finite Tor dimension of the `R`-module `ULift R'`, read off an arbitrary certified derived
tensor product as in Stacks 0652, gives the Tor-amplitude bound in which Stacks 0A6A case (4)
asks for it: vanishing, below some degree, of the homology of the canonical derived tensor
product of the lifted ring `ULift R` against every module. -/
theorem exists_isZero_canonTensor_of_moduleHasFiniteTorDimension
    {R : Type uR} {R' : Type uRp} [CommRing R] [CommRing R'] [Algebra R R']
    (D : CertifiedDerivedTensoring.{uR, max v uR uRp} R)
    (hFinite : ModuleHasFiniteTorDimension D.tensor D.comparison D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR, uRp} R')))) :
    ∃ a : ℤ, ∀ (N : ModuleCat.{max v uR uRp} R) (i : ℤ), i < a →
      IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{max v uR uRp} (ULift.{max v uRp} R)) i).obj
        ((canonTensorMod ((moduleUniverseEquiv.{uR, max v uRp} R).functor.obj N)).obj
          ((moduleUniverseEquiv.{uR, max v uRp} R).functor.mapDerivedCategory.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uRp} R) 0).obj
              ((ModuleCat.restrictScalars (algebraMap R R')).obj
                (ModuleCat.of R' (ULift.{max v uR, uRp} R'))))))) := by
  obtain ⟨a, b, h⟩ := hFinite
  refine ⟨a, fun N i hi => ?_⟩
  exact (hasTorAmplitude_iff_scalarLift.{uR, max v uRp}
    D.tensor D.comparison D.isLeftDerived _ a b).1 h
    ((moduleUniverseEquiv.{uR, max v uRp} R).functor.obj N) i fun hm => not_le.2 hi hm.1

section Algebra

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))

/-- **Stacks 0A6A (4)** at the arguments of Stacks 0E2A: the derived-Hom base-change morphism of
Stacks 0E1X from the algebra `A`, viewed as a degree-zero complex of `R`-modules, is invertible
when `R'` has finite Tor dimension over `R`, `A` is pseudo-coherent as an `R`-module and `K` is
bounded below. The hypotheses on `A` and on `R'` are those of Stacks 0BZM. -/
theorem isIso_derivedHomBaseChangeAtAlgebra_of_finiteTorDimension
    (D : CertifiedDerivedTensoring.{uR, max v uR uA uRp} R)
    (hFinite : ModuleHasFiniteTorDimension D.tensor D.comparison D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR uA, uRp} R'))))
    (hA : IsModulePseudoCoherent (R := R) A)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) (b : ℤ)
    (hK : DerivedCategory.IsGE K b) :
    IsIso (Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
      (algebraMap R R') baseChangeR comparisonR
      ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).obj
          (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K) :=
  Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{uR, uRp, max v uA} (algebraMap R R')
    baseChangeR comparisonR _ K
    (Or.inr (Or.inr (Or.inr
      ⟨exists_isZero_canonTensor_of_moduleHasFiniteTorDimension.{uR, uRp, max v uA} D hFinite,
        isPseudoCoherent_singleULiftAlgebra.{uR, uA, max v uRp} hA, b, hK⟩)))

end Algebra

section Square

variable {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']
  (hTor : RingTheory.TorIndependence.TorIndependent R A R')
  (baseChangeR :
    DerivedCategory (ModuleCat.{max v uR uA uRp} R) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} R'))
  (comparisonR :
    DerivedCategory.Q ⋙ baseChangeR ⟶
      (ModuleCat.extendScalars.{uR, uRp, max v uR uA uRp}
        (algebraMap R R')).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedR : baseChangeR.IsLeftDerivedFunctor comparisonR
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} R) (ComplexShape.up ℤ)))
  (baseChangeA :
    DerivedCategory (ModuleCat.{max v uR uA uRp} A) ⥤
      DerivedCategory (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')))
  (comparisonA :
    DerivedCategory.Q ⋙ baseChangeA ⟶
      (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp}
        (algebraMap A (TensorProduct R A R'))).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerivedA : baseChangeA.IsLeftDerivedFunctor comparisonA
    (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ)))

/-- **Stacks 0BZM, conditional only on the commutation of the comparison square of
Stacks 0E2A.** The hypotheses on `A`, on `R'` and on `K` are exactly those of Stacks 0BZM: `A`
pseudo-coherent as an `R`-module, `R'` of finite Tor dimension over `R` read off a certified
derived tensor product as in Stacks 0652, the square Tor-independent, and `K` bounded below. The
remaining hypothesis `hComparison` is the same square as in
`Dualizing.isIso_derivedHomBaseChange_app_of_flat_of_mateSquare` and
`Dualizing.isIso_derivedHomBaseChange_app_of_isPerfect_of_mateSquare`. -/
theorem isIso_derivedHomBaseChange_app_of_finiteTorDimension_of_mateSquare
    (D : CertifiedDerivedTensoring.{uR, max v uR uA uRp} R)
    (hFinite : ModuleHasFiniteTorDimension D.tensor D.comparison D.isLeftDerived
      ((ModuleCat.restrictScalars (algebraMap R R')).obj
        (ModuleCat.of R' (ULift.{max v uR uA, uRp} R'))))
    (hA : IsModulePseudoCoherent (R := R) A)
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R))
    (hK : (DerivedCategory.TStructure.t
      (C := ModuleCat.{max v uR uA uRp} R)).plus K)
    (hComparison :
      (ModuleCat.restrictScalars
            (Algebra.TensorProduct.includeRight :
              R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
          ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
            baseChangeA comparisonA isLeftDerivedA).app K) =
        (mateSourceIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
            isLeftDerivedA K).hom ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uRp, max v uA}
            (algebraMap R R') baseChangeR comparisonR
            ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
              ((ModuleCat.restrictScalars (algebraMap R A)).obj
                (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) K ≫
          (mateTargetIso hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
            isLeftDerivedA K).inv) :
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  isIso_derivedHomBaseChange_app_of_comparison hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA K _ _ _ hComparison
    (isIso_derivedHomBaseChangeAtAlgebra_of_finiteTorDimension baseChangeR comparisonR
      isLeftDerivedR D hFinite hA K hK.choose hK.choose_spec)

end Square

end Dualizing

end
