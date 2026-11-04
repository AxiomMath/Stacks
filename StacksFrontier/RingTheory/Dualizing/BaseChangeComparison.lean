module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange

/-!
# Base change of the algebra itself

Let `R → A` and `R → R'` be ring maps and `A' = A ⊗_R R'`. The proof of Stacks 0E2A identifies
the restriction along `R' → A'` of the base-change morphism of Stacks 0E29 with the derived-Hom
base-change morphism of Stacks 0E1X; the identification "uses that `A' = A ⊗ᴸ_R R'`", that is, it
needs to know that derived base change along `R → R'` carries the degree-zero complex `A` to the
degree-zero complex `A ⊗_R R'` rather than to a complex with higher Tor terms.

That is what this file proves. The input is the Tor-independence comparison of Stacks 0661: for a
Tor-independent square, the canonical morphism `baseChange_{R→R'} ∘ Res_{A/R} ⟶ Res_{A'/R'} ∘
baseChange_{A→A'}` is invertible. Evaluating it at the unit object of `D(A)` and computing the
`A`-side derived base change there — the degree-zero complex on `A` is K-flat over `A`, so the
comparison of any left-derived extension of scalars is already invertible on it — gives the
identification over `R'`.

Two further steps of the same reduction are recorded here. The reduction to the restriction along
`R' → A'` is an equivalence, not just an implication, because a functor carries isomorphisms to
isomorphisms; and the internal-Hom bifunctor of the fixed tensor--Hom adjunction on `D(R)` is
literally the one the base-change statements of Stacks 0E1W and 0E1X are written with, so no
comparison is needed to pass between them.

## Main results

* `Dualizing.extendScalarsULiftUnitIso` — extension of scalars along `h : A →+* B` carries the
  universe-lifted ring `A`, as a module over itself, to the universe-lifted ring `B`.
* `Dualizing.derivedBaseChangeAlgebraIso` — derived base change along `R → R'` carries `A`,
  viewed as a degree-zero complex of `R`-modules, to `A ⊗_R R'` viewed as a degree-zero complex
  of `R'`-modules.
* `Dualizing.isIso_derivedHomBaseChange_app_iff_restrictScalars` — the base-change morphism of
  Stacks 0E29 is invertible if and only if its restriction along `R' → A'` is.
* `Dualizing.derivedHomAdjunctionOverRing_hom_eq` — the internal-Hom bifunctor of
  `derivedHomAdjunctionOverRing` is `Stacks.DerivedHom.ScalarTransportedInternalHom.hom`.

## Implementation notes

The three rings and the module size carry independent universe parameters, so the modules in play
are universe lifts: the algebra `A` enters as `ULift A` over `A` and the degree-zero object of
`D(R)` is its restriction of scalars. The functors for derived base change and the morphisms
exhibiting their universal properties are taken as arguments, exactly as in
`Dualizing.derivedHomBaseChange`, so that the statement does not depend on a choice of model for
unbounded derived extension of scalars.

## References

* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS uT v w

namespace Dualizing

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Extension of scalars along a ring map is an additive functor. -/
local instance {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T) :
    (ModuleCat.extendScalars.{uS, uT, w} f).Additive := by
  let := f.toAlgebra
  constructor
  intro X Y a b
  ext x
  change (1 : T) ⊗ₜ[S,f] ((a + b) x) =
    (1 : T) ⊗ₜ[S,f] a x + (1 : T) ⊗ₜ[S,f] b x
  rw [show (a + b : X ⟶ Y) x = a x + b x by rfl, TensorProduct.tmul_add]

/-- Extension of scalars along `h : A →+* B` takes `A`, viewed as a module over itself in a large
enough module universe, to `B`: the canonical map `B ⊗_A A → B` is invertible. -/
noncomputable def extendScalarsULiftUnitIso
    {A : Type uS} {B : Type uT} [CommRing A] [CommRing B] (h : A →+* B) :
    (ModuleCat.extendScalars.{uS, uT, max w uS uT} h).obj
        (ModuleCat.of A (ULift.{max w uT} A)) ≅
      ModuleCat.of B (ULift.{max w uS} B) := by
  letI : Algebra A B := h.toAlgebra
  exact LinearEquiv.toModuleIso
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
        (ULift.moduleEquiv (R := A) (M := A))).trans
      ((TensorProduct.AlgebraTensorModule.rid A B B).trans ULift.moduleEquiv.symm))

/-- Derived base change along `R → R'` carries the algebra `A`, viewed as a degree-zero complex of
`R`-modules, to `A ⊗_R R'`, viewed as a degree-zero complex of `R'`-modules. This is the
identification `A' = A ⊗ᴸ_R R'` used in the proof of Stacks 0E2A: Tor independence is what makes
the higher Tor terms vanish, and it enters through the comparison of Stacks 0661. -/
noncomputable def derivedBaseChangeAlgebraIso
    {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
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
      (HomologicalComplex.quasiIso (ModuleCat.{max v uR uA uRp} A) (ComplexShape.up ℤ))) :
    baseChangeR.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R) 0).obj
          ((ModuleCat.restrictScalars (algebraMap R A)).obj
            (ModuleCat.of A (ULift.{max v uR uA uRp} A)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max v uR uA uRp} R') 0).obj
        ((ModuleCat.restrictScalars (algebraMap R' (TensorProduct R A R'))).obj
          (ModuleCat.of (TensorProduct R A R')
            (ULift.{max v uR uA uRp} (TensorProduct R A R')))) := by
  have := isLeftDerivedR
  have := isLeftDerivedA
  let f : R →+* A := algebraMap R A
  let h : A →+* TensorProduct R A R' := algebraMap A (TensorProduct R A R')
  let i : R' →+* TensorProduct R A R' := algebraMap R' (TensorProduct R A R')
  have sq : h.comp f = i.comp (algebraMap R R') :=
    (IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R'))
  let UA : ModuleCat.{max v uR uA uRp} A := ModuleCat.of A (ULift.{max v uR uA uRp} A)
  let X : CochainComplex (ModuleCat.{max v uR uA uRp} A) ℤ :=
    (CochainComplex.singleFunctor (ModuleCat.{max v uR uA uRp} A) 0).obj UA
  have hflat : ∀ n : ℤ, Module.Flat A (X.X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 UA).toLinearEquiv
    · have : Subsingleton (X.X n) := ModuleCat.isZero_iff_subsingleton.mp
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 UA n hn)
      infer_instance
  have hX : CochainComplex.KFlat.{uA, max v uR uA uRp} X :=
    CochainComplex.KFlat.kFlat_of_flat X 0
  have hcA : IsIso (comparisonA.app X) :=
    @CochainComplex.DerivedTensor.KFlatDerived.isIso_extensionCounit_app_of_kFlat.{uA,
      max uA uRp, max v uR} A (TensorProduct R A R') _ _ h _ _ baseChangeA comparisonA
      isLeftDerivedA X hX
  let c := RingTheory.TorIndependence.derivedBaseChangeComparison f (algebraMap R R') h i sq
    baseChangeR baseChangeA comparisonR comparisonA
  have hc : IsIso c.2.1 :=
    RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent
      hTor baseChangeR baseChangeA comparisonR comparisonA
  exact baseChangeR.mapIso
      (((ModuleCat.restrictScalars f).mapDerivedCategorySingleFunctor 0).app UA).symm ≪≫
    asIso (c.2.1.app ((DerivedCategory.singleFunctor
      (ModuleCat.{max v uR uA uRp} A) 0).obj UA)) ≪≫
    (ModuleCat.restrictScalars i).mapDerivedCategory.mapIso
      (asIso (comparisonA.app X) ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars.{uA, max uA uRp, max v uR uA uRp} h)
            (ComplexShape.up ℤ) 0).app UA) ≪≫
        (DerivedCategory.singleFunctor
          (ModuleCat.{max v uR uA uRp} (TensorProduct R A R')) 0).mapIso
          (extendScalarsULiftUnitIso.{uA, max uA uRp, max v uR uRp} h)) ≪≫
    ((ModuleCat.restrictScalars i).mapDerivedCategorySingleFunctor 0).app
      (ModuleCat.of (TensorProduct R A R')
        (ULift.{max v uR uA uRp} (TensorProduct R A R')))

/-- Invertibility of the derived-Hom base-change morphism of Stacks 0E29 is *equivalent* to
invertibility of its restriction of scalars along `R' → A ⊗_R R'`. One direction is the
conservativity reduction `Dualizing.isIso_derivedHomBaseChange_app_of_restrictScalars`, the
opening move of the proof of Stacks 0E2A; the other holds because a functor carries isomorphisms
to isomorphisms. The equivalence is the form in which Stacks 0E2A, itself an "if and only if",
uses the reduction. -/
theorem isIso_derivedHomBaseChange_app_iff_restrictScalars
    {R : Type uR} {A : Type uA} {R' : Type uRp} [CommRing R] [CommRing A] [CommRing R']
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
    (K : DerivedCategory (ModuleCat.{max v uR uA uRp} R)) :
    IsIso ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory.map
      ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
        baseChangeA comparisonA isLeftDerivedA).app K)) ↔
    IsIso ((derivedHomBaseChange.{uR, uA, uRp, v} hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA).app K) :=
  ⟨isIso_derivedHomBaseChange_app_of_restrictScalars hTor baseChangeR comparisonR isLeftDerivedR
      baseChangeA comparisonA isLeftDerivedA K,
    fun h ↦ have := h; inferInstance⟩

/-- The internal-Hom bifunctor of the fixed tensor--Hom adjunction `derivedHomAdjunctionOverRing`
of Stacks 0A63 *is* the universe-transported bifunctor
  `Stacks.DerivedHom.ScalarTransportedInternalHom.hom` with
which the derived-Hom base-change map of Stacks 0E1X and the change-of-rings isomorphism of
Stacks 0E1W are stated: both are the transport along one and the same restriction of scalars
`ULift.ringEquiv` of the K-flat/K-injective construction over `ULift R`. So the two vocabularies
for derived internal Hom in an independently chosen module universe need no comparison map. -/
theorem derivedHomAdjunctionOverRing_hom_eq (R : Type uR) [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max uR v} R)] :
    (StacksDraft.DerivedHom.derivedHomAdjunctionOverRing.{uR, v, w} R).hom =
      Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{uR, v, w} R :=
  rfl

end Dualizing

end
