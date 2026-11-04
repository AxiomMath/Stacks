module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality

/-!
# Base change for derived Hom (Stacks chapter Dualizing Complexes)

Let `R → A` and `R → R'` be ring maps which are Tor-independent, so that `A ⊗_R R'` computes
the derived tensor product and the square
`R → A`, `R → R'`, `A → A ⊗_R A'`, `R' → A ⊗_R R'` is cocartesian in the derived sense. Then
there is a canonical base-change morphism
`RHom_R(A, K) ⊗ᴸ_A (A ⊗_R R') ⟶ RHom_{R'}(A ⊗_R R', K ⊗ᴸ_R R')`,
natural in the object `K` of `D(R)`.

The morphism is the adjoint transpose, for the derived restriction/Hom adjunction over
`R' → A ⊗_R R'`, of the derived base change along `R → R'` of the evaluation counit
`Res_A^R RHom_R(A, K) ⟶ K`. That characterization is recorded as
`Dualizing.derivedHomBaseChange_eq`, and it is what makes the construction canonical: no
choice of adjunction unit or counit enters, only the ones produced by the universal property
of the derived functors.

## Main definitions

* `Dualizing.derivedHomComparison` — the comparison from coextension on complexes to its total
  right derived functor.
* `Dualizing.derivedHomAdjunction` — the derived restriction/Hom adjunction, normalized so
  that its counit is the Kan-extension lift of ordinary evaluation.
* `Dualizing.restrictionBaseChangeIso` — the restriction/base-change identification supplied by
  Tor independence.
* `Dualizing.derivedHomBaseChange` — the base-change morphism.

## Main results

* `Dualizing.derivedHomAdjunction_counit_app` — on complexes the derived counit is induced by
  the ordinary evaluation counit.
* `Dualizing.derivedHomBaseChange_eq` — the base-change map is the mate of the derived tensor
  of the counit for derived Hom.

## Implementation notes

Unbounded derived extension of scalars is not packaged in Mathlib, so the two derived extension
functors and the comparison maps exhibiting their universal properties are taken as arguments
here, which is what keeps the three rings and the module size in independent universes. The
library's own construction, `StacksDraft.PseudoCoherence.extendScalarsDerived`, does exist, but
only for rings and modules in a single universe; the instantiation of the map below at it is
`Dualizing.derivedHomBaseChangeCanonical`, in
`StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChangeCanonical`. Presenting the
base-change morphisms as a natural transformation records their functoriality in `K`.

The three rings and the module size carry independent universe parameters. The derived Hom
functor used here is `Dualizing.derivedHom` of Tag 0A70, whose universe parameters are already
independent; its adjunction is obtained from `ModuleCat.restrictCoextendScalarsAdj` through the
canonical comparison with underived coextension, using only the propositional adjointness
instances supplied by `Dualizing.restrictScalarsDerived_adj_derivedHom`.

The pushout ring is represented by `TensorProduct R A R'`, with its two canonical inclusions as
structure maps, and the restriction/base-change isomorphism comes from the canonical comparison
of Stacks Project, Tag 0661.

## References

* [Stacks Project, Tag 0E29](https://stacks.math.columbia.edu/tag/0E29)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor
open scoped ChangeOfRings

attribute [local instance] HasDerivedCategory.standard

universe uR uA uRp uS uT v w x y z

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

/-- Coextension of scalars along a ring map is an additive functor. -/
local instance {S : Type uS} {T : Type uT} [CommRing S] [CommRing T] (f : S →+* T) :
    (ModuleCat.coextendScalars.{uS, uT, w} f).Additive where
  map_add := by intros; ext; rfl

/-- The comparison from coextension on complexes to its total right derived functor. -/
noncomputable def derivedHomComparison
    {A : Type uS} {B : Type uT} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.coextendScalars.{uS, uT, max v uS uT} f).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ derivedHom.{uS, v, uT} f := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{uS, v, uT} f
  dsimp [derivedHom]
  exact Functor.totalRightDerivedUnit _ _ _

/-- The derived restriction–Hom adjunction induced by the ordinary scalar adjunction, whose
unit and counit are the canonical Kan-extension lifts of the ordinary unit and evaluation
counit. -/
@[no_expose]
noncomputable def derivedHomAdjunction
    {A : Type uS} {B : Type uT} [CommRing A] [CommRing B] (f : A →+* B) :
    (ModuleCat.restrictScalars.{max v uS uT} f).mapDerivedCategory ⊣
      derivedHom.{uS, v, uT} f := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{uS, v, uT} f
  let G := ModuleCat.restrictScalars.{max v uS uT} f
  let F := ModuleCat.coextendScalars.{uS, uT, max v uS uT} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v uS uT} A) (.up ℤ)
  let W' := HomotopyCategory.quasiIso (ModuleCat.{max v uS uT} B) (.up ℤ)
  let α := G.mapDerivedCategoryFactorsh.hom
  let β := derivedHomComparison.{uS, uT, v} f
  have : (derivedHom.{uS, v, uT} f).IsRightDerivedFunctor β W := by
    dsimp [derivedHom, β, derivedHomComparison, W]
    infer_instance
  have : G.mapDerivedCategory.IsLeftDerivedFunctor α W' :=
    Functor.isLeftDerivedFunctor_of_inverts W' _ G.mapDerivedCategoryFactorsh
  let a := (restrictScalarsDerived_adj_derivedHom.{uS, v, uT} f).some
  have : G.mapDerivedCategory.IsLeftAdjoint := a.isLeftAdjoint
  have : (derivedHom.{uS, v, uT} f).IsRightAdjoint := a.isRightAdjoint
  exact (homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{max v uS uT} f)
    (.up ℤ)).derived W' W α β

/-- On complexes the derived counit is induced by the ordinary evaluation counit. -/
theorem derivedHomAdjunction_counit_app
    {A : Type uS} {B : Type uT} [CommRing A] [CommRing B] (f : A →+* B)
    (K : HomotopyCategory (ModuleCat.{max v uS uT} A) (.up ℤ)) :
    (ModuleCat.restrictScalars.{max v uS uT} f).mapDerivedCategory.map
        ((derivedHomComparison.{uS, uT, v} f).app
          K) ≫
      (derivedHomAdjunction.{uS, uT, v} f).counit.app (DerivedCategory.Qh.obj K) =
    (ModuleCat.restrictScalars.{max v uS uT} f).mapDerivedCategoryFactorsh.hom.app
        (((ModuleCat.coextendScalars.{uS, uT, max v uS uT} f).mapHomotopyCategory
          (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{max v uS uT} f)
          (.up ℤ)).counit.app K) := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{uS, v, uT} f
  let G := ModuleCat.restrictScalars.{max v uS uT} f
  let F := ModuleCat.coextendScalars.{uS, uT, max v uS uT} f
  let W := HomotopyCategory.quasiIso (ModuleCat.{max v uS uT} A) (.up ℤ)
  let W' := HomotopyCategory.quasiIso (ModuleCat.{max v uS uT} B) (.up ℤ)
  let α := G.mapDerivedCategoryFactorsh.hom
  let β := derivedHomComparison.{uS, uT, v} f
  have : (derivedHom.{uS, v, uT} f).IsRightDerivedFunctor β W := by
    dsimp [derivedHom, β, derivedHomComparison, W]
    infer_instance
  have : G.mapDerivedCategory.IsLeftDerivedFunctor α W' :=
    Functor.isLeftDerivedFunctor_of_inverts W' _ G.mapDerivedCategoryFactorsh
  let a := (restrictScalarsDerived_adj_derivedHom.{uS, v, uT} f).some
  have : G.mapDerivedCategory.IsLeftAdjoint := a.isLeftAdjoint
  have : (derivedHom.{uS, v, uT} f).IsRightAdjoint := a.isRightAdjoint
  exact (homotopyAdjunction (ModuleCat.restrictCoextendScalarsAdj.{max v uS uT} f)
    (.up ℤ)).derivedε_fac_app W α β K

/-- The identification, supplied by Tor independence, of derived base change along
`R' → A ⊗_R R'` of `RHom_R(A, -)` with derived base change along `R → R'` of its
restriction to `D(R)`. -/
noncomputable def restrictionBaseChangeIso
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
    derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA ⋙
        (ModuleCat.restrictScalars
          (Algebra.TensorProduct.includeRight :
            R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory ≅
      derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙
        (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory ⋙ baseChangeR := by
  let f := algebraMap R A
  let g := algebraMap R R'
  let h := algebraMap A (TensorProduct R A R')
  let i := algebraMap R' (TensorProduct R A R')
  let sq : h.comp f = i.comp g :=
    (IsScalarTower.algebraMap_eq R A (TensorProduct R A R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (TensorProduct R A R'))
  have := isLeftDerivedR
  have := isLeftDerivedA
  let c := RingTheory.TorIndependence.derivedBaseChangeComparison f g h i sq
    baseChangeR baseChangeA comparisonR comparisonA
  have hc : IsIso c.2.1 :=
    RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent
      hTor baseChangeR baseChangeA comparisonR comparisonA
  exact (Functor.associator _ _ _) ≪≫
    isoWhiskerLeft (derivedHom.{uR, max v uRp, uA} f) (asIso c.2.1).symm ≪≫
      (Functor.associator _ _ _).symm

/-- The canonical base-change map
`RHom_R(A, -) ⊗ᴸ_A (A ⊗_R R') ⟶ RHom_{R'}(A ⊗_R R', - ⊗ᴸ_R R')`,
functorial in the object of `D(R)`. -/
@[stacks 0E29]
noncomputable def derivedHomBaseChange
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
    :
    derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA ⟶
      baseChangeR ⋙ derivedHom.{uRp, max v uR, max uA uRp}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom :=
  let adjRA := derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)
  let adjR'A' := derivedHomAdjunction.{uRp, max uA uRp, max v uR}
    (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R A R').toRingHom
  let e := restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR
    baseChangeA comparisonA isLeftDerivedA
  { app := fun K ↦ adjR'A'.homEquiv _ _
      (e.hom.app K ≫ baseChangeR.map (adjRA.counit.app K))
    naturality := by
      intro K L f
      apply adjR'A'.homEquiv_naturality_left_square
      change
        (derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙ baseChangeA ⋙
            (ModuleCat.restrictScalars
              (Algebra.TensorProduct.includeRight :
                R' →ₐ[R] TensorProduct R A R').toRingHom).mapDerivedCategory).map f ≫
            e.hom.app L ≫ baseChangeR.map (adjRA.counit.app L) = _
      rw [e.hom.naturality_assoc]
      change e.hom.app K ≫
          baseChangeR.map
            ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
              ((derivedHom.{uR, max v uRp, uA} (algebraMap R A)).map f)) ≫
            baseChangeR.map (adjRA.counit.app L) = _
      rw [← baseChangeR.map_comp]
      change e.hom.app K ≫
        baseChangeR.map
          ((derivedHom.{uR, max v uRp, uA} (algebraMap R A) ⋙
            (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory).map f ≫
              adjRA.counit.app L) = _
      rw [adjRA.counit.naturality]
      simp }

/-- The defining characterization of the base-change map: after the restriction/base-change
identification, its adjoint transpose is the derived extension of the counit
`Res_A^R RHom_R(A, K) ⟶ K` along `R → R'`. -/
theorem derivedHomBaseChange_eq
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
    (derivedHomBaseChange hTor baseChangeR comparisonR isLeftDerivedR baseChangeA comparisonA
        isLeftDerivedA).app K =
      (derivedHomAdjunction.{uRp, max uA uRp, max v uR}
        (Algebra.TensorProduct.includeRight :
          R' →ₐ[R] TensorProduct R A R').toRingHom).homEquiv _ _
        ((restrictionBaseChangeIso hTor baseChangeR comparisonR isLeftDerivedR
          baseChangeA comparisonA isLeftDerivedA).hom.app K ≫
            baseChangeR.map
              ((derivedHomAdjunction.{uR, uA, max v uRp} (algebraMap R A)).counit.app K)) :=
  rfl

end Dualizing
