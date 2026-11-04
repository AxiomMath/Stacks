module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationCechClass
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.RealizationEdge

/-!
# The pullback of de Rham cohomology on classes of global cocycles

For a commutative square of schemes `f ≫ p = p' ≫ g`, the pullback
`f^* : H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')` of [Stacks, Tag 0FL6] sends the class of a global cocycle
of `Γ(X, Ω^•_{X/S})` to the class of its image under the canonical map of de Rham complexes.

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback_abelianGlobalClass`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open Stacks.Cech.Hypercohomology
open Stacks.Cohomology.Leray (sectionsFunctor)

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **The pullback of de Rham cohomology on classes of global cocycles** ([Stacks, Tag 0FL6]): for
a commutative square `f ≫ p = p' ≫ g`, the pullback `H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')` sends the
class of a global cocycle of `Γ(X, Ω^•_{X/S})` to the class of its image in
`Γ(X, f_*Ω^•_{X'/S'}) = Γ(X', Ω^•_{X'/S'})`. -/
theorem deRhamCohomologyPullback_abelianGlobalClass {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (i : ℤ)
    (s : ((sectionsFunctor X.toRingedSpace.carrier ⊤).mapCochainComplexPlus.obj
      (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras p)))).obj.cycles i) :
    (deRhamCohomologyPullback f p p' g hcomm i).hom
        (abelianGlobalClass (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
          (deRhamAlgebras p) (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (deRhamAlgebras p))) i s) =
      abelianGlobalClass (AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlus
          (deRhamAlgebras p') (AlgebraicGeometry.SheafOfModules.deRhamDifferential
            (deRhamAlgebras p'))) i
        (HomologicalComplex.cyclesMap
          ((sectionsFunctor X.toRingedSpace.carrier ⊤).mapCochainComplexPlus.map
            (deRhamAbelianPushforwardMapPlus f p p' g hcomm)).hom i s) :=
  (deRhamCohomologyPullback_apply f p p' g hcomm i _).trans
    ((congrArg _ (abelianGlobalClass_naturality _ i s)).trans
      (abelianGlobalClass_pushforwardPullback f _ i _))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.SheafOfModules

open Stacks.Cech.Hypercohomology TopologicalSpace
open Stacks.Cohomology.Leray (sectionsFunctor)

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The comparison of the two realizations on classes of global cocycles**: the class of a
global cocycle of the de Rham complex of abelian sheaves is carried to `realizationUnbounded` of
the class of the same cocycle of the underlying complex of the de Rham complex of modules. -/
theorem deRhamCohomologyAbelianIsoDeRhamCohomology_abelianGlobalClass (n : ℤ)
    (sA : ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.obj
      (deRhamAbelianComplexPlus B D)).obj.cycles n) :
    (deRhamCohomologyAbelianIsoDeRhamCohomology B D n).hom.hom
        (abelianGlobalClass (deRhamAbelianComplexPlus B D) n sA) =
      (realizationUnbounded (baseRingedSpace A) (deRhamComplexPlus (X := X) B D) n).hom.hom
        (abelianGlobalClass _ n (HomologicalComplex.cyclesMap
          ((sectionsFunctor X.carrier ⊤).mapCochainComplexPlus.map
            (deRhamAbelianComplexPlusIso B D).hom).hom n sA)) := by
  rw [deRhamCohomologyAbelianIsoDeRhamCohomology_eq]
  exact congrArg
    (realizationUnbounded (baseRingedSpace A) (deRhamComplexPlus (X := X) B D) n).hom.hom
    (abelianGlobalClass_naturality (deRhamAbelianComplexPlusIso B D).hom n sA)

end AlgebraicGeometry.SheafOfModules

end
