module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DeRhamCohomologyFirstChernClass
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.PicardGroupAndFirstCohomology

/-!
# The de Rham first Chern class of the invertible sheaf of a divisor

Let `X` be a scheme and `Y ⊆ X` an effective Cartier divisor, with invertible sheaf
`𝒪_X(Y) = SheafHom(ℐ_Y, 𝒪_X)` and ideal sheaf `𝒪_X(-Y) = ℐ_Y`. This file proves

`c₁^{dR}(𝒪_X(Y)) = -c₁^{dR}(𝒪_X(-Y))`

for the de Rham first Chern class of Section 0FLE, relative to any morphism of sheaves of rings
into `𝒪_X`. It is the first equality in the proof of Stacks Tag 0FMX,
`c₁^{dR}(𝒪_X(Y)) ∪ b = -c₁^{dR}(𝒪_X(-Y)) ∪ b`: the evaluation pairing
`𝒪_X(Y) ⊗ 𝒪_X(-Y) ≅ 𝒪_X` makes the two Picard classes inverse to each other, and `c₁^{dR}` is a
homomorphism out of the Picard group.

## Main results

* `Stacks.Divisors.picardClassOf_invertibleSheaf_add_negativeTwist`:
  `[𝒪_X(Y)] + [𝒪_X(-Y)] = 0` in the Picard group in which the de Rham first Chern class is
  defined.
* `AlgebraicGeometry.SheafOfModules.deRhamFirstChernClassAbelianOf_invertibleSheaf`:
  `c₁^{dR}(𝒪_X(Y)) = -c₁^{dR}(𝒪_X(-Y))`.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyFirstChernClass_invertibleSheaf`: the same
  identity in the sheaf-of-modules realization `H^2_{dR}`, in which the cup product is taken.
* `AlgebraicGeometry.SheafOfModules.derivedSectionsBase_homology_map_comp_apply_eq_zero`: a class
  killed on hypercohomology by `f` is killed by `f ≫ g`.
* `AlgebraicGeometry.SheafOfModules.derivedSectionsBase_map_realization_eq_zero`: a class of the
  abelian-sheaf realization killed by a map of complexes of abelian sheaves is killed, in the
  sheaf-of-modules realization, by a map of complexes of modules whose underlying map it is. This
  is what turns the source's hypothesis `b|_Y = 0`, read in the abelian-sheaf realization in which
  the pullback of de Rham classes is defined, into the vanishing of `b` under the restriction of
  forms in the realization in which boundary maps of short exact sequences of complexes of
  modules act.

## Implementation notes

The library has `Stacks.Divisors.negativeTwistPicardClass_eq_neg`, the same identity in
`Stacks.SheafOfModules.PicardGroup`. The de Rham first Chern class is defined on the other Picard
group of the library, `Stacks.SheafOfModules.Picard.PicardGroup`, so the identity is proved here
again in that group, by the same evaluation pairing.

## References

* [Stacks Project, Tag 0FMX](https://stacks.math.columbia.edu/tag/0FMX)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}} (Y : X.IdealSheafData) [IsEffectiveCartierDivisor Y]

/-- The abelian group structure on the Picard group of a scheme in which the de Rham first Chern
class is defined, named for the reason given at
`AlgebraicGeometry.SheafOfModules.logPolesPicardGroupAddCommGroup`: instance search does not
find it through the universe constraints of the underlying ringed space. -/
local instance divisorPicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup X.toRingedSpace.sheaf.obj
      (structureSheaf X.toRingedSpace.sheaf).property) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.toRingedSpace.sheaf.obj
    (structureSheaf X.toRingedSpace.sheaf).property

/-- **`[𝒪_X(Y)] + [𝒪_X(-Y)] = 0`** in the Picard group of `X` in which the de Rham first Chern
class is defined: the evaluation pairing `𝒪_X(Y) ⊗ ℐ_Y ≅ 𝒪_X` trivializes the tensor product,
and addition of Picard classes is tensor product (Tag 01CX). -/
theorem picardClassOf_invertibleSheaf_add_negativeTwist :
    Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (structureSheaf X.toRingedSpace.sheaf).property (invertibleSheaf' Y) inferInstance +
      Stacks.SheafOfModules.Picard.classOf X.toRingedSpace.sheaf.obj
        (structureSheaf X.toRingedSpace.sheaf).property (negativeTwist' Y) inferInstance = 0 := by
  have hLN := Stacks.Cohomology.Generators.isInvertible_tensorSheaf_of_isInvertible
    X.toRingedSpace (invertibleSheaf' Y) (negativeTwist' Y) inferInstance inferInstance
  rw [Stacks.SheafOfModules.Picard.classOf_tensor _ _ _ _ _ _ hLN,
    ← Stacks.Cohomology.Generators.picardClassOf_unit_eq_zero X.toRingedSpace]
  have := isTensorInvertible_negativeTwist Y
  exact (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff _ _ _ _ _ _).2
    ⟨Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist' Y)⟩

end Stacks.Divisors

namespace AlgebraicGeometry.SheafOfModules

variable {X : Scheme.{u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}
  {φ : A ⟶ X.toRingedSpace.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B) (Y : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor Y]

/-- **`c₁^{dR}(𝒪_X(Y)) = -c₁^{dR}(𝒪_X(-Y))`** for an effective Cartier divisor `Y ⊆ X`: the de
Rham first Chern class of Tag 0FLE is a homomorphism out of the Picard group, in which the
classes of `𝒪_X(Y)` and of its ideal sheaf `𝒪_X(-Y)` are inverse to each other. This is the
first equality of the proof of Tag 0FMX. -/
theorem deRhamFirstChernClassAbelianOf_invertibleSheaf :
    deRhamFirstChernClassAbelianOf B D (Stacks.Divisors.invertibleSheaf' Y) inferInstance =
      -deRhamFirstChernClassAbelianOf B D (Stacks.Divisors.negativeTwist' Y) inferInstance := by
  let _ := Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.toRingedSpace.sheaf.obj
    (structureSheaf X.toRingedSpace.sheaf).property
  show deRhamFirstChernClassAbelian B D _ = -deRhamFirstChernClassAbelian B D _
  rw [← map_neg,
    eq_neg_of_add_eq_zero_left (Stacks.Divisors.picardClassOf_invertibleSheaf_add_negativeTwist Y)]

/-- **`c₁^{dR}(𝒪_X(Y)) = -c₁^{dR}(𝒪_X(-Y))` in the sheaf-of-modules realization** `H^2_{dR}`, the
realization in which the cup product of Section 0FM3 and the morphisms of Tag 0FU7 live. -/
theorem deRhamCohomologyFirstChernClass_invertibleSheaf :
    deRhamCohomologyFirstChernClass B D (Stacks.Divisors.invertibleSheaf' Y) inferInstance =
      -deRhamCohomologyFirstChernClass B D (Stacks.Divisors.negativeTwist' Y) inferInstance := by
  unfold deRhamCohomologyFirstChernClass
  rw [deRhamFirstChernClassAbelianOf_invertibleSheaf, map_neg]

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- A class killed on hypercohomology by a morphism `f` of the derived category of sheaves of
`A`-modules is killed by every composite `f ≫ g`. -/
theorem derivedSectionsBase_homology_map_comp_apply_eq_zero
    {Z W V : DerivedCategory (_root_.SheafOfModules.{u} (underlyingRingSheaf A))}
    (f : Z ⟶ W) (g : W ⟶ V) (m : ℤ)
    (b : (DerivedCategory.homologyFunctor (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤)))
      m).obj ((derivedSectionsBase A).obj Z))
    (h : ((DerivedCategory.homologyFunctor _ m).map ((derivedSectionsBase A).map f)).hom b = 0) :
    ((DerivedCategory.homologyFunctor _ m).map ((derivedSectionsBase A).map (f ≫ g))).hom b =
      0 := by
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply, h, map_zero]

/-! ### Vanishing across the two realizations of de Rham cohomology -/

/-- A de Rham class of the abelian-sheaf realization killed by a map `a` of bounded below
complexes of abelian sheaves out of the de Rham complex is killed, in the Čech model of the
sheaf-of-modules realization, by any map `r` of complexes of modules whose underlying map is `a`
up to an identification `e` of the targets. This is the naturality of the comparison of Tag
01F1. -/
theorem hypercohomologyMap_deRhamCohomologyAbelianIso_eq_zero
    {K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf A))}
    (r : deRhamComplexPlus (X := X) B D ⟶ K)
    {L : CochainComplex.Plus (AbelianSheaf X.carrier)}
    (e : L ≅ (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.obj K)
    (a : deRhamAbelianComplexPlus B D ⟶ L)
    (h : a ≫ e.hom = (deRhamAbelianComplexPlusIso B D).hom ≫
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.map r)
    (m : ℤ) (b : deRhamCohomologyAbelian B D m)
    (hb : ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
      ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map a))).hom b = 0) :
    (Stacks.Cech.Hypercohomology.hypercohomologyMap A r m).hom
        ((deRhamCohomologyAbelianIso B D m).hom.hom b) = 0 := by
  have hnat := Stacks.Cech.Hypercohomology.realizationIsoOfIso_naturality (baseRingedSpace A)
    (deRhamAbelianComplexPlusIso B D) e a r h m
  have h1 := ConcreteCategory.congr_hom hnat b
  have h2 : (Stacks.Cech.Hypercohomology.realizationIsoOfIso (baseRingedSpace A) e m).hom.hom
      (((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map a))).hom b) =
      (Stacks.Cech.Hypercohomology.hypercohomologyMap A r m).hom
        ((deRhamCohomologyAbelianIso B D m).hom.hom b) := h1
  rw [hb] at h2
  exact h2.symm.trans (AddMonoidHom.map_zero _)

/-- **A de Rham class of the abelian-sheaf realization killed by a map `a` of complexes of
abelian sheaves is killed, in the sheaf-of-modules realization `H^m_{dR}`, by any map `r` of
complexes of modules whose underlying map is `a`** up to an identification `e` of the targets.
The class is carried from one realization to the other by
`AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology`, the comparison of
Tag 01F1 followed by the identification of the Čech model of hypercohomology with derived global
sections. -/
theorem derivedSectionsBase_map_realization_eq_zero
    {K : CochainComplex.Plus (_root_.SheafOfModules.{u} (ringSheaf A))}
    (r : deRhamComplexPlus (X := X) B D ⟶ K)
    {L : CochainComplex.Plus (AbelianSheaf X.carrier)}
    (e : L ≅ (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.obj K)
    (a : deRhamAbelianComplexPlus B D ⟶ L)
    (h : a ≫ e.hom = (deRhamAbelianComplexPlusIso B D).hom ≫
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.map r)
    (m : ℤ) (b : deRhamCohomologyAbelian B D m)
    (hb : ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} m).map
      ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map a))).hom b = 0) :
    ((DerivedCategory.homologyFunctor _ m).map ((derivedSectionsBase A).map
      (DerivedCategory.Q.map (show deRhamComplexInt B D ⟶ K.obj from r.hom)))).hom
        ((deRhamCohomologyAbelianIsoDeRhamCohomology B D m).hom.hom b) = 0 := by
  have h0 := hypercohomologyMap_deRhamCohomologyAbelianIso_eq_zero B D r e a h m b hb
  have hnat := (Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso
    (baseRingedSpace A) ⊤).hom.naturality r
  have h3 := congrArg (fun g => (DerivedCategory.homologyFunctor _ m).map g) hnat
  simp only [Functor.map_comp] at h3
  have h4 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h3)
    ((deRhamCohomologyAbelianIso B D m).hom.hom b)
  have h5 : ((DerivedCategory.homologyFunctor _ m).map
      ((Stacks.Cech.Linear.derivedSectionsFunctor (baseRingedSpace A).carrier
        (structureSheafRing (baseRingedSpace A)) ⊤).map r)).hom
        ((deRhamCohomologyAbelianIso B D m).hom.hom b) = 0 := h0
  refine h4.symm.trans ?_
  show ((DerivedCategory.homologyFunctor _ m).map
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso
      (baseRingedSpace A) ⊤).hom.app K)).hom
      (((DerivedCategory.homologyFunctor _ m).map
        ((Stacks.Cech.Linear.derivedSectionsFunctor (baseRingedSpace A).carrier
          (structureSheafRing (baseRingedSpace A)) ⊤).map r)).hom
        ((deRhamCohomologyAbelianIso B D m).hom.hom b)) = 0
  rw [h5]
  exact map_zero _

end AlgebraicGeometry.SheafOfModules

end
