module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnEquivalence

/-!
# Perfect objects under the relocalization of an algebraic space

Let `g : T ⟶ S` be a morphism of a big fppf site and `X` an algebraic space over `T`, with
lower-shriek extension `Λ X` over `S`. The derived equivalence `ρ : D(𝒪_X) ≌ D(𝒪_{Λ X})` of
`AlgebraicGeometry.Space.relocalizeDerivedFunctor` carries perfect objects to perfect objects and
reflects them: both `ρ` and its inverse are induced by direct images along the equivalence of
small étale sites, along which perfectness is invariant.

## Main results

* `AlgebraicGeometry.Space.isPerfect_relocalizeDerivedFunctor_obj_iff`: `K` is perfect if and only
  if `ρ K` is perfect.
* `AlgebraicGeometry.Space.isPerfect_relocalizeDerivedEquivalence_inverse_obj_iff`: the same for
  the inverse equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) {T S : Scheme.{u}} (hT : B.Contains T) (hS : B.Contains S)
  (g : B.obj hT ⟶ B.obj hS) (X : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B T hT X)

/-- The structure map of the reindexing of `𝒪_{Λ X}` back along the equivalence of small étale
sites is invertible. -/
instance isIso_reindexBackSharp_relocalize :
    IsIso (Stacks.SheafOfModules.reindexBackSharp (J' := SmallEtale.topology B T hT X)
      (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX)) := by
  have : IsIso ((sheafToPresheaf _ _).map (Stacks.SheafOfModules.reindexBackSharp
      (J' := SmallEtale.topology B T hT X) (SmallEtale.relocalize B hT hS g X hX)
      (relocalizeRingSheaf B hT hS g X hX))) :=
    inferInstanceAs (IsIso (Functor.whiskerRight
      (NatTrans.op (SmallEtale.relocalize B hT hS g X hX).counit) _))
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

/-- The direct image along the inverse of the equivalence of small étale sites carries perfect
objects of `D(𝒪_{Λ X})` to perfect objects of `D(𝒪_X)`. -/
theorem isPerfect_relocalizeModulesEquivalence_inverse_mapDerivedCategory_obj
    (L : DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX)))
    (hL : RingedSite.IsPerfect (smallEtaleRingedSite B S hS _
      (isAlgebraicSpace_relocalize' B hT hS g X hX)) L) :
    RingedSite.IsPerfect (smallEtaleRingedSite B T hT X hX)
      ((relocalizeModulesEquivalence B hT hS g X hX).inverse.mapDerivedCategory.obj L) :=
  RingedSite.isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (X := smallEtaleRingedSite B T hT X hX)
    (Y := smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX))
    (SmallEtale.relocalize B hT hS g X hX)
    (hfun := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).functor.IsContinuous
      (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)))
    (hinv := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).inverse.IsContinuous
      (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X)))
    (𝟙 _) (hρ := IsIso.id _) L hL

/-- The relocalization of derived categories carries perfect objects of `D(𝒪_X)` to perfect
objects of `D(𝒪_{Λ X})`. -/
theorem isPerfect_relocalizeDerivedFunctor_obj
    (K : DerivedCategory (Modules.{u, u} B T hT X hX))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B T hT X hX) K) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS _
        (isAlgebraicSpace_relocalize' B hT hS g X hX))
      ((relocalizeDerivedFunctor B hT hS g X hX).obj K) :=
  RingedSite.isPerfect_mapDerivedCategory_pushforwardEquivalenceOfIsIso
    (X := smallEtaleRingedSite B S hS _ (isAlgebraicSpace_relocalize' B hT hS g X hX))
    (Y := smallEtaleRingedSite B T hT X hX)
    (SmallEtale.relocalize B hT hS g X hX).symm
    (hfun := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).inverse.IsContinuous
      (SmallEtale.topology B S hS _) (SmallEtale.topology B T hT X)))
    (hinv := inferInstanceAs ((SmallEtale.relocalize B hT hS g X hX).functor.IsContinuous
      (SmallEtale.topology B T hT X) (SmallEtale.topology B S hS _)))
    (Stacks.SheafOfModules.reindexBackSharp (J' := SmallEtale.topology B T hT X)
      (SmallEtale.relocalize B hT hS g X hX) (relocalizeRingSheaf B hT hS g X hX))
    (hρ := isIso_reindexBackSharp_relocalize B hT hS g X hX) K hK

/-- **The relocalization of derived categories preserves and reflects perfect objects**: an object
`K` of `D(𝒪_X)` is perfect if and only if its image in `D(𝒪_{Λ X})` is perfect. -/
theorem isPerfect_relocalizeDerivedFunctor_obj_iff
    (K : DerivedCategory (Modules.{u, u} B T hT X hX)) :
    RingedSite.IsPerfect (smallEtaleRingedSite B S hS _
        (isAlgebraicSpace_relocalize' B hT hS g X hX))
        ((relocalizeDerivedFunctor B hT hS g X hX).obj K) ↔
      RingedSite.IsPerfect (smallEtaleRingedSite B T hT X hX) K := by
  let E := relocalizeModulesEquivalence B hT hS g X hX
  let L := DerivedCategory.Q.objPreimage K
  let eL : DerivedCategory.Q.obj L ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eρ : (relocalizeDerivedFunctor B hT hS g X hX).obj K ≅
      DerivedCategory.Q.obj ((E.functor.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    (relocalizeDerivedFunctor B hT hS g X hX).mapIso eL.symm ≪≫
      (relocalizeDerivedFunctorFactors B hT hS g X hX).app L
  refine ⟨fun h => ?_, isPerfect_relocalizeDerivedFunctor_obj B hT hS g X hX K⟩
  obtain ⟨P, hP, ⟨i⟩⟩ :=
    isPerfect_relocalizeModulesEquivalence_inverse_mapDerivedCategory_obj B hT hS g X hX _ h
  exact ⟨P, hP, ⟨i ≪≫ E.inverse.mapDerivedCategory.mapIso eρ ≪≫
    E.inverse.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((E.mapHomologicalComplex (ComplexShape.up ℤ)).unitIso.app L).symm ≪≫
    eL⟩⟩

/-- **The inverse of the relocalization of derived categories preserves and reflects perfect
objects.** -/
theorem isPerfect_relocalizeDerivedEquivalence_inverse_obj_iff
    (L : DerivedCategory (Modules.{u, u} B S hS ((OverShriek.relocalizePresheafFunctor g).obj X)
      (isAlgebraicSpace_relocalize' B hT hS g X hX))) :
    RingedSite.IsPerfect (smallEtaleRingedSite B T hT X hX)
        ((relocalizeDerivedEquivalence B hT hS g X hX).inverse.obj L) ↔
      RingedSite.IsPerfect (smallEtaleRingedSite B S hS _
        (isAlgebraicSpace_relocalize' B hT hS g X hX)) L :=
  (isPerfect_relocalizeDerivedFunctor_obj_iff B hT hS g X hX _).symm.trans
    ⟨fun ⟨P, hP, ⟨i⟩⟩ =>
      ⟨P, hP, ⟨i ≪≫ (relocalizeDerivedEquivalence B hT hS g X hX).counitIso.app L⟩⟩,
    fun ⟨P, hP, ⟨i⟩⟩ =>
      ⟨P, hP, ⟨i ≪≫ ((relocalizeDerivedEquivalence B hT hS g X hX).counitIso.app L).symm⟩⟩⟩

end AlgebraicGeometry.Space

end
