module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections
public import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSlicedSituation
public import StacksFrontier.Homology.DerivedComplete.PrincipalRecurrence
public import StacksFrontier.Homology.DerivedComplete.PseudoCoherentComplete

/-!
# Derived completeness read off the cohomology objects

Derived completeness of an object of a derived category at a ring element `f` is the assertion
that the endomorphism `1 - f` of its countable product is an isomorphism. Since that
endomorphism is built out of a shift and a scalar, it is an isomorphism exactly when it is so
on every cohomology object. Hence a complex of modules is derived complete at `f` precisely
when each of its cohomology modules, regarded as a complex concentrated in degree zero, is.

The second part of the file transports this across an exact additive functor: a cohomology
object of the image of a complex is the image of the cohomology object, so derived completeness
of the image of a complex is tested on the images of its cohomology objects.

On a ringed site whose topology has enough weakly contractible objects, derived completeness of
a complex of sheaves of modules along a sheaf of ideals is tested on derived sections over the
weakly contractible objects, where the criterion above applies; so there too derived
completeness is read off the cohomology sheaves.

## Main results

* `DerivedCompleteRecurrence.isDerivedCompleteAt_iff_homology`: a complex of modules is derived
  complete at `f` exactly when all of its cohomology modules are.
* `DerivedCompleteRecurrence.homologyMapDerivedCategoryObjIso`: an exact additive functor
  commutes with taking a cohomology object in the derived category.
* `DerivedCompleteRecurrence.isDerivedCompleteAt_mapDerivedCategory_iff`: the criterion for the
  image of a complex under an exact additive functor to the modules over a ring.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_iff_homology`: on a site with enough weakly
  contractible objects, a complex of sheaves of modules is derived complete along a sheaf of
  ideals exactly when all of its cohomology sheaves are.

## Implementation notes

`homologyMapDerivedCategoryObjIso` is proved by choosing a complex representing the object,
which is why it is stated as an isomorphism at each object rather than as a natural
isomorphism of functors: the representative is not functorial.

## References

* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace DerivedCompleteRecurrence

/-- A complex of modules is derived complete at `f` exactly when each of its cohomology
modules, placed in degree zero, is derived complete at `f`. -/
theorem isDerivedCompleteAt_iff_homology
    {A : Type u} [CommRing A]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory (ModuleCat.{u} A)) (f : A) :
    IsDerivedCompleteAt K f ↔
      ∀ p : ℤ, IsDerivedCompleteAt
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj K)) f := by
  rw [isDerivedCompleteAt_iff_isIso, DerivedCategory.isIso_iff]
  refine forall_congr' fun p => ?_
  rw [isIso_homology_map_oneSubSmulShift_iff A K f p,
    isDerivedCompleteAt_single_iff_isIso_oneSubSmulShift]

/-- An exact additive functor commutes with taking the degree `p` cohomology object of an
object of the derived category. -/
def homologyMapDerivedCategoryObjIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory C) (p : ℤ) :
    (DerivedCategory.homologyFunctor D p).obj (F.mapDerivedCategory.obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C p).obj K) := by
  let P := DerivedCategory.Q.objPreimage K
  let e : DerivedCategory.Q.obj P ≅ K := DerivedCategory.Q.objObjPreimageIso K
  exact (DerivedCategory.homologyFunctor D p).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor D p).mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
    (DerivedCategory.homologyFunctorFactors D p).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≪≫
    (P.sc p).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C p).app P).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C p).mapIso e)

/-- The image of a complex under an exact additive functor to modules over a ring is derived
complete at `f` exactly when the images of all of its cohomology objects are. -/
theorem isDerivedCompleteAt_mapDerivedCategory_iff
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {A : Type u} [CommRing A]
    (F : C ⥤ ModuleCat.{u} A) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A))]
    (K : DerivedCategory C) (f : A) :
    IsDerivedCompleteAt (F.mapDerivedCategory.obj K) f ↔
      ∀ p : ℤ, IsDerivedCompleteAt
        (F.mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor C 0).obj
            ((DerivedCategory.homologyFunctor C p).obj K))) f := by
  rw [isDerivedCompleteAt_iff_homology]
  refine forall_congr' fun p => ?_
  let eH := homologyMapDerivedCategoryObjIso F K p
  let eS := (F.mapDerivedCategorySingleFunctor 0).app
    ((DerivedCategory.homologyFunctor C p).obj K)
  exact (isDerivedCompleteAt_iff_of_iso
    ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso eH) f).trans
      (isDerivedCompleteAt_iff_of_iso eS f).symm

end DerivedCompleteRecurrence

namespace AlgebraicGeometry.RingedSite

/-- A complex is derived complete precisely when each cohomology sheaf is. -/
@[stacks 099Q "cohomology_criterion"]
theorem isDerivedComplete_iff_homology_of_slicedObjectsSituation
    (X : RingedSite.{u, v, max u v})
    [HasSheafify X.J AddCommGrpCat.{max u v}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hJ : Stacks.WeaklyContractible.SlicedObjectsSituation.{w, v, u, max u v} X.C X.J)
    (K : DerivedCategory (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I K ↔
      ∀ p : ℤ, AlgebraicGeometry.RingedSite.IsDerivedComplete X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p).obj K)) := by
  have hKp (p : ℤ) :=
    isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X hJ I
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) p).obj K))
  simp_rw [isDerivedComplete_iff_derivedSections_of_slicedObjectsSituation X hJ I K, hKp]
  constructor
  · intro h p U hU
    obtain ⟨hAdd, hLim, hColim, hProd, hComplete⟩ := h U hU
    exact ⟨hAdd, hLim, hColim, hProd, fun f hf =>
      (DerivedCompleteRecurrence.isDerivedCompleteAt_mapDerivedCategory_iff _ K f).mp
        (hComplete f hf) p⟩
  · intro h U hU
    obtain ⟨hAdd, hLim, hColim, hProd, _⟩ := h 0 U hU
    exact ⟨hAdd, hLim, hColim, hProd, fun f hf =>
      (DerivedCompleteRecurrence.isDerivedCompleteAt_mapDerivedCategory_iff _ K f).mpr
        fun p => (h p U hU).2.2.2.2 f hf⟩

/-- A complex is derived complete precisely when each cohomology sheaf is. -/
@[stacks 099Q "cohomology_criterion"]
theorem isDerivedComplete_iff_homology
    (X : RingedSite.{u, v, max u v})
    [Small.{v} X.C] [HasSheafify X.J (Type v)]
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (hJ : X.J.HasEnoughWeaklyContractibleObjects)
    (K : DerivedCategory
      (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) :
    AlgebraicGeometry.RingedSite.IsDerivedComplete X I K ↔
      ∀ p : ℤ, AlgebraicGeometry.RingedSite.IsDerivedComplete X I
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) 0).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) p).obj K)) :=
  isDerivedComplete_iff_homology_of_slicedObjectsSituation X I
    (Stacks.WeaklyContractible.SlicedObjectsSituation.of
      ⟨fun U => X.J.IsWeaklyContractible U, fun {_} hU => hU, hJ⟩
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K

end AlgebraicGeometry.RingedSite

end
