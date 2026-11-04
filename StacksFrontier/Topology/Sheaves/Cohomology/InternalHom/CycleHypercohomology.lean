module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafHypercohomologyOnASpace
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# A global section of the cycles with nonzero class makes hypercohomology nonzero

Let `H` be a complex of `𝒪_X`-modules and `ψ : 𝒪_X ⟶ Z^p(H)` a morphism into its degree-`p`
cycles whose class `ψ ≫ H.homologyπ p` in the cohomology sheaf `H^p(H)` is nonzero. Then the
hypercohomology group `H^p(X, Z)` is nonzero for every object `Z` of `D(𝒪_X)` isomorphic to the
class of `H`. The first three results hold over any abelian category with a derived category.

## Main results

* `StacksDraft.DerivedCategoryHomology.Q_map_ne_zero_of_homologyMap_ne_zero`: a chain map
  nonzero on some homology is nonzero in the derived category.
* `StacksDraft.DerivedCategoryHomology.homologyMap_mkHomFromSingle_ne_zero`: the chain map out of
  the single complex attached to a morphism into the cycles is nonzero on the degree-`p` homology
  as soon as the class of that morphism is nonzero.
* `StacksDraft.DerivedCategoryHomology.shiftedSingleHom_ne_zero`: the passage from a nonzero
  morphism out of the degree-`p` single object to a nonzero morphism out of the degree-`0` one
  into the `p`-th shift.
* `Stacks.SheafOfModules.not_isZero_homology_derivedModuleGlobalSections_of_cycleHom`: a
  global section of the degree-`p` cycles with nonzero class makes `H^p(X, Z)` nonzero, for any
  object `Z` of `D(𝒪_X)` isomorphic to the class of the complex.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0BQR](https://stacks.math.columbia.edu/tag/0BQR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.ModuleSections

universe u

namespace StacksDraft.DerivedCategoryHomology

section Generic

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **A chain map nonzero on one homology object is nonzero in the derived category.** -/
theorem Q_map_ne_zero_of_homologyMap_ne_zero {A B : CochainComplex C ℤ} (φ : A ⟶ B) (p : ℤ)
    (h : HomologicalComplex.homologyMap φ p ≠ 0) : DerivedCategory.Q.map φ ≠ 0 := by
  refine fun hQ ↦ h ?_
  have hn : (DerivedCategory.homologyFunctor C p).map (DerivedCategory.Q.map φ) ≫
      ((DerivedCategory.homologyFunctorFactors C p).app B).hom =
      ((DerivedCategory.homologyFunctorFactors C p).app A).hom ≫
        HomologicalComplex.homologyMap φ p :=
    (DerivedCategory.homologyFunctorFactors C p).hom.naturality φ
  rw [hQ, Functor.map_zero, zero_comp] at hn
  exact (cancel_epi ((DerivedCategory.homologyFunctorFactors C p).app A).hom).mp
    (hn.symm.trans comp_zero.symm)

omit [HasDerivedCategory C] in
/-- **A morphism into the cycles with nonzero class gives a chain map nonzero on homology.** For
`f : A ⟶ Z^p(H)` the chain map `(single A in degree p) ⟶ H` built from `f ≫ H.iCycles p` by
`CategoryTheory.HomologicalComplex.mkHomFromSingle` has degree-`p` homology map nonzero as soon
as `f ≫ H.homologyπ p ≠ 0`. -/
theorem homologyMap_mkHomFromSingle_ne_zero (H : CochainComplex C ℤ) (p : ℤ) {A : C}
    (f : A ⟶ H.cycles p) (hf : f ≫ H.homologyπ p ≠ 0)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel p k → (f ≫ H.iCycles p) ≫ H.d p k = 0) :
    HomologicalComplex.homologyMap
      (HomologicalComplex.mkHomFromSingle (f ≫ H.iCycles p) hφ) p ≠ 0 := by
  refine fun h ↦ hf ?_
  have hcyc : (HomologicalComplex.singleObjCyclesSelfIso (ComplexShape.up ℤ) p A).inv ≫
      HomologicalComplex.cyclesMap
        (HomologicalComplex.mkHomFromSingle (f ≫ H.iCycles p) hφ) p = f := by
    refine (cancel_mono (H.iCycles p)).mp ?_
    simp
  rw [← hcyc, Category.assoc, ← HomologicalComplex.homologyπ_naturality, h, comp_zero, comp_zero]

/-- **From the degree-`p` single object to the degree-`0` one.** For `ψ` a nonzero morphism out of
`(singleFunctor C p).obj A` the morphism `𝒪[0] ⟶ Z⟦p⟧` obtained by shifting it by `p` and
precomposing with `CategoryTheory.SingleFunctors.shiftIso` is nonzero. -/
theorem shiftedSingleHom_ne_zero {A : C} {Z : DerivedCategory C} (p : ℤ)
    (ψ : (DerivedCategory.singleFunctor C p).obj A ⟶ Z) (hψ : ψ ≠ 0) :
    (((DerivedCategory.singleFunctors C).shiftIso p 0 p (add_zero p)).app A).inv ≫
        (shiftFunctor (DerivedCategory C) p).map ψ ≠ 0 := by
  refine fun h ↦ hψ ?_
  rw [← Functor.map_eq_zero_iff (shiftFunctor (DerivedCategory C) p)]
  exact (cancel_epi
    ((((DerivedCategory.singleFunctors C).shiftIso p 0 p (add_zero p)).app A).inv)).mp
      (h.trans comp_zero.symm)

end Generic

end StacksDraft.DerivedCategoryHomology

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **A global section of the cycles whose class is nonzero makes hypercohomology nonzero.** Let
`H` be a complex of `𝒪_X`-modules, let `Z` be an object of `D(𝒪_X)` isomorphic to the class of
`H`, and let `ψ : 𝒪_X ⟶ Z^p(H)` be a global section of the degree-`p` cycles — a morphism out of
the unit — whose class `ψ ≫ H.homologyπ p` in the `p`-th cohomology sheaf is nonzero. Then
`H^p(X, Z) ≠ 0`. -/
theorem not_isZero_homology_derivedModuleGlobalSections_of_cycleHom
    (H : CochainComplex (StructureSheafModules Rc) ℤ) (p : ℤ)
    (ψ : _root_.SheafOfModules.unit (structureSheaf Rc) ⟶ H.cycles p)
    (hψ : ψ ≫ H.homologyπ p ≠ 0)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel p k → (ψ ≫ H.iCycles p) ≫ H.d p k = 0)
    (Z : DerivedCategory (StructureSheafModules Rc))
    (e : DerivedCategory.Q.obj H ≅ Z) :
    ¬ IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} p).obj
      ((derivedModuleGlobalSections (ringedSite Rc)).obj Z)) := by
  have hQ : DerivedCategory.Q.map
      (HomologicalComplex.mkHomFromSingle (ψ ≫ H.iCycles p) hφ) ≠ 0 :=
    StacksDraft.DerivedCategoryHomology.Q_map_ne_zero_of_homologyMap_ne_zero _ p
      (StacksDraft.DerivedCategoryHomology.homologyMap_mkHomFromSingle_ne_zero H p ψ hψ hφ)
  have hcomp : DerivedCategory.Q.map
      (HomologicalComplex.mkHomFromSingle (ψ ≫ H.iCycles p) hφ) ≫ e.hom ≠ 0 :=
    fun h ↦ hQ ((cancel_mono e.hom).mp (h.trans zero_comp.symm))
  exact not_isZero_homology_derivedModuleGlobalSections_of_ne_zero Rc Z p _
    (StacksDraft.DerivedCategoryHomology.shiftedSingleHom_ne_zero p _ hcomp)

end Stacks.SheafOfModules

end
