module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomComplexExtGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 09LC is natural under a differential graded functor

Let `R` be a commutative ring, let `(A, d)` be a differential graded `R`-algebra, let `B` be an
`R`-linear preadditive category and let `F : Mod^dg_(A, d) ⥤ Comp^dg(B)` be a functor of
differential graded categories over `R`. Acting on
homogeneous morphisms, `F` gives a map of Hom complexes

`Hom^•_{(A, d)}(M, N) ⟶ Hom^•(F M, F N)`,

whose target is Mathlib's `CochainComplex.HomComplex`. **Tag 09LC** identifies the degree-`n`
cohomology of each side with the morphisms of the respective homotopy categories into the `n`-th
shift of the target — on the left by
`DifferentialGradedModule.General.homComplexHomologyEquiv`, on the right by Mathlib's
`CochainComplex.HomComplex.homologyAddEquiv` followed by
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv`. This file proves that the map of Hom
complexes is **compatible with those identifications**: on cohomology it is the functor `F`
induces on homotopy categories.

## Main definitions

* `DifferentialGradedModule.dgFunctorHomComplexMap`: the map of Hom complexes induced by `F`,
  with its target written as Mathlib's `CochainComplex.HomComplex`.
* `DifferentialGradedModule.dgFunctorCocycle`: the image under `F` of a closed degree-`n`
  homogeneous morphism, as a degree-`n` cocycle of the target Hom complex.

## Main results

* `DifferentialGradedModule.equivHomShift_symm_dgFunctorCocycle`: at the level of complexes, the
  cocycle `F f` read as a morphism `F M ⟶ (F N)[n]` is the image under `F` of the homomorphism
  `M ⟶ N[n]` that `f` is, followed by the comparison `F(N[n]) ≅ F(N)[n]`.
* `DifferentialGradedModule.homologyAddEquiv_homologyMap_mk`: the degree-`n` cohomology of the
  map of Hom complexes sends the class of a closed degree-`n` homogeneous morphism `f` to the
  cohomology class of the cocycle `F f`.
* `DifferentialGradedModule.homAddEquiv_homologyAddEquiv_homologyMap`: **Tag 09LC, naturality
  under a differential graded functor.** The two previous statements combined: read through the
  identifications of Tag 09LC on both sides, the degree-`n` cohomology of the map of Hom
  complexes is the action of `F` on homotopy-category morphisms, followed by the comparison
  `F(N[n]) ≅ F(N)[n]`.

## Implementation notes

*Why the shift comparison appears explicitly.* The target of Tag 09LC on the right-hand side is
`Hom_{K(B)}(F M, (F N)[n])` as Mathlib presents it, namely morphisms into
`(HomotopyCategory.quotient B _).obj ((F N)⟦n⟧)`, whereas the functor `F` induces on homotopy
categories takes `Hom_{K(A, d)}(M, N[n])` into morphisms whose target is the image of the
homotopy class of `N[n]`. The two are matched by the comparison
`DifferentialGradedModule.dgFunctorToComplexesShiftIso`, which is what the functor's commutation
with the translation is built from
(`DifferentialGradedModule.dgFunctorToComplexesCommShift`); writing that comparison out rather
than the commutation isomorphism of the homotopy-category functor keeps the statement free of
the transport between `(toHomotopyCategory A).obj (N[n])` and
`((toHomotopyCategory A).obj N)⟦n⟧`, which is an equality of objects and not a definitional one.

*How the two cohomology presentations are matched.* The left-hand side is presented by
`DifferentialGradedModule.General.homScHomologyEquiv`, Mathlib's explicit
`CategoryTheory.ShortComplex.abHomologyIso` of the short complex of the three degrees
`n - 1, n, n + 1`; the right-hand side by
`CochainComplex.HomComplex.leftHomologyData`, Mathlib's cocycles-modulo-coboundaries datum for
the short complex of the degrees `c.prev n, n, c.next n`. Both are
`CategoryTheory.ShortComplex.LeftHomologyData`, so the comparison is a
`CategoryTheory.ShortComplex.LeftHomologyMapData` for the morphism of short complexes that
mediates between the two choices of neighbouring degrees
(`DifferentialGradedModule.dgFunctorScMap`); that map data exists and is unique, so it does not
have to be constructed, and `DifferentialGradedModule.leftHomologyMapData_φK` identifies its
component on cocycles with the image under `F`, which is all the computation needs.

*The base ring is arbitrary.* The target is the `R`-linear differential graded category of
cochain complexes, `CochainComplex.dgCategoryLinear B R`, as in
`StacksFrontier.Algebra.DifferentialGraded.Module.DGFunctorToComplexes`; the one identity between
homogeneous morphisms used below is stated in its own section, where only the source occurs,
since at `R = ℤ` the `ℤ`-module structure carried by a differential graded module is not the one
instance synthesis finds.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09LV](https://stacks.math.columbia.edu/tag/09LV)
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.HomComplex

namespace DifferentialGradedModule

universe r u t v

section GradedIdentities

variable {R : Type r} [CommRing R] {A : DifferentialGradedAlgebra.{r, u} R}

/-- **A closed degree-`n` homogeneous morphism, read as a homomorphism into the shift and back.**
The homomorphism `M ⟶ N[n]` attached to a closed degree-`n` homogeneous morphism `f`, composed
with the degree-`n` homogeneous morphism `N[n] ⟶ N` given by the identity of the underlying
module, is `f` again.

This is stated over a general base ring `R`: at `R = ℤ`, which is the base ring of a
differential graded functor into cochain complexes, the `ℤ`-module structure carried by a
differential graded module is not the one instance synthesis finds, so an identity between
underlying linear maps cannot be introduced there. -/
theorem homogeneousMapFromShift_comp_homOfClosed
    {M N : DifferentialGradedModule.{r, u, t} A} {n : ℤ}
    (f : ↥(HomogeneousMap A M N n)) (hf : homogeneousMapDifferential A f = 0) :
    (dgCategory.{r, u, t} A).comp (add_zero n) (homogeneousMapFromShift N n)
        (cocycleOfHom A (General.homOfClosed A M N f hf)).1 = f := by
  apply Subtype.ext
  rw [dgCategory_comp_val, cocycleOfHom_val, General.homOfClosed_toFun]
  exact LinearMap.id_comp _

end GradedIdentities

variable {R : Type r} [CommRing R] {A : DifferentialGradedAlgebra.{r, u} R}
  {B : Type v} [Category.{t} B] [Preadditive B] [Linear R B]
  (F : DGCategory.DGFunctor (dgCategory.{r, u, t} A) (CochainComplex.dgCategoryLinear B R))

/-- **The map of Hom complexes induced by a differential graded functor**, with its target
written as Mathlib's `CochainComplex.HomComplex`: in each degree the action of `F` on
homogeneous morphisms, which is `DGCategory.DGFunctor.homComplexMap`, followed by the
identification `CochainComplex.dgCategoryHomComplexIso` of the Hom complex of the differential
graded category of cochain complexes with Mathlib's Hom complex. -/
def dgFunctorHomComplexMap (M N : DifferentialGradedModule.{r, u, t} A) :
    (dgCategory.{r, u, t} A).homComplex M N ⟶
      ((dgFunctorToComplexes F).obj M).HomComplex ((dgFunctorToComplexes F).obj N) :=
  F.homComplexMap M N ≫ (CochainComplex.dgCategoryHomComplexIso _ _).hom

/-- In degree `n` the map of Hom complexes is the action of `F` on degree-`n` homogeneous
morphisms. -/
theorem dgFunctorHomComplexMap_f (M N : DifferentialGradedModule.{r, u, t} A) (n : ℤ)
    (f : (dgCategory.{r, u, t} A).Hom M N n) :
    AddCommGrpCat.Hom.hom ((dgFunctorHomComplexMap F M N).f n) f = F.map f := rfl

/-- **The image under `F` of a closed degree-`n` homogeneous morphism**, as a degree-`n` cocycle
of the Hom complex of the image complexes: `F` commutes with the differential of the Hom
complexes, so it carries a closed homogeneous morphism to a cocycle. -/
def dgFunctorCocycle {M N : DifferentialGradedModule.{r, u, t} A} {n : ℤ}
    (f : ↥(HomogeneousMap A M N n)) (hf : homogeneousMapDifferential A f = 0) :
    Cocycle ((dgFunctorToComplexes F).obj M) ((dgFunctorToComplexes F).obj N) n :=
  Cocycle.mk (F.map f) (n + 1) rfl (by
    change (CochainComplex.dgCategoryLinear B R).d (F.map f) = 0
    rw [← F.map_d, show (dgCategory.{r, u, t} A).d f = 0 from hf, F.map_zero])

/-- **The image of a closed homogeneous morphism is the image of the attached homomorphism.** A
closed degree-`n` homogeneous morphism `f : M ⟶ N` is a homomorphism `M ⟶ N[n]` of differential
graded modules; the image under `F` of that homomorphism, followed by the comparison
`F(N[n]) ≅ F(N)[n]` of
`DifferentialGradedModule.dgFunctorToComplexesShiftIso`, is the morphism of complexes
`F M ⟶ (F N)[n]` that the cocycle `F f` is.

This is the statement at the level of complexes of which
`DifferentialGradedModule.homAddEquiv_homologyAddEquiv_homologyMap` is the reading on
cohomology. Both sides are compared componentwise, where each is the degree-`(i, i + n)`
component of `F f` because the two homogeneous morphisms composing to `f` are
`DifferentialGradedModule.homogeneousMapFromShift_comp_homOfClosed`. -/
theorem equivHomShift_symm_dgFunctorCocycle
    {M N : DifferentialGradedModule.{r, u, t} A} {n : ℤ}
    (f : ↥(HomogeneousMap A M N n)) (hf : homogeneousMapDifferential A f = 0) :
    Cocycle.equivHomShift.symm (dgFunctorCocycle F f hf) =
      (dgFunctorToComplexes F).map (General.homOfClosed A M N f hf) ≫
        (dgFunctorToComplexesShiftIso F N n).hom := by
  ext i
  rw [HomologicalComplex.comp_f, dgFunctorToComplexes_map_f,
    dgFunctorToComplexesShiftIso_hom_f,
    ← dgFunctor_map_comp_v F (add_zero n) (homogeneousMapFromShift N n)
      (cocycleOfHom A (General.homOfClosed A M N f hf)).1 i i (i + n) (add_zero i) rfl,
    homogeneousMapFromShift_comp_homOfClosed]
  simp [dgFunctorCocycle, Cocycle.equivHomShift_symm_apply, Cocycle.homOf_f,
    Cochain.rightShift_v, CochainComplex.shiftFunctorObjXIso]

/-! ### Tag 09LC under a differential graded functor, on cohomology -/

section Homology

variable (M N : DifferentialGradedModule.{r, u, t} A) (n : ℤ)

/-- The map on cocycles induced by `F`: a closed degree-`n` homogeneous morphism `M ⟶ N` goes to
the degree-`n` cocycle `F f` of the Hom complex of the image complexes. -/
def dgFunctorKerToCocycle :
    (General.homSc A M N n).abLeftHomologyData.K ⟶
      (CochainComplex.HomComplex.leftHomologyData ((dgFunctorToComplexes F).obj M)
        ((dgFunctorToComplexes F).obj N) n).K :=
  AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun f => dgFunctorCocycle F (General.scX₂ A M N n f.1)
      ((General.homSc_g_eq_zero_iff A M N n f.1).mp f.2))
    (fun f g => by
      apply Cocycle.ext
      exact F.map_add _ _))

/-- The morphism of short complexes whose homology map is the degree-`n` cohomology of the map of
Hom complexes, with the source read at the degrees `n - 1, n, n + 1`. -/
def dgFunctorScMap :
    (General.homComplex A M N).sc' (n - 1) n (n + 1) ⟶
      (((dgFunctorToComplexes F).obj M).HomComplex ((dgFunctorToComplexes F).obj N)).sc n :=
  ((General.homComplex A M N).isoSc' (n - 1) n (n + 1) (by simp) (by simp)).inv ≫
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{t} (ComplexShape.up ℤ) n).map
      (dgFunctorHomComplexMap F M N)

variable {M N n}

/-- The map on cocycles of the left homology map data of
`DifferentialGradedModule.dgFunctorScMap` is the image under `F`. -/
theorem leftHomologyMapData_φK
    (γ : ShortComplex.LeftHomologyMapData (dgFunctorScMap F M N n)
      (General.homSc A M N n).abLeftHomologyData
      (CochainComplex.HomComplex.leftHomologyData ((dgFunctorToComplexes F).obj M)
        ((dgFunctorToComplexes F).obj N) n)) :
    γ.φK = dgFunctorKerToCocycle F M N n := by
  rw [← cancel_mono (CochainComplex.HomComplex.leftHomologyData ((dgFunctorToComplexes F).obj M)
    ((dgFunctorToComplexes F).obj N) n).i, γ.commi]
  exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl)

/-- **Tag 09LC is natural under a differential graded functor**, on cohomology classes. The
degree-`n` cohomology of the map of Hom complexes induced by `F` sends the class of a closed
degree-`n` homogeneous morphism `f : M ⟶ N` to the class of the cocycle `F f`. -/
@[stacks 09LC "naturality of the cohomology of the Hom complex under a differential graded \
functor, on cohomology classes"]
theorem homologyAddEquiv_homologyMap_mk
    (f : ↥(AddCommGrpCat.Hom.hom (General.homSc A M N n).g).ker) :
    CochainComplex.HomComplex.homologyAddEquiv ((dgFunctorToComplexes F).obj M)
        ((dgFunctorToComplexes F).obj N) n
        (HomologicalComplex.homologyMap (dgFunctorHomComplexMap F M N) n
          ((General.homScHomologyEquiv A M N n).symm (QuotientAddGroup.mk f))) =
      CochainComplex.HomComplex.CohomologyClass.mk
        (dgFunctorCocycle F (General.scX₂ A M N n f.1)
          ((General.homSc_g_eq_zero_iff A M N n f.1).mp f.2)) := by
  set e := (General.homComplex A M N).isoSc' (n - 1) n (n + 1) (by simp) (by simp)
  set ψ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{t} (ComplexShape.up ℤ) n).map
    (dgFunctorHomComplexMap F M N)
  set α := (General.homScHomologyEquiv A M N n).symm (QuotientAddGroup.mk f) with hα
  have γ : ShortComplex.LeftHomologyMapData (dgFunctorScMap F M N n)
      (General.homSc A M N n).abLeftHomologyData
      (CochainComplex.HomComplex.leftHomologyData ((dgFunctorToComplexes F).obj M)
        ((dgFunctorToComplexes F).obj N) n) := default
  have hθ : ShortComplex.homologyMap (dgFunctorScMap F M N n) =
      ShortComplex.homologyMap e.inv ≫ ShortComplex.homologyMap ψ := by
    rw [dgFunctorScMap, ShortComplex.homologyMap_comp]
  have hid : ShortComplex.homologyMap e.hom ≫ ShortComplex.homologyMap e.inv = 𝟙 _ := by
    rw [← ShortComplex.homologyMap_comp, e.hom_inv_id, ShortComplex.homologyMap_id]
  have hinv : ShortComplex.homologyMap e.inv (ShortComplex.homologyMap e.hom α) = α :=
    (comp_apply (ShortComplex.homologyMap e.hom) (ShortComplex.homologyMap e.inv) α).symm.trans
      ((ConcreteCategory.congr_hom hid α).trans (id_apply α))
  have hξ : (General.homSc A M N n).abLeftHomologyData.homologyIso.hom
      (ShortComplex.homologyMap e.hom α) = QuotientAddGroup.mk f := by
    rw [hα]
    exact (General.homScHomologyEquiv A M N n).apply_symm_apply _
  have hmap : ShortComplex.homologyMap (dgFunctorScMap F M N n)
      (ShortComplex.homologyMap e.hom α) = ShortComplex.homologyMap ψ α := by
    rw [hθ]
    simp only [comp_apply]
    rw [hinv]
  have hcomm := ConcreteCategory.congr_hom γ.homologyMap_comm
    (ShortComplex.homologyMap e.hom α)
  simp only [comp_apply, hmap, hξ] at hcomm
  have hπ := ConcreteCategory.congr_hom γ.commπ f
  simp only [leftHomologyMapData_φK] at hπ
  exact hcomm.trans hπ

/-! ### Tag 09LC under a differential graded functor, on homotopy classes -/

/-- **Tag 09LC is natural under a differential graded functor**, read on homotopy classes. The
degree-`n` cohomology class of the Hom complex `Hom^•_{(A, d)}(M, N)` attached to a closed
degree-`n` homogeneous morphism `f` is the homotopy class of `f : M ⟶ N[n]`
(`DifferentialGradedModule.General.closedToHomotopy`); its image under the degree-`n` cohomology
of the map of Hom complexes induced by `F` is the homotopy class attached to the cocycle `F f`,
and that class is the image of `f : M ⟶ N[n]` under the functor `F` induces on homotopy
categories, followed by the comparison `F(N[n]) ≅ F(N)[n]` of
`DifferentialGradedModule.dgFunctorToComplexesShiftIso`. -/
@[stacks 09LC "naturality of the cohomology of the Hom complex under a differential graded \
functor"]
theorem homAddEquiv_homologyAddEquiv_homologyMap
    (f : ↥(AddCommGrpCat.Hom.hom (General.homSc A M N n).g).ker) :
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv
        (CochainComplex.HomComplex.homologyAddEquiv ((dgFunctorToComplexes F).obj M)
          ((dgFunctorToComplexes F).obj N) n
          (HomologicalComplex.homologyMap (dgFunctorHomComplexMap F M N) n
            ((General.homScHomologyEquiv A M N n).symm (QuotientAddGroup.mk f)))) =
      (dgFunctorToHomotopyCategory F).map (General.closedToHomotopy A M N n f) ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          (dgFunctorToComplexesShiftIso F N n).hom := by
  rw [homologyAddEquiv_homologyMap_mk,
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply,
    CochainComplex.HomComplex.CohomologyClass.toHom_mk,
    equivHomShift_symm_dgFunctorCocycle, Functor.map_comp,
    General.closedToHomotopy_apply, dgFunctorToHomotopyCategory_map]

end Homology

end DifferentialGradedModule

end
