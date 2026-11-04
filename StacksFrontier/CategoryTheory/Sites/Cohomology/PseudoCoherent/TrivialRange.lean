module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DerivedApproximationOnASlice
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# An object with no cohomology from a degree on is pseudo-coherent from that degree

Let `(C, O)` be a ringed site and let `E` be an object of `D(O)` whose cohomology sheaves vanish
in every degree `≥ m`. Then `E` is `m`-pseudo-coherent.

## Main results

* `IsStrictlyPerfect.zero_complex`: the zero complex of modules on a site is strictly perfect.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isZero_homology`: an object of `D(O)`
  whose cohomology vanishes in every degree `≥ m` is `m`-pseudo-coherent.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

universe u v w d

/-- The zero complex of modules on a site is strictly perfect. -/
public theorem IsStrictlyPerfect.zero_complex {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    IsStrictlyPerfect R (0 : CochainComplex (SheafOfModules.{w} R) ℤ) := by
  have hX (i : ℤ) : IsZero ((0 : CochainComplex (SheafOfModules.{w} R) ℤ).X i) :=
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i).map_isZero (isZero_zero _)
  refine ⟨Set.finite_empty.subset ?_, fun i =>
    IsDirectSummandOfFiniteFree.of_isZero_general R (hX i)⟩
  intro i hi
  simp only [Set.mem_ofPred_eq] at hi
  exact False.elim (hi (hX i))

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hSliceDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory

omit hSliceDer in
/-- An object `E` of `D(O)` whose cohomology vanishes in every degree `≥ m` is
`m`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_of_isZero_homology
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (hE : ∀ j : ℤ, m ≤ j →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).obj E)) :
    X.IsPseudoCoherentFrom E m := by
  set K := DerivedCategory.Q.objPreimage E with hK
  have e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have hKzero : ∀ j : ℤ, m ≤ j → IsZero (K.homology j) := fun j hj =>
    IsZero.of_iso
      (IsZero.of_iso (hE j hj)
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).mapIso e))
      ((DerivedCategory.homologyFunctorFactors
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).app K).symm
  refine ⟨K, fun U => ⟨⊤, by simp, fun V _ _ => ?_⟩, ⟨e⟩⟩
  have hsrc : ∀ j : ℤ, IsZero
      ((0 : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ).homology j) :=
    fun j => (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map_isZero (isZero_zero _)
  have htgt : ∀ j : ℤ, m ≤ j → IsZero ((X.restrictComplex K V).homology j) := fun j hj =>
    X.isZero_homology_restrictComplex_general V K j (hKzero j hj)
  refine ⟨0, IsStrictlyPerfect.zero_complex
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V), 0,
    fun j hj => (hsrc j).isIso (htgt j (by omega)) _, ?_⟩
  have := (hsrc m).isIso (htgt m le_rfl)
    (HomologicalComplex.homologyMap (0 : (0 : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) ⟶
        X.restrictComplex K V) m)
  infer_instance

end AlgebraicGeometry.RingedSite

end
