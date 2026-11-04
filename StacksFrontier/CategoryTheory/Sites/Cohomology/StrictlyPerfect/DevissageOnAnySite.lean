module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaPerfect

/-!
# The strictly perfect dévissage, in an arbitrary abelian category and on any ringed site

Let `A` be an abelian category, `U` an object of `A`, and `α : F ⟶ G` a natural transformation
between exact functors out of `D(A)`. If `α` is invertible at `U` placed in every degree, then it
is invertible at every shift of every bounded complex each of whose terms is a retract of a finite
direct sum of copies of `U`: such a complex is built from the `U[i]` by stupid truncations, the
extension step being the five lemma applied to the distinguished triangle of a short exact
sequence of complexes. For `A` the sheaves of modules on a ringed site `(C, O)` and `U = O`, these
complexes are the strictly perfect ones of [Stacks, Tag 08FL].

`Stacks.Cohomology.ProjectionFormulaPerfectDevissage.isIso_app_of_isStrictlyPerfect_of_singleUnit`
proves the sheaf statement for a *small* site. The statements here need no smallness: the abelian
form is about any abelian category with a derived category, and the sheaf form allows the objects
of the site to live in any universe and the morphisms in any other, which is what the small étale
site of an algebraic space needs (its objects form a `Type (u + 1)`, its morphisms and sections
live in `Type u`). The abelian form is also the one to apply where the abelian structure on the
sheaves of modules is not the one instance search finds on a general site.

## Main results

* `Stacks.Cohomology.StrictlyPerfectDevissage.isIso_app_shift_of_retract_biproduct`: the abelian
  dévissage.
* `Stacks.Cohomology.StrictlyPerfectDevissage.isIso_app_shift_of_isStrictlyPerfect`: the
  dévissage on any ringed site, from the structure sheaf placed in each degree to every shift of
  every strictly perfect complex.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.DerivedCategory.BoundedInduction

namespace Stacks.Cohomology.StrictlyPerfectDevissage

universe u v w

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **Invertibility at the degree shifts of an object spreads to bounded complexes of retracts of
its finite direct sums.** Let `A` be an abelian category, `U` an object of `A`, and `α : F ⟶ G` a
natural transformation between exact functors out of `D(A)`, invertible at `U` placed in every
degree. Then `α` is invertible at every shift of every bounded complex each of whose terms is a
retract of a finite direct sum of copies of `U`. -/
theorem isIso_app_shift_of_retract_biproduct {A : Type*} [Category* A] [Abelian A]
    [HasDerivedCategory A] {D : Type*} [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory A ⥤ D)
    (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated) (α : F ⟶ G)
    (U : A) (hunit : ∀ i : ℤ, IsIso (α.app ((DerivedCategory.singleFunctor A i).obj U)))
    (K : CochainComplex A ℤ) (hK : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i : ℤ, ∃ m : ℕ, Nonempty (Retract (K.X i) (⨁ fun _ : Fin m => U))) :
    ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj K)⟦n⟧)) := by
  let _ : F.CommShift ℤ := hFs
  let _ : G.CommShift ℤ := hGs
  let _ : F.IsTriangulated := hFt
  let _ : G.IsTriangulated := hGt
  have hshift : ∀ i n : ℤ,
      IsIso (α.app (((DerivedCategory.singleFunctor A i).obj U)⟦n⟧)) := fun i n =>
    (α.isIso_app_iff_of_iso (((DerivedCategory.singleFunctors A).shiftIso
      n (i - n) i (by omega)).app U)).mpr (hunit (i - n))
  apply property_of_bounded_complex (fun X => ∀ n : ℤ, IsIso (α.app (X⟦n⟧)))
  · intro X Y e h n
    exact (α.isIso_app_iff_of_iso ((shiftFunctor _ n).mapIso e)).mp (h n)
  · intro X hX n
    exact IsZero.isIso (F.map_isZero ((shiftFunctor _ n).map_isZero hX))
      (G.map_isZero ((shiftFunctor _ n).map_isZero hX)) _
  · intro S hS h₁ h₃
    exact isIso_app_middle_of_all_shifts F G α (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃
  · exact hK
  · intro i n
    let H := DerivedCategory.singleFunctor A i ⋙ shiftFunctor _ n
    let β := Functor.whiskerLeft H α
    obtain ⟨m, ⟨r⟩⟩ := hterm i
    exact isIso_app_of_splitRetract (H ⋙ F) (H ⋙ G) β r.i r.r r.retract
      (isIso_app_of_biproduct (H ⋙ F) (H ⋙ G) (fun _ : Fin m => U) β fun _ => hshift i n)

/-- **Invertibility at the structure sheaf in each degree spreads to strictly perfect complexes,
on any ringed site.** Let `(C, O)` be a ringed site, with no smallness condition on `C`, and let
`α : F ⟶ G` be a natural transformation between exact functors out of `D(O)`. If `α` is
invertible at the structure sheaf placed in every degree, then it is invertible at every shift of
every strictly perfect complex of `O`-modules. -/
theorem isIso_app_shift_of_isStrictlyPerfect {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{w})
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    {D : Type*} [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤ D)
    (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated) (α : F ⟶ G)
    (hunit : ∀ i : ℤ, IsIso (α.app ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O) K) :
    ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj K)⟦n⟧)) :=
  isIso_app_shift_of_retract_biproduct F G hFs hGs hFt hGt α _ hunit K hK.bounded fun i =>
    (Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct O
      (K.X i)).mp (hK.termDirectSummand i)

end Stacks.Cohomology.StrictlyPerfectDevissage

end
