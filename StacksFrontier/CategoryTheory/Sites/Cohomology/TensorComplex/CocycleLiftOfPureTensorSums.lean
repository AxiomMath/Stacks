module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.LiftOfPureTensorSums
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TotalComplexMono

/-!
# The lift of a decomposed section through a subcomplex is a cocycle

Let `(C, O)` be a ringed site, let `j : 𝒦 ⟶ ℳ` be a map of cochain complexes of `O`-modules which
is a monomorphism in every degree, and let every term of `𝒩` be flat. Let a section of
`Tot(ℳ ⊗ 𝒩)^0` over an object `W` be written as a finite sum of local pure tensors `∑ a ⊗ b`,
killed by the differential, and suppose each `a` lifts along `j`. Then the corresponding sum of
pure tensors `∑ y ⊗ b` in `Tot(𝒦 ⊗ 𝒩)^0` is killed by the differential of `Tot(𝒦 ⊗ 𝒩)`.

This is the step the source of the first assertion of Stacks 0FPV performs after shrinking to a
subcomplex: having factored the coevaluation's defining section through `Tot(𝒦 ⊗ 𝒩)`, the factored
section must still be a cocycle, because that is what makes it a map of complexes out of `O[0]`
and hence a morphism in the derived category. The factorisation itself is
`AlgebraicGeometry.RingedSite.tensorComplexMap_sum_tensorComplexSection_lift`; the containment
`Tot(𝒦 ⊗ 𝒩) ⊂ Tot(ℳ ⊗ 𝒩)` which makes the factored section unique, and therefore a cocycle, is
`Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general`.

## Main results

* `AlgebraicGeometry.RingedSite.d_sum_tensorComplexSection_lift_eq_zero`: the statement above.

## Implementation notes

The cocycle criterion itself is
`Stacks.Cohomology.LeftDualPerfect.d_eq_zero_of_mono_general`, which is stated for an arbitrary
small site and an arbitrary map of complexes monomorphic in degree one; nothing is restated here.
(The criterion also exists as `d_eq_zero_of_mono`, taking the section over an open of a space;
that form is not the one usable here.) This file supplies the two inputs that criterion asks for,
in the spelling `AlgebraicGeometry.RingedSite.tensorComplexSection` is written in: the degree-one
monomorphism, and the image of the lifted sum.

The two spellings of `Tot(j ⊗ 𝒩)` meet with no bridge. The lift lemma is stated at
`((tensorComplex O).map j).app 𝒩 ≫ ((tensorComplex O).obj ℳ).map (𝟙 𝒩)`, the composite that
`HomologicalComplex.mapBifunctorMap` is defined as, while the monomorphy lemma is stated at
`mapBifunctorMap` itself; the second factor of the composite is the identity by functoriality and
the first is `mapBifunctorMap j (𝟙 𝒩)` by `rfl`.

The degree is `0` because that is where the coevaluation lands: the criterion
`d_eq_zero_of_mono_general` is stated at the differential `d 0 1`, and `0` is the only degree in
which the consumer reads a section of the total tensor complex.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPD](https://stacks.math.columbia.edu/tag/0FPD)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] ringSheafSectionsCommRing presheafOfModulesMonoidalCategory
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable (X : RingedSite.{u, u, u}) [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {A B K :
  CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- `Tot(j ⊗ 𝒩)` in the spelling the lift lemma is stated at — the composite defining
`HomologicalComplex.mapBifunctorMap` — is `mapBifunctorMap j (𝟙 𝒩)`. -/
theorem tensorComplexMap_eq_mapBifunctorMap (j : K ⟶ A) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map j).app B ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (𝟙 B) =
      HomologicalComplex.mapBifunctorMap j (𝟙 B)
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) := by
  rw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact rfl

/-- **The lift of a decomposed cocycle section through a subcomplex is again a cocycle.** If
`j : K ⟶ A` is a monomorphism in every degree, every term of `B` is flat, each section `a p` of
`A` lifts along `j` to `y p`, and the sum of the pure tensors `a p ⊗ b p` is killed by the
differential of `Tot(A ⊗ B)`, then the sum of the pure tensors `y p ⊗ b p` is killed by the
differential of `Tot(K ⊗ B)`.

This is what makes the factorisation of the coevaluation through `Tot(K ⊗ B)` in the proof of
the first assertion of Stacks 0FPV a morphism of the derived category and not merely a section:
by `AlgebraicGeometry.RingedSite.unitComplexHomOfCocycle` a cocycle section in degree zero is a
map of complexes out of `O[0]`. -/
theorem d_sum_tensorComplexSection_lift_eq_zero (j : K ⟶ A) [∀ p, Mono (j.f p)]
    (hB : ∀ q, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (B.X q))
    {W : X.C} {κ : Type} [Fintype κ] (t r : κ → ℤ) (h : ∀ p, t p + r p = 0)
    (a : ∀ p, (A.X (t p)).val.obj (op W)) (b : ∀ p, (B.X (r p)).val.obj (op W))
    (y : ∀ p, (K.X (t p)).val.obj (op W))
    (hy : ∀ p, (j.f (t p)).val.app (op W) (y p) = a p)
    (ha : ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B).d 0 1).val.app
        (op W) (∑ p, tensorComplexSection X (t p) (r p) 0 (h p) (a p) (b p)) = 0) :
    ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj B).d 0 1).val.app (op W)
      (∑ p, tensorComplexSection X (t p) (r p) 0 (h p) (y p) (b p)) = 0 := by
  have hmono : Mono ((((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map j).app B ≫
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (𝟙 B)).f 1) := by
    rw [tensorComplexMap_eq_mapBifunctorMap X j]
    exact Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general (R := X.O) j hB 1
  refine Stacks.Cohomology.LeftDualPerfect.d_eq_zero_of_mono_general
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).map j).app B ≫
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (𝟙 B)) _ ?_
  rw [tensorComplexMap_sum_tensorComplexSection_lift X j 0 t r h a b y hy]
  exact ha

end AlgebraicGeometry.RingedSite

end
