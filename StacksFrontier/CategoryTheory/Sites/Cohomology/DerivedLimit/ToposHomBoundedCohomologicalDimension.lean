module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.RightAdjointBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BoundednessOfToposHom

/-!
# Bounded cohomological dimension of `Rf_*` for a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi, let `A ⊂ Mod(O)` and
`A' ⊂ Mod(O')` be weak Serre subcategories, and let `N` be an integer such that

* `C, O, A` and `C', O', A'` both satisfy the assumption of the Olsson--Laszlo situation of
  Stacks 0D6R,
* `Rᵖf_*F` lies in `A'` for every `p ≥ 0` and every `F` of `A`, and
* `Rᵖf_*F = 0` for every `p > N` and every `F` of `A`.

Then for every `K` of `D_A(O)`, `Rf_*K` lies in `D_{A'}(O')`, and the canonical map
`Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` is an isomorphism for `j ≥ N - n`. This is Stacks 0D6U.

The morphism of ringed topoi is an `AlgebraicGeometry.RingedToposHom`, the two-field morphism of
Stacks 01D3, part (2): a morphism of the underlying topoi together with the structure map, with
no continuous functor between the underlying sites. Its derived direct image `Rf_*` is
`Stacks.Cohomology.DerivedPushforward.derivedPushforward` (Stacks 07A5).

## The argument

The statements of `RightAdjointBoundedCohomologicalDimension` are proved for an arbitrary
exact functor `R : D(O) ⥤ D(O')` which is a right adjoint and preserves boundedness below,
following the proof of Stacks 0D6U (through Stacks 0D6S, 0A07 and 0D6T). The derived direct
image of a morphism of ringed topoi is such a functor: it is right adjoint to `Lf^*` by
Stacks 07A6
(`Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom`), hence
exact, and it carries `D^{≥ n}(O)` into `D^{≥ n}(O')`
(`RingedToposHom.isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom`).

## Main results

* `Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_derivedPushforward_obj_of_ringedToposHom`:
  Stacks 0D6U, part (a).
* `Stacks.Cohomology.OlssonLaszlo.isIso_homology_derivedPushforward_truncGEπ_of_ringedToposHom`:
  Stacks 0D6U, part (b).

## Implementation notes

The standing hypotheses of the two Olsson--Laszlo situations are taken as loose data — a class
of objects, a cofinal system of coverings of each of them and an integer bound — exactly as in
`PushforwardBoundedCohomologicalDimension`, so they are the fields of Stacks 0D6R verbatim.
`Rᵖf_*F` is read as `Hᵖ(Rf_*(F[0]))`, the higher direct image of Stacks 072W. The three
universes of both ringed topoi are collapsed to one, as they are for the adjunction of
Stacks 07A6 on which the argument rests.

## References

* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace Stacks.Cohomology.OlssonLaszlo

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposHom X Y)
  (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [hA : A.IsWeakSerreClass] [hA' : A'.IsWeakSerreClass]
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A' F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          (𝒰.X i) p F))
  (N : ℤ)
  (himage : ∀ (p : ℕ) (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), A F →
    A' ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
  (hvanishImage : ∀ (p : ℕ), N < (p : ℤ) →
    ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
        ((Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))

include hA hA' basisCover vanishing basisCover' vanishing' himage hvanishImage in
/-- **Stacks Project, Tag 0D6U, part (a).** Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism
of ringed topoi and let `A ⊂ Mod(O)`, `A' ⊂ Mod(O')` be weak Serre subcategories such that
`C, O, A` and `C', O', A'` satisfy the assumption of the Olsson--Laszlo situation (Stacks 0D6R),
`Rᵖf_*F` lies in `A'` for `p ≥ 0` and `F` in `A`, and `Rᵖf_*F = 0` for `p > N` and `F` in `A`.
Then `Rf_*K` lies in `D_{A'}(O')` for every `K` in `D_A(O)`. -/
@[stacks 0D6U "part (a)"]
theorem derivedCategoryB_derivedPushforward_obj_of_ringedToposHom
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    DerivedCategoryB.derivedCategoryB A'
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).obj K) := by
  let := DerivedPushforward.derivedPushforwardCommShiftOfToposHomBoundednessOfToposHom f
  have := DerivedPushforward.isTriangulated_derivedPushforward_ofToposHom_boundednessOfToposHom f
  have := (Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom
    f).isRightAdjoint
  exact derivedCategoryB_map_obj_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension
    (A := A) (A' := A') (B := B) (basisCover := basisCover) (degreeBound := degreeBound)
    (coverings := coverings) (vanishing := vanishing) (B' := B') (basisCover' := basisCover')
    (degreeBound' := degreeBound') (coverings' := coverings') (vanishing' := vanishing')
    (R := Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f)
    (hGE := f.isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom) (N := N)
    (himage := himage) (hvanishImage := hvanishImage) K hK

include hA hA' basisCover vanishing basisCover' vanishing' himage hvanishImage in
/-- **Stacks Project, Tag 0D6U, part (b).** In the situation of part (a)
(`derivedCategoryB_derivedPushforward_obj_of_ringedToposHom`), for every `K` in `D_A(O)` the
canonical map `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` induced by the truncation `K ⟶ τ_{≥ -n}K` is an
isomorphism for every `j ≥ N - n`. -/
@[stacks 0D6U "part (b)"]
theorem isIso_homology_derivedPushforward_truncGEπ_of_ringedToposHom
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  let := DerivedPushforward.derivedPushforwardCommShiftOfToposHomBoundednessOfToposHom f
  have := DerivedPushforward.isTriangulated_derivedPushforward_ofToposHom_boundednessOfToposHom f
  have := (Stacks.Cohomology.DerivedPushforward.derivedPullbackPushforwardAdjunctionOfToposHom
    f).isRightAdjoint
  exact isIso_homology_map_truncGEπ_of_isRightAdjoint_rightAdjointBoundedCohomologicalDimension
    (A := A) (A' := A') (B := B) (basisCover := basisCover) (degreeBound := degreeBound)
    (coverings := coverings) (vanishing := vanishing) (B' := B') (basisCover' := basisCover')
    (degreeBound' := degreeBound') (coverings' := coverings') (vanishing' := vanishing')
    (R := Stacks.Cohomology.DerivedPushforward.derivedPushforward (X := X) (Y := Y) f)
    (hGE := f.isGE_derivedPushforward_obj_unconditional_boundednessOfToposHom) (N := N)
    (himage := himage) (hvanishImage := hvanishImage) K hK n j hj

end Stacks.Cohomology.OlssonLaszlo

end
