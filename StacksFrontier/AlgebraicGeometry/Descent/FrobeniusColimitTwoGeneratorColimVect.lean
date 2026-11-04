module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitTwoGeneratorEquivalence
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitOneGeneratorSquare

/-!
# Stacks Tag 0EXD for the categories `colim_F Vect` of Tag 0EXA

[Stacks, Tag 0EXD] is stated for the categories `colim_F Vect(-)` of [Stacks, Tag 0EXA]: for the
almost blowup square of [Stacks, Example 0EVH] in characteristic `p`, the functor
`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')` is an equivalence.
`AlgebraicGeometry.isEquivalence_twoGeneratorFrobeniusColimitComparison` proves this for the
categories of finite locally free modules over the Frobenius colimits of the structure sheaves.
This file carries it back to the categories of Tag 0EXA, along the comparison functors of
[Stacks, Tag 0EXB], which are equivalences on the four corners, all of them quasi-compact and
quasi-separated.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.isEquivalence_of_cube_of_isEquivalence`:
  the converse transport along a cube of categories: if the comparison functor of the target
  square is an equivalence, so is that of the source square.
* `AlgebraicGeometry.isEquivalence_colimVectSquare_of_frobeniusColimitVectorBundlesComparison`:
  for a commutative square of quasi-compact quasi-separated schemes in characteristic `p`, the
  comparison functor on the models `colim_F Vect(-)` is an equivalence as soon as the one on finite
  locally free `colim_F 𝒪`-modules is.
* `AlgebraicGeometry.isEquivalence_twoGeneratorColimVectComparison`: **[Stacks, Tag 0EXD]** for
  the categories `colim_F Vect(-)` of [Stacks, Tag 0EXA].

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius Stacks.AlmostBlowUp

universe u

namespace CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

variable {X A B C X₁ A₁ B₁ C₁ : Type*}
  [Category X] [Category A] [Category B] [Category C]
  [Category X₁] [Category A₁] [Category B₁] [Category C₁]
  {F : A ⥤ B} {G : C ⥤ B} (S : CatCommSqOver F G X)
  {F₁ : A₁ ⥤ B₁} {G₁ : C₁ ⥤ B₁} (S₁ : CatCommSqOver F₁ G₁ X₁)
  (ΦX : X ⥤ X₁) (ΦA : A ⥤ A₁) (ΦB : B ⥤ B₁) (ΦC : C ⥤ C₁)
  (θfst : S.fst ⋙ ΦA ≅ ΦX ⋙ S₁.fst) (θsnd : S.snd ⋙ ΦC ≅ ΦX ⋙ S₁.snd)
  (θF : F ⋙ ΦB ≅ ΦA ⋙ F₁) (θG : G ⋙ ΦB ≅ ΦC ⋙ G₁)

/-- **The converse transport of an equivalence of comparison functors along a cube of
categories.** If the faces of the cube paste to the same 2-cell, `Φ_X`, `Φ_A` and `Φ_C` are
equivalences and `Φ_B` is fully faithful, then the comparison functor `X ⥤ A ×_B C` of `S` is an
equivalence as soon as the comparison functor `X₁ ⥤ A₁ ×_{B₁} C₁` of `S₁` is: the functor induced
on 2-fibre products is an equivalence, and so is the composite through it. -/
theorem isEquivalence_of_cube_of_isEquivalence
    (h : ∀ x : X, ΦB.map (S.iso.hom.app x) ≫ θG.hom.app (S.snd.obj x) ≫
        G₁.map (θsnd.hom.app x) =
      θF.hom.app (S.fst.obj x) ≫ F₁.map (θfst.hom.app x) ≫ S₁.iso.hom.app (ΦX.obj x))
    [ΦX.IsEquivalence] [ΦA.IsEquivalence] [ΦC.IsEquivalence] [ΦB.Full] [ΦB.Faithful]
    (hS₁ : ((toFunctorToCategoricalPullback F₁ G₁ X₁).obj S₁).IsEquivalence) :
    ((toFunctorToCategoricalPullback F G X).obj S).IsEquivalence := by
  have := hS₁
  have : (CategoricalPullback.map F G ΦA ΦC ΦB F₁ G₁ θG.symm θF).IsEquivalence :=
    induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have : ((toFunctorToCategoricalPullback F G X).obj S ⋙
      CategoricalPullback.map F G ΦA ΦC ΦB F₁ G₁ θG.symm θF).IsEquivalence :=
    Functor.isEquivalence_of_iso (comparisonCubeIso S S₁ ΦX ΦA ΦB ΦC θfst θsnd θF θG h).symm
  exact Functor.isEquivalence_of_comp_right _
    (CategoricalPullback.map F G ΦA ΦC ΦB F₁ G₁ θG.symm θF)

end CategoryTheory.Limits.CategoricalPullback.CatCommSqOver

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

section Square

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)

/-- **Transport of the equivalence of comparison functors from finite locally free
`colim_F 𝒪`-modules back to the models `colim_F Vect(-)` of [Stacks, Tag 0EXA].**  The converse
of `AlgebraicGeometry.isEquivalence_frobeniusColimitVectorBundlesComparison_of_colimVect`, along
the same cube of comparison functors of [Stacks, Tag 0EXB]. -/
theorem isEquivalence_colimVectSquare_of_frobeniusColimitVectorBundlesComparison
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace E] [QuasiSeparatedSpace E]
    (hw : q ≫ b = e ≫ z)
    (h : (frobeniusColimitVectorBundlesComparison p b z q e hX hX' hZ hE hw).IsEquivalence) :
    ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
      (colimVectSquareCatCommSqOver p b z q e hX hX' hZ hE hw)).IsEquivalence := by
  have := isEquivalence_frobeniusColimitVectComparison X p hX
  have := isEquivalence_frobeniusColimitVectComparison X' p hX'
  have := isEquivalence_frobeniusColimitVectComparison Z p hZ
  have := isEquivalence_frobeniusColimitVectComparison E p hE
  exact CategoricalPullback.CatCommSqOver.isEquivalence_of_cube_of_isEquivalence
    (colimVectSquareCatCommSqOver p b z q e hX hX' hZ hE hw)
    (frobeniusColimitVectorBundlesCatCommSqOver p b z q e hX hX' hZ hE hw)
    (frobeniusColimitVectComparison X p hX) (frobeniusColimitVectComparison Z p hZ)
    (frobeniusColimitVectComparison E p hE) (frobeniusColimitVectComparison X' p hX')
    (frobeniusColimitVectComparisonPullbackIso p z hZ hX).symm
    (frobeniusColimitVectComparisonPullbackIso p b hX' hX).symm
    (frobeniusColimitVectComparisonPullbackIso p e hE hZ).symm
    (frobeniusColimitVectComparisonPullbackIso p q hE hX').symm
    (fun x => by
      rw [colimVectSquareCatCommSqOver_iso, frobeniusColimitVectorBundlesCatCommSqOver_iso,
        Iso.symm_hom, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom]
      exact frobeniusColimitVectComparison_square_cube p b z q e hX hX' hZ hE hw x) h

end Square

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0)

/-- **[Stacks, Tag 0EXD], for the categories `colim_F Vect` of [Stacks, Tag 0EXA].**  Let `p` be
a prime, `A` a ring in which `p` vanishes and `f₁, f₂ ∈ A`.  For the almost blowup square
`X = Spec A`, `Z = Spec (A/(f₁,f₂))`, `X' = Proj (A[T₀,T₁]/(f₂T₀ - f₁T₁))`, `E = 𝐏¹_Z` of
[Stacks, Example 0EVH], the functor
`colim_F Vect(X) ⟶ colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')`
built from the transition functors of the models `colim_F Vect(-)` is an equivalence.

It is `AlgebraicGeometry.isEquivalence_twoGeneratorFrobeniusColimitComparison` carried back along
the comparison functors of [Stacks, Tag 0EXB]
(`AlgebraicGeometry.isEquivalence_colimVectSquare_of_frobeniusColimitVectorBundlesComparison`):
the base is affine, the modification and the exceptional line are `Proj` of finitely generated
graded rings, so all four corners are quasi-compact and quasi-separated. -/
@[stacks 0EXD "for the categories colim_F Vect of Tag 0EXA"]
theorem isEquivalence_twoGeneratorColimVectComparison :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ((CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback _ _ _).obj
      (colimVectSquareCatCommSqOver p (modificationToBase A f₁ f₂) (centerToBase A f₁ f₂)
        (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
        (isInCharacteristic_spec A p hpA)
        (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
        (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
        (twoGenerator_isPullback A f₁ f₂).w)).IsEquivalence := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have : CompactSpace (Proj (modificationGrading A f₁ f₂)) :=
    compactSpace_proj_modificationGrading A f₁ f₂
  have : CompactSpace (Proj (exceptionalGrading A f₁ f₂)) :=
    Stacks.ProjAmple.compactSpace_proj_polyGrading (centerRing A f₁ f₂) 1
  exact isEquivalence_colimVectSquare_of_frobeniusColimitVectorBundlesComparison p _ _ _ _ _ _ _ _
    (twoGenerator_isPullback A f₁ f₂).w
    (isEquivalence_twoGeneratorFrobeniusColimitComparison A f₁ f₂ p hpA)

end AlgebraicGeometry

end
