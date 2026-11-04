module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitFreeHomFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitRestrictPullback

/-!
# Full faithfulness of the comparison of Tag 0EXD at a trivialised pair of modules

This file shows that the square of Hom-sets of the comparison functor of [Stacks, Tag 0EXD] is
cartesian at a pair of finite locally free modules over `colim_F 𝒪_X` that are isomorphic to free
ones, and that every finite locally free module over `colim_F 𝒪_X` becomes free, as an object of
the category of finite locally free modules, over the members of some open cover of `X`.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFreeFrobeniusColimitFree`: a free `colim_F 𝒪_X`-module on a
  finite index type is finite locally free.
* `AlgebraicGeometry.isPullback_squareComparison_homSquare_of_free_iso`: the square of Hom-sets
  of the comparison functor is cartesian at a pair of modules isomorphic to free ones, for an
  arbitrary commutative square of schemes in characteristic `p` whose Frobenius colimits of global
  sections form a cartesian square.
* `AlgebraicGeometry.isPullback_squareComparison_homSquare_trivialised_twoGenerator`: the same at
  the almost blowup square of [Stacks, Example 0EVH], for a ring `A`, two elements of it and a
  prime `p` vanishing in `A`.
* `AlgebraicGeometry.exists_cover_free_frobeniusColimitVectorBundlesPullback`: a finite locally
  free module over `colim_F 𝒪_X` is carried to a free object by the transition functor of each
  member of some open cover of `X`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Frobenius Stacks.AlmostBlowUp TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-- A free `colim_F 𝒪_X`-module on a finite index type is finite locally free, in the sense of
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`. -/
theorem isFiniteLocallyFreeFrobeniusColimitFree {X : Scheme.{u}}
    (hX : IsInCharacteristic X p) (I : Type u) [Finite I] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I) := by
  exact ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData
    (M := _root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I)⟩

/-- A finite locally free module over `colim_F 𝒪_X` is carried to a free object of
`AlgebraicGeometry.frobeniusColimitVectorBundles` by the transition functor of each member of some
open cover of `X`. -/
theorem exists_cover_free_frobeniusColimitVectorBundlesPullback (X : Scheme.{u})
    (hX : IsInCharacteristic X p) (M : frobeniusColimitVectorBundles X p hX) :
    ∃ (J : Type u) (W : J → X.Opens) (K : J → Type u) (hKfin : ∀ i, Finite (K i)),
      (⨆ i, W i = ⊤) ∧ ∀ i, Nonempty
        ((frobeniusColimitVectorBundlesPullback p (W i).ι
            (isInCharacteristic_toScheme hX (W i)) hX).obj M ≅
          ⟨_root_.SheafOfModules.free (K i),
            @isFiniteLocallyFreeFrobeniusColimitFree p _ (W i).toScheme
              (isInCharacteristic_toScheme hX (W i)) (K i) (hKfin i)⟩) := by
  obtain ⟨J, W, K, hcov, hfin, hiso⟩ :=
    exists_cover_free_frobeniusColimitPullback X p hX M.obj M.property
  exact ⟨J, W, K, hfin, hcov, fun i => ⟨ObjectProperty.isoMk _ (hiso i).some⟩⟩

/-- For every finite index type `I` there is a finite locally free module over `colim_F 𝒪_X`
isomorphic to the free module on `I`. -/
theorem exists_iso_free_frobeniusColimitVectorBundles {X : Scheme.{u}}
    (hX : IsInCharacteristic X p) (I : Type u) [Finite I] :
    ∃ M : frobeniusColimitVectorBundles X p hX, Nonempty
      (M ≅ ⟨_root_.SheafOfModules.free I, isFiniteLocallyFreeFrobeniusColimitFree p hX I⟩) :=
  ⟨_, ⟨Iso.refl _⟩⟩

section Square

variable {X X' Z E : Scheme.{u}} (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p)
  (I L : Type u) [Finite L]
  (hI : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) I))
  (hL : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    (_root_.SheafOfModules.free (R := frobeniusColimitRingSheaf X p hX) L))
  (hsec : IsPullback (frobeniusColimitSectionsRestrictHom p z hZ hX)
    (frobeniusColimitSectionsRestrictHom p b hX' hX)
    (frobeniusColimitSectionsRestrictHom p e hE hZ)
    (frobeniusColimitSectionsRestrictHom p q hE hX'))

include hsec

/-- For a commutative square of schemes in characteristic `p` whose Frobenius colimits of global
sections form a cartesian square, the square of Hom-sets of the comparison functor is cartesian at
a pair of modules isomorphic to free ones. -/
theorem isPullback_squareComparison_homSquare_of_free_iso (hw : q ≫ b = e ≫ z)
    (M N : frobeniusColimitVectorBundles X p hX)
    (eM : M ≅ ⟨_root_.SheafOfModules.free I, hI⟩)
    (eN : N ≅ ⟨_root_.SheafOfModules.free L, hL⟩) :
    IsPullback
      (↾fun f : M ⟶ N => (frobeniusColimitVectorBundlesPullback p z hZ hX).map f)
      (↾fun f : M ⟶ N => (frobeniusColimitVectorBundlesPullback p b hX' hX).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback p z hZ hX).obj M ⟶
          (frobeniusColimitVectorBundlesPullback p z hZ hX).obj N =>
        (frobeniusColimitVectorBundlesPullback p e hE hZ).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app N)
      (↾fun kk : (frobeniusColimitVectorBundlesPullback p b hX' hX).obj M ⟶
          (frobeniusColimitVectorBundlesPullback p b hX' hX).obj N =>
        (frobeniusColimitVectorBundlesSquareIso p b z q e hX hX' hZ hE hw).hom.app M ≫
          (frobeniusColimitVectorBundlesPullback p q hE hX').map kk) :=
  CategoryTheory.Limits.CategoricalPullback.isPullback_squareComparison_homSquare_of_iso
    _ _ _ _ _ eM.symm eN.symm
    (isPullback_squareComparison_homSquare_free p b z q e hX hX' hZ hE I L hI hL hsec hw)

end Square

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The square of Hom-sets of the comparison functor of [Stacks, Tag 0EXD] is cartesian at a pair
of modules trivialised over the base, for the almost blowup square of [Stacks, Example 0EVH]
attached to a ring `A`, two elements of it, and a prime `p` which vanishes in `A`. -/
theorem isPullback_squareComparison_homSquare_trivialised_twoGenerator (hp : p.Prime)
    (A : Type u) [CommRing A] (f₁ f₂ : A) (hpA : (p : A) = 0)
    (I L : Type u) [Finite I] [Finite L]
    (M N : frobeniusColimitVectorBundles (Spec (.of A)) p (isInCharacteristic_spec A p hpA))
    (eM : M ≅ ⟨_root_.SheafOfModules.free I,
      isFiniteLocallyFreeFrobeniusColimitFree p (isInCharacteristic_spec A p hpA) I⟩)
    (eN : N ≅ ⟨_root_.SheafOfModules.free L,
      isFiniteLocallyFreeFrobeniusColimitFree p (isInCharacteristic_spec A p hpA) L⟩) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    IsPullback
      (↾fun f : M ⟶ N =>
        (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
          (isInCharacteristic_spec A p hpA)).map f)
      (↾fun f : M ⟶ N =>
        (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
          (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
          (isInCharacteristic_spec A p hpA)).map f)
      (↾fun gg : (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).obj M ⟶
          (frobeniusColimitVectorBundlesPullback p (centerToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).obj N =>
        (frobeniusColimitVectorBundlesPullback p (exceptionalToCenter A f₁ f₂)
          (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
          (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)).map gg ≫
          (frobeniusColimitVectorBundlesSquareIso p (modificationToBase A f₁ f₂)
            (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
            (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
            (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
            (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
            (twoGenerator_isPullback A f₁ f₂).w).hom.app N)
      (↾fun kk : (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).obj M ⟶
          (frobeniusColimitVectorBundlesPullback p (modificationToBase A f₁ f₂)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
            (isInCharacteristic_spec A p hpA)).obj N =>
        (frobeniusColimitVectorBundlesSquareIso p (modificationToBase A f₁ f₂)
            (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂)
            (exceptionalToCenter A f₁ f₂) (isInCharacteristic_spec A p hpA)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
            (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
            (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
            (twoGenerator_isPullback A f₁ f₂).w).hom.app M ≫
          (frobeniusColimitVectorBundlesPullback p (exceptionalToModification A f₁ f₂)
            (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA)
            (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)).map kk) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  exact isPullback_squareComparison_homSquare_of_free_iso p (modificationToBase A f₁ f₂)
    (centerToBase A f₁ f₂) (exceptionalToModification A f₁ f₂) (exceptionalToCenter A f₁ f₂)
    (isInCharacteristic_spec A p hpA) (isInCharacteristic_twoGeneratorModification A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorCenter A f₁ f₂ p hpA)
    (isInCharacteristic_twoGeneratorExceptional A f₁ f₂ p hpA) I L _ _
    (isPullback_frobeniusColimitSections_twoGenerator p hp A f₁ f₂ hpA)
    (twoGenerator_isPullback A f₁ f₂).w M N eM eN

end AlgebraicGeometry

end
