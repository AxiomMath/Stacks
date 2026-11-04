module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechFrobeniusMatrix
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.CechTermsAcyclic
public import StacksFrontier.Homology.AcyclicResolutionNaturality

/-!
# The higher direct images of `𝐆_a` as `𝐆_a^r`, with their Frobenius

Let `S` be affine, `f : X ⟶ S` separated and `U` a finite open cover of `X` with affine finite
intersections, and let `z₁, …, z_r` be Čech cocycles of degree `q` of `V ↦ Γ((S ×_S X) ×_X V)`
whose classes form a basis of its degree-`q` cohomology over `Γ(S)`. Then
`R^q f_* 𝐆_a ≅ 𝐆_a^r` on the small étale site of `S`: the Zariski Čech resolution of `𝐆_a` is
`f_*`-acyclic, so it computes `R^q f_* 𝐆_a`, and multiplication by the `zᵢ` identifies the
degree-`q` cohomology of its direct image with `𝐆_a^r`. If the prime `p` vanishes on `S`, the
Frobenius of `𝐆_a` becomes the map `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ` for the matrix `a` expressing the
`p`-th powers of the `zᵢ` in the basis.

## Main definitions

* `Stacks.ArtinSchreier.higherDirectImageAdditiveIso`: `R^q f_* 𝐆_a ≅ 𝐆_a^r`.

## Main results

* `Stacks.ArtinSchreier.higherDirectImageAdditiveIso_frobenius`: the Frobenius.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology
open TopologicalSpace Stacks.CategoryTheory.CechComplex

universe u

namespace Stacks.ArtinSchreier

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S] [IsSeparated f] {ι : Type} [Finite ι]
  (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (hUaff : ∀ (n : ℕ) (x : Fin (n + 1) → ι), IsAffineOpen (inter U x))
  {q r : ℕ} (z : Fin r → (baseCech f U).X q)
  (hz : ∀ i, (baseCech f U).d q (q + 1) (z i) = 0)
  (hT : QuasiIsoAt (moduleBasisMap f U z hz) q)

include hU hUaff hT in
/-- **`R^q f_* 𝐆_a ≅ 𝐆_a^r`**, through a Čech basis. -/
def higherDirectImageAdditiveIso :
    ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).obj (additiveSheaf.{u, 0} X) ≅
      freeAdditiveSheaf S r :=
  haveI := quasiIso_zariskiCechAugmentation X U hU
  haveI := quasiIsoAt_basisMap f U hUaff z hz hT
  Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic (etaleAbelianDirectImage.{u, 0} f)
      (zariskiCechAugmentation X U) (acyclic_zariskiCechComplex_X f U hUaff) q ≪≫
    (HomologicalComplex.homologyFunctor _ _ q).mapIso
      (mapCechIso (etaleAbelianDirectImage.{u, 0} f) U (openDirectImagePresheaf X)) ≪≫
    (asIso (HomologicalComplex.homologyMap (basisMap f U z hz) q)).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso _ q _

variable {p : ℕ} (hp : p.Prime) (hS : (p : Γ(S, ⊤)) = 0) (a : Fin r → Fin r → Γ(S, ⊤))
  (w : Fin r → (baseCech f U).X (q - 1))
  (hw : ∀ i, cochainPow f U p (z i) - ∑ j, a i j • z j = (baseCech f U).d (q - 1) q (w i))

include hw in
/-- **Under `R^q f_* 𝐆_a ≅ 𝐆_a^r` the Frobenius of `𝐆_a` is `b ↦ (∑ᵢ aᵢⱼ bᵢ ^ p)ⱼ`**, where
`zᵢ ^ p - ∑ⱼ aᵢⱼ zⱼ = d wᵢ`. -/
theorem higherDirectImageAdditiveIso_frobenius :
    ((etaleAbelianDirectImage.{u, 0} f).rightDerived q).map
        (frobeniusMap.{u, 0} X hp (natCast_eq_zero_source f hS)) ≫
      (higherDirectImageAdditiveIso f U hU hUaff z hz hT).hom =
    (higherDirectImageAdditiveIso f U hU hUaff z hz hT).hom ≫ frobMatrixMap S hp hS a := by
  have := quasiIso_zariskiCechAugmentation X U hU
  have := quasiIsoAt_basisMap f U hUaff z hz hT
  have n1 := Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic_hom_naturality
    (etaleAbelianDirectImage.{u, 0} f) (zariskiCechAugmentation X U) (zariskiCechAugmentation X U)
    (acyclic_zariskiCechComplex_X f U hUaff) (acyclic_zariskiCechComplex_X f U hUaff)
    (frobeniusMap.{u, 0} X hp (natCast_eq_zero_source f hS))
    (zariskiCechFrobenius X U hp (natCast_eq_zero_source f hS))
    (zariskiCechAugmentation_comp_frobenius X U hp (natCast_eq_zero_source f hS)) q
  have n2 := congrArg (fun g => HomologicalComplex.homologyMap g q)
    (mapCechIso_hom_naturality (etaleAbelianDirectImage.{u, 0} f) U (openDirectImagePresheaf X)
      (openDirectImageFrobenius X hp (natCast_eq_zero_source f hS)))
  simp only [HomologicalComplex.homologyMap_comp] at n2
  have n3 := homologyMap_basisMap_comp_frobenius f U hp hS z a hz w hw
  simp only [HomologicalComplex.homologyMap_comp] at n3
  have n3' : HomologicalComplex.homologyMap (directImageCechFrobenius f hp hS U) q ≫
      inv (HomologicalComplex.homologyMap (basisMap f U z hz) q) =
      inv (HomologicalComplex.homologyMap (basisMap f U z hz) q) ≫
        HomologicalComplex.homologyMap
          ((HomologicalComplex.single _ (ComplexShape.up ℕ) q).map (frobMatrixMap S hp hS a))
            q := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, n3, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hiso : (higherDirectImageAdditiveIso f U hU hUaff z hz hT).hom =
      (Stacks.RightDerivedComp.isoRightDerivedObjOfAcyclic (etaleAbelianDirectImage.{u, 0} f)
        (zariskiCechAugmentation X U) (acyclic_zariskiCechComplex_X f U hUaff) q).hom ≫
      HomologicalComplex.homologyMap
        (mapCechIso (etaleAbelianDirectImage.{u, 0} f) U (openDirectImagePresheaf X)).hom q ≫
      inv (HomologicalComplex.homologyMap (basisMap f U z hz) q) ≫
      (HomologicalComplex.singleObjHomologySelfIso _ q _).hom := rfl
  rw [hiso]
  simp only [Category.assoc]
  rw [reassoc_of% n1]
  erw [reassoc_of% n2]
  rw [reassoc_of% n3', HomologicalComplex.singleObjHomologySelfIso_hom_naturality]
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

end Stacks.ArtinSchreier

end
