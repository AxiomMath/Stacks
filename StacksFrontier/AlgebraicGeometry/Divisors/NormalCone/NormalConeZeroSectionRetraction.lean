module

public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeFunctorial
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeZeroSection
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.RetractionSectionAlgebraHom

/-!
# The zero section of a normal cone is the section of the augmentation of its conormal algebra

Let `D ⊆ X` be an effective Cartier divisor. The normal cone `C_DX` is the relative spectrum of
the conormal graded algebra `𝒞_{D/X,*}` over `D` (`Stacks.Conormal.normalCone_eq_gluedSpectrum`).
The zero section `o : D ⟶ C_DX` of [Stacks, Tag 0FEB] is the section of the projection
`C_DX ⟶ D` cut out by a retraction of the structure morphism of `𝒞_{D/X,*}`: its
relative-spectrum pair in the sense of [Stacks, Tag 01LV] is the identity of `D` together with
that retraction.

## Main definitions

* `Stacks.Conormal.normalBundleAlgebraRetraction`: the augmentation `Sym(𝒞_{D/X}) ⟶ 𝒪_D` of the
  algebra of the normal bundle.
* `Stacks.Conormal.conormalAlgebraSheafRetraction`: **the augmentation `𝒞_{D/X,*} ⟶ 𝒪_D`** of the
  conormal algebra of an effective Cartier divisor.

## Main results

* `Stacks.Conormal.hom_comp_normalBundleAlgebraRetraction` and
  `Stacks.Conormal.hom_comp_conormalAlgebraSheafRetraction`: both augmentations retract the
  structure morphism of their algebra.
* `Stacks.Conormal.normalConeZeroSection_eq_retractionSection`: **the zero section
  `o : D ⟶ C_DX` is the section cut out by the augmentation of `𝒞_{D/X,*}`.**

## References

* [Stacks Project, Tag 0FEB](https://stacks.math.columbia.edu/tag/0FEB)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 0637](https://stacks.math.columbia.edu/tag/0637)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D]
  [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent]

/-- **For an effective Cartier divisor the canonical map of algebra sheaves
`Sym(𝒞_{D/X}) ⟶ 𝒞_{D/X,*}` is an isomorphism.** -/
instance isIso_conormalSymmetricAlgebraSheafHom_of_isEffectiveCartierDivisor :
    IsIso (conormalSymmetricAlgebraSheafHom D.subschemeι) :=
  isIso_conormalSymmetricAlgebraSheafHom D.subschemeι
    (isIso_conormalSymmetricHom_app_of_isEffectiveCartierDivisor D)

/-- **The augmentation `Sym(𝒞_{D/X}) ⟶ 𝒪_D` of the algebra of the normal bundle**:
`Stacks.LineBundle.Situation.algebraSheafAugmentation` of the conormal line-bundle situation,
read through the comparison `Stacks.LineBundle.Situation.algebraSheafIsoSymmetricAlgebraSheaf` of
the two ungraded realizations of `Sym(𝒞_{D/X})`. -/
def normalBundleAlgebraRetraction :
    (normalBundleAlgebra D.subschemeι).right.obj ⟶ D.subscheme.presheaf :=
  (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.inv.right.hom ≫
    (conormalSituation D).algebraSheafAugmentation.hom

omit [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent] in
/-- The comparison of the two ungraded realizations of `Sym(𝒞_{D/X})` cancels against its inverse
on the underlying presheaves of rings. -/
theorem algebraSheafIsoSymmetricAlgebraSheaf_hom_inv_right_hom :
    (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.hom.right.hom ≫
        (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.inv.right.hom =
      𝟙 ((conormalSituation D).algebraSheaf.right.obj) :=
  (Stacks.RelativeSpec.AlgebraSheaf.comp_right_hom _ _).trans
    (congrArg (fun t => t.right.hom)
      (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.hom_inv_id)

omit [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent] in
/-- **The augmentation of the algebra of the normal bundle retracts its structure morphism.** -/
theorem hom_comp_normalBundleAlgebraRetraction :
    (normalBundleAlgebra D.subschemeι).hom.hom ≫ normalBundleAlgebraRetraction D =
      𝟙 D.subscheme.presheaf :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (conormalSituation D).algebraSheafAugmentation.hom)
        (Stacks.RelativeSpec.AlgebraSheaf.hom_comp_right_hom
          (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.inv)).trans
      (conormalSituation D).hom_comp_algebraSheafAugmentation)

/-- **The augmentation `𝒞_{D/X,*} ⟶ 𝒪_D` of the conormal algebra of an effective Cartier
divisor**: the inverse of the canonical map `Sym(𝒞_{D/X}) ⟶ 𝒞_{D/X,*}`, which is an isomorphism
here, followed by the augmentation of the symmetric algebra. -/
def conormalAlgebraSheafRetraction :
    (conormalAlgebraSheaf D.subschemeι).right.obj ⟶ D.subscheme.presheaf :=
  (inv (conormalSymmetricAlgebraSheafHom D.subschemeι)).right.hom ≫
    normalBundleAlgebraRetraction D

/-- **The augmentation of the conormal algebra retracts its structure morphism.** -/
theorem hom_comp_conormalAlgebraSheafRetraction :
    (conormalAlgebraSheaf D.subschemeι).hom.hom ≫ conormalAlgebraSheafRetraction D =
      𝟙 D.subscheme.presheaf :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ normalBundleAlgebraRetraction D)
        (Stacks.RelativeSpec.AlgebraSheaf.hom_comp_right_hom
          (inv (conormalSymmetricAlgebraSheafHom D.subschemeι)))).trans
      (hom_comp_normalBundleAlgebraRetraction D))

/-- The canonical map `Sym(𝒞_{D/X}) ⟶ 𝒞_{D/X,*}`, followed by the augmentation of the conormal
algebra, is the augmentation of the symmetric algebra. -/
theorem conormalSymmetricAlgebraSheafHom_comp_conormalAlgebraSheafRetraction :
    (conormalSymmetricAlgebraSheafHom D.subschemeι).right.hom ≫
        conormalAlgebraSheafRetraction D =
      normalBundleAlgebraRetraction D :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ normalBundleAlgebraRetraction D)
        ((Stacks.RelativeSpec.AlgebraSheaf.comp_right_hom _ _).trans
          (congrArg (fun t => t.right.hom)
            (IsIso.hom_inv_id (conormalSymmetricAlgebraSheafHom D.subschemeι))))).trans
      (Category.id_comp _))

omit [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent] in
/-- The comparison of the two ungraded realizations of `Sym(𝒞_{D/X})`, followed by the
augmentation of the algebra of the normal bundle, is the augmentation of the line-bundle
situation. -/
theorem algebraSheafIsoSymmetricAlgebraSheaf_hom_comp_normalBundleAlgebraRetraction :
    (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.hom.right.hom ≫
        normalBundleAlgebraRetraction D =
      (conormalSituation D).algebraSheafAugmentation.hom :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (conormalSituation D).algebraSheafAugmentation.hom)
        (algebraSheafIsoSymmetricAlgebraSheaf_hom_inv_right_hom D)).trans
      (Category.id_comp _))

omit [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent (normalBundleAlgebra D.subschemeι)]
  [(conormalAlgebraSheaf D.subschemeι).IsQuasicoherent] in
/-- **The zero section of the conormal line bundle is the section of the normal bundle cut out by
the augmentation of `Sym(𝒞_{D/X})`.** -/
theorem retractionSection_comp_vectorBundleToTotalSpace :
    Stacks.RelativeSpec.retractionSection (normalBundleSituation D.subschemeι)
          (normalBundleAlgebraRetraction D) (hom_comp_normalBundleAlgebraRetraction D) ≫
        (conormalSituation D).totalSpaceIsoVectorBundle.inv =
      conormalZeroSection D :=
  (Stacks.RelativeSpec.retractionSection_comp_relativeSpectrumMapOfAlgebraHom
      (conormalSituation D).relativeSpecSituation
      (Scheme.Modules.symmetricAlgebraSheaf (conormalSituation D).X (conormalSituation D).L)
      (conormalSituation D).isQuasicoherent_symmetricAlgebraSheaf
      (conormalSituation D).algebraSheafIsoSymmetricAlgebraSheaf.hom
      (normalBundleAlgebraRetraction D) (hom_comp_normalBundleAlgebraRetraction D)).trans
    (Stacks.RelativeSpec.retractionSection_congr _ _
      (algebraSheafIsoSymmetricAlgebraSheaf_hom_comp_normalBundleAlgebraRetraction D))

/-- **The section of the normal cone cut out by the augmentation of `𝒞_{D/X,*}`, followed by the
canonical morphism `C_DX ⟶ N_DX` of [Stacks, Tag 0637], is the section of the normal bundle cut
out by the augmentation of `Sym(𝒞_{D/X})`.** -/
theorem retractionSection_comp_normalConeToNormalBundle :
    Stacks.RelativeSpec.retractionSection (normalConeSituation D.subschemeι)
          (conormalAlgebraSheafRetraction D) (hom_comp_conormalAlgebraSheafRetraction D) ≫
        normalConeToNormalBundle D.subschemeι =
      Stacks.RelativeSpec.retractionSection (normalBundleSituation D.subschemeι)
        (normalBundleAlgebraRetraction D) (hom_comp_normalBundleAlgebraRetraction D) :=
  (Stacks.RelativeSpec.retractionSection_comp_relativeSpectrumMapOfAlgebraHom
      (normalBundleSituation D.subschemeι) (conormalAlgebraSheaf D.subschemeι) inferInstance
      (conormalSymmetricAlgebraSheafHom D.subschemeι)
      (conormalAlgebraSheafRetraction D) (hom_comp_conormalAlgebraSheafRetraction D)).trans
    (Stacks.RelativeSpec.retractionSection_congr _ _
      (conormalSymmetricAlgebraSheafHom_comp_conormalAlgebraSheafRetraction D))

/-- **The zero section `o : D ⟶ C_DX` of [Stacks, Tag 0FEB] is the section of the projection
`C_DX ⟶ D` cut out by the augmentation of the conormal algebra `𝒞_{D/X,*}`.** So the
relative-spectrum pair of `o` under [Stacks, Tag 01LV] is the identity of `D` together with that
augmentation. -/
theorem normalConeZeroSection_eq_retractionSection :
    normalConeZeroSection D =
      Stacks.RelativeSpec.retractionSection (normalConeSituation D.subschemeι)
        (conormalAlgebraSheafRetraction D) (hom_comp_conormalAlgebraSheafRetraction D) := by
  have h1 : conormalZeroSection D ≫ (conormalSituation D).totalSpaceIsoVectorBundle.hom =
      Stacks.RelativeSpec.retractionSection (normalBundleSituation D.subschemeι)
        (normalBundleAlgebraRetraction D) (hom_comp_normalBundleAlgebraRetraction D) :=
    (congrArg (fun k => k ≫ (conormalSituation D).totalSpaceIsoVectorBundle.hom)
        (retractionSection_comp_vectorBundleToTotalSpace D).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => Stacks.RelativeSpec.retractionSection
              (normalBundleSituation D.subschemeι) (normalBundleAlgebraRetraction D)
              (hom_comp_normalBundleAlgebraRetraction D) ≫ k)
            (conormalSituation D).totalSpaceIsoVectorBundle.inv_hom_id).trans
          (Category.comp_id _)))
  have h2 : Stacks.RelativeSpec.retractionSection (normalBundleSituation D.subschemeι)
          (normalBundleAlgebraRetraction D) (hom_comp_normalBundleAlgebraRetraction D) ≫
        (normalConeIsoNormalBundle D).inv =
      Stacks.RelativeSpec.retractionSection (normalConeSituation D.subschemeι)
        (conormalAlgebraSheafRetraction D) (hom_comp_conormalAlgebraSheafRetraction D) :=
    (congrArg (fun k => k ≫ (normalConeIsoNormalBundle D).inv)
        (retractionSection_comp_normalConeToNormalBundle D).symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => Stacks.RelativeSpec.retractionSection
              (normalConeSituation D.subschemeι) (conormalAlgebraSheafRetraction D)
              (hom_comp_conormalAlgebraSheafRetraction D) ≫ k)
            (normalConeIsoNormalBundle D).hom_inv_id).trans
          (Category.comp_id _)))
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ (normalConeIsoNormalBundle D).inv) h1)).trans h2

end Stacks.Conormal

end
