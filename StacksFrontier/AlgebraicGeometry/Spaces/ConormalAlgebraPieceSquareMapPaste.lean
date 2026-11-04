module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraPieceSquareMap

/-!
# Pasting the maps of conormal algebras of commutative squares

For commutative squares `i_{U₁} ≫ φ₁ = p₁ ≫ i` and `i_{U₂} ≫ φ₂ = p₂ ≫ i_{U₁}` of algebraic
spaces, the degree-`n` map of conormal algebras of the outer rectangle
(`AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap`), read through the composition
comparison of Stacks 03LU, is the inverse image along `p₂` of the map of the first square
followed by the map of the second square.  On the ambient spaces this is
`AlgebraicGeometry.Space.kernelIdealSheafZPowSquareMap_comp`; the square comparisons of inverse
images paste by `AlgebraicGeometry.Space.modulePullbackSquareCompIso_paste_comp`.

## Main results

* `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_comp`: the pasting law.
* `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMapOfIso_comp_of_eq`: the pasting law after
  an identification of the source, with the edges of the outer rectangle presented as given
  morphisms.

## References

* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X Z ZU U₁ U₂ Z₁ Z₂ : AlgebraicSpaces B S hS}

/-- **The maps of conormal algebras of two stacked squares paste, on the ambient powers of the
kernel ideal sheaves.** -/
theorem conormalAlgebraPieceSquareMap_comp_kernelIdeal (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) (n : ℤ) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app
          ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫
        ((modulePullbackSquareCompIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU₂).map
          (kernelIdealSheafZPowSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n) =
      (modulePullback B S hS p₂).map
          (((modulePullbackSquareCompIso B S hS p₁ iU₁ i φ₁ h₁).app
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
            (modulePullback B S hS iU₁).map
              (kernelIdealSheafZPowSquareMap B S hS p₁ iU₁ i φ₁ h₁ n)) ≫
        ((modulePullbackSquareCompIso B S hS p₂ iU₂ iU₁ φ₂ h₂).app
          (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU₂).map
          (kernelIdealSheafZPowSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n) :=
  modulePullbackSquareCompIso_paste_comp B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂ _ _ _ _ _ _
    (kernelIdealSheafZPowSquareMap_comp B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂ n)

/-- The degree-`n` map of conormal algebras of a commutative square, with its two factors named
at the ambient powers of the kernel ideal sheaves. -/
theorem conormalAlgebraPieceSquareMap_eq_app (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X) (φ : U ⟶ X)
    (hsq : iU ≫ φ = p ≫ i) (n : ℤ) :
    conormalAlgebraPieceSquareMap B S hS p iU i φ hsq n =
      ((modulePullbackSquareCompIso B S hS p iU i φ hsq).app
          (kernelIdealSheafZPow B S hS i n).toSheafOfModules).hom ≫
        (modulePullback B S hS iU).map (kernelIdealSheafZPowSquareMap B S hS p iU i φ hsq n) :=
  rfl

/-- `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_comp_kernelIdeal` with the maps of the
squares named. -/
theorem conormalAlgebraPieceSquareMap_comp_kernelIdeal' (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) (n : ℤ) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app
          ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) ≫
        conormalAlgebraPieceSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n =
      (modulePullback B S hS p₂).map
          (X := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
          (Y := (modulePullback B S hS iU₁).obj
            (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules)
          (conormalAlgebraPieceSquareMap B S hS p₁ iU₁ i φ₁ h₁ n) ≫
        conormalAlgebraPieceSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n :=
  conormalAlgebraPieceSquareMap_comp_kernelIdeal B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂ n

/-- **The maps of conormal algebras of two stacked squares paste**: the map of the outer
rectangle, read through the composition comparison of Stacks 03LU at `p₂ ≫ p₁`, is the inverse
image along `p₂` of the map of the first square followed by the map of the second. -/
theorem conormalAlgebraPieceSquareMap_comp (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁)
    (h₁₂ : iU₂ ≫ φ₂ ≫ φ₁ = (p₂ ≫ p₁) ≫ i) (n : ℤ) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) ≫
        conormalAlgebraPieceSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n =
      (modulePullback B S hS p₂).map (conormalAlgebraPieceSquareMap B S hS p₁ iU₁ i φ₁ h₁ n) ≫
        conormalAlgebraPieceSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n := by
  have hA : (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) =
      (modulePullbackCompIso B S hS p₂ p₁).hom.app
        ((modulePullback B S hS i).obj (kernelIdealSheafZPow B S hS i n).toSheafOfModules) :=
    (app_retype (modulePullbackCompIso B S hS p₂ p₁).hom
      (conormalAlgebra_piece B S hS i n)).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  have hm : (modulePullback B S hS p₂).map
        (conormalAlgebraPieceSquareMap B S hS p₁ iU₁ i φ₁ h₁ n) =
      (modulePullback B S hS p₂).map
          (X := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
            (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
          (Y := (modulePullback B S hS iU₁).obj
            (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules)
          (conormalAlgebraPieceSquareMap B S hS p₁ iU₁ i φ₁ h₁ n) :=
    (map_retype (modulePullback B S hS p₂)
      (X₁ := (modulePullback B S hS p₁).obj ((conormalAlgebra B S hS i).piece n))
      (Y₁ := (conormalAlgebra B S hS iU₁).piece n)
      (X₂ := (modulePullback B S hS i ⋙ modulePullback B S hS p₁).obj
        (kernelIdealSheafZPow B S hS i n).toSheafOfModules)
      (Y₂ := (modulePullback B S hS iU₁).obj
        (kernelIdealSheafZPow B S hS iU₁ n).toSheafOfModules) rfl rfl _ _
      ((Category.id_comp _).trans (Category.comp_id _)).symm).trans
      ((Category.id_comp _).trans (Category.comp_id _))
  exact (congrArg (· ≫ _) hA).trans
    ((conormalAlgebraPieceSquareMap_comp_kernelIdeal' B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂
      n).trans (congrArg (· ≫ _) hm.symm))

/-- `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMapOfIso`, unfolded. -/
theorem conormalAlgebraPieceSquareMapOfIso_eq_comp (p : ZU ⟶ Z) (iU : ZU ⟶ U) (i : Z ⟶ X)
    (φ : U ⟶ X) (hsq : iU ≫ φ = p ≫ i) (n : ℤ) {M : Modules.{u, u} B S hS Z.1 Z.2}
    (κ : M ≅ (conormalAlgebra B S hS i).piece n) :
    conormalAlgebraPieceSquareMapOfIso B S hS p iU i φ hsq n κ =
      (modulePullback B S hS p).map κ.hom ≫ conormalAlgebraPieceSquareMap B S hS p iU i φ hsq n :=
  rfl

/-- **The maps of conormal algebras of two stacked squares paste, after an identification of the
source**: `AlgebraicGeometry.Space.conormalAlgebraPieceSquareMap_comp` for
`AlgebraicGeometry.Space.conormalAlgebraPieceSquareMapOfIso`, with the edges `p₂ ≫ p₁` and
`φ₂ ≫ φ₁` of the outer rectangle presented as given morphisms `p₁₂` and `φ₁₂`. -/
theorem conormalAlgebraPieceSquareMapOfIso_comp_of_eq (i : Z ⟶ X) (p₁ : Z₁ ⟶ Z)
    (iU₁ : Z₁ ⟶ U₁) (φ₁ : U₁ ⟶ X) (p₂ : Z₂ ⟶ Z₁) (iU₂ : Z₂ ⟶ U₂) (φ₂ : U₂ ⟶ U₁)
    (h₁ : iU₁ ≫ φ₁ = p₁ ≫ i) (h₂ : iU₂ ≫ φ₂ = p₂ ≫ iU₁) (p₁₂ : Z₂ ⟶ Z) (hp : p₂ ≫ p₁ = p₁₂)
    (φ₁₂ : U₂ ⟶ X) (hφ : φ₂ ≫ φ₁ = φ₁₂) (h₁₂ : iU₂ ≫ φ₁₂ = p₁₂ ≫ i) (n : ℤ)
    {M : Modules.{u, u} B S hS Z.1 Z.2} (κ : M ≅ (conormalAlgebra B S hS i).piece n) :
    (modulePullbackCompIso B S hS p₂ p₁).hom.app M ≫
        eqToHom (congrArg (fun k : Z₂ ⟶ Z => (modulePullback B S hS k).obj M) hp) ≫
        conormalAlgebraPieceSquareMapOfIso B S hS p₁₂ iU₂ i φ₁₂ h₁₂ n κ =
      (modulePullback B S hS p₂).map
          (conormalAlgebraPieceSquareMapOfIso B S hS p₁ iU₁ i φ₁ h₁ n κ) ≫
        conormalAlgebraPieceSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n := by
  subst hp hφ
  have nat : (modulePullback B S hS p₂).map ((modulePullback B S hS p₁).map κ.hom) ≫
      (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) =
      (modulePullbackCompIso B S hS p₂ p₁).hom.app M ≫
        (modulePullback B S hS (p₂ ≫ p₁)).map κ.hom :=
    (modulePullbackCompIso B S hS p₂ p₁).hom.naturality κ.hom
  have main := conormalAlgebraPieceSquareMap_comp B S hS i p₁ iU₁ φ₁ p₂ iU₂ φ₂ h₁ h₂ h₁₂ n
  have e0 : (modulePullbackCompIso B S hS p₂ p₁).hom.app M ≫
        eqToHom (congrArg (fun k : Z₂ ⟶ Z => (modulePullback B S hS k).obj M) rfl) ≫
        conormalAlgebraPieceSquareMapOfIso B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n κ =
      (modulePullbackCompIso B S hS p₂ p₁).hom.app M ≫
        (modulePullback B S hS (p₂ ≫ p₁)).map κ.hom ≫
        conormalAlgebraPieceSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n :=
    congrArg (_ ≫ ·) (Category.id_comp _)
  have e1 : (modulePullbackCompIso B S hS p₂ p₁).hom.app M ≫
        (modulePullback B S hS (p₂ ≫ p₁)).map κ.hom ≫
        conormalAlgebraPieceSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n =
      (modulePullback B S hS p₂).map ((modulePullback B S hS p₁).map κ.hom) ≫
        (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) ≫
        conormalAlgebraPieceSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n :=
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) nat.symm)).trans (Category.assoc _ _ _)
  have e2 : (modulePullback B S hS p₂).map ((modulePullback B S hS p₁).map κ.hom) ≫
        (modulePullbackCompIso B S hS p₂ p₁).hom.app ((conormalAlgebra B S hS i).piece n) ≫
        conormalAlgebraPieceSquareMap B S hS (p₂ ≫ p₁) iU₂ i (φ₂ ≫ φ₁) h₁₂ n =
      (modulePullback B S hS p₂).map
          (conormalAlgebraPieceSquareMapOfIso B S hS p₁ iU₁ i φ₁ h₁ n κ) ≫
        conormalAlgebraPieceSquareMap B S hS p₂ iU₂ iU₁ φ₂ h₂ n :=
    (whisker_eq ((modulePullback B S hS p₂).map ((modulePullback B S hS p₁).map κ.hom))
      main).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
      (((modulePullback B S hS p₂).map_comp _ _).symm.trans (congrArg
        (modulePullback B S hS p₂).map
        (conormalAlgebraPieceSquareMapOfIso_eq_comp B S hS p₁ iU₁ i φ₁ h₁ n κ).symm))))
  exact e0.trans (e1.trans e2)

end AlgebraicGeometry.Space

end
