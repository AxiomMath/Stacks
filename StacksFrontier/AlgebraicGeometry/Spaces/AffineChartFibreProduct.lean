module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport

/-!
# Fibre products of affine charts over a separated algebraic space

Let `X` be an algebraic space over `S` that is separated in the absolute sense of Stacks 03BS,
i.e. over `Spec ℤ`. The represented fibre product of two charts of `X` with affine underlying
schemes then has an affine underlying scheme. This is the affine counterpart of
`AlgebraicGeometry.Space.compactSpace_of_isAbsolutelyQuasiSeparated`, and the proof is the same:
write the fibre product as the base change of the absolute diagonal of `X` along the product of
the two charts over `Spec ℤ`, which is affine.

## Main results

* `AlgebraicGeometry.Space.isAffine_of_isAbsolutelySeparated`: for a separated presheaf, the
  represented fibre product of two charts with affine schemes has an affine scheme. The case of
  interest is the relation `R = U ×_X U` of an affine étale atlas, Stacks 03BS together with
  Stacks 01S7.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 01S7](https://stacks.math.columbia.edu/tag/01S7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MorphismProperty Stacks.Spaces

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A fibre product over the terminal scheme of two objects of the big fppf site with affine
underlying schemes has an affine underlying scheme. -/
theorem isAffine_of_isPullback_hom {A A' P : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {p₁ : P ⟶ A} {p₂ : P ⟶ A'} (hpb : IsPullback p₁.left p₂.left A.hom A'.hom)
    (hA : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A))
    (hA' : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj A')) :
    IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj P) := by
  have : IsAffine (B.inclusion.obj A.left) := hA
  have : IsAffine (B.inclusion.obj A'.left) := hA'
  have : IsAffine (B.inclusion.obj (B.obj hZ)) :=
    inferInstanceAs (IsAffine (⊤_ Scheme.{u}))
  exact .of_isIso (hpb.map B.inclusion).isoPullback.hom

/-- **The fibre product of two affine charts of a separated algebraic space is affine.** For a
presheaf `X` on the big fppf site of `S` that is separated over `Spec ℤ` (Stacks 03BS), the
represented fibre product of two charts whose underlying schemes are affine has an affine
underlying scheme: it is the base change of the absolute diagonal of `X`, a closed immersion,
along the product of the two charts over `Spec ℤ`, whose source is affine. -/
theorem isAffine_of_isAbsolutelySeparated
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXsep : IsAbsolutelySeparated B S hS hZ X)
    {A W Q : BigFppfOver B S hS} {c : yoneda.obj A ⟶ X} {g : yoneda.obj W ⟶ X}
    {q₁ : Q ⟶ A} {q₂ : Q ⟶ W}
    (hsq : IsPullback (yoneda.map q₁) (yoneda.map q₂) c g)
    (hA : IsAffine ((BigFppfOver.toScheme B S hS).obj A))
    (hW : IsAffine ((BigFppfOver.toScheme B S hS).obj W)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj Q) := by
  set f : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩ with hf
  set L := OverShriek.relocalizePresheafFunctor f with hL
  have hiso := OverShriek.relocalizeYonedaIso f
  have key : IsPullback (yoneda.map ((Over.map f).map q₁)) (yoneda.map ((Over.map f).map q₂))
      ((hiso.app A).inv ≫ L.map c) ((hiso.app W).inv ≫ L.map g) := by
    refine (hsq.map L).of_iso (hiso.app Q) (hiso.app A) (hiso.app W) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact hiso.hom.naturality q₁
    · exact hiso.hom.naturality q₂
    · simp
    · simp
  have : HasBinaryProducts (BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    CategoryTheory.Over.ConstructProducts.over_binaryProduct_of_pullback
  have hdiag := isPullback_diag_prodMap key
  set i := prodComparison (yoneda : BigFppfOver B (⊤_ Scheme.{u}) hZ ⥤ _)
    ((Over.map f).obj A) ((Over.map f).obj W) with hi
  have : IsIso i := by rw [hi]; infer_instance
  have hlift : yoneda.map (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂)) ≫ i =
      prod.lift (yoneda.map ((Over.map f).map q₁)) (yoneda.map ((Over.map f).map q₂)) := by
    refine prod.hom_ext ?_ ?_ <;> simp [hi, ← yoneda.map_comp]
  have hfinal : IsPullback (yoneda.map ((Over.map f).map q₁) ≫ ((hiso.app A).inv ≫ L.map c))
      (yoneda.map (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂))) (diag (L.obj X))
      (i ≫ prod.map ((hiso.app A).inv ≫ L.map c) ((hiso.app W).inv ≫ L.map g)) := by
    refine isPullback_of_iso_right ?_
    rw [hlift]
    exact hdiag
  have hci := hXsep.property _ _ _ hfinal
  have hprod : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map f).obj A ⨯ (Over.map f).obj W)) :=
    isAffine_of_isPullback_hom B hZ
      (CategoryTheory.Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk prod.fst prod.snd)
        (prodIsProd _ _)) hA hW
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂))) := hci
  exact isAffine_of_isAffineHom
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
      (prod.lift ((Over.map f).map q₁) ((Over.map f).map q₂)))

end AlgebraicGeometry.Space

end
