module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Families of curves over a fixed algebraic space (Stacks 0D54)

Fix an algebraic space `A` over `Spec(ℤ)`. A *family of curves over* `A` is a family of curves
`X ⟶ S` of Stacks 0D4Z together with a morphism `S ⟶ A` from its base, and a morphism of such is a
morphism of families of curves whose base map commutes with the morphisms to `A`. Equivalently it
is an object of the costructured-arrow category of the functor taking a family of curves to its
base scheme read as an algebraic space, which is how the category is defined here.

The absolute and the relative categories of curves form a 2-fibre product square over the big fppf
site of schemes: families of curves over `A` are the 2-fibre product of families of curves with the
schemes over `A`. This is the trivial remark of Stacks 0D54, by which statements about the absolute
category of curves transfer to families of curves over a fixed base algebraic space.

## Main definitions

* `AlgebraicGeometry.curveBaseSpace` takes a family of curves to its base scheme, read as an
  algebraic space over `Spec(ℤ)`; the same base scheme read as a scheme over `Spec(ℤ)` is
  `AlgebraicGeometry.curvesProjectionOver` of
  `StacksFrontier/AlgebraicGeometry/Quot/CurveFamiliesFibered.lean`.
* `AlgebraicGeometry.CurveFamilyOver`: **Stacks 0D54**, the category of families of curves over a
  fixed algebraic space.
* `AlgebraicGeometry.SchemesOverSpace` is the category of schemes of the site carrying a morphism
  to a fixed algebraic space, and `AlgebraicGeometry.schemesOverSpaceProjection` its projection to
  the site.
* `AlgebraicGeometry.CurveFamilyOver.toTwoFibreProduct` is the canonical comparison with the
  2-fibre product.

## Main results

* `AlgebraicGeometry.CurveFamilyOver.isEquivalence_toTwoFibreProduct`: **Stacks 0D54**, the
  comparison is an equivalence.
* `AlgebraicGeometry.CurveFamilyOver.toTwoFibreProduct_comp_fst`,
  `toTwoFibreProduct_comp_snd` and `toTwoFibreProduct_comp_structureFunctor`: the comparison
  respects the two projections and the structure functor to the site *on the nose*, so it is an
  equivalence of categories over the site and not merely an abstract equivalence.

## Implementation notes

The 2-fibre product used is `CategoryTheory.TwoFibreProductOver`, the 2-fibre product of
categories *over* the big fppf site of Stacks 0040, whose comparison isomorphism is required to be
vertical. That is the correct notion here, and not Mathlib's absolute
`CategoryTheory.Limits.CategoricalPullback`: the square of the source is a square of categories
fibred over `Sch_{fppf}`. Because the bottom functor of the square is the identity, a vertical
comparison isomorphism is forced to be the identity on each base scheme, which is why the
comparison functor below can be built with `CategoryTheory.Iso.refl` as its 2-cell.

Essential surjectivity rests on the terminality of `Spec(ℤ)`: two objects of the big fppf site
over `Spec(ℤ)` with the same underlying scheme of the site are *equal*, since their structure
morphisms to the terminal object agree. That is
`AlgebraicGeometry.CurveFamilyOver.bigFppfOver_eq_of_left_eq` below, and it turns the comparison
isomorphism of an object of the 2-fibre product into an `CategoryTheory.eqToHom`, which is what
makes the inverse construction possible without choosing a base change.

The functor reading a scheme of the big fppf site over the base as an algebraic space is
`AlgebraicGeometry.schemeSpaceFunctor`, which collects `AlgebraicGeometry.schemeSpace` and
`AlgebraicGeometry.schemeSpaceMap`; it lives next to those two definitions in
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeAsSpace.lean`, and the lemmas
`schemeSpaceMap_id` and `schemeSpaceMap_comp` of
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamilies.lean` are its `map_id` and `map_comp`.

## References

* [Stacks Project, Tag 0D54](https://stacks.math.columbia.edu/tag/0D54)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable (hZ : B.Contains integerBase)

/-- The base scheme of a family of curves, read as an algebraic space over `Spec(ℤ)`. -/
abbrev curveBaseSpace : CurveFamily B hZ ⥤ AlgebraicSpaces B integerBase hZ :=
  curvesProjectionOver B hZ ⋙ schemeSpaceFunctor B integerBase hZ

/-- **Stacks 0D54.** The category of families of curves over a fixed algebraic space `A`: an object
is a family of curves together with a morphism from its base scheme to `A`, and a morphism is a
morphism of families of curves commuting with those morphisms. -/
@[stacks 0D54 "the category of families of curves over a base algebraic space"]
abbrev CurveFamilyOver (A : AlgebraicSpaces B integerBase hZ) :=
  CostructuredArrow (curveBaseSpace B hZ) A

/-- The category of schemes of the big fppf site over `S` carrying a morphism to a fixed algebraic
space `A`. -/
abbrev SchemesOverSpace (A : AlgebraicSpaces B S hS) :=
  CostructuredArrow (schemeSpaceFunctor B S hS) A

/-- The projection from schemes carrying a morphism to `A` to the big fppf site of schemes. -/
abbrev schemesOverSpaceProjection (A : AlgebraicSpaces B S hS) :
    SchemesOverSpace B S hS A ⥤ B.Schemes :=
  CostructuredArrow.proj (schemeSpaceFunctor B S hS) A ⋙ BigFppfOver.forget B S hS

/-- The projection from families of curves over `A` to the big fppf site of schemes. -/
abbrev curvesOverSpaceProjection (A : AlgebraicSpaces B integerBase hZ) :
    CurveFamilyOver B hZ A ⥤ B.Schemes :=
  CostructuredArrow.proj (curveBaseSpace B hZ) A ⋙ curvesProjection B hZ

namespace CurveFamilyOver

variable {B hZ}

/-- Two schemes of the big fppf site over `Spec(ℤ)` with the same underlying scheme of the site are
equal: their structure morphisms both factor through the terminal scheme `Spec(ℤ)`, hence agree. -/
theorem bigFppfOver_eq_of_left_eq {X Y : BigFppfOver B integerBase hZ} (h : X.left = Y.left) :
    X = Y := by
  obtain ⟨x, xr, xh⟩ := X
  obtain ⟨y, yr, yh⟩ := Y
  dsimp only [Over.left] at h
  subst h
  have hh : xh = yh := B.inclusion.map_injective (specULiftZIsTerminal.hom_ext _ _)
  subst hh
  cases xr
  cases yr
  rfl

variable (B hZ)

/-- The canonical comparison from families of curves over `A` to the 2-fibre product, over the big
fppf site of schemes, of the category of families of curves with the category of schemes over `A`.
The comparison 2-cell is the identity, which is the only vertical one because the bottom functor of
the square is the identity. -/
def toTwoFibreProduct (A : AlgebraicSpaces B integerBase hZ) :
    CurveFamilyOver B hZ A ⥤
      TwoFibreProductOver (curvesProjection B hZ) (schemesOverSpaceProjection B integerBase hZ A)
        (𝟭 B.Schemes) (curvesProjection B hZ) (schemesOverSpaceProjection B integerBase hZ A) :=
  TwoFibreProductOver.lift (curvesProjection B hZ)
    (schemesOverSpaceProjection B integerBase hZ A) (𝟭 B.Schemes) (curvesProjection B hZ)
    (schemesOverSpaceProjection B integerBase hZ A) (curvesOverSpaceProjection B hZ A)
    (CostructuredArrow.proj (curveBaseSpace B hZ) A)
    (CostructuredArrow.pre (curvesProjectionOver B hZ) (schemeSpaceFunctor B integerBase hZ) A)
    rfl rfl (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The comparison respects the first projection on the nose: the family of curves underlying the
image of an object of `CurveFamilyOver` is that object's family of curves. -/
theorem toTwoFibreProduct_comp_fst (A : AlgebraicSpaces B integerBase hZ) :
    toTwoFibreProduct B hZ A ⋙ TwoFibreProductOver.fst (curvesProjection B hZ)
        (schemesOverSpaceProjection B integerBase hZ A) (𝟭 B.Schemes) (curvesProjection B hZ)
        (schemesOverSpaceProjection B integerBase hZ A) =
      CostructuredArrow.proj (curveBaseSpace B hZ) A := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- The comparison respects the second projection on the nose: the scheme over `A` underlying the
image of an object of `CurveFamilyOver` is that object's base scheme with its morphism to `A`. -/
theorem toTwoFibreProduct_comp_snd (A : AlgebraicSpaces B integerBase hZ) :
    toTwoFibreProduct B hZ A ⋙ TwoFibreProductOver.snd (curvesProjection B hZ)
        (schemesOverSpaceProjection B integerBase hZ A) (𝟭 B.Schemes) (curvesProjection B hZ)
        (schemesOverSpaceProjection B integerBase hZ A) =
      CostructuredArrow.pre (curvesProjectionOver B hZ)
        (schemeSpaceFunctor B integerBase hZ) A := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- The comparison is a functor over the big fppf site of schemes, on the nose. -/
theorem toTwoFibreProduct_comp_structureFunctor (A : AlgebraicSpaces B integerBase hZ) :
    toTwoFibreProduct B hZ A ⋙ TwoFibreProductOver.structureFunctor (curvesProjection B hZ)
        (schemesOverSpaceProjection B integerBase hZ A) (𝟭 B.Schemes) (curvesProjection B hZ)
        (schemesOverSpaceProjection B integerBase hZ A) =
      curvesOverSpaceProjection B hZ A := by
  apply CategoryTheory.Functor.hext <;> intros <;> rfl

/-- **Stacks 0D54.** The absolute and the relative categories of curves form a 2-fibre product
square over the big fppf site of schemes: the canonical comparison from families of curves over `A`
to the 2-fibre product of families of curves with the schemes over `A` is an equivalence. -/
@[stacks 0D54 "the base-change square"]
theorem isEquivalence_toTwoFibreProduct (A : AlgebraicSpaces B integerBase hZ) :
    (toTwoFibreProduct B hZ A).IsEquivalence := by
  have hfaithful : (toTwoFibreProduct B hZ A).Faithful := by
    constructor
    intro X Y f g h
    apply CostructuredArrow.hom_ext
    exact congrArg (fun q => TwoFibreProductOver.Hom.a q) h
  have hfull : (toTwoFibreProduct B hZ A).Full := by
    constructor
    intro X Y m
    have hmap : (curvesProjection B hZ).map m.a =
        (schemesOverSpaceProjection B integerBase hZ A).map m.b := by
      have hw := m.w
      change (curvesProjection B hZ).map m.a ≫ 𝟙 _ =
        𝟙 _ ≫ (schemesOverSpaceProjection B integerBase hZ A).map m.b at hw
      simpa only [Category.comp_id, Category.id_comp] using hw
    have hleft : (CurveFamily.Hom.baseMap m.a).left = m.b.left.left := by
      simpa [curvesProjection, BigFppfOver.forget] using hmap
    have hbase : CurveFamily.Hom.baseMap m.a = m.b.left := Over.OverMorphism.ext hleft
    have hspace : (curveBaseSpace B hZ).map m.a =
        (schemeSpaceFunctor B integerBase hZ).map m.b.left :=
      congrArg (schemeSpaceFunctor B integerBase hZ).map hbase
    refine ⟨{ left := m.a, right := 𝟙 X.right, w := ?_ }, ?_⟩
    · change (curveBaseSpace B hZ).map m.a ≫ Y.hom = X.hom
      rw [hspace]
      exact m.b.w
    · apply TwoFibreProductOver.Hom.ext'
      · rfl
      · exact CostructuredArrow.hom_ext _ _ hbase
  have hessSurj : (toTwoFibreProduct B hZ A).EssSurj := by
    constructor
    intro P
    have hleft : P.x.base.left = P.y.left.left := P.hx.trans P.hy.symm
    have hbase : P.x.base = P.y.left := bigFppfOver_eq_of_left_eq hleft
    have hspace := congrArg (schemeSpaceFunctor B integerBase hZ).obj hbase
    let Z : CurveFamilyOver B hZ A := CostructuredArrow.mk (eqToHom hspace ≫ P.y.hom)
    have hmap : (schemeSpaceFunctor B integerBase hZ).map (eqToHom hbase) = eqToHom hspace := by
      simp [schemeSpaceFunctor, schemeSpaceMap, eqToHom_map]
    let bIso : (CostructuredArrow.pre (curvesProjectionOver B hZ)
        (schemeSpaceFunctor B integerBase hZ) A).obj Z ≅ P.y :=
      CostructuredArrow.isoMk (eqToIso hbase) (by
        change (schemeSpaceFunctor B integerBase hZ).map (eqToHom hbase) ≫ P.y.hom =
          eqToHom hspace ≫ P.y.hom
        rw [hmap])
    have hbmap : (schemesOverSpaceProjection B integerBase hZ A).map bIso.hom =
        eqToHom hleft := by
      change Over.Hom.left bIso.hom.left = eqToHom hleft
      have hleftMap : bIso.hom.left = (eqToIso hbase).hom := rfl
      rw [hleftMap]
      change Over.Hom.left (eqToHom hbase) = eqToHom hleft
      simp
    have hvertical : P.iso.hom = eqToHom P.hx ≫ eqToHom P.hy.symm := by
      have := P.vertical
      simpa using IsHomLift.fac' (𝟭 B.Schemes) (𝟙 P.base) P.iso.hom
    have hbaseMap :
        eqToHom ((toTwoFibreProduct B hZ A).obj Z).hy.symm ≫
            (schemesOverSpaceProjection B integerBase hZ A).map bIso.hom ≫ eqToHom P.hy =
          eqToHom ((toTwoFibreProduct B hZ A).obj Z).hx.symm ≫
            (curvesProjection B hZ).map (𝟙 P.x) ≫ eqToHom P.hx := by
      change (schemesOverSpaceProjection B integerBase hZ A).map bIso.hom ≫ eqToHom P.hy =
        eqToHom P.hx
      rw [hbmap]
      exact (eqToHom_trans _ _).trans rfl
    have hw : (curvesProjection B hZ).map (𝟙 P.x) ≫ P.iso.hom =
        ((toTwoFibreProduct B hZ A).obj Z).iso.hom ≫
          (schemesOverSpaceProjection B integerBase hZ A).map bIso.hom := by
      change P.iso.hom = (schemesOverSpaceProjection B integerBase hZ A).map bIso.hom
      rw [hvertical, hbmap]
      exact (eqToHom_trans _ _).trans rfl
    let f : (toTwoFibreProduct B hZ A).obj Z ⟶ P :=
      TwoFibreProductOver.Hom.mk' (𝟙 P.x) bIso.hom hbaseMap hw
    have hIsoA : IsIso f.a := by
      change IsIso (𝟙 P.x)
      infer_instance
    have hIsoB : IsIso f.b := by
      change IsIso bIso.hom
      infer_instance
    have : IsIso f := TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ f hIsoA hIsoB
    exact ⟨Z, ⟨asIso f⟩⟩
  have := hfaithful
  have := hfull
  have := hessSurj
  exact { }

end CurveFamilyOver

end AlgebraicGeometry

end
