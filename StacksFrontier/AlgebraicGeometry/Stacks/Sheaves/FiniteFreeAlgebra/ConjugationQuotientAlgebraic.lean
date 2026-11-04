module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SmoothActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ConjugationActionOnSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.UnitFixingSmooth

/-!
# The quotient stack of the conjugation action is an algebraic stack

The group `G ⊆ GL_d` of **Stacks 05YQ** is smooth over `Spec(ℤ)`
(`AlgebraicGeometry.FiniteFreeAlgebra.smooth_unitFixingScheme`), and the quotient stack of a
smooth group action is an algebraic stack
(`AlgebraicGeometry.Stack.isAlgebraicStack_quotientStackOfAction`). This file joins the two: the
group algebraic space `G_B = B ×_S G_S` over an algebraic space `B` over `S` is smooth over `B`,
so the quotient stack `[X/G]` of the conjugation action on the scheme of structure constants is
an algebraic stack over `S`.

That is the second assertion of Stacks 05YQ — *"In particular `ℋ_d` is an algebraic stack"* —
for the quotient stack side of the equivalence the tag asserts. The statement here is for an
arbitrary algebraic space `B` over `S`; over the base itself, which is the `[X/G]` of the tag,
the statement is also
`AlgebraicGeometry.Stack.isAlgebraicStack_conjugationQuotientStack` in
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/FiniteFreeAlgebra/FiniteCoverAlgebraicStack.lean`.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.smooth_unitFixingBaseChange`: `G_S ⟶ S` is smooth, by
  base change of `G ⟶ Spec(ℤ)`.
* `AlgebraicGeometry.Space.isSmooth_prod_fst_yoneda_obj`: the projection
  `F ⨯ h_a ⟶ F` of the restriction of an algebraic space to an object of the site is smooth as
  soon as the structure morphism of that object is a smooth morphism of schemes.
* `AlgebraicGeometry.Space.isSmooth_groupOverStar_unitFixing`: the structure morphism of
  `G_B = B ×_S G_S` over `B` is smooth.
* `AlgebraicGeometry.Stack.isAlgebraicStack_structureConstantsQuotientStack`: **the quotient
  stack `[X/G]` of the conjugation action, over an arbitrary algebraic space `B` over `S`, is an
  algebraic stack over `S`.** Over the base itself the statement is also
  `AlgebraicGeometry.Stack.isAlgebraicStack_conjugationQuotientStack`.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
* [Stacks Project, Tag 043I](https://stacks.math.columbia.edu/tag/043I)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe u w

namespace AlgebraicGeometry.FiniteFreeAlgebra

variable (d : ℕ) [NeZero d]

/-- **The unit-fixing subgroup scheme `G_S` is smooth over `S`.** It is obtained from `G` by base
change along `S ⟶ Spec(ℤ)`, and `G` is smooth over `Spec(ℤ)` by
`AlgebraicGeometry.FiniteFreeAlgebra.smooth_unitFixingScheme`. -/
theorem smooth_unitFixingBaseChange (S : Scheme.{u}) :
    Smooth (unitFixingBaseChange.{u} d S).hom :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Smooth.{u})
    (IsPullback.of_hasPullback (specULiftZIsTerminal.from (unitFixingScheme.{u} d))
      (specULiftZIsTerminal.from S)) (smooth_unitFixingScheme.{u} d)

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S)

/-- The structure morphism of `G_S` read as a morphism of schemes through the object of the big
fppf site it defines is smooth. -/
theorem smooth_toScheme_map_unitFixingSiteObject :
    Smooth ((BigFppfOver.toScheme 𝒞 S hS).map
      (Over.mkIdTerminal.from (Space.unitFixingSiteObject 𝒞 S hS d))) := by
  have h : Over.mkIdTerminal.from (Space.unitFixingSiteObject 𝒞 S hS d) =
      Over.homMk (Space.unitFixingSiteObject 𝒞 S hS d).hom :=
    Over.mkIdTerminal.hom_ext _ _
  rw [h]
  exact smooth_unitFixingBaseChange.{u} d S

end AlgebraicGeometry.FiniteFreeAlgebra

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The product `F ⨯ h_a` of an algebraic space with an object of the site is an algebraic
space. -/
private theorem isAlgebraicSpace_prod_yoneda_obj_right (a : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F) :
    IsAlgebraicSpace B S hS (F ⨯ yoneda.obj a) :=
  isAlgebraicSpace_of_iso B S hS (prod.braiding F (yoneda.obj a)).symm
    (isAlgebraicSpace_prod_yoneda_obj a hF)

/-- Precomposing a smooth morphism of algebraic spaces with an isomorphism keeps it smooth. -/
private theorem isSmooth_hom_comp_of_isSmooth {X Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hF : IsAlgebraicSpace B S hS F) (e : X ≅ Y) {f : Y ⟶ F} (hf : IsSmooth B S hS f) :
    IsSmooth B S hS (e.hom ≫ f) :=
  isSmooth_comp B S hS hX hY hF _ _ (isSmooth_of_isIso B S hS hX hY _) hf

/-- **The projection from the restriction of an algebraic space to an object of the site is
smooth** as soon as the structure morphism of that object is a smooth morphism of schemes
(Stacks 03ZE). -/
theorem isSmooth_prod_fst_yoneda_obj (a : BigFppfOver B S hS)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (ha : Smooth ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))) :
    IsSmooth B S hS (prod.fst : F ⨯ yoneda.obj a ⟶ F) := by
  have hya : IsAlgebraicSpace B S hS (yoneda.obj a) := isAlgebraicSpace_yoneda B S hS a
  have hterm : IsAlgebraicSpace B S hS
      (yoneda.obj (Over.mk (𝟙 (B.obj hS))) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    isAlgebraicSpace_yoneda B S hS _
  have hpa : IsAlgebraicSpace B S hS (yoneda.obj a ⨯ F) :=
    isAlgebraicSpace_prod_yoneda_obj a hF
  have sq := isPullback_prod_fst_snd_yoneda_obj a F
  have sqSp : IsPullback
      (ObjectProperty.homMk (prod.fst : yoneda.obj a ⨯ F ⟶ yoneda.obj a) :
        (⟨yoneda.obj a ⨯ F, hpa⟩ : AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj a, hya⟩)
      (ObjectProperty.homMk (prod.snd : yoneda.obj a ⨯ F ⟶ F) :
        (⟨yoneda.obj a ⨯ F, hpa⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk (yoneda.map (Over.mkIdTerminal.from a)) :
        (⟨yoneda.obj a, hya⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hterm⟩)
      (ObjectProperty.homMk ((isTerminal_yoneda_obj_base B S hS).from F) :
        (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨_, hterm⟩) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ sq.w) (by simpa using sq)
  have hsnd : IsSmooth B S hS (prod.snd : yoneda.obj a ⨯ F ⟶ F) :=
    (smoothMorphismProperty B S hS).of_isPullback sqSp
      (isSmooth_yoneda_map B S hS (Over.mkIdTerminal.from a) ha)
  have hbr : (prod.braiding F (yoneda.obj a)).hom ≫ (prod.snd : yoneda.obj a ⨯ F ⟶ F) =
      (prod.fst : F ⨯ yoneda.obj a ⟶ F) := by simp
  rw [← hbr]
  exact isSmooth_hom_comp_of_isSmooth (isAlgebraicSpace_prod_yoneda_obj_right a hF) hpa hF _ hsnd

/-- **The structure morphism of a group `B ×_S a` attached to an object of the site is smooth**
when the object is smooth over `S`. -/
theorem isSmooth_groupOverStar_of_smooth {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (G : (BigFppfOver B S hS)ᵒᵖ ⥤ GrpCat.{u})
    {a : BigFppfOver B S hS}
    (r : (G ⋙ forget GrpCat).RepresentableBy a)
    (ha : Smooth ((BigFppfOver.toScheme B S hS).map (Over.mkIdTerminal.from a))) :
    IsSmooth B S hS (groupOverStar B S hS F G).hom := by
  have hprod := isAlgebraicSpace_prod_yoneda_obj_right a hF
  let e : (F ⨯ (G ⋙ forget GrpCat)) ≅ (F ⨯ yoneda.obj a) :=
    prod.mapIso (Iso.refl F) r.toIso.symm
  have hsrc : IsAlgebraicSpace B S hS (F ⨯ (G ⋙ forget GrpCat)) :=
    isAlgebraicSpace_of_iso B S hS e.symm hprod
  have hcomp : e.hom ≫ (prod.fst : F ⨯ yoneda.obj a ⟶ F) =
      (prod.fst : F ⨯ (G ⋙ forget GrpCat) ⟶ F) := by
    simp [e]
  have hhom : (groupOverStar B S hS F G).hom =
      (prod.fst : F ⨯ (G ⋙ forget GrpCat) ⟶ F) := by
    simp only [groupOverStar, overStar, Over.star_obj_hom]
    exact prod.lift_fst _ _
  rw [hhom, ← hcomp]
  exact isSmooth_hom_comp_of_isSmooth hsrc hprod hF e (isSmooth_prod_fst_yoneda_obj a hF ha)

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- **The unit-fixing group `G_B = B ×_S G_S` is smooth over `B`.** -/
theorem isSmooth_groupOverStar_unitFixing (B : AlgebraicSpaces 𝒞 S hS) :
    IsSmooth 𝒞 S hS
      (groupOverStar 𝒞 S hS B.obj (unitFixingPointsOnSite 𝒞 S hS d)).hom :=
  isSmooth_groupOverStar_of_smooth B.property (unitFixingPointsOnSite 𝒞 S hS d)
    (pointsOnSiteRepresentableBy 𝒞 S hS (unitFixingSiteObject 𝒞 S hS d)
      (unitFixingSiteObjectGrpObj 𝒞 S hS d))
    (FiniteFreeAlgebra.smooth_toScheme_map_unitFixingSiteObject d 𝒞 S hS)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack

variable (𝒞 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝒞.Contains S) (d : ℕ) [NeZero d]

/-- **The second assertion of Stacks 05YQ for the quotient stack of the conjugation action.**
The quotient stack `[X/G]` of the conjugation action of the unit-fixing subgroup `G ⊆ GL_d` on
the scheme `X` of structure constants of free `d`-dimensional algebras, formed over an algebraic
space `B` over `S`, is an algebraic stack over `S`.

Over the base itself the statement the tag asserts is also
`AlgebraicGeometry.Stack.isAlgebraicStack_conjugationQuotientStack`. -/
theorem isAlgebraicStack_structureConstantsQuotientStack
    (B : AlgebraicSpaces 𝒞 S hS) :
    IsAlgebraicStack.{u, w} 𝒞 S hS
      (Space.structureConstantsQuotientStack 𝒞 S hS d B) :=
  isAlgebraicStack_quotientStackOfAction B
    (Space.groupOverStar 𝒞 S hS B.obj (Space.unitFixingPointsOnSite 𝒞 S hS d))
    (Space.objectOverStar 𝒞 S hS B.obj
      (yoneda.obj (Space.structureConstantsSiteObject 𝒞 S hS d)))
    _ _ (Space.isSmooth_groupOverStar_unitFixing 𝒞 S hS d B)

end AlgebraicGeometry.Stack

end
