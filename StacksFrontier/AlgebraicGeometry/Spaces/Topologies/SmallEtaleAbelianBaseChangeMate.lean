module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianInverseImageInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianPushforwardComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SmallEtaleBaseChangeMate
public import StacksFrontier.CategoryTheory.Adjunction.MatesChangeOfCategories
public import StacksFrontier.CategoryTheory.Sites.Topos.AbelianAdjunctionForget

/-!
# Étale base change for higher direct images: the canonical comparison is an isomorphism

Let

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

be a cartesian square of algebraic spaces over a scheme `S` contained in a big fppf site `B`,
with `g` étale. For an abelian sheaf `ℱ` on `X_étale` and every degree `n`, the higher direct
image commutes with restriction: `R^n f'_{small,*}(ℱ|_{X'}) = (R^n f_{small,*} ℱ)|_{Y'}`
(Stacks 03LR, part (2)). This file proves that the *canonical* comparison between the two sides
is an isomorphism.

In degree zero the comparison is the adjunction mate of the direct-image comparison of the
square, formed with the adjunctions of the abelian inverse and direct images. In degree `n` it is
obtained from the degree-zero map by applying `R^n`, pulling the exact restriction along `g` out
of the right derived functor, and using that restriction along `i` carries injective resolutions
to injective resolutions.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianBaseChangeMap`: the canonical base-change 2-cell
  `f_{small,*} ∘ g_{small}^{-1} ⟶ i_{small}^{-1} ∘ f'_{small,*}` for abelian sheaves, as the mate
  of the direct-image comparison of the square.
* `StacksTag03LR.rightDerivedBaseChangeMap`: the degree-`n` base-change comparison of a square of
  additive functors, built from the degree-zero one.
* `AlgebraicGeometry.Space.smallEtaleAbelianHigherBaseChangeMap`: the canonical comparison
  `(R^n f_{small,*} ℱ)|_{Y'} ⟶ R^n f'_{small,*}(ℱ|_{X'})`.

## Main results

* `Stacks.Topos.AbelianPushforward.abelianPushforwardSquareIso_forget` and
  `Stacks.Topos.AbelianPushforward.mateEquiv_abelianInverseImage_forgetIso_inv`: the two
  compatibilities of the abelian direct image with the change of coefficients.
* `AlgebraicGeometry.Space.isIso_smallEtaleAbelianBaseChangeMap`: the degree-zero abelian
  base-change 2-cell is an isomorphism.
* `AlgebraicGeometry.Space.isIso_smallEtaleAbelianHigherBaseChangeMap`: the canonical comparison
  of higher direct images is an isomorphism in every degree.
* `AlgebraicGeometry.Space.smallEtalePushforwardEtaleBaseChange_allParts`: base change for the
  direct image of sheaves of sets, for the inverse image, and for the higher direct images of
  abelian sheaves, as a single conjunction.

## References

* [Stacks Project, Tag 03LR](https://stacks.math.columbia.edu/tag/03LR)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

-- Instance search must use the cartesian monoidal structure on `Sheaf J (Type w)` rather than
-- the one inherited from presheaves.
attribute [local instance 5000] CategoryTheory.SemiCartesianMonoidalCategory.toMonoidalCategory

attribute [local instance 5000]
  CategoryTheory.CartesianMonoidalCategory.toSemiCartesianMonoidalCategory

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instCartesianMonoidalCategorySheafType_stacksFrontier

attribute [local instance 3000]
  Stacks.Topos.AbelianInverseImage.instBraidedCategorySheafType_stacksFrontier

universe v u v' u' w w'

/-! ### The abelian direct image against the change of coefficients -/

namespace Stacks.Topos.AbelianPushforward

/-- The left triangle identity of an adjunction, with an identity morphism inserted in the
middle. -/
private theorem leftTriangle_pad {A : Type*} {B : Type*} [Category* A] [Category* B]
    {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) (X : A) :
    𝟙 (L.obj X) =
      L.map (adj.unit.app X) ≫ L.map (𝟙 (R.obj (L.obj X))) ≫ adj.counit.app (L.obj X) := by
  simp

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))

/-- **The direct-image comparison is the mate of the inverse-image comparison**, for the
identification of the inverse and direct images of abelian sheaves with the geometric ones. -/
theorem mateEquiv_abelianInverseImage_forgetIso_inv :
    mateEquiv (abelianInverseImageAdjPushforward J f) f.adj
        (TwoSquare.mk _ _ _ _ (Sites.abelianInverseImage_forgetIso f).inv) =
      TwoSquare.mk _ _ _ _ (abelianPushforward_forgetIso J f).hom := by
  refine (Equiv.eq_symm_apply _).mp (TwoSquare.ext _ _ fun c => ?_)
  have hu := abelianInverseImageAdjPushforward_unit_forget J f c
  simp only [Sites.abelianInverseImage_forgetIso, abelianPushforward_forgetIso, Iso.refl_inv,
    Iso.refl_hom, NatTrans.id_app, mateEquiv, Equiv.coe_fn_symm_mk, NatTrans.comp_app,
    Functor.comp_obj, Functor.id_obj, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_id, Functor.comp_map, Functor.rightUnitor_hom_app,
    Category.comp_id, Category.id_comp]
  rw [hu]
  exact leftTriangle_pad f.adj _

section Square

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C₁ : Type u₁} [Category.{v₁} C₁] {J₁ : GrothendieckTopology C₁}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {C₃ : Type u₃} [Category.{v₃} C₃] {J₃ : GrothendieckTopology C₃}
  {C₄ : Type u₄} [Category.{v₄} C₄] {J₄ : GrothendieckTopology C₄}
  (p : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₂ (Type w)))
  (q : MorphismOfTopoi (Sheaf J₂ (Type w)) (Sheaf J₃ (Type w)))
  (r : MorphismOfTopoi (Sheaf J₁ (Type w)) (Sheaf J₄ (Type w)))
  (s : MorphismOfTopoi (Sheaf J₄ (Type w)) (Sheaf J₃ (Type w)))

/-- **The direct-image comparison of a square at abelian coefficients forgets to the one at set
coefficients.**  Forgetting the abelian-group operations in the lift
`Stacks.Topos.AbelianPushforward.abelianPushforwardSquareIso` of a comparison `α` of composite
direct images of sheaves of sets returns `α`. -/
theorem abelianPushforwardSquareIso_forget
    (α : p.pushforward ⋙ q.pushforward ≅ r.pushforward ⋙ s.pushforward)
    (F : Sheaf J₁ AddCommGrpCat.{w}) :
    (sheafCompose J₃ (forget AddCommGrpCat.{w})).map
        ((abelianPushforwardSquareIso p q r s α).hom.app F) =
      α.hom.app ((sheafCompose J₁ (forget AddCommGrpCat.{w})).obj F) := by
  have key : (sheafCompose J₃ (forget AddCommGrpCat.{w})).map
        ((abelianPushforwardSquareIso p q r s α).hom.app F) =
      q.pushforward.map (𝟙 _) ≫
        α.hom.app ((sheafCompose J₁ (forget AddCommGrpCat.{w})).obj F) ≫
          s.pushforward.map (𝟙 _) := rfl
  rw [key, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact Category.comp_id _

/-- **The cube identity for the change of coefficients.**  The comparison of the two composite
direct images around a square at set coefficients, pasted with the comparisons of the two
coefficient categories, is the comparison at abelian coefficients. -/
theorem abelianPushforward_coefficientCube_eq
    (α : p.pushforward ⋙ q.pushforward ≅ r.pushforward ⋙ s.pushforward) :
    (((mateEquiv (abelianInverseImageAdjPushforward J₁ p) p.adj
              (TwoSquare.mk _ _ _ _ (Sites.abelianInverseImage_forgetIso p).inv)).vComp
            (TwoSquare.mk _ _ _ _ α.hom)).whiskerRight
          (abelianPushforward_forgetIso J₂ q).hom).whiskerLeft
        (abelianPushforward_forgetIso J₁ r).inv =
      (TwoSquare.mk _ _ _ _ (abelianPushforwardSquareIso p q r s α).hom).vComp
        (mateEquiv (abelianInverseImageAdjPushforward J₄ s) s.adj
          (TwoSquare.mk _ _ _ _ (Sites.abelianInverseImage_forgetIso s).inv)) := by
  rw [mateEquiv_abelianInverseImage_forgetIso_inv, mateEquiv_abelianInverseImage_forgetIso_inv]
  refine TwoSquare.ext _ _ fun F => ?_
  refine Eq.trans (rfl : _ = q.pushforward.map (𝟙 _) ≫
      α.hom.app ((sheafCompose J₁ (forget AddCommGrpCat.{w})).obj F) ≫
      s.pushforward.map (𝟙 _)) ?_
  refine Eq.trans ?_ (rfl : (sheafCompose J₃ (forget AddCommGrpCat.{w})).map
      ((abelianPushforwardSquareIso p q r s α).hom.app F) = _)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).trans (abelianPushforwardSquareIso_forget p q r s α F).symm

end Square

end Stacks.Topos.AbelianPushforward

/-! ### The degree-`n` base-change comparison of a square of additive functors -/

namespace StacksTag03LR

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
  {A' : Type u₂} [Category.{v₂} A'] [Abelian A']
  {D : Type u₃} [Category.{v₃} D] [Abelian D]
  {D' : Type u₄} [Category.{v₄} D'] [Abelian D']

/-- **The degree-`n` base-change comparison of a square of additive functors.**  For

```
A --R--> A'
|F       |F'
D --R'-> D'
```

with `R` and `R'` exact, `R` carrying injective objects to injective objects, and a 2-cell
`α : F ⋙ R' ⟶ R ⋙ F'`, the degree-`n` comparison `R^n F ⋙ R' ⟶ R ⋙ R^n F'`: the composite of
the identification `R^n F ⋙ R' ≅ R^n (F ⋙ R')`, the map `R^n α`, and the identification
`R^n (R ⋙ F') ≅ R ⋙ R^n F'`. -/
noncomputable def rightDerivedBaseChangeMap [HasInjectiveResolutions A]
    [HasInjectiveResolutions A'] (R : A ⥤ A') [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [R.PreservesInjectiveObjects] (F : A ⥤ D) [F.Additive]
    (F' : A' ⥤ D') [F'.Additive] (R' : D ⥤ D') [R'.Additive] [PreservesFiniteLimits R']
    [PreservesFiniteColimits R'] (α : F ⋙ R' ⟶ R ⋙ F') (n : ℕ) :
    F.rightDerived n ⋙ R' ⟶ R ⋙ F'.rightDerived n :=
  letI : R'.PreservesHomology := Functor.preservesHomologyOfExact R'
  (Functor.rightDerivedCompIso F R' n).inv ≫ NatTrans.rightDerived α n ≫
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso R F' n).hom

/-- **An invertible degree-zero base-change comparison has invertible higher comparisons**: if
`α` is an isomorphism, so is `StacksTag03LR.rightDerivedBaseChangeMap R F F' R' α n` for every
`n`. -/
theorem isIso_rightDerivedBaseChangeMap [HasInjectiveResolutions A]
    [HasInjectiveResolutions A'] (R : A ⥤ A') [R.Additive] [PreservesFiniteLimits R]
    [PreservesFiniteColimits R] [R.PreservesInjectiveObjects] (F : A ⥤ D) [F.Additive]
    (F' : A' ⥤ D') [F'.Additive] (R' : D ⥤ D') [R'.Additive] [PreservesFiniteLimits R']
    [PreservesFiniteColimits R'] (α : F ⋙ R' ⟶ R ⋙ F') [IsIso α] (n : ℕ) :
    IsIso (rightDerivedBaseChangeMap R F F' R' α n) := by
  let : R'.PreservesHomology := Functor.preservesHomologyOfExact R'
  have : IsIso (NatTrans.rightDerived α n) :=
    inferInstanceAs (IsIso (Functor.rightDerivedIsoOfNatIso (asIso α) n).hom)
  show IsIso ((Functor.rightDerivedCompIso F R' n).inv ≫ NatTrans.rightDerived α n ≫
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso R F' n).hom)
  infer_instance

end StacksTag03LR

/-! ### The cartesian square of algebraic spaces -/

namespace AlgebraicGeometry.Space

open Stacks.Topos.AbelianPushforward

universe uu

variable (B : BigFppfSite.{uu}) (S : Scheme.{uu}) (hS : B.Contains S)
    {X X' Y Y' : AlgebraicSpaces B S hS} (i : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)

/-- **The canonical base-change 2-cell of a cartesian square, for abelian sheaves.**  The
adjunctions of the abelian inverse and direct images of `i` and of `g` turn the direct-image
comparison `i_* f_* ≅ f'_* g_*` of the square into a 2-cell

`f_{small,*} ∘ g_{small}^{-1} ⟶ i_{small}^{-1} ∘ f'_{small,*}`

of functors on abelian sheaves, its mate; the abelian counterpart of
`AlgebraicGeometry.Space.properBaseChangeMap`. -/
noncomputable def smallEtaleAbelianBaseChangeMap (sq : IsPullback i f' f g) :
    abelianPushforward (SmallEtale.topology B S hS X.obj) (smallToposMorphism B S hS f) ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS g) ⟶
      Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        abelianPushforward (SmallEtale.topology B S hS X'.obj) (smallToposMorphism B S hS f') :=
  (mateEquiv (abelianInverseImageAdjPushforward (SmallEtale.topology B S hS X'.obj)
        (smallToposMorphism B S hS i))
      (abelianInverseImageAdjPushforward (SmallEtale.topology B S hS Y'.obj)
        (smallToposMorphism B S hS g))).symm
    (TwoSquare.mk _ _ _ _
      (smallEtaleAbelianPushforwardCommSquareIso B S hS i f' f g sq.w).hom)

/-- The cube identity of
`Stacks.Topos.AbelianPushforward.abelianPushforward_coefficientCube_eq` at the morphisms of small
étale topoi of the square. -/
private theorem smallEtaleAbelian_coefficientCube_eq (sq : IsPullback i f' f g) :
    (((mateEquiv (abelianInverseImageAdjPushforward (SmallEtale.topology B S hS X'.obj)
              (smallToposMorphism B S hS i))
            (smallToposMorphism B S hS i).adj
            (TwoSquare.mk _ _ _ _
              (Sites.abelianInverseImage_forgetIso (smallToposMorphism B S hS i)).inv)).vComp
          (TwoSquare.mk _ _ _ _
            (smallEtalePushforwardCommSquareIso B S hS i f' f g sq.w).hom)).whiskerRight
        (abelianPushforward_forgetIso (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f)).hom).whiskerLeft
      (abelianPushforward_forgetIso (SmallEtale.topology B S hS X'.obj)
        (smallToposMorphism B S hS f')).inv =
    (TwoSquare.mk _ _ _ _
          (smallEtaleAbelianPushforwardCommSquareIso B S hS i f' f g sq.w).hom).vComp
      (mateEquiv (abelianInverseImageAdjPushforward (SmallEtale.topology B S hS Y'.obj)
          (smallToposMorphism B S hS g))
        (smallToposMorphism B S hS g).adj
        (TwoSquare.mk _ _ _ _
          (Sites.abelianInverseImage_forgetIso (smallToposMorphism B S hS g)).inv)) :=
  abelianPushforward_coefficientCube_eq
    (smallToposMorphism B S hS i) (smallToposMorphism B S hS f)
    (smallToposMorphism B S hS f') (smallToposMorphism B S hS g)
    (smallEtalePushforwardCommSquareIso B S hS i f' f g sq.w)

/-- **The abelian base-change 2-cell of a cartesian square with étale bottom arrow is an
isomorphism.** -/
theorem isIso_smallEtaleAbelianBaseChangeMap (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso (smallEtaleAbelianBaseChangeMap B S hS i f' f g sq) := by
  have : IsIso ((mateEquiv (smallToposMorphism B S hS i).adj
      (smallToposMorphism B S hS g).adj).symm
      (TwoSquare.mk _ _ _ _
        (smallEtalePushforwardCommSquareIso B S hS i f' f g sq.w).hom)).natTrans :=
    isIso_properBaseChangeMap B S hS i f' f g sq hg
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (abelianInverseImageAdjPushforward _ (smallToposMorphism B S hS i))
    (abelianInverseImageAdjPushforward _ (smallToposMorphism B S hS g))
    (smallToposMorphism B S hS i).adj (smallToposMorphism B S hS g).adj
    (TwoSquare.mk _ _ _ _
      (Sites.abelianInverseImage_forgetIso (smallToposMorphism B S hS i)).inv)
    (TwoSquare.mk _ _ _ _
      (Sites.abelianInverseImage_forgetIso (smallToposMorphism B S hS g)).inv)
    (abelianPushforward_forgetIso _ (smallToposMorphism B S hS f)).hom
    (abelianPushforward_forgetIso _ (smallToposMorphism B S hS f')).inv
    (TwoSquare.mk _ _ _ _
      (smallEtaleAbelianPushforwardCommSquareIso B S hS i f' f g sq.w).hom)
    (TwoSquare.mk _ _ _ _
      (smallEtalePushforwardCommSquareIso B S hS i f' f g sq.w).hom)
    (smallEtaleAbelian_coefficientCube_eq B S hS i f' f g sq)

/-- **The canonical comparison of higher direct images of a cartesian square, for abelian
sheaves.**  In degree `n` it is

`(R^n f_{small,*} ℱ)|_{Y'} ⟶ R^n f'_{small,*}(ℱ|_{X'})`,

naturally in the abelian sheaf `ℱ`: the degree-`n` comparison
`StacksTag03LR.rightDerivedBaseChangeMap` of the degree-zero 2-cell
`AlgebraicGeometry.Space.smallEtaleAbelianBaseChangeMap`. -/
noncomputable def smallEtaleAbelianHigherBaseChangeMap (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (n : ℕ) :
    (abelianPushforward (SmallEtale.topology B S hS X.obj)
          (smallToposMorphism B S hS f)).rightDerived n ⋙
        Sites.abelianInverseImage (smallToposMorphism B S hS g) ⟶
      Sites.abelianInverseImage (smallToposMorphism B S hS i) ⋙
        (abelianPushforward (SmallEtale.topology B S hS X'.obj)
          (smallToposMorphism B S hS f')).rightDerived n :=
  haveI := preservesInjectiveObjects_abelianInverseImage B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  haveI := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS i)
  haveI := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS g)
  StacksTag03LR.rightDerivedBaseChangeMap _ _ _ _
    (smallEtaleAbelianBaseChangeMap B S hS i f' f g sq) n

/-- **Étale base change for higher direct images.**  For a cartesian square of algebraic spaces
over `S`

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

with `g` étale, and for every `n`, the canonical comparison of higher direct images of abelian
sheaves on the small étale sites is an isomorphism: `R^n f'_{small,*}(ℱ|_{X'})` and
`(R^n f_{small,*} ℱ)|_{Y'}` are identified by it, naturally in the abelian sheaf `ℱ`. -/
@[stacks 03LR "part (2): for every abelian sheaf and every degree n, the canonical comparison
(R^n f_{small,*} F)|_{Y'} ⟶ R^n f'_{small,*}(F|_{X'}) of higher direct images is an isomorphism"]
theorem isIso_smallEtaleAbelianHigherBaseChangeMap (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) (n : ℕ) :
    IsIso (smallEtaleAbelianHigherBaseChangeMap B S hS i f' f g sq hg n) := by
  have := preservesInjectiveObjects_abelianInverseImage B S hS i
    (isEtale_of_isPullback B S hS f' i g f sq.flip hg)
  have := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS i)
  have := StacksTag03LR.abelianInverseImage_additive (smallToposMorphism B S hS g)
  have := isIso_smallEtaleAbelianBaseChangeMap B S hS i f' f g sq hg
  exact StacksTag03LR.isIso_rightDerivedBaseChangeMap _ _ _ _
    (smallEtaleAbelianBaseChangeMap B S hS i f' f g sq) n

/-- **Étale base change on the small étale sites.**  For a cartesian square of algebraic spaces
over `S`

```
X' --i--> X
|f'       |f
Y' --g--> Y
```

with `g` étale, the following three assertions hold. First, the canonical base-change 2-cell
`f_{small,*} ∘ g_{small}^{-1} ⟶ i_{small}^{-1} ∘ f'_{small,*}` of sheaves of sets is invertible,
which is `f'_{small,*}(ℱ|_{X'}) = (f_{small,*}ℱ)|_{Y'}` naturally in `ℱ`. Second,
`(f')_{small}^{-1}(𝒢|_{Y'}) = (f_{small}^{-1}𝒢)|_{X'}`. Third, in every degree `n` the canonical
comparison `(R^n f_{small,*} ℱ)|_{Y'} ⟶ R^n f'_{small,*}(ℱ|_{X'})` of higher direct images of
abelian sheaves is invertible.

The second conjunct is stated as `Nonempty` of an isomorphism of functors; the canonical one is
`AlgebraicGeometry.Space.smallEtaleInverseImageSquareIso`. -/
@[stacks 03LR "the whole statement as one conjunction, in the source's order: part (1), that the \
canonical base-change 2-cell of sheaves of sets is an isomorphism, i.e. f'_* (F|_X') = (f_* F)|_Y'; \
its inverse-image footnote, (f')^{-1}(G|_Y') = (f^{-1} G)|_X'; and part (2), that for every degree \
n the canonical comparison (R^n f_* F)|_Y' -> R^n f'_* (F|_X') of higher direct images of abelian \
sheaves is an isomorphism"]
theorem smallEtalePushforwardEtaleBaseChange_allParts (sq : IsPullback i f' f g)
    (hg : IsEtale B S hS g.hom) :
    IsIso (properBaseChangeMap B S hS f g f' i sq) ∧
      Nonempty ((smallToposMorphism B S hS g).inverseImage ⋙
            (smallToposMorphism B S hS f').inverseImage ≅
          (smallToposMorphism B S hS f).inverseImage ⋙
            (smallToposMorphism B S hS i).inverseImage) ∧
      ∀ n : ℕ, IsIso (smallEtaleAbelianHigherBaseChangeMap B S hS i f' f g sq hg n) :=
  ⟨isIso_properBaseChangeMap B S hS i f' f g sq hg,
    ⟨smallEtaleInverseImageSquareIso B S hS i f' f g sq⟩,
    fun n => isIso_smallEtaleAbelianHigherBaseChangeMap B S hS i f' f g sq hg n⟩

end AlgebraicGeometry.Space

end
