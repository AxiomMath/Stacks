module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeStack
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# The chosen pullback of the prestack of algebraic spaces, explicitly

Let `S` be a scheme contained in a big fppf site `B`. The comma category of Stacks 04U8 is a
fibred category over the big fppf site of `S` (`AlgebraicGeometry.spacesProjection_isFibered`,
Stacks 04UA condition (1)), so every object `X` of the fibre over `U` and every morphism
`g : V ⟶ U` of base schemes have a *chosen* pullback `CategoryTheory.Functor.pullbackFiber`,
supplied abstractly by the fibred structure. This file identifies that chosen pullback with the
explicit presheaf fibre product `(yoneda.obj V) ×_{yoneda.obj U} X`, and does the same one level
up for the finite-type subcategory of Stacks 04UD.

## Main definitions

* `AlgebraicGeometry.spacesBaseChange`, the explicit base change of an object of the comma
  category of Stacks 04U8 along a morphism of base schemes;
* `AlgebraicGeometry.spacesBaseChangeMap`, its projection to the original object;
* `AlgebraicGeometry.pullbackFiberSpacesBaseChangeIso`, the comparison of the chosen pullback
  with it;
* `AlgebraicGeometry.finiteTypeSpacesBaseChange` and
  `AlgebraicGeometry.pullbackFiberFiniteTypeSpacesBaseChangeIso`, the same for the finite-type
  subcategory.

## Main results

* `AlgebraicGeometry.spacesBaseChangeMap_isStronglyCartesian`: the explicit base change is
  strongly cartesian, which is Stacks 04U9 applied to the pullback square it is built from;
* `AlgebraicGeometry.isFiniteTypeSpace_spacesBaseChange`: the explicit base change of a
  finite-type object is of finite type.

## Implementation notes

`StacksFrontier/AlgebraicGeometry/Spaces/Prestack.lean` already carries this comparison, but every
declaration of that file is `private`, so no other module can name it; the proofs here are the
same short arguments, re-run in public form. The private declarations there are left alone.

The comparison itself is `CategoryTheory.Functor.fiberIsoOfCartesian`: both the chosen pullback
and the explicit one carry a cartesian morphism over `g` to the same object, and two cartesian
lifts of one morphism are canonically isomorphic in the fibre.

## References

* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
* [Stacks Project, Tag 04UA](https://stacks.math.columbia.edu/tag/04UA)
* [Stacks Project, Tag 04UD](https://stacks.math.columbia.edu/tag/04UD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The converse half of Stacks 04U9.** A morphism of the comma category of Stacks 04U8 whose
underlying square of presheaves is cartesian is strongly cartesian for the projection to the base
scheme.

`AlgebraicGeometry.isPullback_hom_of_isStronglyCartesian` is the other direction; both are read
off `AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff`. -/
theorem isStronglyCartesian_of_isPullback
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (h : IsPullback A.hom m.left.hom (yoneda.map m.right) C.hom) :
    (spacesProjection B S hS).IsStronglyCartesian m.right m := by
  rw [spacesProjection_isStronglyCartesian_iff]
  have he : pullback.lift A.hom m.left.hom m.w.symm = h.isoPullback.hom :=
    pullback.hom_ext (by rw [pullback.lift_fst, h.isoPullback_hom_fst])
      (by rw [pullback.lift_snd, h.isoPullback_hom_snd])
  have hiso : IsIso (pullback.lift A.hom m.left.hom m.w.symm) := by
    rw [he]; infer_instance
  exact (ObjectProperty.isIso_hom_iff _).1 hiso

/-- The explicit base change of an object of the comma category of Stacks 04U8 along a morphism
of base schemes: the presheaf fibre product of its structure morphism with the Yoneda image of
the morphism, over the new base. -/
noncomputable def spacesBaseChange {V : BigFppfOver B S hS}
    (A : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (g : V ⟶ A.right) :
    Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  ⟨⟨pullback (yoneda.map g) A.hom,
      isAlgebraicSpace_pullback B S hS (yoneda.map g) A.hom
        (isAlgebraicSpace_yoneda B S hS V) A.left.property
        (isAlgebraicSpace_yoneda B S hS A.right)⟩,
    V, pullback.fst (yoneda.map g) A.hom⟩

/-- The projection of the explicit base change onto the object it was formed from. -/
noncomputable def spacesBaseChangeMap {V : BigFppfOver B S hS}
    (A : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (g : V ⟶ A.right) :
    spacesBaseChange B S hS A g ⟶ A where
  left := ObjectProperty.homMk (pullback.snd (yoneda.map g) A.hom)
  right := g
  w := pullback.condition.symm

/-- The projection of the explicit base change lies over `g`. -/
@[simp]
lemma spacesBaseChangeMap_right {V : BigFppfOver B S hS}
    {A : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (g : V ⟶ A.right) : (spacesBaseChangeMap B S hS A g).right = g := rfl

/-- **The explicit base change is strongly cartesian.** This is Stacks 04U9 read at the pullback
square the base change is built from: the comparison of the source with the fibre product is the
identity. -/
theorem spacesBaseChangeMap_isStronglyCartesian {V : BigFppfOver B S hS}
    (A : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (g : V ⟶ A.right) :
    (spacesProjection B S hS).IsStronglyCartesian g (spacesBaseChangeMap B S hS A g) :=
  isStronglyCartesian_of_isPullback B S hS (spacesBaseChangeMap B S hS A g)
    (IsPullback.of_hasPullback (yoneda.map g) A.hom)

/-- The explicit base change carries a cartesian morphism to the object it was formed from. -/
theorem spacesBaseChangeMap_isCartesian {V : BigFppfOver B S hS}
    (A : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (g : V ⟶ A.right) :
    (spacesProjection B S hS).IsCartesian g (spacesBaseChangeMap B S hS A g) :=
  let := spacesBaseChangeMap_isStronglyCartesian B S hS A g
  Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian _ g _

/-- **The chosen pullback of the prestack of algebraic spaces is the explicit presheaf fibre
product.** This is the public form of the comparison that
`StacksFrontier/AlgebraicGeometry/Spaces/Prestack.lean` keeps private. -/
noncomputable def pullbackFiberSpacesBaseChangeIso
    [(spacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    (X : (spacesProjection B S hS).Fiber U) (g : V ⟶ U) :
    Functor.pullbackFiber (spacesProjection B S hS) X g ≅
      ⟨spacesBaseChange B S hS X.1 (g ≫ eqToHom X.2.symm), rfl⟩ :=
  Functor.fiberIsoOfCartesian (p := spacesProjection B S hS) g
    (Functor.IsPreFibered.pullbackMap X.2 g)
    (spacesBaseChangeMap B S hS X.1 (g ≫ eqToHom X.2.symm))
    (Functor.IsPreFibered.pullbackMap.IsCartesian X.2 g)
    (by
      have h : (spacesProjection B S hS).IsCartesian (g ≫ eqToHom X.2.symm)
          (spacesBaseChangeMap B S hS X.1 (g ≫ eqToHom X.2.symm)) :=
        spacesBaseChangeMap_isCartesian B S hS X.1 (g ≫ eqToHom X.2.symm)
      obtain ⟨X0, hX0⟩ := X
      subst hX0
      simpa using h)

/-- **The explicit base change of a finite-type object is of finite type.** This is the source's
appeal to Stacks 03XH inside the proof of Stacks 04UD, read at the explicit pullback square
rather than at an abstract strongly cartesian morphism. -/
theorem isFiniteTypeSpace_spacesBaseChange {V : BigFppfOver B S hS}
    (A : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (g : V ⟶ A.right) (hA : isFiniteTypeSpace B S hS A) :
    isFiniteTypeSpace B S hS (spacesBaseChange B S hS A g) :=
  let hc := spacesBaseChangeMap_isStronglyCartesian B S hS A g
  ⟨(Space.isLocallyOfFiniteType_isStableUnderBaseChange B S hS).of_isPullback
      (isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS
        (spacesBaseChangeMap B S hS A g) hc) hA.1,
    Space.isQuasiCompact_of_isPullback B S hS
      (isPullback_hom_of_isStronglyCartesian B S hS (spacesBaseChangeMap B S hS A g) hc).flip hA.2⟩

/-- The explicit base change of a finite-type algebraic space over a varying base scheme. -/
noncomputable def finiteTypeSpacesBaseChange {V : BigFppfOver B S hS}
    (A : FiniteTypeSpaces B S hS) (g : V ⟶ A.obj.right) : FiniteTypeSpaces B S hS :=
  ⟨spacesBaseChange B S hS A.obj g, isFiniteTypeSpace_spacesBaseChange B S hS A.obj g A.property⟩

/-- The projection of the explicit base change of a finite-type object onto that object. -/
noncomputable def finiteTypeSpacesBaseChangeMap {V : BigFppfOver B S hS}
    (A : FiniteTypeSpaces B S hS) (g : V ⟶ A.obj.right) :
    finiteTypeSpacesBaseChange B S hS A g ⟶ A :=
  ObjectProperty.homMk (spacesBaseChangeMap B S hS A.obj g)

/-- The explicit base change of a finite-type object carries a cartesian morphism to it, for the
projection of Stacks 04UD. -/
theorem finiteTypeSpacesBaseChangeMap_isCartesian {V : BigFppfOver B S hS}
    (A : FiniteTypeSpaces B S hS) (g : V ⟶ A.obj.right) :
    (finiteTypeSpacesProjection B S hS).IsCartesian g
      (finiteTypeSpacesBaseChangeMap B S hS A g) :=
  Functor.isCartesian_of_isCartesian_map_ι (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) g (finiteTypeSpacesBaseChangeMap B S hS A g)
    (spacesBaseChangeMap_isCartesian B S hS A.obj g)

/-- **The chosen pullback of the stack of finite-type algebraic spaces is the explicit presheaf
fibre product.** The finite-type form of
`AlgebraicGeometry.pullbackFiberSpacesBaseChangeIso`. -/
noncomputable def pullbackFiberFiniteTypeSpacesBaseChangeIso
    [(finiteTypeSpacesProjection B S hS).IsFibered]
    {U V : BigFppfOver B S hS}
    (X : (finiteTypeSpacesProjection B S hS).Fiber U) (g : V ⟶ U) :
    Functor.pullbackFiber (finiteTypeSpacesProjection B S hS) X g ≅
      ⟨finiteTypeSpacesBaseChange B S hS X.1 (g ≫ eqToHom X.2.symm), rfl⟩ :=
  Functor.fiberIsoOfCartesian (p := finiteTypeSpacesProjection B S hS) g
    (Functor.IsPreFibered.pullbackMap X.2 g)
    (finiteTypeSpacesBaseChangeMap B S hS X.1 (g ≫ eqToHom X.2.symm))
    (Functor.IsPreFibered.pullbackMap.IsCartesian X.2 g)
    (by
      have h : (finiteTypeSpacesProjection B S hS).IsCartesian (g ≫ eqToHom X.2.symm)
          (finiteTypeSpacesBaseChangeMap B S hS X.1 (g ≫ eqToHom X.2.symm)) :=
        finiteTypeSpacesBaseChangeMap_isCartesian B S hS X.1 (g ≫ eqToHom X.2.symm)
      obtain ⟨X0, hX0⟩ := X
      subst hX0
      simpa using h)

end AlgebraicGeometry

end
