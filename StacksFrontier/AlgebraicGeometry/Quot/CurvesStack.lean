module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.StackOfSpacesGroupoid
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Subcanonical
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization

/-!
# The stack of curves (Stacks 0D52)

The category `Curves` of families of curves of Stacks 0D4Z — flat, proper, finitely presented
morphisms of relative dimension at most one from an algebraic space to a scheme, with cartesian
squares as morphisms — is a stack in groupoids over the big fppf site of schemes.

## Main definitions

* `AlgebraicGeometry.isCurveSpace`: the property of an algebraic space over a scheme that its
  structure morphism is of finite presentation, flat, proper and of relative dimension at most
  one.
* `AlgebraicGeometry.curveFamilyEquivalence`: the category of families of curves is equivalent,
  over the big fppf site of `Spec(ℤ)`, to the category of algebraic spaces over varying base
  schemes with that property and with cartesian squares as morphisms.

## Main results

* `AlgebraicGeometry.cartesianCurveSpacesProjection_isStackInGroupoids`: algebraic spaces over
  varying base schemes of the big fppf site of a scheme `S` which are finitely presented, flat,
  proper and of relative dimension at most one, with cartesian squares as morphisms, form a stack
  in groupoids.
* `AlgebraicGeometry.curvesProjection_isStack`: the category of families of curves is a stack over
  the big fppf site of schemes (Stacks 026F).
* `AlgebraicGeometry.curvesProjection_isStackInGroupoids`: **Stacks 0D52**, the category of
  families of curves is a stack in groupoids over the big fppf site of schemes.

## Implementation notes

The source uses the embedding (0D50) of families of curves into `Spaces'_{fp, flat, proper}`, the
description of its image by the condition of relative dimension at most one, and Stacks 0D1G for
the larger category; it is left to check that the condition descends along an fppf covering, which
is Stacks 04NS. Here the same three inputs are assembled in the order the library provides them:
the condition of relative dimension at most one is added to the three conditions of
`Spaces'_{fp, flat, proper}`, and the category of cartesian morphisms of the resulting full
subcategory of the stack of finite-type families of Stacks 04UD is a stack in groupoids by
`CategoryTheory.Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict`, exactly as Stacks
0D1G is proved in `StacksFrontier/AlgebraicGeometry/Quot/StackOfSpacesGroupoid.lean`. Its two inputs
are base change of the condition (Stacks 04NS part (1),
`AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback'`) and its locality on the base
(`AlgebraicGeometry.SpacesDescent.hasRelativeDimensionLE_of_forall_isPullback_of_mem_topology`).

That category is the category of families of curves, presented as a structure in
`StacksFrontier/AlgebraicGeometry/Quot/CurveFamilies.lean`, up to an equivalence over the big fppf
site of `Spec(ℤ)` which is the identity on underlying data
(`AlgebraicGeometry.curveFamilyEquivalence`), so the families of curves form a stack over that site
by Stacks 042W. The projection of Stacks 0D4Z lands in the big fppf site itself rather than in its
slice over `Spec(ℤ)`; the slice over a terminal object of a subcanonical site is harmless, and the
stack property passes to the composite with the forgetful functor by Stacks 04WV. Finally a stack
whose structure functor is fibred in groupoids (Stacks 0D51) is a stack in groupoids
(`CategoryTheory.Functor.IsStack.isStackInGroupoids`).

The conclusion is stated for covering families indexed in every universe `w`.

## References

* [Stacks Project, Tag 0D52](https://stacks.math.columbia.edu/tag/0D52)
* [Stacks Project, Tag 0D1G](https://stacks.math.columbia.edu/tag/0D1G)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

open SpacesDescent

section Spaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An algebraic space over a scheme in the big fppf site of `S` whose structure morphism is of
finite presentation, flat, proper and of relative dimension at most one: the condition cutting
out families of curves among algebraic spaces over varying base schemes. -/
abbrev isCurveSpace : ObjectProperty
    (Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
  fun X ↦ isProperFlatSpace B S hS X ∧ Space.HasRelativeDimensionLE 1 B S hS X.hom

/-- A family of curves is of finite type over its base. -/
theorem isCurveSpace_le_isFiniteTypeSpace : isCurveSpace B S hS ≤ isFiniteTypeSpace B S hS :=
  fun _ h => h.1.2.2.2.1

/-- **The condition of being a family of curves is stable under base change.** The source of a
strongly cartesian morphism whose target is a family of curves is a family of curves: the three
conditions of `Spaces'_{fp, flat, proper}` by Stacks 03XR, 03MO and 04WP, and the bound on the
relative dimension by Stacks 04NS part (1), the structure morphism of the source being a base
change of that of the target (Stacks 04U9). -/
theorem isCurveSpace_of_isStronglyCartesian {V U : BigFppfOver B S hS}
    {y x : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    (f : V ⟶ U) (φ : y ⟶ x) (h : (spacesProjection B S hS).IsStronglyCartesian f φ)
    (hx : isCurveSpace B S hS x) : isCurveSpace B S hS y := by
  refine ⟨isProperFlatSpace_of_isStronglyCartesian B S hS f φ h hx.1, fun x' => ?_⟩
  obtain ⟨e, he, hAt⟩ := hx.2 (Space.pointsMap B S hS _ φ.left.hom x')
  exact ⟨e, he, (Space.hasRelativeDimensionAt_iff_of_isPullback' B S hS e
    (isPullback_hom_of_isStronglyCartesian_over B S hS f φ h) x.left.property
    (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _)
    (Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hx.1.1.1) x').2 hAt⟩

/-- **The condition of being a family of curves is fppf local on the base.** Its first three
conditions are local by Stacks 041V, 041W and 0422
(`AlgebraicGeometry.isProperFlatSpace_of_forall_isPullback`), and the bound on the relative
dimension by Stacks 04NS part (1) read on points
(`AlgebraicGeometry.SpacesDescent.hasRelativeDimensionLE_of_forall_isPullback_of_mem_topology`). -/
theorem isCurveSpace_of_forall_isPullback {ι : Type*}
    (x : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hxft : isFiniteTypeSpace B S hS x)
    (y : ι → Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) (φ : ∀ i, y i ⟶ x)
    (hcov : Sieve.generate (Presieve.ofArrows (fun i => (y i).right) (fun i => (φ i).right)) ∈
      BigFppfOver.topology B S hS x.right)
    (hsq : ∀ i, IsPullback (φ i).left.hom (y i).hom x.hom (yoneda.map (φ i).right))
    (hy : ∀ i, isCurveSpace B S hS (y i)) : isCurveSpace B S hS x :=
  ⟨isProperFlatSpace_of_forall_isPullback B S hS x y φ hcov hsq fun i => (hy i).1,
    hasRelativeDimensionLE_of_forall_isPullback_of_mem_topology 1 x.left.property x.hom hxft.1
      _ _ hcov _ (fun i => (y i).left.property) _ _ hsq (fun i => (hy i).1.2.2.2.1.1)
      fun i => (hy i).2⟩

/-- Algebraic spaces over varying base schemes in the big fppf site of `S` which are finitely
presented, flat, proper and of relative dimension at most one over their base, with only the
cartesian squares as morphisms. -/
abbrev CartesianCurveSpaces :=
  WideSubcategory
    ((stronglyCartesianOver (spacesProjection B S hS)).inverseImage (isCurveSpace B S hS).ι)

/-- The projection taking a family of curves, presented as an algebraic space over a varying base
scheme, to its base scheme. -/
abbrev cartesianCurveSpacesProjection : CartesianCurveSpaces B S hS ⥤ BigFppfOver B S hS :=
  wideSubcategoryInclusion _ ⋙ (isCurveSpace B S hS).ι ⋙ spacesProjection B S hS

/-- Algebraic spaces over varying base schemes of the big fppf site of `S` which are finitely
presented, flat, proper and of relative dimension at most one over their base, with cartesian
squares as morphisms, form a stack in groupoids over the big fppf site of `S`. This is the proof
of Stacks 0D1G (`AlgebraicGeometry.cartesianProperFlatProjection_isStackInGroupoids`) with the
bound on the relative dimension added to the three conditions, as the proof of Stacks 0D52
asks. -/
theorem cartesianCurveSpacesProjection_isStackInGroupoids :
    (cartesianCurveSpacesProjection B S hS).IsStackInGroupoids.{w}
      (BigFppfOver.topology B S hS) :=
  have := spacesProjection_isFibered B S hS
  Functor.isStackInGroupoids_wideSubcategory_of_isStack_restrict (spacesProjection B S hS)
    (isFiniteTypeSpace B S hS) (closedUnderStronglyCartesian_isFiniteTypeSpace B S hS)
    (isCurveSpace B S hS) (isCurveSpace_le_isFiniteTypeSpace B S hS)
    (BigFppfOver.topology B S hS) (finiteTypeSpacesProjection_isStack_of_bootstrap B S hS)
    (fun f φ h _ hx => isCurveSpace_of_isStronglyCartesian B S hS f φ h hx)
    (fun Uᵢ fᵢ hgen x hx hxft h => by
      obtain ⟨y, φ, hcov, hsq, hy⟩ := exists_isPullback_of_isStronglyCartesian B S hS Uᵢ fᵢ hgen
        (isCurveSpace B S hS) x hx fun i => by
          obtain ⟨y, φ, hφ, -, hy⟩ := h i
          exact ⟨y, φ, hφ, hy⟩
      exact isCurveSpace_of_forall_isPullback B S hS x hxft y φ hcov hsq hy)

end Spaces

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- A family of curves, read as an algebraic space over a varying base scheme with the four
conditions of `AlgebraicGeometry.isCurveSpace`, and a cartesian square of families of curves,
read as a strongly cartesian morphism. -/
@[simps]
def curveFamilyToCartesianCurveSpaces :
    CurveFamily B hZ ⥤ CartesianCurveSpaces B integerBase hZ where
  obj X := ⟨⟨⟨X.total, X.base, X.toBase.hom⟩,
    ⟨⟨X.finitePresentation, X.flat, X.proper⟩, X.relativeDimensionLE⟩⟩⟩
  map f := ⟨ObjectProperty.homMk (CurveFamily.toCartesianProperFlatMap B hZ f).hom,
    CurveFamily.toCartesianProperFlatMap_isStronglyCartesian B hZ f⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- An algebraic space over a varying base scheme with the four conditions of
`AlgebraicGeometry.isCurveSpace`, read as a family of curves, and a strongly cartesian morphism,
read as a cartesian square of families of curves (Stacks 04U9). -/
@[simps]
def cartesianCurveSpacesToCurveFamily :
    CartesianCurveSpaces B integerBase hZ ⥤ CurveFamily B hZ where
  obj Y :=
    { base := Y.obj.obj.right
      total := Y.obj.obj.left
      toBase := ObjectProperty.homMk Y.obj.obj.hom
      flat := Y.obj.property.1.2.1
      proper := Y.obj.property.1.2.2
      finitePresentation := Y.obj.property.1.1
      relativeDimensionLE := Y.obj.property.2 }
  map {X Y} g :=
    { baseMap := g.hom.hom.right
      totalMap := g.hom.hom.left
      cartesian := (isPullback_hom_of_isStronglyCartesian B integerBase hZ
        g.hom.hom g.property).flip.of_map (ObjectProperty.ι _)
        (f := g.hom.hom.left) (g := (ObjectProperty.homMk X.obj.obj.hom :
          X.obj.obj.left ⟶ schemeSpace X.obj.obj.right))
        (h := (ObjectProperty.homMk Y.obj.obj.hom :
          Y.obj.obj.left ⟶ schemeSpace Y.obj.obj.right))
        (i := schemeSpaceMap g.hom.hom.right)
        (ObjectProperty.hom_ext _ g.hom.hom.w) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The category of families of curves, as a category of algebraic spaces.** The category of
families of curves of Stacks 0D4Z, over the big fppf site of `Spec(ℤ)`, is equivalent over that
site to the category of algebraic spaces over varying base schemes which are finitely presented,
flat, proper and of relative dimension at most one over their base, with cartesian squares as
morphisms. Both functors are the identity on underlying data, and the two composites are the
identity functors on the nose. -/
def curveFamilyEquivalence :
    BasedCategory.Equivalence (BasedCategory.ofFunctor (cartesianCurveSpacesProjection B
      integerBase hZ)) (BasedCategory.ofFunctor (curvesProjectionOver B hZ)) where
  functor := { toFunctor := cartesianCurveSpacesToCurveFamily B hZ, w := rfl }
  inverse := { toFunctor := curveFamilyToCartesianCurveSpaces B hZ, w := rfl }
  unitIso := eqToIso (BasedCategory.BasedFunctor.ext' rfl)
  counitIso := eqToIso (BasedCategory.BasedFunctor.ext' rfl)

/-- The category of families of curves is a stack over the big fppf site of `Spec(ℤ)`, through
its projection to that site: Stacks 042W applied to `AlgebraicGeometry.curveFamilyEquivalence`. -/
theorem curvesProjectionOver_isStack :
    (curvesProjectionOver B hZ).IsStack (BigFppfOver.topology B integerBase hZ) :=
  (curveFamilyEquivalence B hZ).isStack_of_isStackInGroupoids
    (cartesianCurveSpacesProjection_isStackInGroupoids.{u + 1} B integerBase hZ)

/-- **The category of families of curves is a stack** over the big fppf site of schemes, in the
sense of Stacks 026F: its projection to the base scheme is a fibred category whose morphism
presheaves are sheaves and whose descent data are effective.

The projection of Stacks 0D4Z is the projection to the slice over `Spec(ℤ)` followed by the
forgetful functor of the slice, so this is Stacks 04WV applied to
`AlgebraicGeometry.curvesProjectionOver_isStack`, the representable presheaf of `Spec(ℤ)` being a
sheaf because the fppf topology is subcanonical. -/
theorem curvesProjection_isStack : (curvesProjection B hZ).IsStack B.topology :=
  Functor.isStack_comp_forget (curvesProjectionOver B hZ)
    ((isSheaf_iff_isSheaf_of_type _ _).2
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _))
    (curvesProjectionOver_isStack B hZ)

/-- **Stacks 0D52.** The category of families of curves is a stack in groupoids over the big fppf
site of schemes, for covering families indexed in every universe.

It is a stack (`AlgebraicGeometry.curvesProjection_isStack`) whose projection is fibred in
groupoids (Stacks 0D51, `AlgebraicGeometry.curvesProjection_isFiberedInGroupoids`), and such a
stack is a stack in groupoids by the implication (3) ⟹ (1) of Stacks 02ZJ. -/
@[stacks 0D52]
theorem curvesProjection_isStackInGroupoids :
    (curvesProjection B hZ).IsStackInGroupoids.{w} B.topology :=
  (curvesProjection_isStack B hZ).isStackInGroupoids
    (curvesProjection_isFiberedInGroupoids B hZ)

end AlgebraicGeometry
