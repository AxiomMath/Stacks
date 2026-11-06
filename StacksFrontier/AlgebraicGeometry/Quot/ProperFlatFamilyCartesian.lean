module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.VaryingBase.SheafGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType

/-!
# Objects and cartesian morphisms of `Spaces'_{fp, flat, proper}`

An object of the category `Spaces'_{fp, flat, proper}` of Stacks 0D1D is a morphism `X ⟶ V` from
an algebraic space to (the presheaf represented by) a scheme of the big fppf site, which is of
finite presentation, flat and proper, and a morphism is a cartesian square. This file supplies the
vocabulary for working with such objects through their underlying presheaves: the total space, the
base and the structure morphism of an object; the object attached to a finitely presented, flat
and proper morphism; the morphism attached to a cartesian square; the base change of an object
along a morphism of schemes with its cartesian projection; and, conversely, the cartesian square
underlying a morphism.

## Main definitions

* `AlgebraicGeometry.CartesianProperFlatSpaces.mk'`: the object attached to a finitely presented,
  flat and proper morphism `X ⟶ yoneda V`.
* `AlgebraicGeometry.CartesianProperFlatSpaces.homOfIsPullback`: the morphism attached to a
  cartesian square.
* `AlgebraicGeometry.CartesianProperFlatSpaces.baseChange` and
  `AlgebraicGeometry.CartesianProperFlatSpaces.baseChangeHom`: base change along `W ⟶ V`.

## Main results

* `AlgebraicGeometry.CartesianProperFlatSpaces.isPullback_hom`: the square underlying a morphism
  is cartesian (Stacks 04U9).

## References

* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CartesianProperFlatSpaces

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The total space of a family. -/
abbrev total (x : CartesianProperFlatSpaces B S hS) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  x.obj.obj.left.obj

/-- The base scheme of a family. -/
abbrev base (x : CartesianProperFlatSpaces B S hS) : BigFppfOver B S hS :=
  x.obj.obj.right

/-- The structure morphism of a family. -/
abbrev toBase (x : CartesianProperFlatSpaces B S hS) : x.total ⟶ yoneda.obj x.base :=
  x.obj.obj.hom

/-- The total space of a family is an algebraic space. -/
theorem isAlgebraicSpace_total (x : CartesianProperFlatSpaces B S hS) :
    IsAlgebraicSpace B S hS x.total :=
  x.obj.obj.left.property

/-- The structure morphism of a family is of finite presentation. -/
theorem isFinitePresentation_toBase (x : CartesianProperFlatSpaces B S hS) :
    Space.IsFinitePresentation B S hS x.toBase :=
  x.obj.property.1

/-- The structure morphism of a family is flat. -/
theorem isFlat_toBase (x : CartesianProperFlatSpaces B S hS) :
    Space.IsFlat B S hS x.toBase :=
  x.obj.property.2.1

/-- The structure morphism of a family is proper. -/
theorem isProper_toBase (x : CartesianProperFlatSpaces B S hS) :
    Space.IsProper B S hS x.toBase :=
  x.obj.property.2.2

/-- The family attached to a finitely presented, flat and proper morphism from an algebraic space
to a scheme of the big fppf site. -/
def mk' (V : BigFppfOver B S hS) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (h : X ⟶ yoneda.obj V)
    (hfp : Space.IsFinitePresentation B S hS h) (hfl : Space.IsFlat B S hS h)
    (hpr : Space.IsProper B S hS h) : CartesianProperFlatSpaces B S hS :=
  ⟨⟨⟨⟨X, hX⟩, V, h⟩, ⟨hfp, hfl, hpr⟩⟩⟩

/-- The morphism of families attached to a cartesian square of presheaves. -/
def homOfIsPullback {x y : CartesianProperFlatSpaces B S hS} (a : x.total ⟶ y.total)
    (g : x.base ⟶ y.base) (h : IsPullback a x.toBase y.toBase (yoneda.map g)) : x ⟶ y :=
  ⟨ObjectProperty.homMk
    ({ left := ObjectProperty.homMk a, right := g, w := h.w } :
      x.obj.obj ⟶ y.obj.obj),
    SpacesDescent.isStronglyCartesian_of_isPullback g _ rfl rfl (by simp) (by simp) (by simp) h⟩

/-- The map of total spaces of `homOfIsPullback a g h` is `a`. -/
@[simp]
theorem homOfIsPullback_left {x y : CartesianProperFlatSpaces B S hS} (a : x.total ⟶ y.total)
    (g : x.base ⟶ y.base) (h : IsPullback a x.toBase y.toBase (yoneda.map g)) :
    (homOfIsPullback a g h).hom.hom.left.hom = a :=
  rfl

/-- The map of bases of `homOfIsPullback a g h` is `g`. -/
@[simp]
theorem homOfIsPullback_right {x y : CartesianProperFlatSpaces B S hS} (a : x.total ⟶ y.total)
    (g : x.base ⟶ y.base) (h : IsPullback a x.toBase y.toBase (yoneda.map g)) :
    (homOfIsPullback a g h).hom.hom.right = g :=
  rfl

/-- The morphism attached to a cartesian square lies over its base morphism. -/
instance isHomLift_homOfIsPullback {x y : CartesianProperFlatSpaces B S hS}
    (a : x.total ⟶ y.total) (g : x.base ⟶ y.base)
    (h : IsPullback a x.toBase y.toBase (yoneda.map g)) :
    (cartesianProperFlatProjection B S hS).IsHomLift g (homOfIsPullback a g h) :=
  IsHomLift.map (p := cartesianProperFlatProjection B S hS) (homOfIsPullback a g h)

/-- **Stacks 04U9 for `Spaces'_{fp, flat, proper}`.** The square of presheaves underlying a
morphism of families is cartesian. -/
theorem isPullback_hom {x y : CartesianProperFlatSpaces B S hS} (φ : x ⟶ y) :
    IsPullback φ.hom.hom.left.hom x.toBase y.toBase (yoneda.map φ.hom.hom.right) :=
  (isPullback_hom_of_isStronglyCartesian B S hS φ.hom.hom φ.property).flip

/-- The base morphism of a morphism of families lying over `f` is `f`. -/
theorem hom_right_eq {x y : CartesianProperFlatSpaces B S hS} (f : x.base ⟶ y.base)
    (φ : x ⟶ y) [hφ : (cartesianProperFlatProjection B S hS).IsHomLift f φ] :
    φ.hom.hom.right = f :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ (cartesianProperFlatProjection B S hS) x y f φ hφ).symm

/-- Two morphisms of families agree when their maps of total spaces and of bases agree. -/
theorem hom_ext' {x y : CartesianProperFlatSpaces B S hS} {φ ψ : x ⟶ y}
    (hl : φ.hom.hom.left.hom = ψ.hom.hom.left.hom) (hr : φ.hom.hom.right = ψ.hom.hom.right) :
    φ = ψ :=
  WideSubcategory.hom_ext _
    (ObjectProperty.hom_ext _ (Comma.hom_ext _ _ (ObjectProperty.hom_ext _ hl) hr))

/-- The map of total spaces of a composite is the composite of the maps of total spaces. -/
@[simp]
theorem comp_left {x y z : CartesianProperFlatSpaces B S hS} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (φ ≫ ψ).hom.hom.left.hom = φ.hom.hom.left.hom ≫ ψ.hom.hom.left.hom :=
  rfl

/-- The map of bases of a composite is the composite of the maps of bases. -/
@[simp]
theorem comp_right {x y z : CartesianProperFlatSpaces B S hS} (φ : x ⟶ y) (ψ : y ⟶ z) :
    (φ ≫ ψ).hom.hom.right = φ.hom.hom.right ≫ ψ.hom.hom.right :=
  rfl

/-- The map of total spaces of the identity of a family is the identity. -/
@[simp]
theorem id_left (x : CartesianProperFlatSpaces B S hS) :
    (𝟙 x : x ⟶ x).hom.hom.left.hom = 𝟙 x.total :=
  rfl

/-- The map of bases of the identity of a family is the identity. -/
@[simp]
theorem id_right (x : CartesianProperFlatSpaces B S hS) :
    (𝟙 x : x ⟶ x).hom.hom.right = 𝟙 x.base :=
  rfl

/-- Flatness of a base change. -/
theorem isFlat_of_isPullback'
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (sq : IsPullback g' f' f g) (hf : Space.IsFlat B S hS f) :
    Space.IsFlat B S hS f' :=
  (Space.isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (Space.isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- Properness of a base change. -/
theorem isProper_of_isPullback'
    {X' X Y' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (hY' : IsAlgebraicSpace B S hS Y') (hY : IsAlgebraicSpace B S hS Y)
    (sq : IsPullback g' f' f g) (hf : Space.IsProper B S hS f) :
    Space.IsProper B S hS f' :=
  (Space.isProper_isStableUnderBaseChange B S hS).of_isPullback
    (Space.isPullback_homMk B S hS hX hY' hY hX' sq) hf

/-- The family attached to a cartesian square whose right edge is a family: the source of the
square, with its left edge as structure morphism, is again finitely presented, flat and proper. -/
def ofIsPullback (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) (h : X ⟶ yoneda.obj W)
    (a : X ⟶ y.total) (g : W ⟶ y.base) (sq : IsPullback a h y.toBase (yoneda.map g)) :
    CartesianProperFlatSpaces B S hS :=
  mk' W X hX h
    (Space.IsFinitePresentation.of_isPullback B S hS hX y.isAlgebraicSpace_total
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS _) sq
      y.isFinitePresentation_toBase)
    (isFlat_of_isPullback' hX y.isAlgebraicSpace_total (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS _) sq y.isFlat_toBase)
    (isProper_of_isPullback' hX y.isAlgebraicSpace_total (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS _) sq y.isProper_toBase)

/-- The cartesian morphism from `AlgebraicGeometry.CartesianProperFlatSpaces.ofIsPullback` to the
family it is a base change of. -/
def ofIsPullbackHom (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) (h : X ⟶ yoneda.obj W)
    (a : X ⟶ y.total) (g : W ⟶ y.base) (sq : IsPullback a h y.toBase (yoneda.map g)) :
    ofIsPullback y X hX h a g sq ⟶ y :=
  homOfIsPullback (x := ofIsPullback y X hX h a g sq) a g sq

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ProperFlatFamilyCartesian :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_ProperFlatFamilyCartesian
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The base change of a family along a morphism of schemes. -/
noncomputable def baseChange (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (g : W ⟶ y.base) : CartesianProperFlatSpaces B S hS :=
  ofIsPullback y (pullback y.toBase (yoneda.map g))
    (isAlgebraicSpace_pullback B S hS _ _ y.isAlgebraicSpace_total
      (isAlgebraicSpace_yoneda B S hS W) (isAlgebraicSpace_yoneda B S hS _))
    (pullback.snd _ _) (pullback.fst _ _) g (IsPullback.of_hasPullback _ _)

/-- The cartesian projection from the base change of a family to the family. -/
noncomputable def baseChangeHom (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (g : W ⟶ y.base) : baseChange y g ⟶ y :=
  ofIsPullbackHom y _ _ _ _ g _

/-- The base of the base change of a family along `g : W ⟶ y.base` is `W`. -/
@[simp]
theorem projection_obj_baseChange (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (g : W ⟶ y.base) : (cartesianProperFlatProjection B S hS).obj (baseChange y g) = W :=
  rfl

/-- The map of total spaces of the base change projection is the first pullback projection. -/
@[simp]
theorem baseChangeHom_left (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (g : W ⟶ y.base) :
    (baseChangeHom y g).hom.hom.left.hom = pullback.fst y.toBase (yoneda.map g) :=
  rfl

/-- The map of bases of the base change projection along `g` is `g`. -/
@[simp]
theorem baseChangeHom_right (y : CartesianProperFlatSpaces B S hS) {W : BigFppfOver B S hS}
    (g : W ⟶ y.base) : (baseChangeHom y g).hom.hom.right = g :=
  rfl

/-- The projection from a base change lies over the morphism of bases. -/
instance isHomLift_baseChangeHom (y : CartesianProperFlatSpaces B S hS)
    {W : BigFppfOver B S hS} (g : W ⟶ y.base) :
    (cartesianProperFlatProjection B S hS).IsHomLift g (baseChangeHom y g) :=
  isHomLift_homOfIsPullback (x := baseChange y g) _ _ (IsPullback.of_hasPullback _ _)

end AlgebraicGeometry.CartesianProperFlatSpaces

end
