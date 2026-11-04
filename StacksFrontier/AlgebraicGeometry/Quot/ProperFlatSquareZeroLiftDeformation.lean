module

public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.SpacesDefoThickeningTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.ThickeningProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedSubspaceIdeal

/-!
# Lifts in `Spaces'_{fp, flat, proper}` along a square-zero thickening are flat deformations

Let `i : T ⟶ T'` be a square-zero closed immersion of the big fppf site of `S` and let `x` be an
object of `Spaces'_{fp, flat, proper}` over `T`, a finitely presented, flat and proper family
`X ⟶ T`. A *lift* of `x` along `i` is an object `y` under `x` whose arrow `x ⟶ y` lies over `i`.
Since the morphisms of `Spaces'_{fp, flat, proper}` are the cartesian squares, `y` is a flat family
`X' ⟶ T'` with a cartesian square

```
X ---> X'
|      |
v      v
T ---> T'
```

which is a flat deformation of `X ⟶ T ⊆ T'` over `T'` in the sense of Stacks 0D17
(`AlgebraicGeometry.Space.FlatThickeningDeformation.Deformation`). This file proves that this
identifies the isomorphism classes of lifts with the isomorphism classes of flat deformations.
Surjectivity is the part with content: a flat deformation of `X ⟶ T` over `T'` is finitely
presented and proper over `T'` because `X ⟶ T` is, by the parts 0CGK, 0CGB, 0CGD and 0CGS of
Stacks 0CG6. This is the step of the proof of Stacks 0D1J (via Stacks 09ZZ) used again in Remark
0D1P.

## Main definitions

* `AlgebraicGeometry.Space.ProperFlatLift.Lift` — the lifts of `x` along `i`.
* `AlgebraicGeometry.Space.ProperFlatLift.Lift.deformation` — the flat deformation of a lift.
* `AlgebraicGeometry.Space.ProperFlatLift.Deformation.lift` — the lift of a flat deformation.
* `AlgebraicGeometry.Space.ProperFlatLift.liftClassesEquivDeformationClasses` — the bijection of
  isomorphism classes.

## Main results

* `AlgebraicGeometry.Space.ProperFlatLift.Lift.nonempty_iso_iff` — two lifts are isomorphic
  exactly when their deformations are.
* `AlgebraicGeometry.Space.ProperFlatLift.Deformation.isProperFlatSpace` — the total space of a
  flat deformation is finitely presented, flat and proper over `T'`.
* `AlgebraicGeometry.Space.ProperFlatLift.isStronglyCartesian_of_isPullback_commaHomAsSpaceMap` —
  a cartesian square of families is a strongly cartesian morphism (the converse direction of
  Stacks 04U9 as used in this development).

## Implementation notes

The base `T ⊆ T'` is the closed subspace `AlgebraicGeometry.Space.squareZeroSubspace` of the
algebraic space represented by `T'`, and `X ⟶ T` is read into it through
`AlgebraicGeometry.Space.rangeSpaceIso`. The base of a lift is `T'` only up to the equality
recorded in the fibre of `Under.post`, so the structure morphism of a lift is composed with the
`eqToHom` of that equality; a morphism of lifts lies over the identity of `T'`
(`AlgebraicGeometry.Space.ProperFlatLift.Lift.base_map`).

## References

* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 0CG6](https://stacks.math.columbia.edu/tag/0CG6)
* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 04U9](https://stacks.math.columbia.edu/tag/04U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.ProperFlatLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {T T' : BigFppfOver B S hS} (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
  (x : CartesianProperFlatSpaces B S hS) (hx : (cartesianProperFlatProjection B S hS).obj x = T)

/-- The algebraic space represented by the thickened base `T'`. -/
abbrev ambient : AlgebraicSpaces B S hS := (schemeSpaceFunctor B S hS).obj T'

/-- The closed subspace `T ⊆ T'` of a square-zero closed immersion. -/
abbrev baseSubspace := squareZeroSubspace B S hS i hi

/-- The structure morphism `X ⟶ T` of `x`, read into the closed subspace `T ⊆ T'`. -/
def specialMap :
    x.obj.obj.left ⟶ (⟨(baseSubspace i hi).1.toFunctor, (baseSubspace i hi).2.1⟩ :
      AlgebraicSpaces B S hS) :=
  commaHomAsSpaceMap x.obj.obj ≫ (schemeSpaceFunctor B S hS).map (eqToHom hx) ≫
    (rangeSpaceIso B S hS i hi.1).hom

/-- The lifts of `x` along `i`: objects of `Spaces'_{fp, flat, proper}` under `x` whose arrow
from `x` lies over `i`. -/
abbrev Lift :=
  (Under.post (cartesianProperFlatProjection B S hS)).Fiber
    (Under.mk (eqToHom hx ≫ i))

variable {i hi x hx}

/-- An equality of objects under `X` identifies their structure morphisms up to the
identification of their targets. -/
theorem under_hom_eq {C : Type*} [Category C] {X : C} {a b : Under X} (h : a = b) :
    a.hom ≫ eqToHom (congrArg Comma.right h) = b.hom := by
  subst h
  simp

private theorem comp_eqToHom_symm_comp_eqToHom {C : Type*} [Category C] {a b c d : C} (f : a ⟶ b)
    (g : b ⟶ c) (e : d = c) : (f ≫ g ≫ eqToHom e.symm) ≫ eqToHom e = f ≫ g := by
  simp

/-- The base of a lift is `T'`. -/
theorem Lift.base_eq (y : Lift i x hx) :
    (cartesianProperFlatProjection B S hS).obj y.1.right = T' :=
  congrArg Comma.right y.2

/-- The arrow of a lift lies over `i`. -/
theorem Lift.map_hom_eq (y : Lift i x hx) :
    (cartesianProperFlatProjection B S hS).map y.1.hom ≫ eqToHom y.base_eq = eqToHom hx ≫ i :=
  under_hom_eq y.2

/-- The comma morphism underlying the arrow of a lift. -/
abbrev Lift.arrow (y : Lift i x hx) : x.obj.obj ⟶ y.1.right.obj.obj :=
  y.1.hom.hom.hom

/-- The base component of the arrow of a lift is `i`, up to the identifications of its
endpoints with `T` and `T'`. -/
theorem Lift.arrow_right (y : Lift i x hx) :
    y.arrow.right = eqToHom hx ≫ i ≫ eqToHom y.base_eq.symm := by
  rw [← reassoc_of% y.map_hom_eq, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

/-- The structure morphism `X' ⟶ T'` of a lift. -/
def Lift.structureMap (y : Lift i x hx) : y.1.right.obj.obj.left ⟶ ambient (T' := T') :=
  commaHomAsSpaceMap y.1.right.obj.obj ≫ (schemeSpaceFunctor B S hS).map (eqToHom y.base_eq)

/-- Re-reading the base of a family along an equality of objects keeps it flat. -/
theorem isFlat_commaHomAsSpaceMap_comp_eqToHom
    {G : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
    {V : BigFppfOver B S hS} (e : G.right = V) (h : IsFlat B S hS G.hom) :
    IsFlat B S hS (commaHomAsSpaceMap G ≫ (schemeSpaceFunctor B S hS).map (eqToHom e)).hom := by
  subst e
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact h

/-- The structure morphism `X' ⟶ T'` of a lift is flat over `T'`. -/
theorem Lift.isFlat_structureMap (y : Lift i x hx) : IsFlat B S hS y.structureMap.hom :=
  isFlat_commaHomAsSpaceMap_comp_eqToHom y.base_eq y.1.right.obj.property.2.1

/-- The arrow of a lift is strongly cartesian over the base. -/
theorem Lift.isStronglyCartesian_arrow (y : Lift i x hx) :
    (spacesProjection B S hS).IsStronglyCartesian y.arrow.right y.arrow :=
  y.1.hom.property

variable (i hi x hx) in
/-- The identification of the space represented by the base of `x` with `T ⊆ T'`. -/
def specialBaseIso :
    schemeSpace x.obj.obj.right ≅ (⟨(baseSubspace i hi).1.toFunctor, (baseSubspace i hi).2.1⟩ :
      AlgebraicSpaces B S hS) :=
  (schemeSpaceFunctor B S hS).mapIso (eqToIso hx) ≪≫ rangeSpaceIso B S hS i hi.1

/-- The identification of the space represented by the base of a lift with `T'`. -/
def Lift.baseIso (y : Lift i x hx) : schemeSpace y.1.right.obj.obj.right ≅ ambient (T' := T') :=
  (schemeSpaceFunctor B S hS).mapIso (eqToIso y.base_eq)

/-- The identification of `T` with the range of `i`, followed by the inclusion into `T'`, is `i`,
on presheaves. -/
private theorem eqToHom_comp_rangeSpaceIso_comp_subspaceInclusion :
    yoneda.map (eqToHom hx) ≫ (rangeSpaceIso B S hS i hi.1).hom.hom ≫
      (subspaceInclusion B S hS ambient (baseSubspace i hi)).hom = yoneda.map (eqToHom hx ≫ i) :=
  (congrArg (yoneda.map (eqToHom hx) ≫ ·) (congrArg (fun φ => φ.hom)
    (rangeSpaceIso_hom_comp_subspaceInclusion B S hS i hi.1))).trans
    (Functor.map_comp yoneda _ _).symm

/-- **The square of a lift is cartesian**: the special fibre of `X' ⟶ T'` over `T ⊆ T'` is `X`. -/
theorem Lift.isPullback (y : Lift i x hx) :
    IsPullback y.arrow.left (specialMap i hi x hx) y.structureMap
      (subspaceInclusion B S hS ambient (baseSubspace i hi)) := by
  refine (isPullback_commaHomAsSpaceMap_of_isStronglyCartesian B S hS y.arrow
    y.isStronglyCartesian_arrow).of_iso (Iso.refl _) (Iso.refl _) (specialBaseIso i hi x hx)
    y.baseIso (by simp) (by rw [Iso.refl_hom, Category.id_comp]; rfl)
    (by rw [Iso.refl_hom, Category.id_comp]; rfl) ?_
  apply ObjectProperty.hom_ext
  show _ = yoneda.map (eqToHom hx) ≫ (rangeSpaceIso B S hS i hi.1).hom.hom ≫
    (subspaceInclusion B S hS ambient (baseSubspace i hi)).hom
  rw [eqToHom_comp_rangeSpaceIso_comp_subspaceInclusion (hi := hi)]
  show yoneda.map y.arrow.right ≫ yoneda.map (eqToHom y.base_eq) = yoneda.map (eqToHom hx ≫ i)
  rw [y.arrow_right]
  exact (Functor.map_comp yoneda _ _).symm.trans
    (congrArg yoneda.map (comp_eqToHom_symm_comp_eqToHom _ _ _))

/-- **The flat deformation of a lift.** A lift `x ⟶ y` of `x` along `T ⊆ T'` is a flat family
`X' ⟶ T'` with a cartesian square over `T ⊆ T'`, which is a flat deformation of `X ⟶ T` over
`T'` in the sense of Stacks 0D17. -/
def Lift.deformation (hi : IsSquareZeroClosedImmersion B S hS i) (y : Lift i x hx) :
    FlatThickeningDeformation.Deformation (specialMap i hi x hx) where
  X' := y.1.right.obj.obj.left
  f' := y.structureMap
  flat := y.isFlat_structureMap
  i := y.arrow.left
  isPullback := y.isPullback

variable (i x hx) in
/-- The total space of a lift, as a functor on the category of lifts. -/
abbrev liftSpaceFunctor : Lift i x hx ⥤ AlgebraicSpaces B S hS :=
  Functor.Fiber.fiberInclusion ⋙ Under.forget x ⋙ wideSubcategoryInclusion _ ⋙
    ObjectProperty.ι _ ⋙ Comma.fst _ _

variable (i x hx) in
/-- The base of a lift, as a functor on the category of lifts. -/
abbrev liftBaseFunctor : Lift i x hx ⥤ BigFppfOver B S hS :=
  Functor.Fiber.fiberInclusion ⋙ Under.forget x ⋙ wideSubcategoryInclusion _ ⋙
    ObjectProperty.ι _ ⋙ Comma.snd _ _

/-- The arrows of two lifts are related by a morphism of lifts. -/
theorem Lift.arrow_comp {y y' : Lift i x hx} (g : y ⟶ y') :
    y.arrow ≫ g.1.right.hom.hom = y'.arrow :=
  congrArg (fun φ => φ.hom.hom) (Under.w g.1)

/-- A morphism under `c` lying over an identity of `Under (q.obj c)` lies over the identity of
the base, after identifying the two bases. -/
private theorem map_right_of_isHomLift_id {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    {c : C} {V : Under (q.obj c)} {a b : Under c} (ha : (Under.post q).obj a = V)
    (hb : (Under.post q).obj b = V) (g : a ⟶ b) [(Under.post q).IsHomLift (𝟙 V) g] :
    ((Under.post q).map g).right ≫ eqToHom (congrArg Comma.right hb) =
      eqToHom (congrArg Comma.right ha) := by
  subst ha
  have h := congrArg (fun φ => φ.right)
    (IsHomLift.fac' (Under.post q) (𝟙 ((Under.post q).obj a)) g)
  simp only [Under.comp_right, Under.eqToHom_right, Category.id_comp] at h
  rw [h, eqToHom_trans, eqToHom_trans]

/-- A morphism of lifts lies over the identity of `T'`. -/
theorem Lift.base_map {y y' : Lift i x hx} (g : y ⟶ y') :
    (cartesianProperFlatProjection B S hS).map g.1.right ≫ eqToHom y'.base_eq =
      eqToHom y.base_eq :=
  have := g.2
  map_right_of_isHomLift_id _ y.2 y'.2 g.1

/-- A morphism of lifts commutes with the structure morphisms to `T'`. -/
theorem Lift.map_comp_structureMap {y y' : Lift i x hx} (g : y ⟶ y') :
    (liftSpaceFunctor i x hx).map g ≫ y'.structureMap = y.structureMap := by
  apply ObjectProperty.hom_ext
  show g.1.right.hom.hom.left.hom ≫ y'.1.right.obj.obj.hom ≫ yoneda.map (eqToHom y'.base_eq) =
    y.1.right.obj.obj.hom ≫ yoneda.map (eqToHom y.base_eq)
  rw [← Category.assoc]
  refine (congrArg (· ≫ yoneda.map (eqToHom y'.base_eq)) g.1.right.hom.hom.w).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (y.1.right.obj.obj.hom ≫ ·) ?_)
  exact (Functor.map_comp yoneda _ _).symm.trans (congrArg yoneda.map (Lift.base_map g))

/-- **An isomorphism of lifts is an isomorphism of their deformations.** -/
def Lift.deformationIso {y y' : Lift i x hx} (e : y ≅ y') :
    y.deformation hi ⟶ y'.deformation hi where
  hom := (liftSpaceFunctor i x hx).mapIso e
  hom_f' := Lift.map_comp_structureMap e.hom
  compat := congrArg (fun φ => φ.left) (Lift.arrow_comp e.hom)

/-- A morphism under `c` between two objects over `V` lies over the identity of `V` as soon as
its base component does. -/
private theorem isHomLift_id_of_map_right {C D : Type*} [Category C] [Category D] (q : C ⥤ D)
    {c : C} {V : Under (q.obj c)} {a b : Under c} (ha : (Under.post q).obj a = V)
    (hb : (Under.post q).obj b = V) (g : a ⟶ b)
    (h : ((Under.post q).map g).right ≫ eqToHom (congrArg Comma.right hb) =
      eqToHom (congrArg Comma.right ha)) :
    (Under.post q).IsHomLift (𝟙 V) g :=
  IsHomLift.of_commsq (Under.post q) (𝟙 V) g ha hb (Under.UnderMorphism.ext (by
    rw [Under.comp_right, Under.comp_right, Under.eqToHom_right, Under.eqToHom_right,
      Under.id_right, Category.comp_id]
    exact h))

/-- For equalities `e : U = W` and `e' : V = W`, the equation
`a ≫ b ≫ F.map (eqToHom e') = c ≫ F.map (eqToHom e)` gives
`a ≫ b = c ≫ F.map (eqToHom (e.trans e'.symm))`. -/
theorem comp_eq_comp_map_eqToHom_trans {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {P Q : D} {U V W : C} (a : P ⟶ Q) (b : Q ⟶ F.obj V) (c : P ⟶ F.obj U) (e : U = W)
    (e' : V = W) (h : a ≫ b ≫ F.map (eqToHom e') = c ≫ F.map (eqToHom e)) :
    a ≫ b = c ≫ F.map (eqToHom (e.trans e'.symm)) := by
  subst e e'
  simpa using h

private theorem comp_eqToHom_trans_eqToHom {C : Type*} [Category C] {a b c d : C} (f : a ⟶ b)
    (e : c = b) (e' : d = b) :
    f ≫ eqToHom e.symm ≫ eqToHom (e.trans e'.symm) = f ≫ eqToHom e'.symm := by
  simp

/-- The isomorphism of families underlying an isomorphism of the deformations of two lifts. -/
def Lift.commaIsoOfDeformation {y y' : Lift i x hx} (d : y.deformation hi ⟶ y'.deformation hi) :
    y.1.right.obj.obj ≅ y'.1.right.obj.obj :=
  Comma.isoMk d.hom (eqToIso (y.base_eq.trans y'.base_eq.symm))
    (comp_eq_comp_map_eqToHom_trans yoneda d.hom.hom.hom y'.1.right.obj.obj.hom
      y.1.right.obj.obj.hom y.base_eq y'.base_eq (congrArg (fun φ => φ.hom) d.hom_f'))

/-- The comma isomorphism of `Lift.commaIsoOfDeformation` is a morphism of
`Spaces'_{fp, flat, proper}`: as an isomorphism it is strongly cartesian. -/
def Lift.familyHomOfDeformation {y y' : Lift i x hx} (d : y.deformation hi ⟶ y'.deformation hi) :
    y.1.right ⟶ y'.1.right :=
  ⟨ObjectProperty.homMk (Lift.commaIsoOfDeformation d).hom, by
    change (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map (Lift.commaIsoOfDeformation d).hom)
      (Lift.commaIsoOfDeformation d).hom
    infer_instance⟩

/-- **An isomorphism of the deformations of two lifts is a morphism of lifts.** -/
def Lift.homOfDeformation {y y' : Lift i x hx} (d : y.deformation hi ⟶ y'.deformation hi) :
    y ⟶ y' :=
  ⟨Under.homMk (Lift.familyHomOfDeformation d) (by
    apply WideSubcategory.hom_ext
    apply (ObjectProperty.ι _).map_injective
    apply Comma.hom_ext
    · exact d.compat
    · change y.arrow.right ≫ eqToHom (y.base_eq.trans y'.base_eq.symm) = y'.arrow.right
      rw [Lift.arrow_right, Lift.arrow_right]
      exact comp_eqToHom_trans_eqToHom (eqToHom hx ≫ i) y.base_eq y'.base_eq), by
    refine isHomLift_id_of_map_right _ y.2 y'.2 _ ?_
    change eqToHom (y.base_eq.trans y'.base_eq.symm) ≫ eqToHom y'.base_eq = eqToHom y.base_eq
    rw [eqToHom_trans]⟩

/-- Two lifts are isomorphic exactly when their deformations are. -/
theorem Lift.nonempty_iso_iff {y y' : Lift i x hx} :
    Nonempty (y ≅ y') ↔ Nonempty (y.deformation hi ⟶ y'.deformation hi) := by
  refine ⟨fun ⟨e⟩ => ⟨Lift.deformationIso e⟩, fun ⟨d⟩ => ⟨?_⟩⟩
  refine ⟨Lift.homOfDeformation d, Lift.homOfDeformation (inv d), ?_, ?_⟩
  all_goals
    apply Functor.Fiber.hom_ext
    apply Under.UnderMorphism.ext
    apply WideSubcategory.hom_ext
    apply (ObjectProperty.ι _).map_injective
    apply Comma.hom_ext
  · exact congrArg (fun φ => φ.hom.hom) (IsIso.hom_inv_id d)
  · show eqToHom (y.base_eq.trans y'.base_eq.symm) ≫
      eqToHom (y'.base_eq.trans y.base_eq.symm) = 𝟙 _
    exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)
  · exact congrArg (fun φ => φ.hom.hom) (IsIso.inv_hom_id d)
  · show eqToHom (y'.base_eq.trans y.base_eq.symm) ≫
      eqToHom (y.base_eq.trans y'.base_eq.symm) = 𝟙 _
    exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)

variable (hi) in
/-- **Lift classes are deformation classes.** The isomorphism class of a lift of `x` along
`T ⊆ T'` goes to the isomorphism class of its flat deformation of `X ⟶ T` over `T'`. -/
def liftClassesToDeformationClasses :
    Quotient (isIsomorphicSetoid (Lift i x hx)) →
      FlatThickeningDeformation.Classes (specialMap i hi x hx) :=
  Quotient.map (Lift.deformation hi) (fun _ _ h => Lift.nonempty_iso_iff.1 h)

/-- The isomorphism class of a lift goes to the isomorphism class of its flat deformation. -/
@[simp]
theorem liftClassesToDeformationClasses_mk (y : Lift i x hx) :
    liftClassesToDeformationClasses hi (Quotient.mk _ y) = Quotient.mk _ (y.deformation hi) :=
  rfl

/-- Non-isomorphic lifts have non-isomorphic deformations. -/
theorem liftClassesToDeformationClasses_injective :
    Function.Injective (liftClassesToDeformationClasses (i := i) (x := x) (hx := hx) hi) := by
  intro a b h
  induction a using Quotient.inductionOn
  induction b using Quotient.inductionOn
  exact Quotient.sound (Lift.nonempty_iso_iff.2 (Quotient.exact h))

/-! ### Every flat deformation comes from a lift -/

/-- **A cartesian square of families is a strongly cartesian morphism** (the converse of
`AlgebraicGeometry.isPullback_commaHomAsSpaceMap_of_isStronglyCartesian`, Stacks 04U9). -/
theorem isStronglyCartesian_of_isPullback_commaHomAsSpaceMap
    {A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)} (m : A ⟶ C)
    (h : IsPullback m.left (commaHomAsSpaceMap A) (commaHomAsSpaceMap C)
      (schemeSpaceMap m.right)) :
    (spacesProjection B S hS).IsStronglyCartesian m.right m := by
  rw [spacesProjection_isStronglyCartesian_iff]
  have hp : IsPullback A.hom m.left.hom (yoneda.map m.right) C.hom :=
    (AlgebraicSpaces.isPullback_hom B S hS h).flip
  have hl : pullback.lift A.hom m.left.hom m.w.symm = hp.isoPullback.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
    · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  have hiso : IsIso (pullback.lift A.hom m.left.hom m.w.symm) := by
    rw [hl]
    infer_instance
  have : IsIso ((ObjectProperty.ι (IsAlgebraicSpace B S hS)).map
      (ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm) :
        A.left ⟶ AlgebraicSpaces.fiberProduct B S hS
          (schemeSpaceMap m.right) (ObjectProperty.homMk C.hom))) := hiso
  exact isIso_of_reflects_iso _ (ObjectProperty.ι (IsAlgebraicSpace B S hS))

variable (D : FlatThickeningDeformation.Deformation (specialMap i hi x hx))

/-- The closed fibre `f'⁻¹(T) ⊆ X'` of a flat deformation. -/
abbrev Deformation.fibre : ClosedSubspaces B S hS D.X'.1 :=
  preimageSubspace B S hS D.f' (baseSubspace i hi)

/-- **The special fibre of a flat deformation is the space it deforms**, on presheaves. -/
def Deformation.fibreIsoPresheaf : x.obj.obj.left.obj ≅ (Deformation.fibre D).1.toFunctor :=
  (AlgebraicSpaces.isPullback_hom B S hS D.isPullback).isoIsPullback _ _
    (isPullback_preimageSubspace B S hS D.f' (baseSubspace i hi))

/-- The special fibre of a flat deformation is the space it deforms. -/
def Deformation.fibreIso :
    x.obj.obj.left ≅ (⟨(Deformation.fibre D).1.toFunctor, (Deformation.fibre D).2.1⟩ :
      AlgebraicSpaces B S hS) :=
  (ObjectProperty.fullyFaithfulι _).preimageIso (Deformation.fibreIsoPresheaf D)

/-- The identification of `X` with the closed fibre of a flat deformation, followed by the
projection of the fibre to `T ⊆ T'`, is the structure morphism `X ⟶ T` read into `T ⊆ T'`. -/
theorem Deformation.fibreIso_hom_comp_preimageProjection :
    (Deformation.fibreIso D).hom ≫ preimageProjection B S hS D.f' (baseSubspace i hi) =
      specialMap i hi x hx := by
  apply ObjectProperty.hom_ext
  exact IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The square of `Spaces'_{fp, flat, proper}`'s conditions, read on the closed fibre of a
flat deformation, is a cartesian finite-order deformation of algebraic spaces (Stacks 0CG6). -/
def Deformation.cartesianFiniteOrder : CartesianFiniteOrderDeformation B S hS where
  X' := D.X'
  Y' := ambient (T' := T')
  B' := ambient (T' := T')
  X := (Deformation.fibre D).1
  Y := (baseSubspace i hi).1
  B := (baseSubspace i hi).1
  base_finiteOrder :=
    (isFirstOrderThickening_squareZeroSubspace B S hS i hi).isFiniteOrderThickening
  source_thickening :=
    (isFirstOrderThickening_preimage_squareZeroSubspace B S hS i hi D.f').isThickening
  target_thickening := (isFirstOrderThickening_squareZeroSubspace B S hS i hi).isThickening
  f := (preimageProjection B S hS D.f' (baseSubspace i hi)).hom
  f' := D.f'.hom
  g := 𝟙 _
  g' := 𝟙 _
  comm_f := (isPullback_preimageSubspace B S hS D.f' (baseSubspace i hi)).w.symm
  comm_g := by simp
  isPullback_X := by
    rw [Category.comp_id, Category.comp_id]
    exact isPullback_preimageSubspace B S hS D.f' (baseSubspace i hi)
  isPullback_Y := IsPullback.id_vert _
  flat_X' := by
    rw [Category.comp_id]
    exact D.flat

/-- A property of morphisms of algebraic spaces stable under base change passes from the
structure morphism of `x` to the closed fibre of a flat deformation of `X ⟶ T`. -/
theorem Deformation.preimageProjection_of_isStableUnderBaseChange
    {P : MorphismProperty (AlgebraicSpaces B S hS)} [P.IsStableUnderBaseChange]
    (h : P (commaHomAsSpaceMap x.obj.obj)) :
    P (preimageProjection B S hS D.f' (baseSubspace i hi)) := by
  have h₁ : P (specialMap i hi x hx) :=
    (P.cancel_right_of_respectsIso _ (specialBaseIso i hi x hx).hom).2 h
  rw [← Deformation.fibreIso_hom_comp_preimageProjection D] at h₁
  exact (P.cancel_left_of_respectsIso _ _).1 h₁

/-- **The total space of a flat deformation of `x` is finitely presented, flat and proper over
`T'`** (Stacks 0CG6, parts 0CGK, 0CGB, 0CGD and 0CGS). -/
theorem Deformation.isProperFlatSpace :
    Space.IsFinitePresentation B S hS D.f'.hom ∧ IsFlat B S hS D.f'.hom ∧
      Space.IsProper B S hS D.f'.hom := by
  have hxP := x.obj.property
  have hfp : Space.IsFinitePresentation B S hS
      (preimageProjection B S hS D.f' (baseSubspace i hi)).hom := by
    have := Space.isFinitePresentation_isStableUnderBaseChange B S hS
    exact Deformation.preimageProjection_of_isStableUnderBaseChange D
      (P := fun _ _ f => Space.IsFinitePresentation B S hS f.hom) hxP.1
  have hpr : Space.IsProper B S hS
      (preimageProjection B S hS D.f' (baseSubspace i hi)).hom := by
    have := Space.isProper_isStableUnderBaseChange B S hS
    exact Deformation.preimageProjection_of_isStableUnderBaseChange D
      (P := fun _ _ f => Space.IsProper B S hS f.hom) hxP.2.2
  let D' := Deformation.cartesianFiniteOrder D
  exact ⟨⟨(D'.isLocallyOfFinitePresentation_iff).1 hfp.1, (D'.isQuasiCompact_iff).1 hfp.2.1,
      (D'.isSeparated_iff_and_isQuasiSeparated_iff).2.1 hfp.2.2⟩, D.flat,
    (D'.isProper_iff).1 hpr⟩

variable (i hi x hx) in
/-- The identification of the base of `x` with `T ⊆ T'`, followed by the inclusion into `T'`,
is `i`. -/
theorem specialBaseIso_hom_comp_subspaceInclusion :
    (specialBaseIso i hi x hx).hom ≫ subspaceInclusion B S hS ambient (baseSubspace i hi) =
      (schemeSpaceFunctor B S hS).map (eqToHom hx ≫ i) := by
  apply ObjectProperty.hom_ext
  exact eqToHom_comp_rangeSpaceIso_comp_subspaceInclusion (hi := hi)

variable (i hi x hx) in
/-- The structure morphism of `x`, read into `T ⊆ T'` and then into `T'`, is the structure
morphism of `x` followed by `i`. -/
theorem specialMap_comp_subspaceInclusion :
    specialMap i hi x hx ≫ subspaceInclusion B S hS ambient (baseSubspace i hi) =
      commaHomAsSpaceMap x.obj.obj ≫ (schemeSpaceFunctor B S hS).map (eqToHom hx ≫ i) := by
  apply ObjectProperty.hom_ext
  show x.obj.obj.hom ≫ yoneda.map (eqToHom hx) ≫ (rangeSpaceIso B S hS i hi.1).hom.hom ≫
    (subspaceInclusion B S hS ambient (baseSubspace i hi)).hom = x.obj.obj.hom ≫
      yoneda.map (eqToHom hx ≫ i)
  exact congrArg (x.obj.obj.hom ≫ ·) (eqToHom_comp_rangeSpaceIso_comp_subspaceInclusion (hi := hi))

/-- The family `X' ⟶ T'` of a flat deformation. -/
abbrev Deformation.family :
    Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  left := D.X'
  right := T'
  hom := D.f'.hom

/-- The arrow `x ⟶ (X' ⟶ T')` of a flat deformation, over `i`. -/
def Deformation.familyArrow : x.obj.obj ⟶ Deformation.family D where
  left := D.i
  right := eqToHom hx ≫ i
  w := congrArg (fun φ => φ.hom)
    (D.isPullback.w.trans (specialMap_comp_subspaceInclusion i hi x hx))

/-- The arrow `x ⟶ (X' ⟶ T')` of a flat deformation is strongly cartesian over its base
component. -/
theorem Deformation.isStronglyCartesian_familyArrow :
    (spacesProjection B S hS).IsStronglyCartesian (Deformation.familyArrow D).right
      (Deformation.familyArrow D) := by
  apply isStronglyCartesian_of_isPullback_commaHomAsSpaceMap
  refine D.isPullback.of_iso (Iso.refl _) (Iso.refl _) (specialBaseIso i hi x hx).symm
    (Iso.refl _) ((Category.comp_id D.i).trans (Category.id_comp _).symm) ?_
    (by apply ObjectProperty.hom_ext; rfl) ?_
  · rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom]
    exact (show (commaHomAsSpaceMap x.obj.obj ≫ (specialBaseIso i hi x hx).hom) ≫
      (specialBaseIso i hi x hx).inv = commaHomAsSpaceMap x.obj.obj by
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  · exact (Category.comp_id _).trans
      ((Iso.eq_inv_comp _).2 (specialBaseIso_hom_comp_subspaceInclusion i hi x hx))

/-- **The lift of a flat deformation.** A flat deformation `X' ⟶ T'` of `X ⟶ T` is finitely
presented, flat and proper over `T'`, and its square over `T ⊆ T'` is cartesian, so it is a
lift of `x` along `i` in `Spaces'_{fp, flat, proper}`. -/
def Deformation.lift : Lift i x hx :=
  ⟨Under.mk (⟨ObjectProperty.homMk (Deformation.familyArrow D),
      Deformation.isStronglyCartesian_familyArrow D⟩ :
        x ⟶ (⟨⟨Deformation.family D, Deformation.isProperFlatSpace D⟩⟩ :
          CartesianProperFlatSpaces B S hS)), rfl⟩

/-- The deformation of the lift of a flat deformation is that deformation. -/
def Deformation.liftDeformationIso : (Deformation.lift D).deformation hi ⟶ D where
  hom := Iso.refl _
  hom_f' := by
    apply ObjectProperty.hom_ext
    have h : yoneda.map (eqToHom (Lift.base_eq (Deformation.lift D))) = 𝟙 (yoneda.obj T') :=
      (congrArg yoneda.map (eqToHom_refl T' _)).trans (yoneda.map_id T')
    exact congrArg (D.f'.hom ≫ ·) h.symm
  compat := Category.comp_id _

/-- **Every flat deformation of `X ⟶ T` over `T'` comes from a lift of `x`.** -/
theorem liftClassesToDeformationClasses_surjective :
    Function.Surjective (liftClassesToDeformationClasses (i := i) (x := x) (hx := hx) hi) := by
  intro c
  induction c using Quotient.inductionOn with
  | _ D => exact ⟨Quotient.mk _ (Deformation.lift D),
      Quotient.sound ⟨Deformation.liftDeformationIso D⟩⟩

variable (i hi x hx) in
/-- **The lift classes of `x` along a square-zero thickening `T ⊆ T'` are the isomorphism
classes of flat deformations of `X ⟶ T` over `T'`** in the sense of Stacks 0D17: a lift
`x ⟶ y` in `Spaces'_{fp, flat, proper}` is the flat family `X' ⟶ T'` of `y` with the cartesian
square of the arrow, and conversely every flat deformation of `X ⟶ T` over `T'` is finitely
presented and proper over `T'` (Stacks 0CG6). -/
def liftClassesEquivDeformationClasses :
    Quotient (isIsomorphicSetoid (Lift i x hx)) ≃
      FlatThickeningDeformation.Classes (specialMap i hi x hx) :=
  Equiv.ofBijective (liftClassesToDeformationClasses hi)
    ⟨liftClassesToDeformationClasses_injective (hi := hi),
      liftClassesToDeformationClasses_surjective (hi := hi)⟩

end AlgebraicGeometry.Space.ProperFlatLift

end
