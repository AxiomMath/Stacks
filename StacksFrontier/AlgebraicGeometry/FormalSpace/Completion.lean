module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Completion of an algebraic space along a set of points

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a presheaf on the big fppf
site of `S` and let `T` be a set of points of `X`. The *completion* `X_{/T}` of `X` along `T`
is the fppf sheafification of the subfunctor of `X` whose sections over an object `U` of the
site are the sections whose point-set image lies in `T`, the image being tested on the
field-valued points of `U`.

This file proves that completion is compatible with base change: for a morphism `f : X' ⟶ X`
and `T' = |f|⁻¹ T`, the square formed by the two completions and the two ambient sheaves is
cartesian, and the induced morphism `X'_{/T'} ⟶ X_{/T}` is representable by algebraic spaces
when `X` and `X'` are algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Space.HasImageIn` is the condition that a section of a presheaf have
  point-set image inside a set of points.
* `AlgebraicGeometry.Space.completionSubfunctor` is the subfunctor of sections with image in
  the given set of points, and `AlgebraicGeometry.Space.completionSheaf` its fppf
  sheafification, the completion itself: **Stacks 0AMC**, the completion of `X` along `T`.
* `AlgebraicGeometry.Space.completionMap` and `AlgebraicGeometry.Space.completionSheafMap`
  are the morphisms induced on completions by a morphism of presheaves.
* `AlgebraicGeometry.Space.sheafifiedULift` is the fppf sheafification of the universe lift
  of a presheaf, with `AlgebraicGeometry.Space.sheafifiedULiftMap` its functoriality and
  `AlgebraicGeometry.Space.completionSheafInclusion` the morphism from a completion into it.

## Main results

* `AlgebraicGeometry.Space.isPullback_completionSheafMap`: **Stacks 0APV**, the completion
  square of a morphism of presheaves is cartesian.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_completionMap`:
  **Stacks 0APV**, the induced morphism of completions of algebraic spaces is representable
  by algebraic spaces.

## Implementation notes

The set of points of a presheaf lies in `Type (u + 1)`, so the completion is formed inside
presheaves of `Type (u + 1)`: the subfunctor is taken inside the universe lift
`X ⋙ CategoryTheory.uliftFunctor.{u + 1}`, which is the value universe in which a formal
algebraic space lives.

The cartesian square is already cartesian before sheafifying, where it is checked
sectionwise: a section of `X'` over `U` whose image in `X` has point-set image in `T` has
point-set image in `|f|⁻¹ T`, because the field-valued points of `X'` restricted from `U` map
to those of `X`. Sheafification preserves fibre products, so the sheafified square is
cartesian too.

Representability then follows from Stacks 0APZ applied to the universe lift of `f`, once the
sheafified universe lifts of `X'` and `X` in the square are identified with the universe lifts
themselves; these are already sheaves because `X'` and `X` are.

Closedness of `T` is used nowhere here: it is what makes the completion a formal algebraic
space, which is a separate assertion, so both statements are proved for an arbitrary set of
points.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0AIZ](https://stacks.math.columbia.edu/tag/0AIZ)
* [Stacks Project, Tag 0APV](https://stacks.math.columbia.edu/tag/0APV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The completion of a presheaf along a set of its points -/

/-- A section of a presheaf `X` over an object `U` of the big fppf site of `S` has point-set
image in a set `T` of points of `X` when every field-valued point of `U` restricts it to a
field-valued point of `X` whose class belongs to `T`. -/
def HasImageIn (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : Set (points B S hS X))
    (U : BigFppfOver B S hS) (f : X.obj (Opposite.op U)) : Prop :=
  ∀ p : FieldValuedPoint B S hS (yoneda.obj U),
    (⟨p.carrier, p.contained, p.toBase, X.map p.value.op f⟩ :
      FieldValuedPoint B S hS X).class B S hS X ∈ T

/-- The subfunctor of the universe lift of `X` whose sections are those with point-set image
in `T`. Restriction preserves the condition, since a field-valued point of the smaller object
composes with the restriction to a field-valued point of the larger one. -/
def completionSubfunctor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) : Subfunctor (X ⋙ uliftFunctor.{u + 1}) where
  obj U := {f | HasImageIn B S hS X T U.unop f.down}
  map {U V} i f hf := by
    change HasImageIn B S hS X T _ (X.map i f.down)
    intro p
    let q : FieldValuedPoint B S hS (yoneda.obj U.unop) :=
      { carrier := p.carrier
        field := p.field
        contained := p.contained
        toBase := p.toBase
        value := p.value ≫ i.unop }
    have hq := hf q
    dsimp [q] at hq
    simpa only [op_comp, Quiver.Hom.unop_op, Functor.map_comp,
      ConcreteCategory.comp_apply] using hq

/-- **Stacks 0AMC.** The completion `X_{/T}` of `X` along `T`: the fppf sheafification of the
subfunctor of sections with point-set image in `T`.

For `X` an algebraic space over `S` and `T ⊆ |X|` closed this is the object Stacks 0AMC names
the *completion of `X` along `T`*, namely the formal algebraic space of Stacks 0AIZ: the fppf
sheafification of the functor sending `U` to the morphisms `f : U ⟶ X` with `f(|U|) ⊆ T`.
Stacks 0AIZ, that it is a formal algebraic space, is not proved in this library; the object
named here is the sheaf itself, defined for an arbitrary presheaf `X` and an arbitrary set `T`
of its points. The affine case of 0AIZ is
`AlgebraicGeometry.FormalSpace.hasSomeSurjectivePresentation_completionSheaf` (Stacks 0AIY). -/
@[stacks 0AMC "the completion along a closed subset; 0AIZ, formal algebraic space, not proved"]
def completionSheaf (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (T : Set (points B S hS X)) :
    Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  ⟨(BigFppfOver.topology B S hS).sheafify (completionSubfunctor B S hS X T).toFunctor,
    (BigFppfOver.topology B S hS).sheafify_isSheaf _⟩

/-! ### Functoriality of the completion -/

/-- A section of `X'` has point-set image in `|f|⁻¹ T` exactly when its image in `X` has
point-set image in `T`. -/
private theorem hasImageIn_preimage_iff {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) (U : BigFppfOver B S hS) (x : X'.obj (Opposite.op U)) :
    HasImageIn B S hS X' (pointsMap B S hS X' f ⁻¹' T) U x ↔
      HasImageIn B S hS X T U (f.app _ x) := by
  refine forall_congr' fun p => ?_
  change pointsMap B S hS X' f _ ∈ T ↔ _
  rw [pointsMap_class, ← NatTrans.naturality_apply f p.value.op x]
  rfl

/-- The morphism of completion subfunctors induced by a morphism `f : X' ⟶ X`, the source
being completed along the inverse image of the set of points of the target. -/
def completionMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).toFunctor ⟶
      (completionSubfunctor B S hS X T).toFunctor where
  app U := ↾fun x => ⟨ULift.up (f.app U x.1.down), by
    change HasImageIn B S hS X T U.unop (f.app U x.1.down)
    intro p
    have hp := x.2 p
    change pointsMap B S hS X' f
      ((⟨p.carrier, p.contained, p.toBase, X'.map p.value.op x.1.down⟩ :
        FieldValuedPoint B S hS X').class B S hS X') ∈ T at hp
    rw [pointsMap_class] at hp
    convert hp using 1
    congr 1
    congr 1
    exact (NatTrans.naturality_apply f p.value.op x.1.down).symm⟩
  naturality U V i := by
    ext x
    apply Subtype.ext
    apply ULift.ext
    exact NatTrans.naturality_apply f i x.1.down

/-- The morphism of completions `X'_{/|f|⁻¹ T} ⟶ X_{/T}` induced by a morphism
`f : X' ⟶ X`. -/
def completionSheafMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    completionSheaf B S hS X' (pointsMap B S hS X' f ⁻¹' T) ⟶
      completionSheaf B S hS X T :=
  ObjectProperty.homMk
    ((BigFppfOver.topology B S hS).sheafifyMap (completionMap B S hS f T))

/-- The fppf sheafification of the universe lift of a presheaf of `Type u` to
`Type (u + 1)`. -/
def sheafifiedULift (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    Sheaf (BigFppfOver.topology B S hS) (Type (u + 1)) :=
  ⟨(BigFppfOver.topology B S hS).sheafify (X ⋙ uliftFunctor.{u + 1}),
    (BigFppfOver.topology B S hS).sheafify_isSheaf _⟩

/-- The morphism `X_{/T} ⟶ X` from the completion of `X` along `T` into `X` itself,
sheafified in `Type (u + 1)`. -/
def completionSheafInclusion (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (T : Set (points B S hS X)) :
    completionSheaf B S hS X T ⟶ sheafifiedULift B S hS X :=
  ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (completionSubfunctor B S hS X T).ι)

/-- The morphism of sheafified universe lifts induced by a morphism of presheaves. -/
def sheafifiedULiftMap {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X) :
    sheafifiedULift B S hS X' ⟶ sheafifiedULift B S hS X :=
  ObjectProperty.homMk ((BigFppfOver.topology B S hS).sheafifyMap
    (Functor.whiskerRight f uliftFunctor.{u + 1}))

/-! ### The completion square -/

/-- The completion square of a morphism of presheaves is cartesian already before
sheafifying: it is a cartesian square of presheaves of `Type (u + 1)`, checked on sections
over each object of the site. -/
private theorem completionSubfunctor_square_isPullback
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    IsPullback
      ((completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι)
      (completionMap B S hS f T)
      (Functor.whiskerRight f uliftFunctor.{u + 1})
      ((completionSubfunctor B S hS X T).ι) := by
  apply IsPullback.of_forall_isPullback_app
  intro U
  apply (Types.isPullback_iff
    (t := (NatTrans.app
      ((completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι) U))
    (r := (NatTrans.app (Functor.whiskerRight f uliftFunctor.{u + 1}) U))
    (l := (NatTrans.app (completionMap B S hS f T) U))
    (b := (NatTrans.app ((completionSubfunctor B S hS X T).ι) U))).2
  refine ⟨by ext z; rfl, fun a b h => Subtype.ext h.left, ?_⟩
  intro x y h
  have hval : f.app U x.down = y.1.down := congrArg ULift.down h
  refine ⟨⟨x, ?_⟩, ?_, ?_⟩
  · exact (hasImageIn_preimage_iff B S hS f T U.unop x.down).2 (hval ▸ y.2)
  · rfl
  · exact Subtype.ext (ULift.ext hval)

/-- **Stacks 0APV.** Completion is compatible with base change: for a morphism `f : X' ⟶ X`
of presheaves on the big fppf site of `S` and a set `T` of points of `X`, the square formed
by the completion of `X'` along `|f|⁻¹ T`, the completion of `X` along `T` and the two
ambient sheaves is a cartesian square of fppf sheaves. -/
@[stacks 0APV "cartesian square"]
theorem isPullback_completionSheafMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X' ⟶ X)
    (T : Set (points B S hS X)) :
    IsPullback
      (completionSheafInclusion B S hS X' (pointsMap B S hS X' f ⁻¹' T))
      (completionSheafMap B S hS f T)
      (sheafifiedULiftMap B S hS f)
      (completionSheafInclusion B S hS X T) :=
  (completionSubfunctor_square_isPullback B S hS f T).map
    (CategoryTheory.plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1)))

/-- **Stacks 0APV.** For a morphism `f : X' ⟶ X` of algebraic spaces over `S` and a set `T`
of points of `X`, the induced morphism of completions `X'_{/|f|⁻¹ T} ⟶ X_{/T}` is
representable by algebraic spaces. -/
@[stacks 0APV "representable by algebraic spaces"]
theorem isRepresentableByAlgebraicSpacesULift_completionMap
    {X' X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX' : IsAlgebraicSpace B S hS X') (hX : IsAlgebraicSpace B S hS X)
    (f : X' ⟶ X) (T : Set (points B S hS X)) :
    IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (completionSheafMap B S hS f T).hom := by
  let C := BigFppfOver B S hS
  let J := BigFppfOver.topology B S hS
  let H := (Functor.whiskeringRight Cᵒᵖ (Type u) (Type (u + 1))).obj uliftFunctor.{u + 1}
  have hlarge : IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (H.map f) :=
    (isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS f).mpr fun U ξ =>
      isAlgebraicSpace_pullback B S hS ξ f (isAlgebraicSpace_yoneda B S hS U) hX' hX
  have hX'large : IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj X') :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X').mpr hX'
  have hXlarge : IsAlgebraicSpaceULift.{u + 1} B S hS (H.obj X) :=
    (isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X).mpr hX
  let eX' : H.obj X' ≅ (sheafifiedULift B S hS X').obj := J.isoSheafify hX'large.isSheaf
  let eX : H.obj X ≅ (sheafifiedULift B S hS X).obj := J.isoSheafify hXlarge.isSheaf
  have hpb := (isPullback_completionSheafMap B S hS f T).map
    (sheafToPresheaf J (Type (u + 1)))
  have hcomm : (sheafifiedULiftMap B S hS f).hom ≫ eX.inv = eX'.inv ≫ H.map f := by
    have hn' : H.map f ≫ eX.hom = eX'.hom ≫ (sheafifiedULiftMap B S hS f).hom := by
      change (Functor.whiskerRight f uliftFunctor.{u + 1}) ≫
          J.toSheafify (X ⋙ uliftFunctor.{u + 1}) =
        J.toSheafify (X' ⋙ uliftFunctor.{u + 1}) ≫
          J.sheafifyMap (Functor.whiskerRight f uliftFunctor.{u + 1})
      exact J.toSheafify_naturality _
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
    exact hn'.symm
  have hp : IsPullback
      ((completionSheafInclusion B S hS X' (pointsMap B S hS X' f ⁻¹' T)).hom ≫ eX'.inv)
      (completionSheafMap B S hS f T).hom
      (H.map f)
      ((completionSheafInclusion B S hS X T).hom ≫ eX.inv) :=
    IsPullback.of_iso hpb (Iso.refl _) eX'.symm (Iso.refl _) eX.symm
      (by simp) (by simp) hcomm (by simp)
  exact isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS _ _ _ _ hp hlarge

end AlgebraicGeometry.Space

end
