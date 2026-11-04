module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# Modifications of an algebraic space and their base change

Let `W` be an algebraic space over a scheme `S` and let `W₀` be a subfunctor of `W`,
thought of as an open subspace. A *modification of `W` outside `W₀`* is an algebraic space
over `W` whose base change to `W₀` is an isomorphism, that is, a morphism of algebraic
spaces `X ⟶ W` which is an isomorphism over `W₀`. These form a full subcategory of the
slice category over the presheaf underlying `W`.

Base change along a morphism `f : V ⟶ W` of algebraic spaces carries a modification of `W`
outside `W₀` to a modification of `V` outside the preimage `f^{-1}W₀`, and the resulting
functor is the restriction of the pullback functor `Over W ⥤ Over V`.

Requiring in addition that the structure morphism be locally of finite type cuts out the
modifications used in the algebraization of formal modifications: the category whose objects
are the morphisms `X ⟶ W` of algebraic spaces which are locally of finite type and become
isomorphisms over `W₀`.

## Main definitions

* `AlgebraicGeometry.Space.openComplement` is the open complement of a subfunctor: a
  section lies in it when every restriction of that section which factors through the
  subfunctor is over an empty scheme.
* `AlgebraicGeometry.Space.IsModification` and `AlgebraicGeometry.Space.Modification` are
  the property and the category of algebraic spaces over `W` which are unchanged over `W₀`.
* `AlgebraicGeometry.Space.IsFiniteTypeModification` and
  `AlgebraicGeometry.Space.FiniteTypeModification` are the same property and category with
  the structure morphism required to be locally of finite type: **Stacks 0AS2**.

## Main results

* `AlgebraicGeometry.Space.isModification_pullback`: base change of a modification along an
  arbitrary morphism of algebraic spaces is a modification outside the preimage.
* `AlgebraicGeometry.Space.baseChangeFunctor` is the induced functor on modifications,
  together with the natural isomorphism identifying it with the pullback functor on slice
  categories.
* `AlgebraicGeometry.Space.isFiniteTypeModification_iff` spells out the three conditions of
  Stacks 0AS2 on a morphism of algebraic spaces.

## Implementation notes

The complement of a subfunctor is defined by the condition that every base change which
factors through the subfunctor has empty source scheme, which is the sheaf-theoretic way of
saying that a section misses the subfunctor.

Being a modification is phrased with `CategoryTheory.Limits.pullback.snd` of the structure
morphism along the inclusion of the subfunctor, so the condition is literally that the base
change to `W₀` is an isomorphism. The base-change functor is obtained by lifting
`CategoryTheory.Over.pullback` through the full subcategory, so the natural isomorphism
asked for by the statement is the identity.

The geometric input is `AlgebraicGeometry.isAlgebraicSpace_pullback` for the fibre product
of algebraic spaces and `CategoryTheory.Subfunctor.isPullback_fromPreimage` for the fact
that the preimage of a subfunctor is a fibre product; everything else is pasting of fibre
product squares.

The finite-type condition is imposed on top of `IsModification` rather than alongside its two
conjuncts, so that the two notions share one definition and every lemma about modifications
applies to the finite-type ones through `IsFiniteTypeModification.isModification`. Both are
stated for an arbitrary subfunctor `W₀`, since openness of `W₀` is not needed to form the
category; in the application `W` is the spectrum of a Noetherian ring and `W₀` the complement
of the closed set cut out by an ideal, which is `openComplement`.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
* [Stacks Project, Tag 0AS2](https://stacks.math.columbia.edu/tag/0AS2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The open complement of a closed subspace: a section lies in it if every
restriction of that section which factors through the closed subspace is over
an empty scheme. -/
def openComplement {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : Subfunctor W) : Subfunctor W where
  obj U := {x | ∀ (A : (BigFppfOver B S hS)ᵒᵖ) (a : U ⟶ A),
    W.map a x ∈ T.obj A → IsEmpty ((BigFppfOver.toScheme B S hS).obj A.unop)}
  map := by
    intro U V i x hx A a ha
    apply hx A (i ≫ a)
    simpa only [Functor.map_comp_apply] using ha

/-- An algebraic space over `W` which is unchanged over the open `W₀`. -/
def IsModification {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W₀ : Subfunctor W)
    (X : Over W) : Prop :=
  IsAlgebraicSpace B S hS X.left ∧ IsIso (pullback.snd X.hom W₀.ι)

/-- The category of algebraic-space modifications of `W` supported outside `W₀`. -/
abbrev Modification {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W₀ : Subfunctor W) :=
  ObjectProperty.FullSubcategory (IsModification B S hS W₀)

section FiniteType

/-- **Stacks 0AS2.** An algebraic space over `W`, locally of finite type over `W` and
unchanged over `W₀`. -/
@[stacks 0AS2 "the three defining conditions"]
def IsFiniteTypeModification {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W₀ : Subfunctor W)
    (X : Over W) : Prop :=
  IsModification B S hS W₀ X ∧ IsLocallyOfFiniteType B S hS X.hom

/-- **Stacks 0AS2.** The category of algebraic spaces over `W` which are locally of finite
type over `W` and isomorphisms over `W₀`. -/
@[stacks 0AS2 "the category they form"]
abbrev FiniteTypeModification {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (W₀ : Subfunctor W) :=
  ObjectProperty.FullSubcategory (IsFiniteTypeModification B S hS W₀)

variable {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W₀ : Subfunctor W} {X : Over W}

/-- **Stacks 0AS2.** The three conditions of Stacks 0AS2: the source is an algebraic space,
the structure morphism is locally of finite type, and its base change to `W₀` is an
isomorphism. The tag is the set-builder expression delimiting the morphisms that satisfy
exactly these three conditions, so this equivalence is the whole of it. -/
@[stacks 0AS2]
theorem isFiniteTypeModification_iff :
    IsFiniteTypeModification B S hS W₀ X ↔
      IsAlgebraicSpace B S hS X.left ∧ IsLocallyOfFiniteType B S hS X.hom ∧
        IsIso (pullback.snd X.hom W₀.ι) :=
  ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

/-- A finite-type modification is in particular a modification. -/
theorem IsFiniteTypeModification.isModification (h : IsFiniteTypeModification B S hS W₀ X) :
    IsModification B S hS W₀ X := h.1

/-- The source of a finite-type modification is an algebraic space. -/
theorem IsFiniteTypeModification.source_isAlgebraicSpace
    (h : IsFiniteTypeModification B S hS W₀ X) : IsAlgebraicSpace B S hS X.left := h.1.1

/-- The structure morphism of a finite-type modification is locally of finite type. -/
theorem IsFiniteTypeModification.isLocallyOfFiniteType
    (h : IsFiniteTypeModification B S hS W₀ X) :
    IsLocallyOfFiniteType B S hS X.hom := h.2

/-- The base change of a finite-type modification to `W₀` is an isomorphism. -/
theorem IsFiniteTypeModification.isIso_pullback_snd
    (h : IsFiniteTypeModification B S hS W₀ X) : IsIso (pullback.snd X.hom W₀.ι) := h.1.2

/-- The base change to `W₀` of an object of the category of finite-type modifications is an
isomorphism. -/
instance FiniteTypeModification.isIso_pullback_snd (M : FiniteTypeModification B S hS W₀) :
    IsIso (pullback.snd M.obj.hom W₀.ι) := M.property.1.2

end FiniteType

/-- A morphism which is an isomorphism over a subfunctor stays an isomorphism over the
preimage of that subfunctor after an arbitrary base change. -/
theorem isIso_pullback_snd_preimage {V W X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : X ⟶ W) (p : V ⟶ W) (W₀ : Subfunctor W) (h : IsIso (pullback.snd g W₀.ι)) :
    IsIso (pullback.snd (pullback.snd g p) (W₀.preimage p).ι) := by
  have hA := IsPullback.of_hasPullback (pullback.snd g p) (W₀.preimage p).ι
  have hB := IsPullback.of_hasPullback g p
  have hC := IsPullback.of_hasPullback g W₀.ι
  have hBig : IsPullback
      (pullback.fst (pullback.snd g p) (W₀.preimage p).ι ≫ pullback.fst g p)
      (pullback.snd (pullback.snd g p) (W₀.preimage p).ι) g
      (W₀.fromPreimage p ≫ W₀.ι) := by
    rw [W₀.fromPreimage_ι p]
    exact (IsPullback.paste_vert hA.flip hB.flip).flip
  have hw : (pullback.fst (pullback.snd g p) (W₀.preimage p).ι ≫ pullback.fst g p) ≫ g
      = (pullback.snd (pullback.snd g p) (W₀.preimage p).ι ≫ W₀.fromPreimage p) ≫ W₀.ι := by
    rw [Category.assoc]
    exact hBig.w
  have hleft : IsPullback
      (pullback.lift _ _ hw) (pullback.snd (pullback.snd g p) (W₀.preimage p).ι)
      (pullback.snd g W₀.ι) (W₀.fromPreimage p) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ hw) hC
    rw [pullback.lift_fst]
    exact hBig
  exact hleft.isIso_snd_of_isIso

/-- Base change of a modification along an arbitrary morphism of algebraic spaces is a
modification outside the preimage of the open subspace. -/
theorem isModification_pullback {V W : AlgebraicSpaces B S hS} (f : V ⟶ W)
    (W₀ : Subfunctor W.obj) (X : Modification B S hS W₀) :
    IsModification B S hS (W₀.preimage f.hom)
      ((Over.pullback f.hom).obj (ObjectProperty.ι (IsModification B S hS W₀) |>.obj X)) :=
  ⟨isAlgebraicSpace_pullback B S hS X.obj.hom f.hom X.property.1 V.property W.property,
    isIso_pullback_snd_preimage B S hS X.obj.hom f.hom W₀ X.property.2⟩

/-- **Stacks 0BGY.** Pullback of modifications, canonically identified with pullback of
their underlying presheaves over the base. -/
@[stacks 0BGY "the base-change functor"]
noncomputable def baseChangeFunctor {V W : AlgebraicSpaces B S hS}
    (f : V ⟶ W) (W₀ : Subfunctor W.obj) :
    Σ F : Modification B S hS W₀ ⥤ Modification B S hS (W₀.preimage f.hom),
      F ⋙ ObjectProperty.ι (IsModification B S hS (W₀.preimage f.hom)) ≅
        ObjectProperty.ι (IsModification B S hS W₀) ⋙ Over.pullback f.hom :=
  ⟨ObjectProperty.lift _ (ObjectProperty.ι (IsModification B S hS W₀) ⋙ Over.pullback f.hom)
      (isModification_pullback B S hS f W₀),
    ObjectProperty.liftCompιIso _ _ _⟩

end AlgebraicGeometry.Space

end
