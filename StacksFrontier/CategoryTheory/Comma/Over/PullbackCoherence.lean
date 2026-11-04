module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coherence of a compositor of right adjoints, and the cocycle law for `Over.pullback`

A compositor of left adjoints, `τ : L₀₁ ⋙ L₁₂ ⟶ L₀₂`, has a mate `R₂₀ ⟶ R₂₁ ⋙ R₁₀` between
the right adjoints.  The first half of this file shows that the mate inherits the associativity
cocycle law: if the compositors of the left adjoints satisfy it, so do their mates.  This is the
dual of `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`, which transports a cocycle law in
the opposite direction, from the right adjoints to the left adjoints.

The second half applies this to the over categories.  `CategoryTheory.Over.map` is a *strict*
functor of the base — `CategoryTheory.Over.mapComp_eq` is an equality of functors — and
`CategoryTheory.Over.pullback` is its right adjoint, with `CategoryTheory.Over.pullbackComp`
the mate of `CategoryTheory.Over.mapComp`.  So the cocycle law for `Over.pullbackComp` is a
formal consequence of the strictness of `Over.map`, even though `Over.pullbackComp` is itself a
genuine comparison of fibre products and not an identity.

## Main definitions

* `CategoryTheory.Adjunction.rightAdjointCompNatTrans` is the mate, between the right adjoints,
  of a compositor of left adjoints.
* `CategoryTheory.Over.pullbackCongr'` transports the pullback functor along an equality of
  morphisms of the base; it is the mate of `CategoryTheory.Over.mapCongr`.

## Main results

* `CategoryTheory.Adjunction.rightAdjointCompNatTrans_assoc`: the mates of three compositors of
  left adjoints satisfying the associativity cocycle law again satisfy it.
* `CategoryTheory.Over.mapComp_assoc`: the cocycle law for `CategoryTheory.Over.mapComp`.
* `CategoryTheory.Over.pullbackComp_assoc'`: the cocycle law for
  `CategoryTheory.Over.pullbackComp`.
* `CategoryTheory.Over.isEquivalence_pullback_of_isIso`: base change along an isomorphism is an
  equivalence of slice categories, which is the unit counterpart of those two laws and the one
  Mathlib carries for `CategoryTheory.Over.map` only.

## Implementation notes

The proof of `rightAdjointCompNatTrans_assoc` is the image of the hypothesis under
`CategoryTheory.conjugateEquiv`, rewritten by the three compatibilities of the mates calculus
that Mathlib supplies: `CategoryTheory.conjugateEquiv_comp` for a composite,
`CategoryTheory.conjugateEquiv_whiskerLeft` and `CategoryTheory.conjugateEquiv_whiskerRight`
for the two whiskerings, and `CategoryTheory.conjugateEquiv_associator_hom` for the associator.
Unlike the left-adjoint version in Mathlib, no surjectivity of the conjugation bijection is
needed: the cocycle law is being pushed along the bijection rather than pulled back through it.

The base of `Over.pullbackComp (f ≫ g) h` is `(f ≫ g) ≫ h` while the base of
`Over.pullbackComp f (g ≫ h)` is `f ≫ g ≫ h`, and these are equal but not syntactically so; the
cocycle law therefore carries one `CategoryTheory.Over.pullbackCongr'`, which is the identity
whenever associativity in the base category holds definitionally.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]

section

variable {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
  {L₀₂ : A ⥤ C} {R₂₀ : C ⥤ A}
  (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₀₂ : L₀₂ ⊣ R₂₀)

/-- The mate of a compositor `L₀₁ ⋙ L₁₂ ⟶ L₀₂` of left adjoints: the natural transformation
`R₂₀ ⟶ R₂₁ ⋙ R₁₀` between the right adjoints conjugate to it. -/
def rightAdjointCompNatTrans (τ : L₀₁ ⋙ L₁₂ ⟶ L₀₂) : R₂₀ ⟶ R₂₁ ⋙ R₁₀ :=
  conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂) τ

end

variable {L₀₁ : A ⥤ B} {R₁₀ : B ⥤ A} {L₁₂ : B ⥤ C} {R₂₁ : C ⥤ B}
  {L₂₃ : C ⥤ D} {R₃₂ : D ⥤ C} {L₀₂ : A ⥤ C} {R₂₀ : C ⥤ A}
  {L₁₃ : B ⥤ D} {R₃₁ : D ⥤ B} {L₀₃ : A ⥤ D} {R₃₀ : D ⥤ A}
  (adj₀₁ : L₀₁ ⊣ R₁₀) (adj₁₂ : L₁₂ ⊣ R₂₁) (adj₂₃ : L₂₃ ⊣ R₃₂)
  (adj₀₂ : L₀₂ ⊣ R₂₀) (adj₁₃ : L₁₃ ⊣ R₃₁) (adj₀₃ : L₀₃ ⊣ R₃₀)

/-- **The associativity cocycle law passes from a compositor of left adjoints to its mate.**
If four compositors of left adjoints satisfy the cocycle law, then so do the four mates between
the right adjoints.

This is the dual of `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`, which carries a
cocycle law from the right adjoints to the left adjoints. -/
theorem rightAdjointCompNatTrans_assoc
    (τ₀₁₂ : L₀₁ ⋙ L₁₂ ⟶ L₀₂) (τ₁₂₃ : L₁₂ ⋙ L₂₃ ⟶ L₁₃)
    (τ₀₁₃ : L₀₁ ⋙ L₁₃ ⟶ L₀₃) (τ₀₂₃ : L₀₂ ⋙ L₂₃ ⟶ L₀₃)
    (h : whiskerRight τ₀₁₂ L₂₃ ≫ τ₀₂₃ =
      (associator L₀₁ L₁₂ L₂₃).hom ≫ whiskerLeft L₀₁ τ₁₂₃ ≫ τ₀₁₃) :
    rightAdjointCompNatTrans adj₀₂ adj₂₃ adj₀₃ τ₀₂₃ ≫
        whiskerLeft R₃₂ (rightAdjointCompNatTrans adj₀₁ adj₁₂ adj₀₂ τ₀₁₂) =
      rightAdjointCompNatTrans adj₀₁ adj₁₃ adj₀₃ τ₀₁₃ ≫
        whiskerRight (rightAdjointCompNatTrans adj₁₂ adj₂₃ adj₁₃ τ₁₂₃) R₁₀ ≫
          (associator R₃₂ R₂₁ R₁₀).hom := by
  have key := congrArg (conjugateEquiv adj₀₃ ((adj₀₁.comp adj₁₂).comp adj₂₃)) h
  rw [← conjugateEquiv_comp adj₀₃ (adj₀₂.comp adj₂₃) ((adj₀₁.comp adj₁₂).comp adj₂₃)
      τ₀₂₃ (whiskerRight τ₀₁₂ L₂₃),
    conjugateEquiv_whiskerRight adj₀₂ (adj₀₁.comp adj₁₂) adj₂₃ τ₀₁₂] at key
  rw [← conjugateEquiv_comp adj₀₃ (adj₀₁.comp (adj₁₂.comp adj₂₃))
      ((adj₀₁.comp adj₁₂).comp adj₂₃) (whiskerLeft L₀₁ τ₁₂₃ ≫ τ₀₁₃)
      (associator L₀₁ L₁₂ L₂₃).hom,
    conjugateEquiv_associator_hom adj₀₁ adj₁₂ adj₂₃,
    ← conjugateEquiv_comp adj₀₃ (adj₀₁.comp adj₁₃) (adj₀₁.comp (adj₁₂.comp adj₂₃))
      τ₀₁₃ (whiskerLeft L₀₁ τ₁₂₃),
    conjugateEquiv_whiskerLeft adj₁₃ (adj₁₂.comp adj₂₃) adj₀₁ τ₁₂₃] at key
  simpa only [rightAdjointCompNatTrans, Category.assoc] using key

end CategoryTheory.Adjunction

namespace CategoryTheory.Over

open CategoryTheory.Adjunction

universe v u

variable {T : Type u} [Category.{v} T]

/-- The inverse image along two equal morphisms of the base: the mate of
`CategoryTheory.Over.mapCongr`.

Only pullbacks along the two morphisms are assumed, and the isomorphism runs from the inverse
image along the right-hand morphism to the one along the left-hand morphism; both differ from
`CategoryTheory.Over.pullbackCongr` of
`StacksFrontier.CategoryTheory.Sites.RelocalizationMorphism`, which assumes all pullbacks in the
base and runs in the other direction. -/
noncomputable def pullbackCongr' {X Y : T} {a b : X ⟶ Y} (e : a = b) [HasPullbacksAlong a]
    [HasPullbacksAlong b] : pullback b ≅ pullback a :=
  conjugateIsoEquiv (mapPullbackAdj b) (mapPullbackAdj a) (Over.mapCongr a b e)

/-- `CategoryTheory.Over.pullbackComp` is the mate of `CategoryTheory.Over.mapComp`. -/
theorem pullbackComp_hom {W X Y : T} (f : W ⟶ X) (g : X ⟶ Y) [HasPullbacksAlong f]
    [HasPullbacksAlong g] :
    (pullbackComp f g).hom =
      rightAdjointCompNatTrans (mapPullbackAdj f) (mapPullbackAdj g)
        (mapPullbackAdj (f ≫ g)) (Over.mapComp f g).inv :=
  rfl

/-- **The cocycle law for `CategoryTheory.Over.mapComp`.**  The two ways of comparing
`map f ⋙ map g ⋙ map h` with `map (f ≫ g ≫ h)` agree.  Both sides are the identity on the
underlying objects, so this holds componentwise. -/
theorem mapComp_assoc {W X Y Z : T} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    whiskerRight (Over.mapComp f g).inv (map h) ≫
        (Over.mapComp (f ≫ g) h).inv ≫ (Over.mapCongr _ _ (Category.assoc f g h)).hom =
      (associator (map f) (map g) (map h)).hom ≫
        whiskerLeft (map f) (Over.mapComp g h).inv ≫ (Over.mapComp f (g ≫ h)).inv := by
  ext A
  simp [Over.mapComp, Over.mapCongr]

/-- **The cocycle law for `CategoryTheory.Over.pullbackComp`.**  The two ways of comparing
`pullback (f ≫ g ≫ h)` with `pullback h ⋙ pullback g ⋙ pullback f` agree.

The inverse image along a morphism of the base is a genuine comparison of fibre products and
not an identity, but it is the right adjoint of `CategoryTheory.Over.map`, which *is* strict;
the cocycle law is the mate of `CategoryTheory.Over.mapComp_assoc`.

Only pullbacks along the morphisms involved are assumed, and the law is stated as an equality
of two composites of comparison isomorphisms; both differ from
`CategoryTheory.Over.pullbackComp_assoc` of
`StacksFrontier.CategoryTheory.Bicategory.OverPullbackPseudofunctor`, which assumes all pullbacks
in the base and states the pentagon as a single composite equal to an `eqToHom`. -/
@[sga "4 VI 6.1.2" "special case"]
theorem pullbackComp_assoc' {W X Y Z : T} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    [HasPullbacksAlong f] [HasPullbacksAlong g] [HasPullbacksAlong h]
    [HasPullbacksAlong (f ≫ g)] [HasPullbacksAlong (g ≫ h)]
    [HasPullbacksAlong ((f ≫ g) ≫ h)] [HasPullbacksAlong (f ≫ g ≫ h)] :
    (pullbackCongr' (Category.assoc f g h)).hom ≫ (pullbackComp (f ≫ g) h).hom ≫
        whiskerLeft (pullback h) (pullbackComp f g).hom =
      (pullbackComp f (g ≫ h)).hom ≫
        whiskerRight (pullbackComp g h).hom (pullback f) ≫
          (associator (pullback h) (pullback g) (pullback f)).hom := by
  have key := rightAdjointCompNatTrans_assoc (mapPullbackAdj f) (mapPullbackAdj g)
    (mapPullbackAdj h) (mapPullbackAdj (f ≫ g)) (mapPullbackAdj (g ≫ h))
    (mapPullbackAdj (f ≫ g ≫ h)) (Over.mapComp f g).inv (Over.mapComp g h).inv
    (Over.mapComp f (g ≫ h)).inv
    ((Over.mapComp (f ≫ g) h).inv ≫ (Over.mapCongr _ _ (Category.assoc f g h)).hom)
    (mapComp_assoc f g h)
  rw [rightAdjointCompNatTrans, ← conjugateEquiv_comp (mapPullbackAdj (f ≫ g ≫ h))
      (mapPullbackAdj ((f ≫ g) ≫ h))
      ((mapPullbackAdj (f ≫ g)).comp (mapPullbackAdj h))] at key
  simpa only [pullbackComp_hom, pullbackCongr', conjugateIsoEquiv_apply_hom,
    rightAdjointCompNatTrans, Category.assoc] using key

/-- **Base change along an isomorphism is an equivalence of slice categories.**
`CategoryTheory.Over.map` along an isomorphism is an equivalence,
`CategoryTheory.Over.mapIso`, and `CategoryTheory.Over.pullback` is its right adjoint,
`CategoryTheory.Over.mapPullbackAdj`; the right adjoint of an equivalence is an equivalence.

Mathlib carries this for `CategoryTheory.Over.map` and not for
`CategoryTheory.Over.pullback`, so this is what lets instance synthesis find the latter. -/
instance isEquivalence_pullback_of_isIso {X Y : T} (f : X ⟶ Y) [IsIso f]
    [HasPullbacksAlong f] : (pullback f).IsEquivalence :=
  (mapPullbackAdj f).isEquivalence_right_of_isEquivalence_left

end CategoryTheory.Over

end
