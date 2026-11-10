module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension

/-!
# The comma square is Guitart exact, and the base change of a right Kan extension along it

Let `R : C₂ ⥤ C₄` and `B : C₃ ⥤ C₄` be two functors into one category.  The comma category
`CategoryTheory.Comma R B` of triples `(X₂, X₃, R X₂ ⟶ B X₃)` sits in the square

```
  Comma R B --fst--> C₂
     |                |
    snd               R
     v                v
     C₃ ----B----->   C₄
```

which commutes up to the tautological `2`-cell `CategoryTheory.Comma.natTrans`, whose component at
an object of the comma category is that object's own structure morphism.  **This square is Guitart
exact**, and therefore Mathlib's base change transformation of right Kan extensions along it is an
isomorphism:

`Ran_B(F) ∘ R ≅ Ran_{fst}(F ∘ snd)`

for every `F : C₃ ⥤ H`.  Read pointwise at an object `X₂` of `C₂`, this says that the limit
computing `(Ran_B F)(R X₂)` — over the objects of `C₃` receiving a map from `R X₂` through `B` —
agrees with the limit over the objects of the comma category lying over `X₂`.  That is the
*flattening* of a right Kan extension followed by a restriction into a single right Kan extension,
which is what makes an iterated Kan extension computable as one limit over a category of tuples.

## Main definitions

* `CategoryTheory.TwoSquare.commaSquare` — the square above, as a `CategoryTheory.TwoSquare`.
* `CategoryTheory.TwoSquare.ranCommaIso` — the isomorphism
  `B.ran ⋙ (-) ∘ R ≅ (-) ∘ snd ⋙ fst.ran` of functors `(C₃ ⥤ H) ⥤ (C₂ ⥤ H)`, i.e. the base change
  of the comma square, which the Guitart exactness below makes invertible.

## Main results

* `CategoryTheory.TwoSquare.guitartExact_commaSquare` — **the comma square is Guitart exact.**

## Implementation notes

Guitart exactness is proved in the form
`CategoryTheory.TwoSquare.guitartExact_iff_isConnected_downwards`: for every
`g : R X₂ ⟶ B X₃` the auxiliary category of factorizations of `g` through an object of the comma
category is connected.  It does *not* have an initial object: an object of it is a triple
`(X₁, a : X₂ ⟶ X₁.left, b : X₁.right ⟶ X₃)` factoring `g`, and a morphism out of the tautological
factorization `(⟨X₂, X₃, g⟩, 𝟙, 𝟙)` into such a triple would need a morphism
`X₃ ⟶ X₁.right` pointing the wrong way.  What is true is that every object is joined to the
tautological one by a zigzag of length two, through the factorization
`(⟨X₂, X₁.right, R a ≫ X₁.hom⟩, 𝟙, b)` which maps to both; that is `commaZigzagMid` below.

-/

@[expose] public section

namespace CategoryTheory

open Category CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]

namespace TwoSquare

variable (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- **The comma square.**  The two projections of `CategoryTheory.Comma R B` together with `R` and
`B` form a square of categories which commutes up to the `2`-cell whose component at an object of
the comma category is that object's structure morphism. -/
def commaSquare : TwoSquare (Comma.fst R B) (Comma.snd R B) R B :=
  Comma.natTrans R B

/-- The component of the `2`-cell of `commaSquare R B` at an object `X` of the comma category is
the structure morphism `X.hom`. -/
@[simp]
theorem commaSquare_app (X : Comma R B) : (commaSquare R B).app X = X.hom :=
  rfl

variable {R B} {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)

/-- **The tautological factorization of `g : R X₂ ⟶ B X₃`**: the object of the comma category
`⟨X₂, X₃, g⟩` itself, with both legs the identity. -/
abbrev commaDownwardsSelf : (commaSquare R B).CostructuredArrowDownwards g :=
  CostructuredArrowDownwards.mk _ g ⟨X₂, X₃, g⟩ (𝟙 X₂) (𝟙 X₃) (by simp)

variable (X₁ : Comma R B) (a : X₂ ⟶ X₁.left) (b : X₁.right ⟶ X₃)
  (comm : R.map a ≫ (commaSquare R B).app X₁ ≫ B.map b = g)

/-- **The middle term of the zigzag joining a factorization of `g` to the tautological one.**  A
factorization of `g` through `X₁` with legs `a` and `b` is refined by the one through
`⟨X₂, X₁.right, R a ≫ X₁.hom⟩` whose first leg is the identity; this one admits a morphism both to
the given factorization and to the tautological one. -/
abbrev commaZigzagMid : (commaSquare R B).CostructuredArrowDownwards g :=
  CostructuredArrowDownwards.mk _ g ⟨X₂, X₁.right, R.map a ≫ X₁.hom⟩ (𝟙 X₂) b (by
    simpa using comm)

/-- The morphism of comma objects underlying `commaZigzagMidToSelf`. -/
def commaZigzagMidHomSelf :
    (⟨X₂, X₁.right, R.map a ≫ X₁.hom⟩ : Comma R B) ⟶ X₁ :=
  CommaMorphism.mk a (𝟙 X₁.right) (by simp)

/-- The morphism of comma objects underlying `commaZigzagMidToTaut`. -/
def commaZigzagMidHomTaut :
    (⟨X₂, X₁.right, R.map a ≫ X₁.hom⟩ : Comma R B) ⟶ ⟨X₂, X₃, g⟩ :=
  CommaMorphism.mk (𝟙 X₂) b (by simpa using comm.symm)

/-- The middle term of the zigzag maps to the given factorization. -/
def commaZigzagMidToSelf : commaZigzagMid g X₁ a b comm ⟶
    CostructuredArrowDownwards.mk _ g X₁ a b comm := by
  refine CostructuredArrow.homMk
    (StructuredArrow.homMk (commaZigzagMidHomSelf X₁ a) ?_) ?_
  · simp [commaZigzagMidHomSelf]
  · ext
    dsimp [structuredArrowDownwards, Comma.mapRight, StructuredArrow.pre,
      StructuredArrow.post, StructuredArrow.homMk]
    simp [commaZigzagMidHomSelf]

/-- The middle term of the zigzag maps to the tautological factorization. -/
def commaZigzagMidToTaut : commaZigzagMid g X₁ a b comm ⟶ commaDownwardsSelf g := by
  refine CostructuredArrow.homMk
    (StructuredArrow.homMk (commaZigzagMidHomTaut g X₁ a b comm) ?_) ?_
  · simp [commaZigzagMidHomTaut]
  · ext
    dsimp [structuredArrowDownwards, Comma.mapRight, StructuredArrow.pre,
      StructuredArrow.post, StructuredArrow.homMk, StructuredArrow.Hom.right]
    simp [commaZigzagMidHomTaut]

/-- **The comma square is Guitart exact.**  Every factorization of `g : R X₂ ⟶ B X₃` through an
object of the comma category is joined to the tautological one by a zigzag of length two, through
`commaZigzagMid`, so the category of such factorizations is connected. -/
instance guitartExact_commaSquare : (commaSquare R B).GuitartExact := by
  rw [guitartExact_iff_isConnected_downwards]
  intro X₂ X₃ g
  have key : ∀ A : (commaSquare R B).CostructuredArrowDownwards g,
      Zigzag A (commaDownwardsSelf g) := by
    intro A
    obtain ⟨X₁, a, b, comm, rfl⟩ := CostructuredArrowDownwards.mk_surjective A
    exact Relation.ReflTransGen.trans
      (Relation.ReflTransGen.single
        (Or.inr ⟨commaZigzagMidToSelf g X₁ a b comm⟩))
      (Relation.ReflTransGen.single
        (Or.inl ⟨commaZigzagMidToTaut g X₁ a b comm⟩))
  have : Nonempty ((commaSquare R B).CostructuredArrowDownwards g) :=
    ⟨commaDownwardsSelf g⟩
  exact zigzag_isConnected fun A A' ↦ (key A).trans (zigzag_equivalence.symm (key A'))

section BaseChange

variable {H : Type u₁} [Category.{v₁} H] (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)
  [∀ F : Comma R B ⥤ H, (Comma.fst R B).HasRightKanExtension F]
  [∀ F : C₃ ⥤ H, B.HasPointwiseRightKanExtension F]

/-- **The base change of a right Kan extension along the comma square.**  Restricting the right
Kan extension of `F : C₃ ⥤ H` along `B` to `C₂` through `R` is the right Kan extension along the
first projection of `CategoryTheory.Comma R B` of the restriction of `F` along the second
projection.

This is the flattening of a right Kan extension followed by a restriction into a single right Kan
extension, and it is Mathlib's base change transformation of the square, invertible because
`guitartExact_commaSquare` says the square is Guitart exact. -/
noncomputable def ranCommaIso :
    B.ran ⋙ (Functor.whiskeringLeft C₂ C₄ H).obj R ≅
      (Functor.whiskeringLeft (Comma R B) C₃ H).obj (Comma.snd R B) ⋙ (Comma.fst R B).ran :=
  asIso (commaSquare R B).ranBaseChange

end BaseChange

end TwoSquare

end CategoryTheory

end
