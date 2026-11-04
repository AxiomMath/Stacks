module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# The mate of a natural transformation into a right adjoint

Let `L ⊣ R` be an adjunction and let `P : A ⥤ B`, `Q : A ⥤ C` be functors into its two sides.
A natural transformation `β : P ⟶ Q ⋙ R` then has a mate `P ⋙ L ⟶ Q`, given at an object by
the adjunct of the component of `β`.

## Main definitions

* `CategoryTheory.Adjunction.mateNatTrans`: the mate `P ⋙ L ⟶ Q` of a natural transformation
  `P ⟶ Q ⋙ R`.

## Main results

* `CategoryTheory.Adjunction.mateNatTrans_app_homEquiv_symm`: its component at an object is the
  adjunct of the component of the given transformation.
* `CategoryTheory.Adjunction.mateNatTrans_eq_whiskerRight_homEquiv_symm`: the construction is
  the inverse hom-set bijection of `CategoryTheory.Adjunction.whiskerRight`.
* `CategoryTheory.Adjunction.mateNatTrans_bijective`: the construction is a bijection.
* `CategoryTheory.Adjunction.mateNatTrans_comp_left` and
  `CategoryTheory.Adjunction.mateNatTrans_comp_right`: naturality in the two functors `P`
  and `Q`.
* `CategoryTheory.Adjunction.mateNatTrans_whiskerLeft`: compatibility with reindexing the
  source category.
* `CategoryTheory.Adjunction.mateNatTrans_unit` and
  `CategoryTheory.Adjunction.mateNatTrans_id`: the mate of the whiskered unit is the identity,
  and the mate of the identity is the whiskered counit.

## Implementation notes

The point of the construction is that the naturality square of the mate is proved here, once,
at free variables: it is the naturality of the given transformation followed by the naturality
of the counit. Taking the adjunct one object at a time gives a family with the same components
but no naturality, and proving naturality for that family at concretely given functors forces
the unifier to compare the two sides of the square after unfolding whatever those functors are
built from.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A : Type*} [Category* A] {B : Type*} [Category* B] {C : Type*} [Category* C]
  {L : B ⥤ C} {R : C ⥤ B} (adj : L ⊣ R) (P : A ⥤ B) (Q : A ⥤ C)

/-- The mate `P ⋙ L ⟶ Q` of a natural transformation `β : P ⟶ Q ⋙ R` along an adjunction
`L ⊣ R`: at an object it is the adjunct of the component of `β`. -/
@[simps]
def mateNatTrans (β : P ⟶ Q ⋙ R) : P ⋙ L ⟶ Q where
  app X := L.map (β.app X) ≫ adj.counit.app (Q.obj X)
  naturality {X Y} f := by
    dsimp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, β.naturality f, Functor.comp_map, Functor.map_comp_assoc,
      adj.counit_naturality, Category.assoc]

/-- The component of the mate at `X` is the image of `β.app X` under the inverse of the hom-set
bijection of the adjunction. -/
theorem mateNatTrans_app_homEquiv_symm (β : P ⟶ Q ⋙ R) (X : A) :
    (adj.mateNatTrans P Q β).app X =
      (adj.homEquiv (P.obj X) (Q.obj X)).symm (β.app X) :=
  (adj.homEquiv_counit _ _ (β.app X)).symm

/-- **The mate is the inverse hom-set bijection of the whiskered adjunction.** Postcomposition
with `L` is left adjoint to postcomposition with `R` on functors out of `A`
(`CategoryTheory.Adjunction.whiskerRight`), and `mateNatTrans` is the inverse of that
adjunction's hom-set bijection at `P` and `Q`.

This is how a generic fact about an adjunction is brought to bear on the construction, for
instance `CategoryTheory.Adjunction.mateNatTrans_bijective`. -/
theorem mateNatTrans_eq_whiskerRight_homEquiv_symm (β : P ⟶ Q ⋙ R) :
    adj.mateNatTrans P Q β = ((Adjunction.whiskerRight A adj).homEquiv P Q).symm β := by
  ext X
  rw [Adjunction.homEquiv_counit]
  simp [Adjunction.whiskerRight]

/-- The mate is a bijection: a transformation `P ⋙ L ⟶ Q` comes from exactly one
transformation `P ⟶ Q ⋙ R`. -/
theorem mateNatTrans_bijective : Function.Bijective (adj.mateNatTrans P Q) := by
  have h : adj.mateNatTrans P Q = ((Adjunction.whiskerRight A adj).homEquiv P Q).symm :=
    funext fun β => adj.mateNatTrans_eq_whiskerRight_homEquiv_symm P Q β
  rw [h]
  exact (Adjunction.whiskerRight A adj).homEquiv P Q |>.symm.bijective

variable {P Q}

/-- Naturality of the mate in the source functor: precomposing the given transformation with
`f : P' ⟶ P` whiskers the mate by `f`. -/
@[reassoc]
theorem mateNatTrans_comp_left {P' : A ⥤ B} (f : P' ⟶ P) (β : P ⟶ Q ⋙ R) :
    adj.mateNatTrans P' Q (f ≫ β) = Functor.whiskerRight f L ≫ adj.mateNatTrans P Q β := by
  ext X
  simp

/-- Naturality of the mate in the target functor: postcomposing the given transformation with
`Q.map g` whiskered into `R` appends `g` to the mate. -/
@[reassoc]
theorem mateNatTrans_comp_right {Q' : A ⥤ C} (β : P ⟶ Q ⋙ R) (g : Q ⟶ Q') :
    adj.mateNatTrans P Q' (β ≫ Functor.whiskerRight g R) = adj.mateNatTrans P Q β ≫ g := by
  ext X
  simp [adj.counit_naturality]

/-- The mate commutes with reindexing the source category: whiskering the mate on the left by
`T` is the mate of the transformation whiskered on the left by `T`. -/
theorem mateNatTrans_whiskerLeft {A' : Type*} [Category* A'] (T : A' ⥤ A) (β : P ⟶ Q ⋙ R) :
    Functor.whiskerLeft T (adj.mateNatTrans P Q β) =
      adj.mateNatTrans (T ⋙ P) (T ⋙ Q) (Functor.whiskerLeft T β) :=
  rfl

variable (P Q)

/-- The mate of the unit is the identity: this is the left triangle identity. -/
theorem mateNatTrans_unit :
    adj.mateNatTrans P (P ⋙ L) (Functor.whiskerLeft P adj.unit) = 𝟙 (P ⋙ L) := by
  ext X
  simp

/-- The mate of the identity is the counit. -/
theorem mateNatTrans_id :
    adj.mateNatTrans (Q ⋙ R) Q (𝟙 (Q ⋙ R)) = Functor.whiskerLeft Q adj.counit := by
  ext X
  simp

end CategoryTheory.Adjunction

end
