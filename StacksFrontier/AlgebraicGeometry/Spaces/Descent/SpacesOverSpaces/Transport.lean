module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescentData
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Products

/-!
# Transporting along a family of gluing isomorphisms

A family of gluing isomorphisms satisfying a cocycle condition is the same thing as an
operation that *moves* a point of one member of a family of objects over a common base to
another member, along a prescribed image in the base. This file packages that operation as
`CategoryTheory.FamilyTransport` and shows that the two descriptions are interchangeable:
`CategoryTheory.familyTransportOfGluing` builds the operation from the isomorphisms and
`CategoryTheory.FamilyTransport.gluing` builds the isomorphisms back, satisfying the cocycle
condition.

## Main definitions

* `CategoryTheory.FamilyTransport` is the move operation attached to a family of gluing
  isomorphisms, and `CategoryTheory.FamilyTransport.comap` reindexes it.
* `CategoryTheory.FamilyTransport.gluing` and `CategoryTheory.familyTransportOfGluing` convert
  between move operations and families of gluing isomorphisms.
* `CategoryTheory.BaseChangeSquare` is a square with the lifting property used for base change,
  `CategoryTheory.FamilyBaseChangeSquare` a family of them, and
  `CategoryTheory.FamilyTransport.baseChange` the resulting base-changed move operation.
* `CategoryTheory.BaseChangeSquare.compare` compares two lifts of the same object along maps
  completing the same square.
* `CategoryTheory.overBaseChangeSquare` turns a pullback square of underlying objects into a
  base-change square of over-categories.

## Main results

* `CategoryTheory.FamilyTransport.gluing_cocycle`: the gluing isomorphisms of a move operation
  satisfy the cocycle condition.
* `CategoryTheory.FamilyTransport.baseChange_gluing` and
  `CategoryTheory.FamilyTransport.move_baseChange` are the two directions of the statement that
  base change of a move operation is base change of its gluing isomorphisms.
* `CategoryTheory.FamilyTransport.gluing_comm`: a family of maps commuting with two move
  operations commutes with their gluing isomorphisms.
* `CategoryTheory.BaseChangeSquare.map_move`, `CategoryTheory.BaseChangeSquare.compare_comp`,
  `CategoryTheory.BaseChangeSquare.compare_move`,
  `CategoryTheory.BaseChangeSquare.compare_naturality` and
  `CategoryTheory.BaseChangeSquare.compare_gluing` describe the comparison maps.

## References

* [Stacks Project, Tag 0ADI](https://stacks.math.columbia.edu/tag/0ADI)
-/

@[expose] public section

noncomputable section

open CategoryTheory.Limits

universe w w' v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']

/-- The operation of moving a point of one member of a family of objects over a common base to
another member, along a prescribed image in the base. -/
structure FamilyTransport {I : Type w} (A B : I → C) (p : ∀ i, A i ⟶ B i) where
  /-- Move a point of `A i` to the member `A j` singled out by a point of `B j`. -/
  move {i j : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) : Z ⟶ A j
  /-- Moving is natural in the source object. -/
  comp_move {i j : I} {Z W : C} (k : W ⟶ Z) (v : Z ⟶ A i) (y : Z ⟶ B j) :
    k ≫ move v y = move (k ≫ v) (k ≫ y)
  /-- A moved point lies over the point of the base it was moved to. -/
  move_base {i j : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) : move v y ≫ p j = y
  /-- Moving a point to its own image in the base does nothing. -/
  move_self {i : I} {Z : C} (v : Z ⟶ A i) : move v (v ≫ p i) = v
  /-- Moving twice is moving once. -/
  move_comp {i j k : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) (z : Z ⟶ B k) :
    move (move v y) z = move v z

namespace FamilyTransport

variable {I : Type w} {A B : I → C} {p : ∀ i, A i ⟶ B i}

/-- Reindexing a move operation along a map of index types. -/
def comap (t : FamilyTransport A B p) {I' : Type w'} (α : I' → I) :
    FamilyTransport (fun i ↦ A (α i)) (fun i ↦ B (α i)) (fun i ↦ p (α i)) where
  move v y := t.move v y
  comp_move k v y := t.comp_move k v y
  move_base v y := t.move_base v y
  move_self v := t.move_self v
  move_comp v y z := t.move_comp v y z

/-- Reindexing does not change the move operation. -/
@[simp]
lemma comap_move (t : FamilyTransport A B p) {I' : Type w'} (α : I' → I) {i j : I'} {Z : C}
    (v : Z ⟶ A (α i)) (y : Z ⟶ B (α j)) : (t.comap α).move v y = t.move v y := rfl

variable [HasBinaryProducts C]

/-- The gluing isomorphism between the two ways of forming a pairwise product, recovered from
the move operation. -/
def gluing (t : FamilyTransport A B p) (i j : I) :
    Over.mk (prod.map (p i) (𝟙 (B j))) ≅ Over.mk (prod.map (𝟙 (B i)) (p j)) := by
  refine Over.isoMk ⟨prod.lift (prod.fst ≫ p i) (t.move prod.fst prod.snd),
    prod.lift (t.move prod.snd prod.fst) (prod.snd ≫ p j), ?_, ?_⟩ ?_
  all_goals
    apply prod.hom_ext <;>
      simp [prod.comp_lift, t.comp_move, t.move_base, t.move_comp, t.move_self]

/-- The underlying map of the gluing isomorphism of a move operation: the first projection is
carried to the base and the second to the moved point. -/
@[simp]
lemma gluing_hom (t : FamilyTransport A B p) (i j : I) :
    (t.gluing i j).hom.left = prod.lift (prod.fst ≫ p i) (t.move prod.fst prod.snd) := rfl

/-- Reindexing does not change the gluing isomorphisms. -/
@[simp]
lemma comap_gluing (t : FamilyTransport A B p) {I' : Type w'} (α : I' → I) (i j : I') :
    (t.comap α).gluing i j = t.gluing (α i) (α j) := rfl

/-- The gluing isomorphisms recovered from a move operation satisfy the cocycle condition. -/
lemma gluing_cocycle (t : FamilyTransport A B p) (i j k : I) :
    prod.map (t.gluing i j).hom.left (𝟙 (B k)) ≫ prodMapLastTwo (t.gluing j k).hom.left =
      prodMapFirstThird (t.gluing i k).hom.left := by
  apply prod.hom_ext
  all_goals (try apply prod.hom_ext) <;>
    simp [prodMapLastTwo, prodMapFirstThird, Limits.prod.associator, prod.braiding,
      prod.comp_lift, t.comp_move, t.move_base, t.move_comp]

/-- A family of maps commuting with two move operations over the same base commutes with their
gluing isomorphisms. -/
lemma gluing_comm {E : I → C} {s : ∀ i, E i ⟶ B i} (t : FamilyTransport A B p)
    (u : FamilyTransport E B s) (m : ∀ i, A i ⟶ E i) (hm : ∀ i, m i ≫ s i = p i)
    (ht : ∀ {i j : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j),
      t.move v y ≫ m j = u.move (v ≫ m i) y) (i j : I) :
    prod.map (m i) (𝟙 (B j)) ≫ (u.gluing i j).hom.left =
      (t.gluing i j).hom.left ≫ prod.map (𝟙 (B i)) (m j) := by
  apply prod.hom_ext <;> simp [hm, ht, u.comp_move]

end FamilyTransport

/-- The move operation attached to a family of gluing isomorphisms satisfying the cocycle
condition. -/
def familyTransportOfGluing {I : Type w} [HasBinaryProducts C] {A B : I → C}
    (p : ∀ i, A i ⟶ B i)
    (gluing : ∀ i j, Over.mk (prod.map (p i) (𝟙 (B j))) ≅ Over.mk (prod.map (𝟙 (B i)) (p j)))
    (cocycle : ∀ i j k, prod.map (gluing i j).hom.left (𝟙 (B k)) ≫
        prodMapLastTwo (gluing j k).hom.left = prodMapFirstThird (gluing i k).hom.left) :
    FamilyTransport A B p := by
  let move {i j : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) :=
    prod.lift v y ≫ (gluing i j).hom.left ≫ prod.snd
  have comp_move {i j : I} {Z W : C} (k : W ⟶ Z) (v : Z ⟶ A i) (y : Z ⟶ B j) :
      k ≫ move v y = move (k ≫ v) (k ≫ y) := by
    simp [move, ← prod.comp_lift, Category.assoc]
  have move_base {i j : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) : move v y ≫ p j = y := by
    have hg := congrArg (fun k ↦ k ≫ prod.snd) (Over.w (gluing i j).hom)
    simpa [move, Category.assoc] using congrArg (fun k ↦ prod.lift v y ≫ k) hg
  have move_comp {i j k : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) (z : Z ⟶ B k) :
      move (move v y) z = move v z := by
    simpa [move, prodMapLastTwo, prodMapFirstThird, Limits.prod.associator, prod.braiding,
      Category.assoc, prod.comp_lift, prod.comp_lift_assoc, prod.lift_map, move_base] using
      congrArg (fun m ↦ prod.lift (prod.lift v y) z ≫ m ≫ prod.snd) (cocycle i j k)
  have move_self {i : I} {Z : C} (v : Z ⟶ A i) : move v (v ≫ p i) = v := by
    have hk : move ((prod.lift (v ≫ p i) v ≫ (gluing i i).inv.left) ≫ prod.fst)
        ((prod.lift (v ≫ p i) v ≫ (gluing i i).inv.left) ≫ prod.snd) = v := by
      simp only [move, ← prod.comp_lift, prod.lift_fst_snd]
      have hi : (gluing i i).inv.left ≫ (gluing i i).hom.left = 𝟙 _ :=
        congrArg Over.Hom.left (gluing i i).inv_hom_id
      simp [Category.assoc, reassoc_of% hi]
    rw [← hk, move_base, move_comp]
  exact ⟨@move, @comp_move, @move_base, @move_self, @move_comp⟩

/-- The move operation built from a family of gluing isomorphisms lifts a point and its
prescribed image to the pairwise product, applies the gluing isomorphism and takes the second
projection. -/
@[simp]
lemma familyTransportOfGluing_move {I : Type w} [HasBinaryProducts C] {A B : I → C}
    (p : ∀ i, A i ⟶ B i)
    (gluing : ∀ i j, Over.mk (prod.map (p i) (𝟙 (B j))) ≅ Over.mk (prod.map (𝟙 (B i)) (p j)))
    (cocycle : ∀ i j k, prod.map (gluing i j).hom.left (𝟙 (B k)) ≫
        prodMapLastTwo (gluing j k).hom.left = prodMapFirstThird (gluing i k).hom.left)
    {i j : I} {Z : C} (v : Z ⟶ A i) (y : Z ⟶ B j) :
    (familyTransportOfGluing p gluing cocycle).move v y =
      prod.lift v y ≫ (gluing i j).hom.left ≫ prod.snd := rfl

/-- A square whose vertical maps `p` and `p'` live in `C` and `C'`, whose horizontal maps `q`
and `r` go from the image of `C'` under `H` to `C`, and which has the lifting property of a
cartesian square: a map into `A` compatible with a map into `B'` lifts uniquely to `A'`. -/
structure BaseChangeSquare (H : C' ⥤ C) {A B : C} {A' B' : C'} (p : A ⟶ B) (p' : A' ⟶ B')
    (q : H.obj A' ⟶ A) (r : H.obj B' ⟶ B) where
  /-- The square commutes. -/
  square : q ≫ p = H.map p' ≫ r
  /-- The lift of a map to `A` compatible with a map to `B'`. -/
  lift {Z : C'} (v : H.obj Z ⟶ A) (y : Z ⟶ B') (w : v ≫ p = H.map y ≫ r) : Z ⟶ A'
  /-- The lift recovers the map to `A`. -/
  lift_q {Z : C'} (v : H.obj Z ⟶ A) (y : Z ⟶ B') (w : v ≫ p = H.map y ≫ r) :
    H.map (lift v y w) ≫ q = v
  /-- The lift recovers the map to `B'`. -/
  lift_p {Z : C'} (v : H.obj Z ⟶ A) (y : Z ⟶ B') (w : v ≫ p = H.map y ≫ r) :
    lift v y w ≫ p' = y
  /-- The lift is the unique such map. -/
  hom_ext {Z : C'} (v w : Z ⟶ A') : H.map v ≫ q = H.map w ≫ q → v ≫ p' = w ≫ p' → v = w

/-- A family of base-change squares over a family of maps. -/
abbrev FamilyBaseChangeSquare (H : C' ⥤ C) {I : Type w} {A B : I → C} {A' B' : I → C'}
    (p : ∀ i, A i ⟶ B i) (p' : ∀ i, A' i ⟶ B' i) (q : ∀ i, H.obj (A' i) ⟶ A i)
    (r : ∀ i, H.obj (B' i) ⟶ B i) :=
  ∀ i, BaseChangeSquare H (p i) (p' i) (q i) (r i)

namespace FamilyTransport

variable {H : C' ⥤ C} {I : Type w} {A B : I → C} {A' B' : I → C'} {p : ∀ i, A i ⟶ B i}
  {p' : ∀ i, A' i ⟶ B' i} {q : ∀ i, H.obj (A' i) ⟶ A i} {r : ∀ i, H.obj (B' i) ⟶ B i}

/-- The base change of a move operation along a family of base-change squares. -/
def baseChange (L : FamilyBaseChangeSquare H p p' q r) (t : FamilyTransport A B p) :
    FamilyTransport A' B' p' where
  move v y := (L _).lift (t.move (H.map v ≫ q _) (H.map y ≫ r _)) y (t.move_base _ _)
  comp_move k v y := by
    refine (L _).hom_ext _ _ ?_ ?_
    · simp only [Functor.map_comp, Category.assoc, BaseChangeSquare.lift_q]
      rw [t.comp_move]
    · simp only [Category.assoc, BaseChangeSquare.lift_p]
  move_base _ _ := (L _).lift_p _ _ _
  move_self {i} _ v := by
    refine (L _).hom_ext _ _ ?_ ?_
    · simp only [BaseChangeSquare.lift_q, Functor.map_comp]
      rw [Category.assoc, ← (L i).square, ← Category.assoc, t.move_self]
    · simp only [BaseChangeSquare.lift_p]
  move_comp v y z := by
    refine (L _).hom_ext _ _ ?_ ?_
    · simp only [BaseChangeSquare.lift_q, t.move_comp]
    · simp only [BaseChangeSquare.lift_p]

/-- A base-changed moved point projects to the point moved by the original operation. -/
@[simp]
lemma baseChange_move_q (L : FamilyBaseChangeSquare H p p' q r) (t : FamilyTransport A B p)
    {i j : I} {Z : C'} (v : Z ⟶ A' i) (y : Z ⟶ B' j) :
    H.map ((baseChange L t).move v y) ≫ q j = t.move (H.map v ≫ q i) (H.map y ≫ r j) :=
  (L j).lift_q _ _ _

variable [HasBinaryProducts C] [HasBinaryProducts C']

/-- The gluing isomorphisms of a base-changed move operation are the base changes of the
original gluing isomorphisms. -/
lemma baseChange_gluing (L : FamilyBaseChangeSquare H p p' q r) (t : FamilyTransport A B p)
    (i j : I) :
    H.map ((baseChange L t).gluing i j).hom.left ≫
        prod.lift (H.map prod.fst ≫ r i) (H.map prod.snd ≫ q j) =
      prod.lift (H.map prod.fst ≫ q i) (H.map prod.snd ≫ r j) ≫ (t.gluing i j).hom.left := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, gluing_hom]
    rw [← H.map_comp_assoc, prod.lift_fst, H.map_comp]
    simp [(L i).square]
  · simp only [Category.assoc, prod.lift_snd, gluing_hom]
    rw [← H.map_comp_assoc, prod.lift_snd, baseChange_move_q]
    simp [comp_move]

/-- Conversely, a move operation whose gluing isomorphisms are the base changes of the original
ones is the base change of the original move operation. -/
lemma move_baseChange (t : FamilyTransport A B p) (t' : FamilyTransport A' B' p')
    (hg : ∀ i j, H.map (t'.gluing i j).hom.left ≫
        prod.lift (H.map prod.fst ≫ r i) (H.map prod.snd ≫ q j) =
      prod.lift (H.map prod.fst ≫ q i) (H.map prod.snd ≫ r j) ≫ (t.gluing i j).hom.left)
    {i j : I} {Z : C'} (v : Z ⟶ A' i) (y : Z ⟶ B' j) :
    H.map (t'.move v y) ≫ q j = t.move (H.map v ≫ q i) (H.map y ≫ r j) := by
  have he := congrArg (fun k ↦ H.map (prod.lift v y) ≫ k ≫ prod.snd) (hg i j)
  simp only [gluing_hom, Category.assoc, prod.lift_snd] at he
  simp only [comp_move, prod.lift_fst, prod.lift_snd, ← Category.assoc, ← H.map_comp] at he
  simpa [Category.assoc] using he

end FamilyTransport

namespace BaseChangeSquare

attribute [local simp] lift_q lift_p

variable {H : C' ⥤ C} {I : Type w} {A B : I → C} {p : ∀ i, A i ⟶ B i}

/-- A family of maps commuting with two move operations on `C` still commutes with their base
changes to `C'`. -/
lemma map_move {E : I → C} {A' B' E' : I → C'} {s : ∀ i, E i ⟶ B i} {p' : ∀ i, A' i ⟶ B' i}
    {s' : ∀ i, E' i ⟶ B' i} {q : ∀ i, H.obj (A' i) ⟶ A i} {qE : ∀ i, H.obj (E' i) ⟶ E i}
    {r : ∀ i, H.obj (B' i) ⟶ B i} {i j : I}
    (L : BaseChangeSquare H (s j) (s' j) (qE j) (r j)) (t : FamilyTransport A B p)
    (u : FamilyTransport E B s) (t' : FamilyTransport A' B' p') (u' : FamilyTransport E' B' s')
    (ht : ∀ {k l : I} {Z : C'} (v : Z ⟶ A' k) (y : Z ⟶ B' l),
      H.map (t'.move v y) ≫ q l = t.move (H.map v ≫ q k) (H.map y ≫ r l))
    (hu : ∀ {k l : I} {Z : C'} (v : Z ⟶ E' k) (y : Z ⟶ B' l),
      H.map (u'.move v y) ≫ qE l = u.move (H.map v ≫ qE k) (H.map y ≫ r l))
    (m : ∀ i, A i ⟶ E i) (m' : ∀ i, A' i ⟶ E' i) (hp : m' j ≫ s' j = p' j)
    (hq : ∀ k, H.map (m' k) ≫ qE k = q k ≫ m k)
    (hm : ∀ {k l : I} {Z : C} (v : Z ⟶ A k) (y : Z ⟶ B l),
      t.move v y ≫ m l = u.move (v ≫ m k) y)
    {Z : C'} (v : Z ⟶ A' i) (y : Z ⟶ B' j) :
    t'.move v y ≫ m' j = u'.move (v ≫ m' i) y := by
  refine L.hom_ext _ _ ?_ ?_
  · simp only [Functor.map_comp, Category.assoc, hq, hu]
    rw [← Category.assoc, ht, hm]
    simp only [Category.assoc]
  · simp [Category.assoc, hp, t'.move_base, u'.move_base]

section Compare

variable {i : I} {A' B' A₀ : C'} {p' : A' ⟶ B'} {p₀ : A₀ ⟶ B'} {q : H.obj A' ⟶ A i}
  {q₀ : H.obj A₀ ⟶ A i} {r r₀ : H.obj B' ⟶ B i}

/-- The comparison map from one lift of `A i` to another, along the map prescribed by the move
operation. -/
def compare (L : BaseChangeSquare H (p i) p' q r) (t : FamilyTransport A B p) (p₀ : A₀ ⟶ B')
    (q₀ : H.obj A₀ ⟶ A i) : A₀ ⟶ A' :=
  L.lift (t.move q₀ (H.map p₀ ≫ r)) p₀ (t.move_base _ _)

/-- The comparison map projects to the map prescribed by the move operation. -/
@[simp]
lemma compare_q (L : BaseChangeSquare H (p i) p' q r) (t : FamilyTransport A B p)
    (p₀ : A₀ ⟶ B') (q₀ : H.obj A₀ ⟶ A i) :
    H.map (L.compare t p₀ q₀) ≫ q = t.move q₀ (H.map p₀ ≫ r) := L.lift_q _ _ _

/-- The comparison map lies over the structure map of its source. -/
@[simp]
lemma compare_p (L : BaseChangeSquare H (p i) p' q r) (t : FamilyTransport A B p)
    (p₀ : A₀ ⟶ B') (q₀ : H.obj A₀ ⟶ A i) : L.compare t p₀ q₀ ≫ p' = p₀ := L.lift_p _ _ _

/-- The two comparison maps between two lifts of the same object are mutually inverse. -/
lemma compare_comp (L : BaseChangeSquare H (p i) p' q r) (t : FamilyTransport A B p)
    (L₀ : BaseChangeSquare H (p i) p₀ q₀ r₀) :
    L.compare t p₀ q₀ ≫ L₀.compare t p' q = 𝟙 A₀ := by
  refine L₀.hom_ext _ _ ?_ ?_
  · simp only [Functor.map_comp, Category.assoc, compare_q, t.comp_move, t.move_comp,
      Functor.map_id, Category.id_comp]
    rw [← H.map_comp_assoc, compare_p, ← L₀.square]
    simpa using t.move_self q₀
  · simp

/-- The comparison map commutes with the base-changed move operations. -/
lemma compare_move {A₁ A₂ : I → C'} {P : ∀ k, A₁ k ⟶ B'} {P₀ : ∀ k, A₂ k ⟶ B'}
    {Q : ∀ k, H.obj (A₁ k) ⟶ A k} {Q₀ : ∀ k, H.obj (A₂ k) ⟶ A k} {R R₀ : ∀ k, H.obj B' ⟶ B k}
    (L : BaseChangeSquare H (p i) (P i) (Q i) (R i)) (t : FamilyTransport A B p)
    (t' : FamilyTransport A₁ (fun _ ↦ B') P) (t₀ : FamilyTransport A₂ (fun _ ↦ B') P₀)
    (ht : ∀ {k l : I} {Z : C'} (v : Z ⟶ A₁ k) (y : Z ⟶ B'),
      H.map (t'.move v y) ≫ Q l = t.move (H.map v ≫ Q k) (H.map y ≫ R l))
    (ht₀ : ∀ {k l : I} {Z : C'} (v : Z ⟶ A₂ k) (y : Z ⟶ B'),
      H.map (t₀.move v y) ≫ Q₀ l = t.move (H.map v ≫ Q₀ k) (H.map y ≫ R₀ l))
    {Z : C'} (v : Z ⟶ A₂ i) (y : Z ⟶ B') :
    t₀.move v y ≫ L.compare t (P₀ i) (Q₀ i) = t'.move (v ≫ L.compare t (P₀ i) (Q₀ i)) y := by
  refine L.hom_ext _ _ ?_ ?_
  · simp only [Functor.map_comp, Category.assoc, compare_q, t.comp_move, ht, ht₀, t.move_comp]
    rw [← H.map_comp_assoc, t₀.move_base]
  · simp [t₀.move_base, t'.move_base]

/-- The comparison maps are natural in a family of maps commuting with the move operations. -/
lemma compare_naturality {E : I → C} {s : ∀ i, E i ⟶ B i} {A₁ E₀ E₁ : C'} {p₁ : A₁ ⟶ B'}
    {s₀ : E₀ ⟶ B'} {s₁ : E₁ ⟶ B'} {q₁ : H.obj A₁ ⟶ A i} {qE₀ : H.obj E₀ ⟶ E i}
    {qE₁ : H.obj E₁ ⟶ E i} (L : BaseChangeSquare H (p i) p₁ q₁ r)
    (K : BaseChangeSquare H (s i) s₁ qE₁ r) (t : FamilyTransport A B p)
    (u : FamilyTransport E B s) (m : ∀ i, A i ⟶ E i) (m₀ : A₀ ⟶ E₀) (m₁ : A₁ ⟶ E₁)
    (hp₀ : m₀ ≫ s₀ = p₀) (hp₁ : m₁ ≫ s₁ = p₁) (hq₀ : H.map m₀ ≫ qE₀ = q₀ ≫ m i)
    (hq₁ : H.map m₁ ≫ qE₁ = q₁ ≫ m i)
    (ht : ∀ {k l : I} {Z : C} (v : Z ⟶ A k) (y : Z ⟶ B l),
      t.move v y ≫ m l = u.move (v ≫ m k) y) :
    m₀ ≫ K.compare u s₀ qE₀ = L.compare t p₀ q₀ ≫ m₁ := by
  refine K.hom_ext _ _ ?_ ?_
  · simp only [Functor.map_comp, Category.assoc, compare_q, u.comp_move, hq₀, hq₁]
    rw [← H.map_comp_assoc, hp₀, ← Category.assoc, compare_q, ht]
  · simp [Category.assoc, hp₀, hp₁]

variable [HasBinaryProducts C]

/-- The comparison map between two lifts is characterised by the gluing isomorphism. -/
lemma compare_gluing {A₁ : C'} {p₁ : A₁ ⟶ B'} {q₁ : H.obj A₁ ⟶ A i}
    (L₀ : BaseChangeSquare H (p i) p₀ q₀ r₀) (L₁ : BaseChangeSquare H (p i) p₁ q₁ r)
    (t : FamilyTransport A B p) :
    prod.lift q₀ (H.map p₀ ≫ r) ≫ (t.gluing i i).hom.left =
      H.map (L₁.compare t p₀ q₀) ≫ prod.lift (H.map p₁ ≫ r₀) q₁ := by
  apply prod.hom_ext
  · simp only [FamilyTransport.gluing_hom, Category.assoc, prod.lift_fst, prod.lift_fst_assoc]
    rw [← H.map_comp_assoc, compare_p]
    exact L₀.square
  · simp [FamilyTransport.gluing_hom, t.comp_move]

end Compare

end BaseChangeSquare

section Over

variable {X X' Y Y' : C} (a : Y ⟶ X) (a' : Y' ⟶ X') (h : X' ⟶ X) (f : Y' ⟶ Y)
  (ha : f ≫ a = a' ≫ h)

/-- The map of objects over `X` induced by a map `f : Y' ⟶ Y` completing a commutative square
over `h : X' ⟶ X`. -/
def overStructureBase : (Over.map h).obj (Over.mk a') ⟶ Over.mk a := Over.homMk f ha

/-- The underlying map of `CategoryTheory.overStructureBase` is the given map of bases. -/
@[simp]
lemma overStructureBase_left : (overStructureBase a a' h f ha).left = f := rfl

variable (V : Over Y) (V' : Over Y') (m : V'.left ⟶ V.left)
  (hm : IsPullback V'.hom m f V.hom)

/-- The map of objects over `X` induced by a pullback square identifying `V'` with the base
change of `V` along `f`. -/
def overStructureProjection :
    (Over.map h).obj ((Over.map a').obj V') ⟶ (Over.map a).obj V :=
  Over.homMk m (by
    have hw : m ≫ V.hom = V'.hom ≫ f := hm.w.symm
    change m ≫ V.hom ≫ a = (V'.hom ≫ a') ≫ h
    rw [← Category.assoc, hw, Category.assoc, ha, Category.assoc])

/-- The underlying map of `CategoryTheory.overStructureProjection` is the given map of
underlying objects. -/
@[simp]
lemma overStructureProjection_left :
    (overStructureProjection a a' h f ha V V' m hm).left = m := rfl

/-- A pullback square identifying `V'` with the base change of `V` along `f` is a base-change
square for the structure maps of `V'` and `V` viewed over `X'` and `X`. -/
def overBaseChangeSquare :
    BaseChangeSquare (Over.map h) (Over.homMk V.hom : (Over.map a).obj V ⟶ Over.mk a)
      (Over.homMk V'.hom : (Over.map a').obj V' ⟶ Over.mk a')
      (overStructureProjection a a' h f ha V V' m hm) (overStructureBase a a' h f ha) where
  square := by
    apply Over.OverMorphism.ext
    change m ≫ V.hom = V'.hom ≫ f
    exact hm.w.symm
  lift {Z} v y w := by
    refine Over.homMk (hm.lift y.left v.left ?_) ?_
    · simpa only [Over.comp_left, Over.homMk_left, Over.map_map_left, overStructureBase_left]
        using (congrArg Over.Hom.left w).symm
    · rw [show ((Over.map a').obj V').hom = V'.hom ≫ a' from rfl, ← Category.assoc, hm.lift_fst]
      exact Over.w y
  lift_q v y w := by
    apply Over.OverMorphism.ext
    exact hm.lift_snd _ _ _
  lift_p v y w := by
    apply Over.OverMorphism.ext
    exact hm.lift_fst _ _ _
  hom_ext v w hq hp := by
    apply Over.OverMorphism.ext
    refine hm.hom_ext ?_ ?_
    · simpa only [Over.comp_left, Over.homMk_left] using congrArg Over.Hom.left hp
    · simpa only [Over.comp_left, Over.map_map_left, overStructureProjection_left] using
        congrArg Over.Hom.left hq

end Over

/-- An object of `Over Y'` identified with the base change of an object of `Over Y` along
`f : Y' ⟶ Y` sits in a pullback square over `f`. -/
lemma isPullback_of_overPullbackIso [Limits.HasPullbacks C] {Y Y' : C} (f : Y' ⟶ Y)
    (V : Over Y) (V' : Over Y') (e : V' ≅ (Over.pullback f).obj V) :
    IsPullback V'.hom (e.hom.left ≫ pullback.fst V.hom f) f V.hom := by
  have hw : e.hom.left ≫ pullback.snd V.hom f = V'.hom := Over.w e.hom
  refine (IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget Y').mapIso e) rfl hw).flip
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ f) hw

end CategoryTheory

end
