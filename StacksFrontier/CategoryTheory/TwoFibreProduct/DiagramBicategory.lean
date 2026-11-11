module

public import StacksFrontier.CategoryTheory.Bicategory.TwoOneCategory
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Defs

/-!
# The 2-category of 2-commutative diagrams over a cospan (Stacks 003O)

Fix a bicategory `B` and a cospan `f : x ⟶ z`, `g : y ⟶ z`. Stacks 003O defines the
*2-category of 2-commutative diagrams over `f` and `g`*:

1. objects are the 2-commutative squares `(w, a, b, φ)` (`TwoCommSq f g`);
2. 1-morphisms are the triples `(k, α, β)` subject to the compatibility square
   (`TwoCommSq.PreHom`), composed by `(k, α, β) ∘ (k', α', β') =
   (k ∘ k', (α ⋆ id_{k'}) ∘ α', (β ⋆ id_{k'}) ∘ β')` (`TwoCommSq.PreHom.comp`);
3. 2-morphisms `(k₁, α₁, β₁) ⟶ (k₂, α₂, β₂)` are the 2-morphisms `δ : k₁ ⟶ k₂` of `B` with
   `(id_a ⋆ δ) ∘ α₁ = α₂` and `(id_b ⋆ δ) ∘ β₁ = β₂` (`TwoCommSq.PreHom.Hom₂`, from
   `Defs.lean`);
4. vertical composition is that of the `δ`'s, and horizontal composition is the horizontal
   composition `δ ⋆ δ'` of `B`.

Here this is built, with all of its 2-morphisms, as a bicategory `TwoCommSqBicat f g`
(`TwoCommSqBicat.bicategory`): `B` is a bicategory rather than a strict 2-category, so the
composition of 1-morphisms is associative and unital up to the associators and unitors of `B`,
which are 2-morphisms of diagrams. When every 2-morphism of `B` is invertible, so is every
2-morphism of diagrams (`TwoCommSqBicat.isLocallyGroupoid`), as Stacks remarks.

The category `TwoCommSq.category` of `Defs.lean` is the *homotopy category* of this bicategory:
its morphisms are the 1-morphisms modulo the existence of an invertible 2-morphism. It discards
the 2-morphisms, and in particular whether they are unique. The final objects of this
2-category in the sense of Stacks 003P (`CategoryTheory.Bicategory.IsBiterminal`) are, in a
locally groupoidal `B`, exactly the 2-fibre products `IsFinalTwoCommSq` of Stacks 003Q
(`TwoCommSqBicat.isBiterminal_mk_iff`).

## Main definitions

* `CategoryTheory.Bicategory.TwoCommSq.PreHom.homCategory`: the hom-category of 1-morphisms
  and 2-morphisms between two squares, with vertical composition (Stacks 003O (5)).
* `CategoryTheory.Bicategory.TwoCommSqBicat.bicategory`: the 2-category of 2-commutative
  diagrams over `(f, g)` (Stacks 003O).

## Main results

* `CategoryTheory.Bicategory.TwoCommSqBicat.isBiterminal_mk_iff`: in a `(2,1)`-category, a
  square is a final object of that 2-category (Stacks 003P) exactly when it is a 2-fibre product
  `IsFinalTwoCommSq` (Stacks 003Q).

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003P](https://stacks.math.columbia.edu/tag/003P)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
-/

@[expose] public section

open CategoryTheory Bicategory CategoryTheory.Limits

namespace CategoryTheory.Bicategory

universe w v u
variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

namespace TwoCommSq.PreHom

attribute [reassoc (attr := simp)] Hom₂.isoFst_hom_comp Hom₂.isoSnd_hom_comp

variable {T S U : TwoCommSq f g}

/-- **The hom-category of 2-commutative diagrams** (Stacks 003O (5)): the 1-morphisms
`T ⟶ S` and the 2-morphisms between them, composed vertically, as the 2-morphisms `δ` of `B`
are. -/
instance homCategory (T S : TwoCommSq f g) : Category (TwoCommSq.PreHom T S) where
  Hom F G := Hom₂ F G
  id F := Hom₂.id F
  comp η θ := Hom₂.comp η θ
  id_comp _ := Hom₂.ext (Category.id_comp _)
  comp_id _ := Hom₂.ext (Category.comp_id _)
  assoc _ _ _ := Hom₂.ext (Category.assoc _ _ _)

/-- Two 2-morphisms of diagrams are equal when their underlying 2-morphisms of `B` are. -/
@[ext]
lemma hom₂_ext {F G : TwoCommSq.PreHom T S} {η θ : F ⟶ G} (h : η.hom = θ.hom) : η = θ :=
  Hom₂.ext h

@[simp]
lemma id_hom₂ (F : TwoCommSq.PreHom T S) : Hom₂.hom (𝟙 F) = 𝟙 F.hom := rfl

@[simp]
lemma comp_hom₂ {F G H : TwoCommSq.PreHom T S} (η : F ⟶ G) (θ : G ⟶ H) :
    Hom₂.hom (η ≫ θ) = η.hom ≫ θ.hom := rfl

/-- Left whiskering of a 2-morphism of diagrams by a 1-morphism of diagrams: the left
whiskering `id_F.hom ⋆ η` of `B`. -/
def whiskerLeft₂ (F : TwoCommSq.PreHom T S) {G H : TwoCommSq.PreHom S U} (η : G ⟶ H) :
    F.comp G ⟶ F.comp H where
  hom := F.hom ◁ η.hom
  isoFst_hom_comp := by
    dsimp [comp]
    simp only [whiskerLeftIso_hom, Category.assoc]
    rw [← associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, Hom₂.isoFst_hom_comp]
  isoSnd_hom_comp := by
    dsimp [comp]
    simp only [whiskerLeftIso_hom, Category.assoc]
    rw [← associator_inv_naturality_middle, ← whiskerLeft_comp_assoc, Hom₂.isoSnd_hom_comp]

/-- Right whiskering of a 2-morphism of diagrams by a 1-morphism of diagrams: the right
whiskering `η ⋆ id_H.hom` of `B`. -/
def whiskerRight₂ {F G : TwoCommSq.PreHom T S} (η : F ⟶ G) (H : TwoCommSq.PreHom S U) :
    F.comp H ⟶ G.comp H where
  hom := η.hom ▷ H.hom
  isoFst_hom_comp := by
    dsimp [comp]
    rw [← η.isoFst_hom_comp]
    simp only [whiskerLeftIso_hom, Category.assoc, ← associator_inv_naturality_left,
      ← whisker_exchange_assoc]
  isoSnd_hom_comp := by
    dsimp [comp]
    rw [← η.isoSnd_hom_comp]
    simp only [whiskerLeftIso_hom, Category.assoc, ← associator_inv_naturality_left,
      ← whisker_exchange_assoc]

/-- The associator of 1-morphisms of diagrams: the associator of `B` on the underlying
1-morphisms. -/
def associator₂ {V : TwoCommSq f g} (F : TwoCommSq.PreHom T S) (G : TwoCommSq.PreHom S U)
    (H : TwoCommSq.PreHom U V) : (F.comp G).comp H ≅ F.comp (G.comp H) where
  hom :=
    { hom := (α_ F.hom G.hom H.hom).hom
      isoFst_hom_comp := by
        dsimp [comp]
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
          whiskerLeft_comp]
        bicategory
      isoSnd_hom_comp := by
        dsimp [comp]
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
          whiskerLeft_comp]
        bicategory }
  inv :=
    { hom := (α_ F.hom G.hom H.hom).inv
      isoFst_hom_comp := by
        dsimp [comp]
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
          whiskerLeft_comp]
        bicategory
      isoSnd_hom_comp := by
        dsimp [comp]
        simp only [Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom, Category.assoc,
          whiskerLeft_comp]
        bicategory }
  hom_inv_id := hom₂_ext (Iso.hom_inv_id _)
  inv_hom_id := hom₂_ext (Iso.inv_hom_id _)

/-- The left unitor of 1-morphisms of diagrams: the left unitor of `B` on the underlying
1-morphism. -/
def leftUnitor₂ (F : TwoCommSq.PreHom T S) : (id T).comp F ≅ F where
  hom :=
    { hom := (λ_ F.hom).hom
      isoFst_hom_comp := by dsimp [comp, id]; simp only [Category.assoc]; simp
      isoSnd_hom_comp := by dsimp [comp, id]; simp only [Category.assoc]; simp }
  inv :=
    { hom := (λ_ F.hom).inv
      isoFst_hom_comp := by dsimp [comp, id]; simp
      isoSnd_hom_comp := by dsimp [comp, id]; simp }
  hom_inv_id := hom₂_ext (Iso.hom_inv_id _)
  inv_hom_id := hom₂_ext (Iso.inv_hom_id _)

/-- The right unitor of 1-morphisms of diagrams: the right unitor of `B` on the underlying
1-morphism. -/
def rightUnitor₂ (F : TwoCommSq.PreHom T S) : F.comp (id S) ≅ F where
  hom :=
    { hom := (ρ_ F.hom).hom
      isoFst_hom_comp := by dsimp [comp, id]; simp
      isoSnd_hom_comp := by dsimp [comp, id]; simp }
  inv :=
    { hom := (ρ_ F.hom).inv
      isoFst_hom_comp := by dsimp [comp, id]; simp
      isoSnd_hom_comp := by dsimp [comp, id]; simp }
  hom_inv_id := hom₂_ext (Iso.hom_inv_id _)
  inv_hom_id := hom₂_ext (Iso.inv_hom_id _)

@[simp]
lemma whiskerLeft₂_hom (F : TwoCommSq.PreHom T S) {G H : TwoCommSq.PreHom S U} (η : G ⟶ H) :
    (whiskerLeft₂ F η).hom = F.hom ◁ η.hom := rfl

@[simp]
lemma whiskerRight₂_hom {F G : TwoCommSq.PreHom T S} (η : F ⟶ G) (H : TwoCommSq.PreHom S U) :
    (whiskerRight₂ η H).hom = η.hom ▷ H.hom := rfl

@[simp]
lemma associator₂_hom_hom {V : TwoCommSq f g} (F : TwoCommSq.PreHom T S)
    (G : TwoCommSq.PreHom S U) (H : TwoCommSq.PreHom U V) :
    (associator₂ F G H).hom.hom = (α_ F.hom G.hom H.hom).hom := rfl

@[simp]
lemma associator₂_inv_hom {V : TwoCommSq f g} (F : TwoCommSq.PreHom T S)
    (G : TwoCommSq.PreHom S U) (H : TwoCommSq.PreHom U V) :
    (associator₂ F G H).inv.hom = (α_ F.hom G.hom H.hom).inv := rfl

@[simp]
lemma leftUnitor₂_hom_hom (F : TwoCommSq.PreHom T S) :
    (leftUnitor₂ F).hom.hom = (λ_ F.hom).hom := rfl

@[simp]
lemma leftUnitor₂_inv_hom (F : TwoCommSq.PreHom T S) :
    (leftUnitor₂ F).inv.hom = (λ_ F.hom).inv := rfl

@[simp]
lemma rightUnitor₂_hom_hom (F : TwoCommSq.PreHom T S) :
    (rightUnitor₂ F).hom.hom = (ρ_ F.hom).hom := rfl

@[simp]
lemma rightUnitor₂_inv_hom (F : TwoCommSq.PreHom T S) :
    (rightUnitor₂ F).inv.hom = (ρ_ F.hom).inv := rfl

/-- An isomorphism of 1-morphisms of diagrams relates them in the 2-cell equivalence
`TwoCommSq.PreHom.Rel` whose classes are the morphisms of the homotopy category
`TwoCommSq.category`. -/
lemma rel_of_iso {F G : TwoCommSq.PreHom T S} (e : F ≅ G) : Rel F G :=
  ⟨{ hom := e.hom.hom, inv := e.inv.hom
     hom_inv_id := congrArg Hom₂.hom e.hom_inv_id
     inv_hom_id := congrArg Hom₂.hom e.inv_hom_id }, e.hom.isoFst_hom_comp, e.hom.isoSnd_hom_comp⟩

end TwoCommSq.PreHom

/-- The underlying type of the **2-category of 2-commutative diagrams over `(f, g)`**
(Stacks 003O): a copy of `TwoCommSq f g`, kept separate so that its bicategory structure does
not clash with the homotopy category `TwoCommSq.category` on `TwoCommSq f g`. -/
structure TwoCommSqBicat (f : x ⟶ z) (g : y ⟶ z) where
  /-- the underlying 2-commutative square -/
  as : TwoCommSq f g

open TwoCommSq TwoCommSq.PreHom in
/-- **Stacks 003O.** The 2-category of 2-commutative diagrams over the cospan `(f, g)`:
objects are the 2-commutative squares `(w, a, b, φ)`, 1-morphisms are the triples
`(k, α, β)` satisfying the compatibility square (`TwoCommSq.PreHom`), composed by
`TwoCommSq.PreHom.comp`, and 2-morphisms are the 2-morphisms `δ : k₁ ⟶ k₂` compatible with the
comparison 2-cells (`TwoCommSq.PreHom.Hom₂`), composed vertically and horizontally as in `B`.
Since `B` is a bicategory, this is a bicategory, whose associators and unitors are those of `B`;
it is a strict 2-category when `B` is. -/
@[stacks 003O]
instance TwoCommSqBicat.bicategory : Bicategory (TwoCommSqBicat f g) where
  Hom X Y := TwoCommSq.PreHom X.as Y.as
  id X := TwoCommSq.PreHom.id X.as
  comp F G := F.comp G
  homCategory X Y := TwoCommSq.PreHom.homCategory X.as Y.as
  whiskerLeft F _ _ η := whiskerLeft₂ F η
  whiskerRight η H := whiskerRight₂ η H
  associator F G H := associator₂ F G H
  leftUnitor F := leftUnitor₂ F
  rightUnitor F := rightUnitor₂ F
  whiskerLeft_id := by
    intros
    exact hom₂_ext <| Bicategory.whiskerLeft_id ..
  whiskerLeft_comp := by
    intros
    exact hom₂_ext <| Bicategory.whiskerLeft_comp ..
  id_whiskerLeft := by
    intros
    exact hom₂_ext <| Bicategory.id_whiskerLeft ..
  comp_whiskerLeft := by
    intros
    exact hom₂_ext <| Bicategory.comp_whiskerLeft ..
  id_whiskerRight := by
    intros
    exact hom₂_ext <| Bicategory.id_whiskerRight ..
  comp_whiskerRight := by
    intros
    exact hom₂_ext <| Bicategory.comp_whiskerRight ..
  whiskerRight_id := by
    intros
    exact hom₂_ext <| Bicategory.whiskerRight_id ..
  whiskerRight_comp := by
    intros
    exact hom₂_ext <| Bicategory.whiskerRight_comp ..
  whisker_assoc := by
    intros
    exact hom₂_ext <| Bicategory.whisker_assoc ..
  whisker_exchange := by
    intros
    exact hom₂_ext <| Bicategory.whisker_exchange ..
  pentagon := by
    intros
    exact hom₂_ext <| Bicategory.pentagon ..
  triangle := by
    intros
    exact hom₂_ext <| Bicategory.triangle ..

namespace TwoCommSqBicat

/-- In a `(2,1)`-category `B`, every 2-morphism of diagrams is invertible, with inverse the
inverse in `B` of its underlying 2-morphism. -/
lemma isIso_hom₂ [IsLocallyGroupoid B] {T S : TwoCommSq f g} {F G : TwoCommSq.PreHom T S}
    (η : F ⟶ G) : IsIso η :=
  ⟨{ hom := inv η.hom
     isoFst_hom_comp := by
       rw [← η.isoFst_hom_comp, Category.assoc, ← comp_whiskerRight, IsIso.hom_inv_id,
         id_whiskerRight, Category.comp_id]
     isoSnd_hom_comp := by
       rw [← η.isoSnd_hom_comp, Category.assoc, ← comp_whiskerRight, IsIso.hom_inv_id,
         id_whiskerRight, Category.comp_id] },
    TwoCommSq.PreHom.hom₂_ext (IsIso.hom_inv_id η.hom),
    TwoCommSq.PreHom.hom₂_ext (IsIso.inv_hom_id η.hom)⟩

/-- **The 2-category of 2-commutative diagrams is a `(2,1)`-category when `B` is** (the remark
after Stacks 003O): if every 2-morphism of `B` is invertible, so is every 2-morphism of
diagrams. -/
instance isLocallyGroupoid [IsLocallyGroupoid B] : IsLocallyGroupoid (TwoCommSqBicat f g) :=
  fun X Y => { all_isIso := fun η => isIso_hom₂ (T := X.as) (S := Y.as) η }

end TwoCommSqBicat

namespace TwoCommSqBicat

/-- **Final objects of the 2-category of 2-commutative diagrams are the 2-fibre products.** In a
`(2,1)`-category `B`, a square `P` is a final object of `TwoCommSqBicat.bicategory` in the sense
of Stacks 003P (`CategoryTheory.Bicategory.IsBiterminal`) exactly when it is a 2-fibre product
`IsFinalTwoCommSq` of Stacks 003Q: both say that every square admits a 1-morphism of diagrams to
`P` and that any two of them are related by a unique 2-morphism of diagrams, every 2-morphism of
diagrams being invertible here (`TwoCommSqBicat.isIso_hom₂`). -/
theorem isBiterminal_mk_iff [IsLocallyGroupoid B] (P : TwoCommSq f g) :
    IsBiterminal (TwoCommSqBicat.mk P) ↔ Nonempty (IsFinalTwoCommSq P) := by
  rw [isBiterminal_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    choose δ _ hδ using fun (Q : TwoCommSqBicat f g) (F G : Q ⟶ TwoCommSqBicat.mk P) => h₂ Q F G
    exact ⟨{ preHom := fun Q => (h₁ (TwoCommSqBicat.mk Q)).some
             uniqueHom₂ := fun {Q} F G =>
              { default := δ (TwoCommSqBicat.mk Q) F G
                uniq := fun η => hδ (TwoCommSqBicat.mk Q) F G η (isIso_hom₂ η) } }⟩
  · rintro ⟨hP⟩
    exact ⟨fun Q => ⟨hP.preHom Q.as⟩, fun Q F G =>
      ⟨(hP.uniqueHom₂ F G).default, isIso_hom₂ _, fun η _ => (hP.uniqueHom₂ F G).uniq η⟩⟩

end TwoCommSqBicat

end CategoryTheory.Bicategory
