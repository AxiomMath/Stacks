module

public import StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidalFunctor
public import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Karoubi envelope of a monoidal functor

A monoidal functor `F : A ⥤ B` induces a monoidal functor between the Karoubi envelopes: the
functor sending the formal direct factor `(X, p)` of `A` to the formal direct factor
`(F.obj X, F.map p)` of `B` is monoidal for the tensor products
`(X, p) ⊗ (Y, q) = (X ⊗ Y, p ⊗ q)`, its unit and tensor comparison morphisms being those of `F`
cut down by the idempotents. It is braided, hence symmetric monoidal, when `F` is.

## Main definitions

* `CategoryTheory.Idempotents.Karoubi.mapFunctor`: the functor `Karoubi A ⥤ Karoubi B` induced
  by a functor `F : A ⥤ B`.
* `CategoryTheory.Idempotents.Karoubi.mapεIso` and
  `CategoryTheory.Idempotents.Karoubi.mapμIso`: the unit and tensor comparison isomorphisms of
  `mapFunctor F`, namely those of `F` cut down by the idempotents.
* `CategoryTheory.Idempotents.Karoubi.mapFunctorCoreMonoidal`: the monoidal structure on
  `mapFunctor F`, as a `Functor.CoreMonoidal`.
* `CategoryTheory.Idempotents.Karoubi.toKaroubiCompMapFunctorIso`: the isomorphism
  `toKaroubi A ⋙ mapFunctor F ≅ F ⋙ toKaroubi B` expressing that `mapFunctor F` extends `F`.
* `CategoryTheory.Idempotents.Karoubi.ofComm_whiskerLeft` and
  `CategoryTheory.Idempotents.Karoubi.ofComm_whiskerRight`: whiskering a morphism of formal
  direct factors induced by an intertwining morphism.

## Main results

* `CategoryTheory.Idempotents.Karoubi.mapFunctorMonoidal`: `mapFunctor F` is monoidal when `F`
  is.
* `CategoryTheory.Idempotents.Karoubi.mapFunctorLaxBraided` and
  `CategoryTheory.Idempotents.Karoubi.mapFunctorBraided`: `mapFunctor F` is braided when `F`
  is; for symmetric monoidal `A` and `B` this says that `mapFunctor F` is symmetric monoidal.
* `CategoryTheory.Idempotents.Karoubi.mapFunctor_eq_functorExtension₂`: `mapFunctor F` is the
  functor constructed by Mathlib's `functorExtension₂`.
* `CategoryTheory.Idempotents.Karoubi.toKaroubiCompMapFunctorIso_isMonoidal`: the isomorphism
  `toKaroubi A ⋙ mapFunctor F ≅ F ⋙ toKaroubi B` is monoidal.

## Implementation notes

Mathlib has no monoidal structure on a Karoubi envelope at all, so none of these statements can
be made there; the monoidal structure used is the one in
`StacksFrontier.CategoryTheory.Idempotents.KaroubiMonoidal`.

The underlying functor is Mathlib's: `mapFunctor_eq_functorExtension₂` records that
`mapFunctor F` and `(functorExtension₂ A B).obj F` agree by `rfl`, so nothing is duplicated
mathematically. The definition is nevertheless spelled out, as a reducible abbreviation, because
`functorExtension₂` is not reducible: without that, `(((functorExtension₂ A B).obj F).obj P).X`
does not reduce to `F.obj P.X` at the transparency used by `simp` and by `rw`, and a lemma about
`Karoubi B` cannot then be applied to a morphism of `B` whose type is spelled with `F.obj`. With
the objects and morphisms of `mapFunctor F` reducing, every coherence goal becomes a goal about
`B`.

The braided statements are made for `[F.Braided]` rather than for `[F.Monoidal] [F.LaxBraided]`:
the latter pair carries two unrelated `F.LaxMonoidal` structures, so `LaxMonoidal.μ F` in the
hypothesis and `LaxMonoidal.μ (mapFunctor F)` in the conclusion would be built from different
tensor comparison morphisms. `Functor.Braided` bundles the two coherently.

Every structural morphism of a Karoubi envelope is an `ofComm`, and `mapFunctor F` sends
`ofComm g h` to `ofComm (F.map g) _` (`mapFunctor_map_ofComm`), so each coherence identity
reduces by `ofComm_congr` to the corresponding identity for `F`. `Functor.CoreMonoidal` is used
rather than `Functor.LaxMonoidal` because the comparison morphisms are isomorphisms and the
braided structure needs them to be.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Category Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Idempotents

namespace Karoubi

section Whiskering

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- An intertwining morphism, tensored on the right with the identity of a formal direct factor,
intertwines. -/
theorem comm_whiskerRight {P Q : Karoubi C} {g : P.X ⟶ Q.X} (h : P.p ≫ g = g ≫ Q.p)
    (R : Karoubi C) : (P ⊗ R).p ≫ (g ⊗ₘ 𝟙 R.X) = (g ⊗ₘ 𝟙 R.X) ≫ (Q ⊗ R).p :=
  comm_tensor h (by simp)

/-- An intertwining morphism, tensored on the left with the identity of a formal direct factor,
intertwines. -/
theorem comm_whiskerLeft (R : Karoubi C) {P Q : Karoubi C} {g : P.X ⟶ Q.X}
    (h : P.p ≫ g = g ≫ Q.p) :
    (R ⊗ P).p ≫ (𝟙 R.X ⊗ₘ g) = (𝟙 R.X ⊗ₘ g) ≫ (R ⊗ Q).p :=
  comm_tensor (by simp) h

/-- Whiskering `ofComm g h` on the right by `R` is the morphism induced by `g ⊗ₘ 𝟙 R.X`. -/
theorem ofComm_whiskerRight {P Q : Karoubi C} (g : P.X ⟶ Q.X) (h : P.p ≫ g = g ≫ Q.p)
    (R : Karoubi C) : ofComm g h ▷ R = ofComm (g ⊗ₘ 𝟙 R.X) (comm_whiskerRight h R) := by
  apply Karoubi.hom_ext
  simp only [whiskerRight_f, ofComm_f, tensorObj_p, MonoidalCategory.tensorHom_comp_tensorHom,
    comp_id]

/-- Whiskering `ofComm g h` on the left by `R` is the morphism induced by `𝟙 R.X ⊗ₘ g`. -/
theorem ofComm_whiskerLeft (R : Karoubi C) {P Q : Karoubi C} (g : P.X ⟶ Q.X)
    (h : P.p ≫ g = g ≫ Q.p) : R ◁ ofComm g h = ofComm (𝟙 R.X ⊗ₘ g) (comm_whiskerLeft R h) := by
  apply Karoubi.hom_ext
  simp only [whiskerLeft_f, ofComm_f, tensorObj_p, MonoidalCategory.tensorHom_comp_tensorHom,
    comp_id]

end Whiskering

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- The functor between Karoubi envelopes induced by a functor `F : A ⥤ B`: it sends the formal
direct factor of `X` cut out by an idempotent `p` to the formal direct factor of `F.obj X` cut
out by `F.map p`. -/
@[sga "4 I 8.7.8"]
abbrev mapFunctor (F : A ⥤ B) : Karoubi A ⥤ Karoubi B where
  obj P := ⟨F.obj P.X, F.map P.p, by rw [← F.map_comp, P.idem]⟩
  map {P Q} f := ⟨F.map f.f, by
    change F.map P.p ≫ F.map f.f ≫ F.map Q.p = F.map f.f
    rw [← F.map_comp, ← F.map_comp, f.comm]⟩

/-- `mapFunctor F` is the extension of `F` to the Karoubi envelopes constructed by Mathlib's
`functorExtension₂`. -/
theorem mapFunctor_eq_functorExtension₂ (F : A ⥤ B) :
    mapFunctor F = (functorExtension₂ A B).obj F :=
  rfl

/-- `mapFunctor F` does not change the underlying object. -/
@[simp] theorem mapFunctor_obj_X (F : A ⥤ B) (P : Karoubi A) :
    ((mapFunctor F).obj P).X = F.obj P.X :=
  rfl

/-- `mapFunctor F` applies `F` to the idempotent cutting out a formal direct factor. -/
@[simp] theorem mapFunctor_obj_p (F : A ⥤ B) (P : Karoubi A) :
    ((mapFunctor F).obj P).p = F.map P.p :=
  rfl

/-- `mapFunctor F` applies `F` to the underlying morphism. -/
@[simp] theorem mapFunctor_map_f (F : A ⥤ B) {P Q : Karoubi A} (f : P ⟶ Q) :
    ((mapFunctor F).map f).f = F.map f.f :=
  rfl

/-- The image under `F` of a morphism intertwining two idempotents intertwines their images. -/
theorem comm_map (F : A ⥤ B) {P Q : Karoubi A} {g : P.X ⟶ Q.X} (h : P.p ≫ g = g ≫ Q.p) :
    ((mapFunctor F).obj P).p ≫ F.map g = F.map g ≫ ((mapFunctor F).obj Q).p := by
  show F.map P.p ≫ F.map g = F.map g ≫ F.map Q.p
  rw [← F.map_comp, h, F.map_comp]

/-- `mapFunctor F` sends the morphism of formal direct factors induced by an intertwining
morphism `g` to the one induced by `F.map g`. -/
theorem mapFunctor_map_ofComm (F : A ⥤ B) {P Q : Karoubi A} (g : P.X ⟶ Q.X)
    (h : P.p ≫ g = g ≫ Q.p) :
    (mapFunctor F).map (ofComm g h) = ofComm (F.map g) (comm_map F h) := by
  apply Karoubi.hom_ext
  show F.map (P.p ≫ g) = F.map P.p ≫ F.map g
  rw [F.map_comp]

/-- `mapFunctor F` extends `F`: on the formal direct factors cut out by identities it is `F`, up
to the isomorphism identifying `F.map (𝟙 X)` with `𝟙 (F.obj X)`. -/
def toKaroubiCompMapFunctorIso (F : A ⥤ B) : toKaroubi A ⋙ mapFunctor F ≅ F ⋙ toKaroubi B :=
  NatIso.ofComponents (fun X => isoOfIso (Iso.refl (F.obj X)) (by simp))
    (fun f => by apply Karoubi.hom_ext; simp [ofComm_f])

section Monoidal

variable [MonoidalCategory A] [MonoidalCategory B] (F : A ⥤ B) [F.Monoidal]

/-- The unit comparison morphism of `F` intertwines the idempotents of the units. -/
theorem comm_mapε :
    (𝟙_ (Karoubi B)).p ≫ LaxMonoidal.ε F =
      LaxMonoidal.ε F ≫ ((mapFunctor F).obj (𝟙_ (Karoubi A))).p := by
  show 𝟙 (𝟙_ B) ≫ LaxMonoidal.ε F = LaxMonoidal.ε F ≫ F.map (𝟙 (𝟙_ A))
  rw [id_comp, F.map_id, comp_id]

/-- The tensor comparison morphism of `F` intertwines the tensor products of the idempotents;
this is the naturality of `LaxMonoidal.μ F`, applied to the idempotents. -/
theorem comm_mapμ (P Q : Karoubi A) :
    ((mapFunctor F).obj P ⊗ (mapFunctor F).obj Q).p ≫ LaxMonoidal.μ F P.X Q.X =
      LaxMonoidal.μ F P.X Q.X ≫ ((mapFunctor F).obj (P ⊗ Q)).p := by
  show (F.map P.p ⊗ₘ F.map Q.p) ≫ LaxMonoidal.μ F P.X Q.X =
    LaxMonoidal.μ F P.X Q.X ≫ F.map (P.p ⊗ₘ Q.p)
  exact LaxMonoidal.μ_natural F P.p Q.p

/-- The unit comparison isomorphism of `mapFunctor F`: that of `F`, cut down by the idempotents
of the units, which are identities. -/
def mapεIso : 𝟙_ (Karoubi B) ≅ (mapFunctor F).obj (𝟙_ (Karoubi A)) :=
  isoOfIso (Monoidal.εIso F) (comm_mapε F)

/-- The tensor comparison isomorphism of `mapFunctor F`: that of `F`, cut down by the
idempotents. -/
def mapμIso (P Q : Karoubi A) :
    (mapFunctor F).obj P ⊗ (mapFunctor F).obj Q ≅ (mapFunctor F).obj (P ⊗ Q) :=
  isoOfIso (Monoidal.μIso F P.X Q.X) (comm_mapμ F P Q)

/-- `mapεIso F` is induced by the unit comparison morphism of `F`. -/
theorem mapεIso_hom : (mapεIso F).hom = ofComm (LaxMonoidal.ε F) (comm_mapε F) :=
  rfl

/-- `mapμIso F P Q` is induced by the tensor comparison morphism of `F`. -/
theorem mapμIso_hom (P Q : Karoubi A) :
    (mapμIso F P Q).hom = ofComm (LaxMonoidal.μ F P.X Q.X) (comm_mapμ F P Q) :=
  rfl

/-- The monoidal structure of `mapFunctor F : Karoubi A ⥤ Karoubi B` for a monoidal functor
`F : A ⥤ B`: the unit and tensor comparison isomorphisms are those of `F`, cut down by the
idempotents. -/
def mapFunctorCoreMonoidal : (mapFunctor F).CoreMonoidal where
  εIso := mapεIso F
  μIso := mapμIso F
  μIso_hom_natural_left {P Q} f X' := by
    rw [eq_ofComm f, ofComm_whiskerRight, mapFunctor_map_ofComm, mapFunctor_map_ofComm]
    simp only [ofComm_whiskerRight, mapμIso_hom, ofComm_comp]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.tensorHom_id] using LaxMonoidal.μ_natural_left F f.f X'.X
  μIso_hom_natural_right {P Q} X' f := by
    rw [eq_ofComm f, ofComm_whiskerLeft, mapFunctor_map_ofComm, mapFunctor_map_ofComm]
    simp only [ofComm_whiskerLeft, mapμIso_hom, ofComm_comp]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.id_tensorHom] using LaxMonoidal.μ_natural_right F X'.X f.f
  associativity P Q R := by
    rw [associator_hom P Q R, mapFunctor_map_ofComm]
    simp only [associator_hom, mapμIso_hom, ofComm_whiskerRight, ofComm_whiskerLeft, ofComm_comp,
      tensorObj_X]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] using
      LaxMonoidal.associativity F P.X Q.X R.X
  left_unitality P := by
    rw [leftUnitor_hom P, mapFunctor_map_ofComm]
    simp only [leftUnitor_hom, mapεIso_hom, mapμIso_hom, ofComm_whiskerRight, ofComm_comp,
      tensorUnit_X]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.tensorHom_id] using LaxMonoidal.left_unitality F P.X
  right_unitality P := by
    rw [rightUnitor_hom P, mapFunctor_map_ofComm]
    simp only [rightUnitor_hom, mapεIso_hom, mapμIso_hom, ofComm_whiskerLeft, ofComm_comp,
      tensorUnit_X]
    refine ofComm_congr _ _ ?_
    simpa only [MonoidalCategory.id_tensorHom] using LaxMonoidal.right_unitality F P.X

/-- For a monoidal functor `F : A ⥤ B` the induced functor `Karoubi A ⥤ Karoubi B` is
monoidal. -/
instance mapFunctorMonoidal : (mapFunctor F).Monoidal :=
  (mapFunctorCoreMonoidal F).toMonoidal

/-- The unit comparison morphism of `mapFunctor F` is `mapεIso F`. -/
theorem mapFunctor_ε : LaxMonoidal.ε (mapFunctor F) = (mapεIso F).hom :=
  rfl

/-- The tensor comparison morphism of `mapFunctor F` is `mapμIso F`. -/
theorem mapFunctor_μ (P Q : Karoubi A) :
    LaxMonoidal.μ (mapFunctor F) P Q = (mapμIso F P Q).hom :=
  rfl

/-- The isomorphism `toKaroubi A ⋙ mapFunctor F ≅ F ⋙ toKaroubi B` is monoidal: `mapFunctor F`
extends `F` as a monoidal functor. -/
instance toKaroubiCompMapFunctorIso_isMonoidal :
    NatTrans.IsMonoidal (toKaroubiCompMapFunctorIso F).hom where
  unit := by
    apply Karoubi.hom_ext
    simp [toKaroubiCompMapFunctorIso, ofComm_f, mapFunctor_ε, mapεIso_hom]
  tensor X Y := by
    apply Karoubi.hom_ext
    simp [toKaroubiCompMapFunctorIso, ofComm_f, mapFunctor_μ, mapμIso_hom]

end Monoidal

section Braided

variable [MonoidalCategory A] [MonoidalCategory B] [BraidedCategory A] [BraidedCategory B]
  (F : A ⥤ B) [F.Braided]

/-- For a braided monoidal functor `F : A ⥤ B` the induced functor `Karoubi A ⥤ Karoubi B` is
lax braided: the commutativity constraints of the Karoubi envelopes are those of `A` and `B`
cut down by the idempotents. -/
instance mapFunctorLaxBraided : (mapFunctor F).LaxBraided where
  braided P Q := by
    rw [braiding_hom P Q, mapFunctor_map_ofComm]
    simp only [mapFunctor_μ, braiding_hom, mapμIso_hom, ofComm_comp]
    refine ofComm_congr _ _ ?_
    exact Functor.LaxBraided.braided (F := F) P.X Q.X

/-- For a braided monoidal functor `F : A ⥤ B` the induced functor `Karoubi A ⥤ Karoubi B` is
braided; for `A` and `B` symmetric monoidal this says that it is a symmetric monoidal
functor. -/
instance mapFunctorBraided : (mapFunctor F).Braided where

end Braided

end Karoubi

end CategoryTheory.Idempotents

end
