module

public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The twist of the integers by a character of a group acting on an object of a site

Let `C` be a site, let `W` be an object of `C` and let a group `G` act on `W` by
automorphisms. A character `χ : G → ℤˣ` twists the free abelian sheaf on `W`: the quotient
`ℤ(χ)` of that sheaf which identifies the class of a morphism `g ∘ φ : V ⟶ W` with `χ g`
times the class of `φ`. Its defining property is that a map `ℤ(χ) ⟶ F` of abelian sheaves is
the same thing as a section of `F` over `W` transforming according to `χ`.

## Main definitions

* `CategoryTheory.characterSections` is the subgroup of sections over `W` of an abelian
  presheaf that transform according to `χ`.
* `CategoryTheory.characterRelations` is the subgroup of relations imposed by `χ` on the free
  abelian group on the morphisms into `W`, and `CategoryTheory.characterTwistPresheaf` is the
  resulting quotient presheaf.
* `CategoryTheory.characterTwist` is the sheafification `ℤ(χ)` of that presheaf, and
  `CategoryTheory.freeYonedaCharacterTwistProjection` exhibits `ℤ(χ)` as a quotient of the
  free abelian sheaf on `W`.

## Main results

* `CategoryTheory.characterTwistHomEquiv`: a map `ℤ(χ) ⟶ F` of abelian sheaves is the same
  thing as a section of `F` over `W` transforming according to `χ`, and
  `CategoryTheory.characterTwistHomEquiv_comp` is the naturality of that identification in
  `F`.
* `CategoryTheory.characterTwistPresheafHomEquiv` is the same statement for an abelian
  presheaf, before sheafification.

## Implementation notes

The group acts through `CategoryTheory.Aut W`, so that the twist is attached to an action of
`G` on the object `W` of the site, and `χ` is a monoid homomorphism to `ℤˣ`, which is the
shape of `Equiv.Perm.sign`.

The relations are imposed at every morphism `φ : V ⟶ W` and not only at the identity of `W`,
which is what makes them a subpresheaf. On sections over `W` this is no extra demand: the
relation at `φ` is the restriction of the relation at the identity along `φ`, which is why
`CategoryTheory.characterSections` only constrains the action of `g` on a section over `W`.

The twist is built at the level of presheaves, as an objectwise quotient of the free abelian
group on the morphisms into `W`, and only then sheafified. The identification of maps out of
it is then the sheafification adjunction followed by the universal properties of a free
abelian group and of a quotient group, and it is given by evaluating at the class of the
identity of `W`, so it is manifestly additive in the map.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] (W : C) {G : Type w} [Group G] (act : G →* Aut W)
    (χ : G →* ℤˣ)

/-! ### Sections transforming according to a character -/

/-- The sections of an abelian presheaf `F` over `W` that transform according to the
character `χ`: the sections `s` with `g · s = χ g • s` for every `g` in the group. -/
def characterSections (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    AddSubgroup (F.obj (op W)) where
  carrier := {s | ∀ g : G, (F.map ((act g).asIso.hom).op) s = (χ g : ℤ) • s}
  zero_mem' g := by simp
  add_mem' {a b} ha hb g := by rw [map_add, ha g, hb g, smul_add]
  neg_mem' {a} ha g := by rw [map_neg, ha g, smul_neg]

/-- A section lies in `characterSections` exactly when every `g` acts on it as `χ g`. -/
lemma mem_characterSections_iff {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}} {s : F.obj (op W)} :
    s ∈ characterSections W act χ F ↔
      ∀ g : G, (F.map ((act g).asIso.hom).op) s = (χ g : ℤ) • s :=
  Iff.rfl

/-! ### The twisted free abelian presheaf -/

/-- The relations imposed by the character `χ` on the free abelian group on the morphisms
`V ⟶ W`: the generator at `g ∘ φ` is `χ g` times the generator at `φ`. -/
def characterRelations (V : C) : AddSubgroup (FreeAbelianGroup (V ⟶ W)) :=
  AddSubgroup.closure {x | ∃ (g : G) (φ : V ⟶ W),
    x = FreeAbelianGroup.of (φ ≫ (act g).asIso.hom) - (χ g : ℤ) • FreeAbelianGroup.of φ}

/-- Precomposition with a morphism of the site carries the relations imposed by `χ` into the
relations imposed by `χ`. -/
lemma characterRelations_le_comap {V V' : C} (f : V' ⟶ V) :
    characterRelations W act χ V ≤
      AddSubgroup.comap (FreeAbelianGroup.map (fun φ : V ⟶ W => f ≫ φ))
        (characterRelations W act χ V') := by
  rw [characterRelations, AddSubgroup.closure_le]
  rintro x ⟨g, φ, rfl⟩
  refine AddSubgroup.subset_closure ⟨g, f ≫ φ, ?_⟩
  simp only [map_sub, map_zsmul, FreeAbelianGroup.map_of_apply, Category.assoc]

/-- Two homomorphisms out of the free abelian group on the morphisms `V ⟶ W` modulo the
relations imposed by `χ` agree as soon as they agree on the classes of the generators. -/
lemma characterRelations_hom_ext {V : C} {M : Type*} [AddCommGroup M]
    (f f' : (FreeAbelianGroup (V ⟶ W) ⧸ characterRelations W act χ V) →+ M)
    (h : ∀ φ : V ⟶ W, f (QuotientAddGroup.mk (FreeAbelianGroup.of φ)) =
      f' (QuotientAddGroup.mk (FreeAbelianGroup.of φ))) : f = f' := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    exact congrArg (fun k => k z) (FreeAbelianGroup.lift_ext
      (f.comp (QuotientAddGroup.mk' _)) (f'.comp (QuotientAddGroup.mk' _)) h)

/-- The free abelian presheaf on the representable presheaf of `W`, divided objectwise by the
relations imposed by the character `χ`. -/
def characterTwistPresheaf : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj V := AddCommGrpCat.of
    (FreeAbelianGroup (V.unop ⟶ W) ⧸ characterRelations W act χ V.unop)
  map {V V'} m := AddCommGrpCat.ofHom
    (QuotientAddGroup.map _ _ (FreeAbelianGroup.map (fun φ : V.unop ⟶ W => m.unop ≫ φ))
      (characterRelations_le_comap W act χ m.unop))
  map_id V := by
    apply AddCommGrpCat.hom_ext
    refine characterRelations_hom_ext W act χ _ _ fun φ => ?_
    simp
  map_comp {V V' V''} m m' := by
    apply AddCommGrpCat.hom_ext
    refine characterRelations_hom_ext W act χ _ _ fun φ => ?_
    simp

/-- The class of a morphism `φ : V ⟶ W` in the twisted free abelian presheaf. -/
def twistedGenerator {V : C} (φ : V ⟶ W) :
    (characterTwistPresheaf W act χ).obj (op V) :=
  QuotientAddGroup.mk (FreeAbelianGroup.of φ)

/-- Restricting the class of `φ : V ⟶ W` along `f : V' ⟶ V` gives the class of `f ≫ φ`. -/
@[simp]
lemma characterTwistPresheaf_map_twistedGenerator {V V' : C} (f : V' ⟶ V) (φ : V ⟶ W) :
    ((characterTwistPresheaf W act χ).map f.op) (twistedGenerator W act χ φ) =
      twistedGenerator W act χ (f ≫ φ) :=
  rfl

/-- The class of `g ∘ φ` is `χ g` times the class of `φ`. -/
lemma twistedGenerator_act {V : C} (φ : V ⟶ W) (g : G) :
    twistedGenerator W act χ (φ ≫ (act g).asIso.hom) =
      (χ g : ℤ) • twistedGenerator W act χ φ := by
  have h : FreeAbelianGroup.of (φ ≫ (act g).asIso.hom) -
      (χ g : ℤ) • FreeAbelianGroup.of φ ∈ characterRelations W act χ V :=
    AddSubgroup.subset_closure ⟨g, φ, rfl⟩
  have h' := (QuotientAddGroup.eq_iff_sub_mem (N := characterRelations W act χ V)).mpr h
  rwa [QuotientAddGroup.mk_zsmul] at h'

/-- A map out of the twisted free abelian presheaf is determined on the class of a morphism
`φ : V ⟶ W` by its value on the class of the identity of `W`. -/
lemma app_twistedGenerator {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    (u : characterTwistPresheaf W act χ ⟶ F) {V : C} (φ : V ⟶ W) :
    (u.app (op V)) (twistedGenerator W act χ φ) =
      (F.map φ.op) ((u.app (op W)) (twistedGenerator W act χ (𝟙 W))) := by
  have hnat := NatTrans.naturality_apply u φ.op (twistedGenerator W act χ (𝟙 W))
  rwa [characterTwistPresheaf_map_twistedGenerator, Category.comp_id] at hnat

/-- Two maps out of the twisted free abelian presheaf agree as soon as they agree on the
class of the identity of `W`. -/
lemma characterTwistPresheaf_hom_ext {F : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    {u u' : characterTwistPresheaf W act χ ⟶ F}
    (h : (u.app (op W)) (twistedGenerator W act χ (𝟙 W)) =
      (u'.app (op W)) (twistedGenerator W act χ (𝟙 W))) : u = u' := by
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  refine characterRelations_hom_ext W act χ _ _ fun φ => ?_
  exact (app_twistedGenerator W act χ u φ).trans
    ((congrArg (fun t => (F.map φ.op) t) h).trans
      (app_twistedGenerator W act χ u' φ).symm)

/-- The map from the twisted free abelian presheaf to an abelian presheaf attached to a
section over `W` transforming according to `χ`, read on one object of the site. -/
def characterSectionsApp (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (s : characterSections W act χ F)
    (V : Cᵒᵖ) : (characterTwistPresheaf W act χ).obj V ⟶ F.obj V :=
  AddCommGrpCat.ofHom
    (QuotientAddGroup.lift _
      (FreeAbelianGroup.lift fun φ : V.unop ⟶ W => (F.map φ.op) s.1) (by
        intro x hx
        refine (show characterRelations W act χ V.unop ≤
            (FreeAbelianGroup.lift fun φ : V.unop ⟶ W => (F.map φ.op) s.1).ker from ?_) hx
        rw [characterRelations, AddSubgroup.closure_le]
        rintro y ⟨g, φ, rfl⟩
        simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_zsmul,
          FreeAbelianGroup.lift_apply_of, sub_eq_zero, op_comp, Functor.map_comp]
        rw [show (ConcreteCategory.hom (F.map ((act g).asIso.hom).op ≫ F.map φ.op)) s.1 =
          (F.map φ.op) ((F.map ((act g).asIso.hom).op) s.1) from rfl, s.2 g, map_zsmul]))

/-- The map attached to a section `s` sends the class of `φ : V ⟶ W` to the restriction of
`s` along `φ`. -/
@[simp]
lemma characterSectionsApp_twistedGenerator (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (s : characterSections W act χ F) {V : C} (φ : V ⟶ W) :
    (characterSectionsApp W act χ F s (op V)) (twistedGenerator W act χ φ) =
      (F.map φ.op) s.1 := by
  simp only [characterSectionsApp, twistedGenerator]
  exact FreeAbelianGroup.lift_apply_of _ _

/-- A map from the twisted free abelian presheaf to an abelian presheaf is the same thing as a
section over `W` transforming according to the character `χ`. -/
def characterTwistPresheafHomEquiv (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    (characterTwistPresheaf W act χ ⟶ F) ≃ characterSections W act χ F where
  toFun u := ⟨(u.app (op W)) (twistedGenerator W act χ (𝟙 W)), by
    intro g
    have h := app_twistedGenerator W act χ u ((act g).asIso.hom)
    have hgen : twistedGenerator W act χ ((act g).asIso.hom) =
        (χ g : ℤ) • twistedGenerator W act χ (𝟙 W) := by
      have hid := twistedGenerator_act W act χ (𝟙 W) g
      rwa [Category.id_comp] at hid
    rw [hgen, map_zsmul] at h
    exact h.symm⟩
  invFun s :=
    { app := characterSectionsApp W act χ F s
      naturality := by
        intro V₁ V₂ m
        apply AddCommGrpCat.hom_ext
        refine characterRelations_hom_ext W act χ _ _ fun φ => ?_
        change (characterSectionsApp W act χ F s V₂)
            ((characterTwistPresheaf W act χ).map m (twistedGenerator W act χ φ)) =
          (F.map m) ((characterSectionsApp W act χ F s V₁) (twistedGenerator W act χ φ))
        rw [show (characterTwistPresheaf W act χ).map m (twistedGenerator W act χ φ) =
            twistedGenerator W act χ (m.unop ≫ φ) from rfl,
          characterSectionsApp_twistedGenerator, characterSectionsApp_twistedGenerator,
          op_comp, F.map_comp]
        rfl }
  left_inv u := by
    apply characterTwistPresheaf_hom_ext
    rw [characterSectionsApp_twistedGenerator]
    simp
  right_inv s := by
    apply Subtype.ext
    exact (characterSectionsApp_twistedGenerator W act χ F s (𝟙 W)).trans (by simp)

/-- The section attached to a map out of the twisted free abelian presheaf is its value on the
class of the identity of `W`. -/
@[simp]
lemma characterTwistPresheafHomEquiv_apply (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    (u : characterTwistPresheaf W act χ ⟶ F) :
    ((characterTwistPresheafHomEquiv W act χ F u) : F.obj (op W)) =
      (u.app (op W)) (twistedGenerator W act χ (𝟙 W)) :=
  rfl

/-! ### The twisted sheaf -/

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- The sheaf `ℤ(χ)`: the sheafification of the free abelian presheaf on the representable
presheaf of `W`, divided by the relations imposed by the character `χ`. -/
noncomputable def characterTwist : Sheaf J AddCommGrpCat.{v} :=
  (presheafToSheaf J AddCommGrpCat.{v}).obj (characterTwistPresheaf W act χ)

/-- A map `ℤ(χ) ⟶ F` of abelian sheaves is the same thing as a section of `F` over `W`
transforming according to the character `χ`. -/
noncomputable def characterTwistHomEquiv (F : Sheaf J AddCommGrpCat.{v}) :
    (characterTwist W act χ J ⟶ F) ≃ characterSections W act χ F.obj :=
  ((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv
      (characterTwistPresheaf W act χ) F).trans
    (characterTwistPresheafHomEquiv W act χ F.obj)

/-- The section attached to a map `ℤ(χ) ⟶ F` of abelian sheaves is its value on the image in
the sheafification of the class of the identity of `W`. -/
lemma characterTwistHomEquiv_apply (F : Sheaf J AddCommGrpCat.{v})
    (u : characterTwist W act χ J ⟶ F) :
    ((characterTwistHomEquiv W act χ J F u) : F.obj.obj (op W)) =
      (u.hom.app (op W)) ((toSheafify J (characterTwistPresheaf W act χ)).app (op W)
        (twistedGenerator W act χ (𝟙 W))) :=
  rfl

/-- The identification of maps out of `ℤ(χ)` with the sections transforming according to `χ`
is natural in the sheaf: composing with a morphism of sheaves takes its component at `W`. -/
lemma characterTwistHomEquiv_comp {F F' : Sheaf J AddCommGrpCat.{v}}
    (u : characterTwist W act χ J ⟶ F) (k : F ⟶ F') :
    ((characterTwistHomEquiv W act χ J F' (u ≫ k)) : F'.obj.obj (op W)) =
      (k.hom.app (op W)) ((characterTwistHomEquiv W act χ J F u) : F.obj.obj (op W)) :=
  rfl

/-! ### The twist as a quotient of the free abelian sheaf -/

/-- The quotient map from the free abelian presheaf on the representable presheaf of `W` to
the twisted free abelian presheaf. -/
def freeYonedaCharacterTwistProjectionPresheaf :
    (yoneda.obj W ⋙ AddCommGrpCat.free) ⟶ characterTwistPresheaf W act χ where
  app V := AddCommGrpCat.ofHom (QuotientAddGroup.mk' (characterRelations W act χ V.unop))
  naturality := by
    intro V₁ V₂ m
    apply AddCommGrpCat.hom_ext
    refine FreeAbelianGroup.lift_ext _ _ fun φ => ?_
    rfl

/-- `ℤ(χ)` is a quotient of the free abelian sheaf on `W`. -/
noncomputable def freeYonedaCharacterTwistProjection :
    (presheafToSheaf J AddCommGrpCat.{v}).obj (yoneda.obj W ⋙ AddCommGrpCat.free) ⟶
      characterTwist W act χ J :=
  (presheafToSheaf J AddCommGrpCat.{v}).map
    (freeYonedaCharacterTwistProjectionPresheaf W act χ)

/-- The quotient map sends the generator of the free abelian group at `φ : V ⟶ W` to the class
of `φ`. -/
@[simp]
lemma freeYonedaCharacterTwistProjectionPresheaf_app_of {V : C} (φ : V ⟶ W) :
    ((freeYonedaCharacterTwistProjectionPresheaf W act χ).app (op V))
        (FreeAbelianGroup.of φ) =
      twistedGenerator W act χ φ :=
  rfl

end CategoryTheory

end
