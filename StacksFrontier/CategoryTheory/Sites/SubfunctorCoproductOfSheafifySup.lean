module

public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Two locally covering, locally disjoint subsheaves form a coproduct

Let `F` be a sheaf of sets on a site `(C, J)` and let `V`, `W` be subfunctors of `F` which are
sheaves. Suppose that `V` and `W` cover `F` locally, `(V ⊔ W).sheafify J = ⊤`, and that they
meet only over objects covered by the empty sieve, `V ⊓ W ≤ (⊥ : Subfunctor F).sheafify J`.
Then the two inclusions exhibit `F` as the coproduct of `V` and `W` in `Sheaf J (Type w)`.

This is the converse of the description of a coproduct of algebraic spaces by its two
open-and-closed pieces: it is the shape in which Stacks 082H and Stacks 0ADU state the
decomposition `U ×_Y X = W ⨿ V`, and the shape in which Stacks 0824 (the normalization of a
disjoint union) consumes it, as a colimit cofan.

## Main definitions

* `CategoryTheory.Subfunctor.supDesc`: the morphism out of `V ⊔ W` glued from morphisms out of
  `V` and out of `W` which agree on `V ⊓ W`.
* `CategoryTheory.Subfunctor.isColimitCofanOfSheafifySup`: the two inclusions of `V` and `W` into
  `F` form a colimit cofan of sheaves.

## Implementation notes

Gluing on the presheaf `V ⊔ W` needs the two morphisms to agree on `V ⊓ W` only; over an object
covered by the empty sieve every sheaf has at most one section, which is how the hypothesis on
`V ⊓ W` is used. The glued morphism is then extended from `V ⊔ W` to its sheafification by
`CategoryTheory.Subfunctor.sheafifyLift`, and the sheafification is all of `F`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u w

namespace CategoryTheory.Subfunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w}

variable (V W : Subfunctor F)

/-- The morphism out of `V ⊔ W` glued from a morphism out of `V` and a morphism out of `W` which
agree on every section lying in both. A section of `V ⊔ W` lying in `V` is sent where the first
morphism sends it, and any other section where the second does. -/
noncomputable def supDesc {Z : Cᵒᵖ ⥤ Type w} (a : V.toFunctor ⟶ Z) (b : W.toFunctor ⟶ Z)
    (hab : ∀ (U : Cᵒᵖ) (s : F.obj U) (hV : s ∈ V.obj U) (hW : s ∈ W.obj U),
      a.app U ⟨s, hV⟩ = b.app U ⟨s, hW⟩) : (V ⊔ W).toFunctor ⟶ Z where
  app U := TypeCat.ofHom fun x => by
    classical
    exact if h : x.1 ∈ V.obj U then a.app U ⟨x.1, h⟩ else b.app U ⟨x.1, x.2.resolve_left h⟩
  naturality U U' i := by
    classical
    ext x
    have na : ∀ y : V.toFunctor.obj U, Z.map i (a.app U y) = a.app U' (V.toFunctor.map i y) :=
      fun y => (NatTrans.naturality_apply a i y).symm
    have nb : ∀ y : W.toFunctor.obj U, Z.map i (b.app U y) = b.app U' (W.toFunctor.map i y) :=
      fun y => (NatTrans.naturality_apply b i y).symm
    dsimp
    split_ifs with h1 h2 h2
    · exact (na ⟨x.1, h2⟩).symm
    · exact (hab _ _ _ _).trans (nb ⟨x.1, x.2.resolve_left h2⟩).symm
    · exact absurd (V.map i h2) h1
    · exact (nb ⟨x.1, x.2.resolve_left h2⟩).symm

/-- The glued morphism restricts to the given morphism on `V`. -/
theorem homOfLe_supDesc_left {Z : Cᵒᵖ ⥤ Type w} (a : V.toFunctor ⟶ Z) (b : W.toFunctor ⟶ Z)
    (hab : ∀ (U : Cᵒᵖ) (s : F.obj U) (hV : s ∈ V.obj U) (hW : s ∈ W.obj U),
      a.app U ⟨s, hV⟩ = b.app U ⟨s, hW⟩) :
    homOfLe le_sup_left ≫ supDesc V W a b hab = a := by
  ext U x
  exact dite_eq_left x.2

/-- The glued morphism restricts to the given morphism on `W`. -/
theorem homOfLe_supDesc_right {Z : Cᵒᵖ ⥤ Type w} (a : V.toFunctor ⟶ Z) (b : W.toFunctor ⟶ Z)
    (hab : ∀ (U : Cᵒᵖ) (s : F.obj U) (hV : s ∈ V.obj U) (hW : s ∈ W.obj U),
      a.app U ⟨s, hV⟩ = b.app U ⟨s, hW⟩) :
    homOfLe le_sup_right ≫ supDesc V W a b hab = b := by
  classical
  ext U x
  change dite _ _ _ = _
  split_ifs with h
  · exact hab _ _ h x.2
  · rfl

/-- A morphism out of `V ⊔ W` is determined by its restrictions to `V` and to `W`. -/
theorem eq_supDesc {Z : Cᵒᵖ ⥤ Type w} (a : V.toFunctor ⟶ Z) (b : W.toFunctor ⟶ Z)
    (hab : ∀ (U : Cᵒᵖ) (s : F.obj U) (hV : s ∈ V.obj U) (hW : s ∈ W.obj U),
      a.app U ⟨s, hV⟩ = b.app U ⟨s, hW⟩) (m : (V ⊔ W).toFunctor ⟶ Z)
    (ha : homOfLe le_sup_left ≫ m = a) (hb : homOfLe le_sup_right ≫ m = b) :
    m = supDesc V W a b hab := by
  classical
  ext U x
  change _ = dite _ _ _
  split_ifs with h
  · rw [← ha]
    rfl
  · rw [← hb]
    rfl

variable {V W}

/-- **Two subsheaves which cover locally and meet only over objects covered by the empty sieve
form a coproduct.** Let `F` be a sheaf of sets and `V`, `W` subfunctors which are sheaves, with
`(V ⊔ W).sheafify J = ⊤` and `V ⊓ W ≤ (⊥ : Subfunctor F).sheafify J`. Then the inclusions of
`V` (index `true`) and `W` (index `false`) form a colimit cofan of sheaves with vertex `F`. -/
noncomputable def isColimitCofanOfSheafifySup (hF : Presheaf.IsSheaf J F)
    (hVW : ∀ b : Bool, Presheaf.IsSheaf J (cond b V W).toFunctor)
    (hsup : (V ⊔ W).sheafify J = ⊤) (hinf : V ⊓ W ≤ (⊥ : Subfunctor F).sheafify J) :
    IsColimit (Cofan.mk (⟨F, hF⟩ : Sheaf J (Type w))
      (fun b => ObjectProperty.homMk (cond b V W).ι :
        ∀ b : Bool, (⟨(cond b V W).toFunctor, hVW b⟩ : Sheaf J (Type w)) ⟶ ⟨F, hF⟩)) := by
  have hle : Subfunctor.range (𝟙 F) ≤ (V ⊔ W).sheafify J := hsup ▸ le_top
  let ℓ : F ⟶ ((V ⊔ W).sheafify J).toFunctor := Subfunctor.lift (𝟙 F) hle
  have hℓ : ∀ b : Bool, (cond b V W).ι ≫ ℓ =
      homOfLe (show cond b V W ≤ V ⊔ W by cases b <;> simp) ≫ homOfLe (le_sheafify J _) :=
    fun b => rfl
  have hab : ∀ (Z : Sheaf J (Type w)) (U : Cᵒᵖ) (s : F.obj U) (hV : s ∈ V.obj U)
      (hW : s ∈ W.obj U) (x y : Z.obj.obj U), x = y := by
    intro Z U s hV hW x y
    have h := hinf U ⟨hV, hW⟩
    change (⊥ : Subfunctor F).sieveOfSection s ∈ J (unop U) at h
    rw [show (⊥ : Subfunctor F).sieveOfSection s = ⊥ from le_antisymm (fun _ _ h => h) bot_le]
      at h
    exact ((isSheaf_iff_isSheaf_of_type _ _).1 Z.property ⊥ h).isSeparatedFor.ext
      fun _ _ hf => hf.elim
  refine Cofan.IsColimit.mk _
    (fun t => ObjectProperty.homMk (ℓ ≫ sheafifyLift _ (supDesc V W (t.inj true).hom
      (t.inj false).hom (fun U s hV hW => hab t.pt U s hV hW _ _))
      ((isSheaf_iff_isSheaf_of_type _ _).1 t.pt.property)))
    (fun t b => ?_) (fun t m hm => ?_)
  · refine Sheaf.hom_ext ?_
    change (cond b V W).ι ≫ ℓ ≫ _ = _
    rw [← Category.assoc, hℓ, Category.assoc, to_sheafifyLift]
    cases b
    · exact homOfLe_supDesc_right V W _ _ _
    · exact homOfLe_supDesc_left V W _ _ _
  · refine Sheaf.hom_ext ?_
    change m.hom = ℓ ≫ _
    have hm' : ((V ⊔ W).sheafify J).ι ≫ m.hom = sheafifyLift _ (supDesc V W (t.inj true).hom
        (t.inj false).hom (fun U s hV hW => hab t.pt U s hV hW _ _))
        ((isSheaf_iff_isSheaf_of_type _ _).1 t.pt.property) := by
      refine to_sheafify_lift_unique (G := V ⊔ W)
        ((isSheaf_iff_isSheaf_of_type _ _).1 t.pt.property) _ _ ?_
      rw [to_sheafifyLift]
      exact eq_supDesc V W _ _ _ _ (Sheaf.hom_ext_iff.1 (hm true)) (Sheaf.hom_ext_iff.1 (hm false))
    rw [← hm', ← Category.assoc]
    rfl

end CategoryTheory.Subfunctor
