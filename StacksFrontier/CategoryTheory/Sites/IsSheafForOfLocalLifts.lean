module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Hom into a sheaf out of a family of presheaves which is locally a colimit

Let `K` be a Grothendieck topology on a category `𝒜`, let `G` be a `K`-sheaf of types on `𝒜`,
and let `Φ : D ⥤ (𝒜ᵒᵖ ⥤ Type w)` be a functor from an arbitrary category `D` to the presheaves
on `𝒜`. Then `Z ↦ (Φ Z ⟶ G)` is a presheaf of types on `D`. This file proves that it satisfies
the sheaf condition for a sieve `S` on an object `Y` of `D` as soon as the cocone
`(Φ Z ⟶ Φ Y)_{(g : Z ⟶ Y) ∈ S}` is *`K`-locally a colimit on elements*:

* (local surjectivity) every element `a` of `(Φ Y)(T)` lifts, locally on `T`, along some arrow
  of `S`;
* (local injectivity) two lifts `b₁ ∈ (Φ Z₁)(T)` and `b₂ ∈ (Φ Z₂)(T)` of the same element, along
  arrows `g₁` and `g₂` of `S`, are connected locally on `T` through a common lift along some
  `Z ⟶ Z₁` and `Z ⟶ Z₂` making the square over `Y` commute.

The amalgamation of a compatible family is computed elementwise: its value at `a` is glued,
using the sheaf property of `G`, from the values of the family at the local lifts of `a`. The
two conditions are exactly what makes this well defined.

## Main results

* `CategoryTheory.Presieve.isSheafFor_op_comp_yoneda_of_localLifts`: the sheaf condition for
  `Φ.op ⋙ yoneda.obj G` along `S`, under the two local conditions.
-/

@[expose] public section

open CategoryTheory Opposite

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Presieve

variable {𝒜 : Type u₁} [Category.{v₁} 𝒜] {K : GrothendieckTopology 𝒜}
  {G : 𝒜ᵒᵖ ⥤ Type w} {D : Type u₂} [Category.{v₂} D] (Φ : D ⥤ (𝒜ᵒᵖ ⥤ Type w))
  {Y : D} (S : Sieve Y)

namespace LocalLifts

/-- An element `a` of `(Φ Y)(T)` *lifts along `S` at `t : T' ⟶ T`* when its restriction to `T'`
is the image of an element of `(Φ Z)(T')` under an arrow `Z ⟶ Y` of `S`. The arrows `t` at which
`a` lifts form a sieve on `T`. -/
def liftSieve {T : 𝒜} (a : (Φ.obj Y).obj (op T)) : Sieve T where
  arrows T' t := ∃ (Z : D) (g : Z ⟶ Y), S g ∧
    ∃ b : (Φ.obj Z).obj (op T'), (Φ.map g).app (op T') b = (Φ.obj Y).map t.op a
  downward_closed := by
    rintro T' T'' t ⟨Z, g, hg, b, hb⟩ s
    refine ⟨Z, g, hg, (Φ.obj Z).map s.op b, ?_⟩
    rw [NatTrans.naturality_apply, hb, op_comp, Functor.map_comp_apply]

variable {Φ S}

/-- The value of a family at a chosen lift of `a` at an arrow of its lift sieve. -/
noncomputable def liftValue (x : FamilyOfElements (Φ.op ⋙ yoneda.obj G) S.arrows) {T : 𝒜}
    {a : (Φ.obj Y).obj (op T)} {T' : 𝒜} {t : T' ⟶ T} (ht : liftSieve Φ S a t) : G.obj (op T') :=
  (x ht.choose_spec.choose ht.choose_spec.choose_spec.1).app (op T')
    ht.choose_spec.choose_spec.2.choose

/-- The family, on the lift sieve of `a`, of the values of `x` at chosen lifts. -/
noncomputable def liftFamily (x : FamilyOfElements (Φ.op ⋙ yoneda.obj G) S.arrows) {T : 𝒜}
    (a : (Φ.obj Y).obj (op T)) : FamilyOfElements G (liftSieve Φ S a).arrows :=
  fun _ _ ht => liftValue x ht

end LocalLifts

open LocalLifts

variable {Φ S}

/-- Under the local injectivity condition, the values of a compatible family at two lifts of
one element agree. -/
theorem LocalLifts.value_eq (hG : Presieve.IsSheaf K G)
    (hinj : ∀ ⦃Z₁ Z₂ : D⦄ (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y), S g₁ → S g₂ →
      ∀ (T : 𝒜) (b₁ : (Φ.obj Z₁).obj (op T)) (b₂ : (Φ.obj Z₂).obj (op T)),
        (Φ.map g₁).app (op T) b₁ = (Φ.map g₂).app (op T) b₂ →
        ∃ M ∈ K T, ∀ ⦃T' : 𝒜⦄ (t : T' ⟶ T), M t →
          ∃ (Z : D) (h₁ : Z ⟶ Z₁) (h₂ : Z ⟶ Z₂), h₁ ≫ g₁ = h₂ ≫ g₂ ∧
            ∃ c : (Φ.obj Z).obj (op T'), (Φ.map h₁).app (op T') c = (Φ.obj Z₁).map t.op b₁ ∧
              (Φ.map h₂).app (op T') c = (Φ.obj Z₂).map t.op b₂)
    {x : FamilyOfElements (Φ.op ⋙ yoneda.obj G) S.arrows} (hx : x.Compatible)
    {Z₁ Z₂ : D} {g₁ : Z₁ ⟶ Y} {g₂ : Z₂ ⟶ Y} (hg₁ : S g₁) (hg₂ : S g₂) {T : 𝒜}
    {b₁ : (Φ.obj Z₁).obj (op T)} {b₂ : (Φ.obj Z₂).obj (op T)}
    (hb : (Φ.map g₁).app (op T) b₁ = (Φ.map g₂).app (op T) b₂) :
    (x g₁ hg₁).app (op T) b₁ = (x g₂ hg₂).app (op T) b₂ := by
  obtain ⟨M, hM, hMlift⟩ := hinj g₁ g₂ hg₁ hg₂ T b₁ b₂ hb
  refine (hG M hM).isSeparatedFor.ext fun T' t ht => ?_
  obtain ⟨Z, h₁, h₂, hcomm, c, hc₁, hc₂⟩ := hMlift t ht
  have hx'' := congrArg (fun φ : Φ.obj Z ⟶ G => φ.app (op T') c) (hx h₁ h₂ hg₁ hg₂ hcomm)
  dsimp at hx''
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  dsimp only [Functor.op_obj, Opposite.unop_op]
  rw [← hc₁, ← hc₂]
  exact hx''

/-- Under the local injectivity condition, the value of a compatible family at the chosen lift
equals its value at any other lift. -/
private theorem LocalLifts.liftValue_eq (hG : Presieve.IsSheaf K G)
    (hinj : ∀ ⦃Z₁ Z₂ : D⦄ (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y), S g₁ → S g₂ →
      ∀ (T : 𝒜) (b₁ : (Φ.obj Z₁).obj (op T)) (b₂ : (Φ.obj Z₂).obj (op T)),
        (Φ.map g₁).app (op T) b₁ = (Φ.map g₂).app (op T) b₂ →
        ∃ M ∈ K T, ∀ ⦃T' : 𝒜⦄ (t : T' ⟶ T), M t →
          ∃ (Z : D) (h₁ : Z ⟶ Z₁) (h₂ : Z ⟶ Z₂), h₁ ≫ g₁ = h₂ ≫ g₂ ∧
            ∃ c : (Φ.obj Z).obj (op T'), (Φ.map h₁).app (op T') c = (Φ.obj Z₁).map t.op b₁ ∧
              (Φ.map h₂).app (op T') c = (Φ.obj Z₂).map t.op b₂)
    {x : FamilyOfElements (Φ.op ⋙ yoneda.obj G) S.arrows} (hx : x.Compatible)
    {T T' : 𝒜} {a : (Φ.obj Y).obj (op T)} {t : T' ⟶ T} (ht : liftSieve Φ S a t)
    {Z : D} {g : Z ⟶ Y} (hg : S g) (b : (Φ.obj Z).obj (op T'))
    (hb : (Φ.map g).app (op T') b = (Φ.obj Y).map t.op a) :
    liftValue x ht = (x g hg).app (op T') b :=
  value_eq hG hinj hx _ hg (ht.choose_spec.choose_spec.2.choose_spec.trans hb.symm)

/-- Under the local injectivity condition, the family of values of a compatible family at the
lifts of `a` is compatible. -/
private theorem LocalLifts.liftFamily_compatible (hG : Presieve.IsSheaf K G)
    (hinj : ∀ ⦃Z₁ Z₂ : D⦄ (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y), S g₁ → S g₂ →
      ∀ (T : 𝒜) (b₁ : (Φ.obj Z₁).obj (op T)) (b₂ : (Φ.obj Z₂).obj (op T)),
        (Φ.map g₁).app (op T) b₁ = (Φ.map g₂).app (op T) b₂ →
        ∃ M ∈ K T, ∀ ⦃T' : 𝒜⦄ (t : T' ⟶ T), M t →
          ∃ (Z : D) (h₁ : Z ⟶ Z₁) (h₂ : Z ⟶ Z₂), h₁ ≫ g₁ = h₂ ≫ g₂ ∧
            ∃ c : (Φ.obj Z).obj (op T'), (Φ.map h₁).app (op T') c = (Φ.obj Z₁).map t.op b₁ ∧
              (Φ.map h₂).app (op T') c = (Φ.obj Z₂).map t.op b₂)
    {x : FamilyOfElements (Φ.op ⋙ yoneda.obj G) S.arrows} (hx : x.Compatible)
    {T : 𝒜} (a : (Φ.obj Y).obj (op T)) : (liftFamily x a).Compatible := by
  rw [compatible_iff_sieveCompatible]
  intro T' T'' t s ht
  dsimp only [liftFamily]
  obtain ⟨Z, g, hg, b, hb⟩ := id ht
  rw [liftValue_eq hG hinj hx ht hg b hb,
    liftValue_eq hG hinj hx ((liftSieve Φ S a).downward_closed ht s) hg ((Φ.obj Z).map s.op b)
      (by rw [NatTrans.naturality_apply, hb, op_comp, Functor.map_comp_apply]),
    ← NatTrans.naturality_apply]
  rfl

/-- **The sheaf condition for `Z ↦ (Φ Z ⟶ G)` along a sieve which is locally a colimit.** Let
`G` be a `K`-sheaf of types on `𝒜` and `Φ : D ⥤ (𝒜ᵒᵖ ⥤ Type w)` a functor. If every element of
`(Φ Y)(T)` lifts along `S` locally on `T` (`hsurj`), and two lifts of one element along arrows
of `S` are locally connected through a common lift (`hinj`), then the presheaf
`Φ.op ⋙ yoneda.obj G` on `D` is a sheaf for `S`. -/
theorem isSheafFor_op_comp_yoneda_of_localLifts (hG : Presieve.IsSheaf K G)
    (hsurj : ∀ (T : 𝒜) (a : (Φ.obj Y).obj (op T)), liftSieve Φ S a ∈ K T)
    (hinj : ∀ ⦃Z₁ Z₂ : D⦄ (g₁ : Z₁ ⟶ Y) (g₂ : Z₂ ⟶ Y), S g₁ → S g₂ →
      ∀ (T : 𝒜) (b₁ : (Φ.obj Z₁).obj (op T)) (b₂ : (Φ.obj Z₂).obj (op T)),
        (Φ.map g₁).app (op T) b₁ = (Φ.map g₂).app (op T) b₂ →
        ∃ M ∈ K T, ∀ ⦃T' : 𝒜⦄ (t : T' ⟶ T), M t →
          ∃ (Z : D) (h₁ : Z ⟶ Z₁) (h₂ : Z ⟶ Z₂), h₁ ≫ g₁ = h₂ ≫ g₂ ∧
            ∃ c : (Φ.obj Z).obj (op T'), (Φ.map h₁).app (op T') c = (Φ.obj Z₁).map t.op b₁ ∧
              (Φ.map h₂).app (op T') c = (Φ.obj Z₂).map t.op b₂) :
    IsSheafFor (Φ.op ⋙ yoneda.obj G) S.arrows := by
  intro x hx
  have hval := @liftValue_eq _ _ _ _ _ _ _ _ _ hG hinj _ hx
  have hcomp := @liftFamily_compatible _ _ _ _ _ _ _ _ _ hG hinj _ hx
  -- the amalgamation, elementwise
  let glue : ∀ (T : 𝒜), (Φ.obj Y).obj (op T) → G.obj (op T) := fun T a =>
    (hG _ (hsurj T a)).amalgamate _ (hcomp a)
  -- the glued value at an arrow, computed through any lift
  have hglue : ∀ {T T' : 𝒜} (a : (Φ.obj Y).obj (op T)) {t : T' ⟶ T} {Z : D} {g : Z ⟶ Y}
      (hg : S g) (b : (Φ.obj Z).obj (op T')) (hb : (Φ.map g).app (op T') b = (Φ.obj Y).map t.op a),
      G.map t.op (glue T a) = (x g hg).app (op T') b := fun a _ _ _ hg b hb =>
    ((hG _ (hsurj _ a)).valid_glue (hcomp a) _ ⟨_, _, hg, b, hb⟩).trans (hval _ hg b hb)
  -- the glued value at a restriction is the restriction of the glued value
  have hnat : ∀ {T₁ T₂ : 𝒜} (s : T₂ ⟶ T₁) (a : (Φ.obj Y).obj (op T₁)),
      glue T₂ ((Φ.obj Y).map s.op a) = G.map s.op (glue T₁ a) := by
    intro T₁ T₂ s a
    refine ((hG _ (hsurj T₂ ((Φ.obj Y).map s.op a))).isSeparatedFor.ext fun T' t ht => ?_)
    obtain ⟨Z, g, hg, b, hb⟩ := ht
    rw [hglue _ hg b hb, ← Functor.map_comp_apply, ← op_comp,
      hglue a hg b (by rw [hb, op_comp, Functor.map_comp_apply])]
  let τ : Φ.obj Y ⟶ G :=
    { app := fun T => ↾(fun a => glue T.unop a)
      naturality := fun T₁ T₂ s => by
        ext a
        exact hnat s.unop a }
  -- the glued value at the image of a lift is the value of the family there
  have hτ : ∀ {Z : D} {g : Z ⟶ Y} (hg : S g) (T : 𝒜) (b : (Φ.obj Z).obj (op T)),
      τ.app (op T) ((Φ.map g).app (op T) b) = (x g hg).app (op T) b := by
    intro Z g hg T b
    have h := hglue ((Φ.map g).app (op T) b) hg b (t := 𝟙 T)
      (by rw [op_id, Functor.map_id_apply])
    rwa [op_id, Functor.map_id_apply] at h
  refine ⟨τ, fun Z g hg => ?_, fun τ' hτ' => ?_⟩
  · refine NatTrans.ext (funext fun T => ?_)
    ext b
    exact hτ hg T.unop b
  · refine NatTrans.ext (funext fun T => ?_)
    ext a
    refine (hG _ (hsurj T.unop a)).isSeparatedFor.ext fun T' t ht => ?_
    change G.map t.op (τ'.app T a) = G.map t.op (glue T.unop a)
    obtain ⟨Z, g, hg, b, hb⟩ := id ht
    rw [hglue a hg b hb, ← NatTrans.naturality_apply]
    dsimp only [Functor.op_obj, Opposite.unop_op]
    rw [← hb]
    exact congrArg (fun φ : Φ.obj Z ⟶ G => φ.app (op T') b) (hτ' g hg)

end CategoryTheory.Presieve

end
