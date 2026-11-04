module

public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Inverse image of a sheafified representable, for large sheaves of sets

Let `u : C ⥤ D` be a continuous functor of sites whose sheaf pushforward has a left adjoint
`u_s`. Then `u_s` carries the sheafified representable `h_U^#` on `C` to the sheafified
representable `h_{u(U)}^#` on `D`, naturally in `U`.

This is the analogue of `sheafPullback_sheafify_yoneda_natIso` for sheaves of sets valued in
`Type (max u v)` rather than `Type v`, that is, for the sheafified Yoneda embedding
`CategoryTheory.Sheaf.sheafifiedYoneda` built from `CategoryTheory.uliftYoneda` rather than from
`CategoryTheory.yoneda`. The two sites are taken with the same universe for their objects.

## Main definitions

* `CategoryTheory.Sheaf.sheafPullbackSheafifiedYonedaIso`: the isomorphism
  `u_s (h_U^#) ≅ h_{u(U)}^#`.
* `CategoryTheory.Sheaf.sheafPullbackCompSheafifiedYonedaIso`: the same isomorphism read as an
  isomorphism of functors `h_•^# ⋙ u_s ≅ u ⋙ h_•^#`, natural in the object.
* `CategoryTheory.Sheaf.sheafifiedYonedaCompSheafPullbackIso`: the isomorphism of functors
  `sheafifiedYoneda J ⋙ u_s ≅ u ⋙ sheafifiedYoneda K`.

## References

* [Stacks Project, Tag 04D3](https://stacks.math.columbia.edu/tag/04D3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u₁

namespace CategoryTheory.Sheaf

variable {C : Type u₁} [Category.{v} C] {D : Type u₁} [Category.{v} D]
  (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [u.IsContinuous J K]
  [HasWeakSheafify J (Type max u₁ v)] [HasWeakSheafify K (Type max u₁ v)]
  [(u.sheafPushforwardContinuous (Type max u₁ v) J K).IsRightAdjoint]

omit [HasWeakSheafify J (Type max u₁ v)] [HasWeakSheafify K (Type max u₁ v)]
  [(u.sheafPushforwardContinuous (Type max u₁ v) J K).IsRightAdjoint] in
/-- Sections of the pushforward `u^s G` over `U` are sections of `G` over `u(U)`: the pushforward
is precomposition with `u.op`, so the two are the same type. -/
def pushforwardSectionsEquiv (G : Sheaf K (Type max u₁ v)) (U : C) :
    ((u.sheafPushforwardContinuous (Type max u₁ v) J K).obj G).obj.obj (op U) ≃
      G.obj.obj (op (u.obj U)) :=
  Equiv.refl _

omit [HasWeakSheafify J (Type max u₁ v)] [HasWeakSheafify K (Type max u₁ v)]
  [(u.sheafPushforwardContinuous (Type max u₁ v) J K).IsRightAdjoint] in
/-- `pushforwardSectionsEquiv` is the identity on sections. -/
@[simp]
lemma pushforwardSectionsEquiv_apply (G : Sheaf K (Type max u₁ v)) (U : C)
    (x : ((u.sheafPushforwardContinuous (Type max u₁ v) J K).obj G).obj.obj (op U)) :
    pushforwardSectionsEquiv u J K G U x = x :=
  rfl

/-- The bijection `Hom(u_s(h_U^#), G) ≃ (u^s G)(U)` exhibiting the inverse image of a sheafified
representable as a corepresenting object for `G ↦ (u^s G)(U)`. -/
def pullbackSheafifiedYonedaEquiv (U : C) (G : Sheaf K (Type max u₁ v)) :
    ((u.sheafPullback (Type max u₁ v) J K).obj
        ((presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj U)) ⟶ G) ≃
      ((u.sheafPushforwardContinuous (Type max u₁ v) J K).obj G).obj.obj (op U) :=
  ((u.sheafAdjunctionContinuous (Type max u₁ v) J K).homEquiv _ _).trans
    (((sheafificationAdjunction J (Type max u₁ v)).homEquiv _ _).trans uliftYonedaEquiv.{u₁})

/-- The bijection `Hom(h_d^#, G) ≃ G(d)` exhibiting a sheafified representable as a
corepresenting object. -/
def sheafifiedYonedaEquiv (d : D) (G : Sheaf K (Type max u₁ v)) :
    ((presheafToSheaf K (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj d) ⟶ G) ≃
      G.obj.obj (op d) :=
  ((sheafificationAdjunction K (Type max u₁ v)).homEquiv _ _).trans uliftYonedaEquiv.{u₁}

omit [HasWeakSheafify K (Type max u₁ v)] in
/-- The corepresentability bijection for the inverse image is natural in the test sheaf. -/
lemma pullbackSheafifiedYonedaEquiv_naturality (U : C)
    {G G' : Sheaf K (Type max u₁ v)} (α : G ⟶ G')
    (f : (u.sheafPullback (Type max u₁ v) J K).obj
      ((presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj U)) ⟶ G) :
    pushforwardSectionsEquiv u J K G' U (pullbackSheafifiedYonedaEquiv u J K U G' (f ≫ α)) =
      α.hom.app (op (u.obj U))
        (pushforwardSectionsEquiv u J K G U (pullbackSheafifiedYonedaEquiv u J K U G f)) := by
  simp only [pushforwardSectionsEquiv_apply, pullbackSheafifiedYonedaEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  exact uliftYonedaEquiv_comp _ _

/-- The corepresentability bijection for a sheafified representable is natural in the test
sheaf. -/
lemma sheafifiedYonedaEquiv_naturality (d : D) {G G' : Sheaf K (Type max u₁ v)} (α : G ⟶ G')
    (g : (presheafToSheaf K (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj d) ⟶ G) :
    sheafifiedYonedaEquiv K d G' (g ≫ α) =
      α.hom.app (op d) (sheafifiedYonedaEquiv K d G g) := by
  simp only [sheafifiedYonedaEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  exact uliftYonedaEquiv_comp _ _

/-- The natural isomorphism of corepresented functors
`Hom(u_s(h_U^#), -) ≅ Hom(h_{u(U)}^#, -)`, both being `G ↦ G(u(U))`. -/
def pullbackSheafifiedYonedaCorepIso (U : C) :
    coyoneda.obj (op ((u.sheafPullback (Type max u₁ v) J K).obj
        ((presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj U)))) ≅
      coyoneda.obj (op ((presheafToSheaf K (Type max u₁ v)).obj
        (uliftYoneda.{u₁}.obj (u.obj U)))) :=
  NatIso.ofComponents
    (fun G ↦ Equiv.toIso (((pullbackSheafifiedYonedaEquiv u J K U G).trans
      (pushforwardSectionsEquiv u J K G U)).trans
      (sheafifiedYonedaEquiv K (u.obj U) G).symm))
    (by
      intro G G' α
      ext f
      change (sheafifiedYonedaEquiv K (u.obj U) G').symm (pushforwardSectionsEquiv u J K G' U
          (pullbackSheafifiedYonedaEquiv u J K U G' (f ≫ α))) =
        (sheafifiedYonedaEquiv K (u.obj U) G).symm (pushforwardSectionsEquiv u J K G U
          (pullbackSheafifiedYonedaEquiv u J K U G f)) ≫ α
      apply (sheafifiedYonedaEquiv K (u.obj U) G').injective
      rw [Equiv.apply_symm_apply, pullbackSheafifiedYonedaEquiv_naturality,
        sheafifiedYonedaEquiv_naturality, Equiv.apply_symm_apply])

/-- For a continuous functor `u : C ⥤ D` of sites whose pushforward has a left adjoint `u_s`, and
an object `U` of `C`, the canonical isomorphism `u_s (h_U^#) ≅ h_{u(U)}^#` of sheaves of sets on
`D`. -/
def sheafPullbackSheafifiedYonedaIso (U : C) :
    (u.sheafPullback (Type max u₁ v) J K).obj
        ((presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj U)) ≅
      (presheafToSheaf K (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj (u.obj U)) :=
  ((Coyoneda.fullyFaithful (C := Sheaf K (Type max u₁ v))).preimageIso
    (pullbackSheafifiedYonedaCorepIso u J K U)).unop.symm

/-- Precomposition with `CategoryTheory.Sheaf.sheafPullbackSheafifiedYonedaIso` carries the
corepresentability bijection of the inverse image to that of the sheafified representable. -/
lemma sheafPullbackSheafifiedYonedaIso_hom_comp (U : C) (G : Sheaf K (Type max u₁ v))
    (g : (presheafToSheaf K (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj (u.obj U)) ⟶ G) :
    pushforwardSectionsEquiv u J K G U (pullbackSheafifiedYonedaEquiv u J K U G
        ((sheafPullbackSheafifiedYonedaIso u J K U).hom ≫ g)) =
      sheafifiedYonedaEquiv K (u.obj U) G g := by
  have key : (sheafPullbackSheafifiedYonedaIso u J K U).hom ≫ g =
      (pullbackSheafifiedYonedaEquiv u J K U G).symm ((pushforwardSectionsEquiv u J K G U).symm
        (sheafifiedYonedaEquiv K (u.obj U) G g)) := by
    have hmap : coyoneda.map
        ((Coyoneda.fullyFaithful (C := Sheaf K (Type max u₁ v))).preimageIso
          (pullbackSheafifiedYonedaCorepIso u J K U)).inv =
        (pullbackSheafifiedYonedaCorepIso u J K U).inv :=
      (Coyoneda.fullyFaithful (C := Sheaf K (Type max u₁ v))).map_preimage _
    have hpre : (sheafPullbackSheafifiedYonedaIso u J K U).hom ≫ g =
        (coyoneda.map ((Coyoneda.fullyFaithful (C := Sheaf K (Type max u₁ v))).preimageIso
          (pullbackSheafifiedYonedaCorepIso u J K U)).inv).app G g := rfl
    rw [hpre, hmap]
    simp [pullbackSheafifiedYonedaCorepIso, NatIso.ofComponents_inv_app,
      Equiv.toIso_inv_hom_apply, Equiv.symm_symm]
  rw [key, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

omit [HasWeakSheafify K (Type max u₁ v)] in
/-- The corepresentability bijection for the inverse image is natural in the object. -/
lemma pullbackSheafifiedYonedaEquiv_naturality_obj {U V : C} (g : U ⟶ V)
    (G : Sheaf K (Type max u₁ v))
    (f : (u.sheafPullback (Type max u₁ v) J K).obj
      ((presheafToSheaf J (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj V)) ⟶ G) :
    pushforwardSectionsEquiv u J K G U (pullbackSheafifiedYonedaEquiv u J K U G
        ((u.sheafPullback (Type max u₁ v) J K).map
          ((presheafToSheaf J (Type max u₁ v)).map (uliftYoneda.{u₁}.map g)) ≫ f)) =
      G.obj.map (u.map g).op (pushforwardSectionsEquiv u J K G V
        (pullbackSheafifiedYonedaEquiv u J K V G f)) := by
  simp only [pushforwardSectionsEquiv_apply, pullbackSheafifiedYonedaEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality.{u₁} _ g.op).symm

/-- The corepresentability bijection for a sheafified representable is natural in the
object. -/
lemma sheafifiedYonedaEquiv_naturality_obj {d e : D} (g : d ⟶ e)
    (G : Sheaf K (Type max u₁ v))
    (s : (presheafToSheaf K (Type max u₁ v)).obj (uliftYoneda.{u₁}.obj e) ⟶ G) :
    sheafifiedYonedaEquiv K d G
        ((presheafToSheaf K (Type max u₁ v)).map (uliftYoneda.{u₁}.map g) ≫ s) =
      G.obj.map g.op (sheafifiedYonedaEquiv K e G s) := by
  simp only [sheafifiedYonedaEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality.{u₁} _ g.op).symm

/-- The isomorphisms `u_s (h_U^#) ≅ h_{u(U)}^#` of
`CategoryTheory.Sheaf.sheafPullbackSheafifiedYonedaIso`, as an isomorphism of functors natural in
the object `U`. -/
def sheafPullbackCompSheafifiedYonedaIso :
    uliftYoneda.{u₁} ⋙ presheafToSheaf J (Type max u₁ v) ⋙
        u.sheafPullback (Type max u₁ v) J K ≅
      u ⋙ uliftYoneda.{u₁} ⋙ presheafToSheaf K (Type max u₁ v) :=
  NatIso.ofComponents (fun U ↦ sheafPullbackSheafifiedYonedaIso u J K U) (by
    intro U V g
    have key : ∀ (G : Sheaf K (Type max u₁ v))
        (s : (presheafToSheaf K (Type max u₁ v)).obj
          (uliftYoneda.{u₁}.obj (u.obj V)) ⟶ G),
        pushforwardSectionsEquiv u J K G U (pullbackSheafifiedYonedaEquiv u J K U G
            (((u.sheafPullback (Type max u₁ v) J K).map
                ((presheafToSheaf J (Type max u₁ v)).map (uliftYoneda.{u₁}.map g)) ≫
              (sheafPullbackSheafifiedYonedaIso u J K V).hom) ≫ s)) =
          pushforwardSectionsEquiv u J K G U (pullbackSheafifiedYonedaEquiv u J K U G
            (((sheafPullbackSheafifiedYonedaIso u J K U).hom ≫
              (presheafToSheaf K (Type max u₁ v)).map
                (uliftYoneda.{u₁}.map (u.map g))) ≫ s)) := by
      intro G s
      rw [Category.assoc, Category.assoc, pullbackSheafifiedYonedaEquiv_naturality_obj u J K g G,
        sheafPullbackSheafifiedYonedaIso_hom_comp u J K V G s,
        sheafPullbackSheafifiedYonedaIso_hom_comp u J K U G _,
        sheafifiedYonedaEquiv_naturality_obj K (u.map g) G s]
    have hαβ := key _ (𝟙 _)
    simp only [Category.comp_id] at hαβ
    exact (pullbackSheafifiedYonedaEquiv u J K U _).injective
      ((pushforwardSectionsEquiv u J K _ U).injective hαβ))

/-- The inverse image `u_s` commutes with the sheafified Yoneda embedding:
`sheafifiedYoneda J ⋙ u_s ≅ u ⋙ sheafifiedYoneda K`. -/
def sheafifiedYonedaCompSheafPullbackIso :
    sheafifiedYoneda J ⋙ u.sheafPullback (Type max u₁ v) J K ≅ u ⋙ sheafifiedYoneda K :=
  (Functor.associator _ _ _) ≪≫ sheafPullbackCompSheafifiedYonedaIso u J K

end CategoryTheory.Sheaf

end
