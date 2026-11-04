module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheaf pullback of a sheafified representable

Stacks tag 04D3: for a continuous functor `u : C ⥤ D` between sites `(C, J)` and `(D, K)`, the
left adjoint `u_s` of the sheaf pushforward `u^s` carries the sheafification of the
representable presheaf `h_U` on `C` to the sheafification of `h_{u(U)}` on `D`, naturally in
`U`. The proof is by corepresentability: chaining the two adjunctions with `yonedaEquiv`
exhibits both `Hom(u_s(h_U^♯), -)` and `Hom(h_{u(U)}^♯, -)` as the functor `G ↦ G(u(U))` on
`Sh(D)`, and coyoneda is fully faithful. Stacks states the conclusion as an equality of
sheaves; with fixed concrete constructions the faithful rendering is a canonical isomorphism.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
variable (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable [u.IsContinuous J K]
variable [HasWeakSheafify J (Type v)] [HasWeakSheafify K (Type v)]
variable [(u.sheafPushforwardContinuous (Type v) J K).IsRightAdjoint]

-- Helper constructions for the corepresentability argument.

/-- `Hom(u_s(a_J h_U), G) ≃ G.val (u U)`, the LHS corepresentability bijection. -/
noncomputable def lhsEquiv (U : C) (G : Sheaf K (Type v)) :
    ((u.sheafPullback (Type v) J K).obj
        ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⟶ G) ≃
    G.obj.obj (Opposite.op (u.obj U)) :=
  (u.sheafAdjunctionContinuous (Type v) J K).homEquiv _ _ |>.trans
    ((sheafificationAdjunction J (Type v)).homEquiv _ _ |>.trans yonedaEquiv)

/-- `Hom(a_K h_{u U}, G) ≃ G.val (u U)`, the RHS corepresentability bijection. -/
@[sga "4 VIII 7.9.1"]
noncomputable def rhsEquiv (U : C) (G : Sheaf K (Type v)) :
    ((presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj U)) ⟶ G) ≃
    G.obj.obj (Opposite.op (u.obj U)) :=
  (sheafificationAdjunction K (Type v)).homEquiv _ _ |>.trans yonedaEquiv

/-- Naturality in the object of the bijection `Hom(a_L h_X, F) ≃ F.val X`. -/
private lemma sheafify_yonedaEquiv_naturality_left {E : Type*} [Category.{v} E]
    (L : GrothendieckTopology E) [HasWeakSheafify L (Type v)] {X Y : E} (g : X ⟶ Y)
    {F : Sheaf L (Type v)} (s : (presheafToSheaf L (Type v)).obj (yoneda.obj Y) ⟶ F) :
    yonedaEquiv ((sheafificationAdjunction L (Type v)).homEquiv _ _
        ((presheafToSheaf L (Type v)).map (yoneda.map g) ≫ s)) =
      F.obj.map g.op (yonedaEquiv ((sheafificationAdjunction L (Type v)).homEquiv _ _ s)) := by
  rw [Adjunction.homEquiv_naturality_left]
  exact (yonedaEquiv_naturality _ _).symm

omit [HasWeakSheafify K (Type v)] in
/-- Naturality of `lhsEquiv` in the test sheaf `G`. -/
lemma lhsEquiv_naturality (U : C) {G G' : Sheaf K (Type v)} (α : G ⟶ G')
    (f : (u.sheafPullback (Type v) J K).obj
        ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ⟶ G) :
    lhsEquiv u J K U G' (f ≫ α) = α.hom.app (Opposite.op (u.obj U)) (lhsEquiv u J K U G f) := by
  simp only [lhsEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_right]
  erw [yonedaEquiv_comp]

/-- Naturality of `rhsEquiv` in the test sheaf `G`. -/
lemma rhsEquiv_naturality (U : C) {G G' : Sheaf K (Type v)} (α : G ⟶ G')
    (g : (presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj U)) ⟶ G) :
    rhsEquiv u K U G' (g ≫ α) = α.hom.app (Opposite.op (u.obj U)) (rhsEquiv u K U G g) := by
  simp only [rhsEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  erw [yonedaEquiv_comp]

/-- The composite natural isomorphism of corepresented (coyoneda) functors:
`Hom(u_s(a_J h_U), -) ≅ Hom(a_K h_{u U}, -)`, both naturally iso to `G ↦ G.val(u U)`. -/
noncomputable def corepNatIso (U : C) :
    coyoneda.obj (Opposite.op ((u.sheafPullback (Type v) J K).obj
        ((presheafToSheaf J (Type v)).obj (yoneda.obj U)))) ≅
    coyoneda.obj (Opposite.op ((presheafToSheaf K (Type v)).obj
        (yoneda.obj (u.obj U)))) :=
  NatIso.ofComponents
    (fun G => Equiv.toIso ((lhsEquiv u J K U G).trans (rhsEquiv u K U G).symm))
    (by
      intro G G' α
      ext f
      change (rhsEquiv u K U G').symm (lhsEquiv u J K U G' (f ≫ α)) =
        (rhsEquiv u K U G).symm (lhsEquiv u J K U G f) ≫ α
      apply (rhsEquiv u K U G').injective
      rw [Equiv.apply_symm_apply, lhsEquiv_naturality, rhsEquiv_naturality,
        Equiv.apply_symm_apply])

/-- The pointwise isomorphism, obtained by corepresentability (coyoneda is fully
faithful, so the natural iso `corepNatIso` of corepresented functors is the image
of a unique iso of corepresenting objects). -/
@[sga "4 III 4.2" "partial"]
noncomputable def sheafPullbackSheafifyYonedaIso (U : C) :
    (u.sheafPullback (Type v) J K).obj
        ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ≅
    (presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj U)) :=
  ((Coyoneda.fullyFaithful (C := Sheaf K (Type v))).preimageIso (corepNatIso u J K U)).unop.symm

-- Sub-lemmas isolating the content of naturality-in-`U`.

/-- DEFINING PROPERTY of the pointwise iso.

`sheafPullbackSheafifyYonedaIso u J K U` is, by construction, the corepresenting-object
incarnation of `corepNatIso u J K U`, whose components are `lhsEquiv.trans rhsEquiv.symm`.
Concretely this means: precomposition with `Φ_U.hom` carries the RHS bijection to the
LHS bijection, i.e. for every test sheaf `G` and `g : a_K h_{u U} ⟶ G`,
`lhsEquiv U G (Φ_U.hom ≫ g) = rhsEquiv U G g`.

Argument: unfold `sheafPullbackSheafifyYonedaIso` and use the round-trip
property of `Coyoneda.fullyFaithful.preimageIso`: `coyoneda.map (preimageIso h).hom.op`
is `h.hom` (resp. its inverse for `.unop.symm`). Hence `coyoneda.map Φ_U.hom.op` equals
the appropriate component morphism of `corepNatIso u J K U`, whose action on `g` is
`(rhsEquiv U G).symm (lhsEquiv U G ·)` / its inverse `(lhsEquiv U G).symm (rhsEquiv U G ·)`.
Evaluating `coyoneda.map Φ_U.hom.op` on `g` gives `Φ_U.hom ≫ g`; chasing through
`corepNatIso.app G = lhsEquiv.trans rhsEquiv.symm` (and `Equiv.apply_symm_apply`)
yields `lhsEquiv U G (Φ_U.hom ≫ g) = rhsEquiv U G g`.
Relevant API: `Functor.FullyFaithful.preimageIso`, `Functor.FullyFaithful.map_preimage`,
`Coyoneda.fullyFaithful`, `coyoneda_map_app_apply` / `coyoneda.map …` unfolding,
`Iso.unop`, `Iso.symm`, `NatIso.ofComponents_hom_app`, `Equiv.toIso`,
`Equiv.apply_symm_apply`. -/
@[sga "4 III 4.2" "partial"]
lemma sheafPullbackSheafifyYonedaIso_hom_comp (U : C) (G : Sheaf K (Type v))
    (g : (presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj U)) ⟶ G) :
    lhsEquiv u J K U G ((sheafPullbackSheafifyYonedaIso u J K U).hom ≫ g) = rhsEquiv u K U G g := by
  have hmap := congr_arg (fun t => t.app G g)
    ((Coyoneda.fullyFaithful (C := Sheaf K (Type v))).map_preimage (corepNatIso u J K U).inv)
  have key : (sheafPullbackSheafifyYonedaIso u J K U).hom ≫ g
      = (lhsEquiv u J K U G).symm (rhsEquiv u K U G g) := by
    refine hmap.trans ?_
    simp [corepNatIso]
  rw [key, Equiv.apply_symm_apply]

omit [HasWeakSheafify K (Type v)] in
/-- Naturality of `lhsEquiv` in the object `U` (along `g : U ⟶ V`).

`lhsEquiv` is built from `homEquiv`s of two adjunctions followed by `yonedaEquiv`.
Precomposing a morphism `f : u_s(a_J h_V) ⟶ G` with the functor image
`u_s(a_J(yoneda.map g)) : u_s(a_J h_U) ⟶ u_s(a_J h_V)` corresponds, under the two
`homEquiv` adjunction naturalities (`Adjunction.homEquiv_naturality_left`), to
precomposing `h_U → (u^s G).val` with `yoneda.map g`; under `yonedaEquiv` (its
naturality in the index object, `yonedaEquiv_naturality` / `yonedaEquiv_comp`) this
becomes applying `(u^s G).val.map g.op = G.val.map (u.map g).op` to the evaluated
element. Hence:
`lhsEquiv U G (u_s(a_J(yoneda.map g)) ≫ f) = G.val.map (u.map g).op (lhsEquiv V G f)`.
Argument: `simp only [lhsEquiv, Equiv.trans_apply]`, then rewrite by
`Adjunction.homEquiv_naturality_left` twice (the functor `u_s = a_J ∘ u_p` composite
matches `sheafAdjunctionContinuous` then `sheafificationAdjunction`). This leaves
EXACTLY the goal
  `yonedaEquiv (yoneda.map g ≫ φ) = G.val.map (u.map g).op (yonedaEquiv φ)`
where `φ : h_V ⟶ (u^s G).val`. This is `yonedaEquiv_naturality` applied with the
functor `F := (u^s G).val` at morphism `g`, MODULO the definitional identity
`(u^s G).val.map g.op = G.val.map (u.map g).op` (since `u^s G = G ∘ u^op` by
`Functor.sheafPushforwardContinuous`). NOTE: in this Mathlib, `erw/rw [yonedaEquiv_naturality]`
fails to unify because the RHS is displayed via `G.val.map (u.map g).op` rather than
`(u^s G).val.map g.op`; bridge it first, e.g. `show … (u^s G).val.map g.op … ` (or
`change`/`conv` to rewrite the functor on the RHS using
`Functor.sheafPushforwardContinuous`), then `exact (yonedaEquiv_naturality _ _).symm`
(cf. the fully-worked `rhsEquiv_naturality_U` below, which is the one-adjunction analogue
and closes by `rw [homEquiv_naturality_left]; erw [yonedaEquiv_naturality]; rfl`). -/
lemma lhsEquiv_naturality_U {U V : C} (g : U ⟶ V) (G : Sheaf K (Type v))
    (f : (u.sheafPullback (Type v) J K).obj
        ((presheafToSheaf J (Type v)).obj (yoneda.obj V)) ⟶ G) :
    lhsEquiv u J K U G
        ((u.sheafPullback (Type v) J K).map
            ((presheafToSheaf J (Type v)).map (yoneda.map g)) ≫ f) =
      G.obj.map (u.map g).op (lhsEquiv u J K V G f) := by
  simp only [lhsEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  exact sheafify_yonedaEquiv_naturality_left J _ _

/-- Naturality of `rhsEquiv` in the object `U` (along `g : U ⟶ V`).

Same shape as `lhsEquiv_naturality_U`, one adjunction shorter:
`rhsEquiv U G (a_K(yoneda.map (u.map g)) ≫ s) = G.val.map (u.map g).op (rhsEquiv V G s)`.
Argument: `simp only [rhsEquiv, Equiv.trans_apply]`, rewrite by
`Adjunction.homEquiv_naturality_left` (for `sheafificationAdjunction`), then
`yonedaEquiv` naturality in the source object (`yonedaEquiv_naturality`/`yonedaEquiv_comp`)
turns precomposition with `yoneda.map (u.map g)` into `G.val.map (u.map g).op`. -/
lemma rhsEquiv_naturality_U {U V : C} (g : U ⟶ V) (G : Sheaf K (Type v))
    (s : (presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj V)) ⟶ G) :
    rhsEquiv u K U G
        ((presheafToSheaf K (Type v)).map (yoneda.map (u.map g)) ≫ s) =
      G.obj.map (u.map g).op (rhsEquiv u K V G s) := by
  simp only [rhsEquiv, Equiv.trans_apply]
  exact sheafify_yonedaEquiv_naturality_left K _ _

/-- Stacks Tag 04D3 (Lemma 7.13.5), pointwise form.

For a continuous functor `u : C ⥤ D` between sites `(C, J)` and `(D, K)` and an
object `U` of `C`, applying the left-adjoint sheaf functor `u_s = u.sheafPullback`
to the sheafification of the representable presheaf `h_U` yields the sheafification
of the representable presheaf `h_{u(U)}` on `D`:
  `u_s (h_U^#) ≅ h_{u(U)}^#`. -/
@[stacks 04D3, sga "4 III 4.2" "partial"]
theorem sheafPullback_sheafify_yoneda_iso (U : C) :
    Nonempty
      ((u.sheafPullback (Type v) J K).obj
        ((presheafToSheaf J (Type v)).obj (yoneda.obj U)) ≅
      (presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj U))) :=
  ⟨sheafPullbackSheafifyYonedaIso u J K U⟩

/-- Stacks Tag 04D3 (Lemma 7.13.5), natural-in-`U` form.

The isomorphism `u_s (h_U^#) ≅ h_{u(U)}^#` is natural in `U`: there is an
isomorphism of functors `C ⥤ Sheaf K (Type v)`
  `(yoneda ⋙ a_J ⋙ u_s) ≅ (u ⋙ yoneda ⋙ a_K)`,
where `a_J = presheafToSheaf J (Type v)` and `a_K = presheafToSheaf K (Type v)`.

The components are the pointwise isos `sheafPullbackSheafifyYonedaIso`; naturality
reduces, by faithfulness of `coyoneda`, to the naturality-in-`U` of the
corepresentability bijections, packaged in the three sub-lemmas above. -/
@[sga "4 III 1.4" "partial"]
theorem sheafPullback_sheafify_yoneda_natIso :
    Nonempty
      ((yoneda ⋙ presheafToSheaf J (Type v) ⋙ u.sheafPullback (Type v) J K) ≅
      (u ⋙ yoneda ⋙ presheafToSheaf K (Type v))) := by
  refine ⟨NatIso.ofComponents (fun U => sheafPullbackSheafifyYonedaIso u J K U) ?_⟩
  intro U V g
  -- Naturality square for `g : U ⟶ V`. Write `Φ_W := sheafPullbackSheafifyYonedaIso u J K W`.
  -- Goal (after `NatIso.ofComponents`, with `.map` on the composite functors unfolded):
  --   `u_s(a_J(yoneda.map g)) ≫ Φ_V.hom = Φ_U.hom ≫ a_K(yoneda.map (u.map g))`.
  -- Abbreviate the two sides as `α, β : u_s(a_J h_U) ⟶ a_K h_{u V}`.
  -- KEY per-test-sheaf identity: for every sheaf `G` and `s : a_K h_{u V} ⟶ G`,
  --   `lhsEquiv U G (α ≫ s) = lhsEquiv U G (β ≫ s)`,
  -- both equal to `G.val.map (u.map g).op (rhsEquiv V G s)`:
  --   α-side: `Category.assoc`, `lhsEquiv_naturality_U`, then DP `…_hom_comp` at `V`;
  --   β-side: `Category.assoc`, DP `…_hom_comp` at `U`, then `rhsEquiv_naturality_U`.
  -- Since `lhsEquiv U G` is injective, taking `G := a_K h_{u V}`, `s := 𝟙` and using
  -- `Category.comp_id` reduces the per-`s` identity to `α = β`, the goal.
  have key : ∀ (G : Sheaf K (Type v))
      (s : (presheafToSheaf K (Type v)).obj (yoneda.obj (u.obj V)) ⟶ G),
      lhsEquiv u J K U G
          (((u.sheafPullback (Type v) J K).map
              ((presheafToSheaf J (Type v)).map (yoneda.map g)) ≫
            (sheafPullbackSheafifyYonedaIso u J K V).hom) ≫ s) =
        lhsEquiv u J K U G
          (((sheafPullbackSheafifyYonedaIso u J K U).hom ≫
              (presheafToSheaf K (Type v)).map (yoneda.map (u.map g))) ≫ s) := by
    intro G s
    rw [Category.assoc, Category.assoc, lhsEquiv_naturality_U u J K g G,
      sheafPullbackSheafifyYonedaIso_hom_comp u J K V G s,
      sheafPullbackSheafifyYonedaIso_hom_comp u J K U G _,
      rhsEquiv_naturality_U u K g G s]
  have hαβ := key _ (𝟙 _)
  simp only [Category.comp_id] at hαβ
  exact (lhsEquiv u J K U _).injective hαβ

-- **Stacks 03FP, part (1).** Enlarging a site carries the sheaf represented by an object to the
-- sheaf represented by the same object, canonically and naturally.  For the inclusion of sites
-- that is the theorem above, representables being written as sheafified Yoneda presheaves.
add_to_stacks 03FP "part (1), canonical naturality" sheafPullback_sheafify_yoneda_natIso
