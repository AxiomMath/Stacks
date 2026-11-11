module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksFrontier.CategoryTheory.Sites.Point.StalkLeftAdjoint

/-! # Stalks at a functor to sets satisfying the covering conditions of Stacks 00Y8

Let `K` be a coverage on `C` (the coverings of a site) and `u : C ⥤ Type w` a functor such that,
for every covering `{U_i → U}`, (a) `∐ u(U_i) → u(U)` is surjective and (b) the maps
`u(U_i ×_U U_j) → u(U_i) ×_{u(U)} u(U_j)` are surjective (`StalkConditions`).

## Main results

* `PresheafPushforwardStalkAdjunction.isSheaf_presheafPushforward`: `u^p E` is a sheaf for
  every set `E` (Stacks 00Y8 (1)); `skyscraper` is the resulting functor `u^s`.
* `PresheafPushforwardStalkAdjunction.sheafStalk_adjoint_skyscraper`: the stalk functor
  `Sh(C) → Sets` is left adjoint to `u^s` (Stacks 00Y8 (2)).
* `PresheafPushforwardStalkAdjunction.isIso_presheafStalk_map_toSheafify`: the canonical map
  `F_p → (F^#)_p` is an isomorphism for every presheaf of sets `F` (Stacks 00Y8 (3)).

Tags covered: 00Y8.
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe v u w

namespace PresheafPushforwardStalkAdjunction

variable {C : Type u} [Category.{v} C] (K : Coverage C) (u : C ⥤ Type w)

/-- The conditions of Stacks 00Y8 on a functor `u : C ⥤ Type w` relative to the coverings `K`
of a site: for every covering `{U_i → U}`,
(a) the map `∐ u(U_i) → u(U)` is surjective, and
(b) the fibre products `U_i ×_U U_j` exist (a site axiom) and the maps
`u(U_i ×_U U_j) → u(U_i) ×_{u(U)} u(U_j)` are surjective. -/
structure StalkConditions : Prop where
  /-- (a): `∐ u(U_i) → u(U)` is surjective for every covering `{U_i → U}`. -/
  surjective_cover : ∀ ⦃X : C⦄, ∀ R ∈ K.coverings X, ∀ x : u.obj X,
    ∃ (Y : C) (f : Y ⟶ X) (_ : R f) (y : u.obj Y), u.map f y = x
  /-- The fibre product of two members of a covering exists. -/
  hasPullback : ∀ ⦃X : C⦄, ∀ R ∈ K.coverings X, ∀ ⦃Y₁ Y₂ : C⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄,
    R f₁ → R f₂ → Limits.HasPullback f₁ f₂
  /-- (b): `u(U_i ×_U U_j) → u(U_i) ×_{u(U)} u(U_j)` is surjective for every covering. -/
  surjective_pullback : ∀ ⦃X : C⦄ (R : Presieve X) (hR : R ∈ K.coverings X)
    ⦃Y₁ Y₂ : C⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := hasPullback R hR h₁ h₂
    Function.Surjective (fun z : u.obj (Limits.pullback f₁ f₂) =>
      (⟨(u.map (Limits.pullback.fst f₁ f₂) z, u.map (Limits.pullback.snd f₁ f₂) z), by
        rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
          Limits.pullback.condition]⟩ :
        {p : u.obj Y₁ × u.obj Y₂ // u.map f₁ p.1 = u.map f₂ p.2}))

variable {K u}

/-- **Stacks 00Y8 (1).** If `u : C ⥤ Type w` satisfies conditions (a) and (b) for every covering
of the site, then the presheaf `u^p E : U ↦ Map(u(U), E)` is a sheaf for every set `E`. -/
@[stacks 00Y8 "(1): `u^p E` is a sheaf for every set `E`"]
theorem isSheaf_presheafPushforward (h : StalkConditions K u) (E : Type w) :
    Presheaf.IsSheaf K.toGrothendieck ((presheafPushforward u).obj E) := by
  rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
  intro X R hR x hx
  -- The values of a compatible family agree on points with the same image in `u(X)`.
  have key : ∀ ⦃Y₁ Y₂ : C⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂)
      (y₁ : u.obj Y₁) (y₂ : u.obj Y₂), u.map f₁ y₁ = u.map f₂ y₂ →
      x f₁ h₁ y₁ = x f₂ h₂ y₂ := by
    intro Y₁ Y₂ f₁ f₂ h₁ h₂ y₁ y₂ hy
    have := h.hasPullback R hR h₁ h₂
    obtain ⟨z, hz⟩ := h.surjective_pullback R hR h₁ h₂ ⟨(y₁, y₂), hy⟩
    have hz' := congrArg Subtype.val hz
    simp only [Prod.mk.injEq] at hz'
    have h3 := hx (Limits.pullback.fst f₁ f₂) (Limits.pullback.snd f₁ f₂) h₁ h₂
      Limits.pullback.condition
    have h4 := congrArg (fun g : u.obj (Limits.pullback f₁ f₂) → E => g z) h3
    simp only [presheafPushforward_obj_map_apply, Quiver.Hom.unop_op] at h4
    rw [← hz'.1, ← hz'.2]
    exact h4
  choose Yc fc hfc yc hyc using fun s : u.obj X => h.surjective_cover R hR s
  refine ⟨fun s => x (fc s) (hfc s) (yc s), ?_, ?_⟩
  · intro Y f hf
    funext y
    rw [presheafPushforward_obj_map_apply, Quiver.Hom.unop_op]
    exact key _ _ _ _ (hyc _)
  · intro t ht
    funext s
    have h4 := congrArg (fun g : u.obj (Yc s) → E => g (yc s)) (ht (fc s) (hfc s))
    simp only [presheafPushforward_obj_map_apply, Quiver.Hom.unop_op, hyc] at h4
    exact h4

variable (K u) in
/-- The stalk functor `Sh(C) → Sets`, `F ↦ F_p`, of a functor `u : C ⥤ Type w`: the stalk
`presheafStalk u` of the underlying presheaf. -/
noncomputable abbrev sheafStalk [Limits.HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    Sheaf K.toGrothendieck (Type w) ⥤ Type w :=
  sheafToPresheaf K.toGrothendieck (Type w) ⋙ presheafStalk u

/-- The functor `u^s : Sets → Sh(C)`, `E ↦ u^p E`, for a functor `u` satisfying the conditions
of Stacks 00Y8 (well defined by `isSheaf_presheafPushforward`). -/
noncomputable def skyscraper (h : StalkConditions K u) : Type w ⥤ Sheaf K.toGrothendieck (Type w) :=
  ObjectProperty.lift (Presheaf.IsSheaf K.toGrothendieck) (presheafPushforward u)
    (isSheaf_presheafPushforward h)

/-- The underlying presheaf of `u^s E` is `u^p E`. -/
theorem skyscraper_obj_obj (h : StalkConditions K u) (E : Type w) :
    ((skyscraper h).obj E).obj = (presheafPushforward u).obj E :=
  rfl

/-- The adjunction between the stalk functor on sheaves and `u^s`: the restriction of the
adjunction `presheafStalk u ⊣ presheafPushforward u` of Stacks 00Y7 to sheaves. -/
noncomputable def sheafAdjunction [Limits.HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (h : StalkConditions K u) : sheafStalk K u ⊣ skyscraper h :=
  (adjunction u).restrictFullyFaithful (iC := sheafToPresheaf K.toGrothendieck (Type w))
    (iD := 𝟭 (Type w)) (fullyFaithfulSheafToPresheaf _ _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm)

/-- **Stacks 00Y8 (2).** If `u : C ⥤ Type w` satisfies conditions (a) and (b) for every covering
of the site, then the stalk functor `Sh(C) → Sets`, `F ↦ F_p`, is left adjoint to
`u^s : Sets → Sh(C)`. -/
@[stacks 00Y8 "(2): the stalk functor on sheaves is left adjoint to `u^s`"]
theorem sheafStalk_adjoint_skyscraper [Limits.HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (h : StalkConditions K u) : Nonempty (sheafStalk K u ⊣ skyscraper h) :=
  ⟨sheafAdjunction h⟩

/-- **Stacks 00Y8 (3).** If `u : C ⥤ Type w` satisfies conditions (a) and (b) for every covering
of the site, then for every presheaf of sets `F` the canonical map `F_p → (F^#)_p`, the stalk of
the sheafification map `F → F^#`, is an isomorphism. -/
@[stacks 00Y8 "(3): the canonical map `F_p → (F^#)_p` is an isomorphism"]
theorem isIso_presheafStalk_map_toSheafify [Limits.HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    [HasWeakSheafify K.toGrothendieck (Type w)] (h : StalkConditions K u)
    (F : Cᵒᵖ ⥤ Type w) :
    IsIso ((presheafStalk u).map (toSheafify K.toGrothendieck F)) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro E
  let J := K.toGrothendieck
  let adj := adjunction u
  let e₂ : (sheafify J F ⟶ (presheafPushforward u).obj E) ≃
      (F ⟶ (presheafPushforward u).obj E) :=
    { toFun := fun α => toSheafify J F ≫ α
      invFun := fun β => sheafifyLift J β (isSheaf_presheafPushforward h E)
      left_inv := fun α => by
        symm
        apply sheafifyLift_unique
        rfl
      right_inv := fun β => toSheafify_sheafifyLift J β (isSheaf_presheafPushforward h E) }
  let Φ := (adj.homEquiv (sheafify J F) E).trans (e₂.trans (adj.homEquiv F E).symm)
  have hΦ : ∀ g, Φ g = (presheafStalk u).map (toSheafify J F) ≫ g := fun g => by
    dsimp only [Φ, e₂, Equiv.trans_apply, Equiv.coe_fn_mk]
    rw [← adj.homEquiv_naturality_left, Equiv.symm_apply_apply]
  convert Φ.bijective using 1
  exact (funext hΦ).symm

end PresheafPushforwardStalkAdjunction
