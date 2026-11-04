module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk functor of a functor to sets is left adjoint to pushforward

Stacks tag 00Y7. Let `u : C ⥤ Type w` be a covariant functor. Its pushforward
`u^p = presheafPushforward u` sends a set `E` to the presheaf `V ↦ (u(V) → E)`, and its
stalk functor `presheafStalk u` sends a presheaf `F : Cᵒᵖ ⥤ Type w` to the colimit
`colim_{(V, x) ∈ u.Elementsᵒᵖ} F(V)` over the opposite of the category of elements of `u`
(tag 04EH). These two are adjoint: maps of sets out of the stalk of `F` correspond
naturally to maps of presheaves `F ⟶ u^p E`.
-/

@[expose] public section


open CategoryTheory Limits Opposite

universe v u w a b

namespace CategoryTheory

/-- The colimit of the sections of a presheaf over the category of elements of a covariant
functor to sets.  This is the shape in which a point of a site computes its stalks. -/
noncomputable abbrev elementColimit {C : Type u} [Category.{v} C] (H : C ⥤ Type w)
    (A : Type a) [Category.{b} A] [HasColimitsOfShape H.Elementsᵒᵖ A] : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryOfElements.π H).op ⋙ Limits.colim

end CategoryTheory

namespace PresheafPushforwardStalkAdjunction

variable {C : Type u} [Category.{v} C]

/-- The pushforward functor `u^p : Type w ⥤ (Cᵒᵖ ⥤ Type w)` associated with a
functor `u : C ⥤ Type w`.  It sends a set `E` to the presheaf
`V ↦ (u.obj V → E)`. -/
@[implicit_reducible]
def presheafPushforward (u : C ⥤ Type w) :
    Type w ⥤ (Cᵒᵖ ⥤ Type w) where
  obj E :=
    { obj := fun V => u.obj V.unop → E
      map := fun {V W} f => ↾fun g => g ∘ u.map f.unop
      map_id := fun X => by ext g x; simp
      map_comp := fun f h => by ext g x; simp }
  map {E E'} h := { app := fun _ => ↾fun g => h ∘ g }

/-- The restriction maps of `u^p E` are precomposition with `u`. -/
lemma presheafPushforward_obj_map_apply (u : C ⥤ Type w) (E : Type w) {V W : Cᵒᵖ} (f : V ⟶ W)
    (g : u.obj V.unop → E) (s : u.obj W.unop) :
    ((presheafPushforward u).obj E).map f g s = g (u.map f.unop s) :=
  rfl

/-- The action of `u^p` on a map of sets is postcomposition. -/
lemma presheafPushforward_map_app_apply (u : C ⥤ Type w) {E E' : Type w} (h : E ⟶ E') (V : Cᵒᵖ)
    (g : u.obj V.unop → E) (s : u.obj V.unop) :
    ((presheafPushforward u).map h).app V g s = h (g s) :=
  rfl

/-- The stalk functor (Stacks 04EH) for an arbitrary functor `u : C ⥤ Type w`.
It sends a presheaf `F : Cᵒᵖ ⥤ Type w` to the colimit of `F` over the
opposite of the category of elements of `u`. -/
@[implicit_reducible, ega "0 3.1.6" "partial"]
noncomputable def presheafStalk (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    (Cᵒᵖ ⥤ Type w) ⥤ Type w :=
  elementColimit u (Type w)

/-- The stalk functor acts on a map of presheaves by the induced map of colimits. -/
lemma presheafStalk_map (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    {F G : Cᵒᵖ ⥤ Type w} (φ : F ⟶ G) :
    (presheafStalk u).map φ = colimMap (Functor.whiskerLeft (CategoryOfElements.π u).op φ) :=
  rfl

/-- The class `[(U, x, s)]` of a triple in the stalk `F_p`, where `x ∈ u(U)` and
`s ∈ F(U)`. -/
noncomputable def stalkMk (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] (F : Cᵒᵖ ⥤ Type w)
    (U : C) (x : u.obj U) (s : F.obj (op U)) : (presheafStalk u).obj F :=
  colimit.ι ((CategoryOfElements.π u).op ⋙ F) (op (u.elementsMk U x)) s

/-- The cocone over `(π u).op ⋙ F` with apex `E`, used to define the forward
direction of the hom-equivalence. -/
noncomputable def toFunCocone (u : C ⥤ Type w)
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (α : F ⟶ (presheafPushforward u).obj E) :
    Cocone ((CategoryOfElements.π u).op ⋙ F) where
  pt := E
  ι :=
    { app := fun X => ↾fun x => α.app (op X.unop.1) x X.unop.2
      naturality := by
        intro X Y f
        ext x
        -- After `ext`, the goal expresses pointwise compatibility:
        -- α.app (op Y.unop.1) (F.map f.unop.1.op x) Y.unop.2 =
        --   α.app (op X.unop.1) x X.unop.2.
        have hnat : α.app (op Y.unop.1) (F.map f.unop.1.op x) =
                    ((presheafPushforward u).obj E).map f.unop.1.op
                      (α.app (op X.unop.1) x) :=
          ConcreteCategory.congr_hom (α.naturality f.unop.1.op) x
        have hY : α.app (op Y.unop.1) (F.map f.unop.1.op x) Y.unop.2 =
                  α.app (op X.unop.1) x (u.map f.unop.1 Y.unop.2) :=
          by rw [hnat, presheafPushforward_obj_map_apply, Quiver.Hom.unop_op]
        have helem : u.map f.unop.1 Y.unop.2 = X.unop.2 := f.unop.2
        dsimp only [Functor.const_obj_obj, Functor.comp_obj, Functor.op_obj,
          CategoryOfElements.π_obj, Functor.comp_map, Functor.op_map, CategoryOfElements.π_map,
          TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
          Functor.const_obj_map, types_id_apply]
        rw [hY, helem] }

/-- The forward map of the hom-equivalence underlying the adjunction.
Sends `α : F ⟶ presheafPushforward u E` to the morphism out of the colimit
`presheafStalk u F ⟶ E` given by `(V, s) ↦ x ↦ α.app (op V) x s`. -/
noncomputable def toFun
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (α : F ⟶ (presheafPushforward u).obj E) :
    (presheafStalk u).obj F ⟶ E :=
  colimit.desc _ (toFunCocone u F E α)

/-- The value of `toFun u F E α` on a colimit generator: the class of `x ∈ F(V)` at the
neighbourhood `X = (V, s)` is sent to `α.app (op V) x s`.  This is `colimit.ι_desc` for
`toFunCocone`, and it is the only computation the inverse laws `leftInv`, `rightInv` and the
naturality lemmas need. -/
lemma toFun_ι_apply
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (α : F ⟶ (presheafPushforward u).obj E)
    (X : u.Elementsᵒᵖ) (x : F.obj (op X.unop.1)) :
    toFun u F E α (colimit.ι ((CategoryOfElements.π u).op ⋙ F) X x) =
      α.app (op X.unop.1) x X.unop.2 :=
  ConcreteCategory.congr_hom (colimit.ι_desc (toFunCocone u F E α) X) x

/-- The inverse map of the hom-equivalence underlying the adjunction.
Sends `φ : presheafStalk u F ⟶ E` to the natural transformation
`F ⟶ presheafPushforward u E` with `α_V(x)(s) = φ(ι_{(V,s)}(x))`. -/
noncomputable def invFun
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (φ : (presheafStalk u).obj F ⟶ E) :
    F ⟶ (presheafPushforward u).obj E where
  app V := ↾fun x s =>
    φ (colimit.ι ((CategoryOfElements.π u).op ⋙ F) (op (u.elementsMk V.unop s)) x)
  naturality := by
    intro V W f
    ext x
    funext s
    -- After `ext` / `funext`, the goal is (pointwise) an equation between
    -- `φ (ι _ (op ⟨W.unop, s⟩) (F.map f x))` and
    -- `φ (ι _ (op ⟨V.unop, u.map f.unop s⟩) x)`.
    -- Use the morphism (f.unop, rfl) : ⟨W.unop, s⟩ ⟶ ⟨V.unop, u.map f.unop s⟩
    -- (note: in u.Elements, ⟨V, x⟩ ⟶ ⟨W, y⟩ requires u.map _ x = y).
    let A : u.Elements := u.elementsMk W.unop s
    let B : u.Elements := u.elementsMk V.unop (u.map f.unop s)
    let g : A ⟶ B := ⟨f.unop, rfl⟩
    let h : op B ⟶ op A := g.op
    -- `((π u).op ⋙ F).map h` is `F.map f.unop.op`, which is `F.map f`.
    have hmap : ((CategoryOfElements.π u).op ⋙ F).map h = F.map f := rfl
    dsimp only [Functor.comp_obj, Functor.op_obj, TypeCat.Fun.toFun_apply, types_comp_apply,
      TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, presheafPushforward_obj_map_apply]
    rw [← hmap, colimit.w_apply]

/-- The value of `invFun u F E φ` at `x ∈ F(V)` and `s ∈ u(V)`. -/
lemma invFun_app_apply
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (φ : (presheafStalk u).obj F ⟶ E) (V : Cᵒᵖ) (x : F.obj V) (s : u.obj V.unop) :
    (invFun u F E φ).app V x s =
      φ (colimit.ι ((CategoryOfElements.π u).op ⋙ F) (op (u.elementsMk V.unop s)) x) :=
  rfl

/-- Composition `invFun ∘ toFun = id`. -/
lemma leftInv
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (α : F ⟶ (presheafPushforward u).obj E) :
    invFun u F E (toFun u F E α) = α := by
  ext V x
  funext s
  -- Goal: φ (ι (op ⟨V.unop, s⟩) x) = α.app V x s, where φ = toFun u F E α.
  dsimp only [TypeCat.Fun.toFun_apply]
  rw [invFun_app_apply, toFun_ι_apply]

/-- Two maps out of a stalk agree when they agree on every class `[(X, x)]`. -/
private theorem stalk_hom_ext {u : C ⥤ Type w} [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    {F : Cᵒᵖ ⥤ Type w} {E : Type w} {f g : (presheafStalk u).obj F ⟶ E}
    (h : ∀ (X : u.Elementsᵒᵖ) (x : F.obj (op X.unop.1)),
      f (colimit.ι ((CategoryOfElements.π u).op ⋙ F) X x) =
        g (colimit.ι ((CategoryOfElements.π u).op ⋙ F) X x)) :
    f = g :=
  colimit.hom_ext fun X => by ext x; exact h X x

/-- Composition `toFun ∘ invFun = id`. -/
lemma rightInv
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w)
    (φ : (presheafStalk u).obj F ⟶ E) :
    toFun u F E (invFun u F E φ) = φ := by
  refine stalk_hom_ext fun X x => ?_
  rw [toFun_ι_apply, invFun_app_apply]
  rfl

/-- The hom-equivalence underlying the adjunction. -/
noncomputable def homEquiv
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w) :
    ((presheafStalk u).obj F ⟶ E) ≃ (F ⟶ (presheafPushforward u).obj E) where
  toFun := invFun u F E
  invFun := toFun u F E
  left_inv φ := rightInv u F E φ
  right_inv α := leftInv u F E α

/-- The forward map of `homEquiv` is `invFun`. -/
lemma homEquiv_apply
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w) (φ : (presheafStalk u).obj F ⟶ E) :
    homEquiv u F E φ = invFun u F E φ :=
  rfl

/-- The inverse map of `homEquiv` is `toFun`. -/
lemma homEquiv_symm_apply
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    (F : Cᵒᵖ ⥤ Type w) (E : Type w) (α : F ⟶ (presheafPushforward u).obj E) :
    (homEquiv u F E).symm α = toFun u F E α :=
  rfl

/-- The stalk functor sends the class of `x` at `X` to the class of `β x`. -/
lemma presheafStalk_map_ι_apply
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    {F F' : Cᵒᵖ ⥤ Type w} (β : F' ⟶ F) (X : u.Elementsᵒᵖ) (x : F'.obj (op X.unop.1)) :
    (presheafStalk u).map β (colimit.ι ((CategoryOfElements.π u).op ⋙ F') X x) =
      colimit.ι ((CategoryOfElements.π u).op ⋙ F) X (β.app (op X.unop.1) x) :=
  colimit.ι_map_apply (Functor.whiskerLeft (CategoryOfElements.π u).op β) X x

/-- Naturality of the hom-equivalence in the left argument. -/
@[ega "0 3.5.4" "special case"]
lemma homEquiv_naturality_left_symm
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    {F F' : Cᵒᵖ ⥤ Type w} (β : F' ⟶ F) {E : Type w}
    (α : F ⟶ (presheafPushforward u).obj E) :
    (homEquiv u F' E).symm (β ≫ α) =
      (presheafStalk u).map β ≫ (homEquiv u F E).symm α := by
  rw [homEquiv_symm_apply, homEquiv_symm_apply]
  refine stalk_hom_ext fun X x => ?_
  -- Both sides send the class of `x` at `X` to `α.app (op X.unop.1) (β.app _ x) X.unop.2`.
  rw [types_comp_apply, toFun_ι_apply, presheafStalk_map_ι_apply, toFun_ι_apply, NatTrans.comp_app,
    types_comp_apply]

/-- Naturality of the hom-equivalence in the right argument. -/
lemma homEquiv_naturality_right
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)]
    {F : Cᵒᵖ ⥤ Type w} {E E' : Type w} (φ : (presheafStalk u).obj F ⟶ E)
    (h : E ⟶ E') :
    homEquiv u F E' (φ ≫ h) =
      homEquiv u F E φ ≫ (presheafPushforward u).map h := by
  rw [homEquiv_apply, homEquiv_apply]
  ext V x
  funext s
  -- Both sides are `h (φ (ι _ (op ⟨V.unop, s⟩) x))`.
  dsimp only [TypeCat.Fun.toFun_apply]
  rw [NatTrans.comp_app, types_comp_apply, presheafPushforward_map_app_apply, invFun_app_apply,
    invFun_app_apply, types_comp_apply]

/-- The stalk functor at `u` is left adjoint to the pushforward `u^p`, by the
hom-equivalence `homEquiv`. -/
noncomputable def adjunction (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    presheafStalk u ⊣ presheafPushforward u :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv u
      homEquiv_naturality_left_symm := fun β α =>
        homEquiv_naturality_left_symm u β α
      homEquiv_naturality_right := fun φ h =>
        homEquiv_naturality_right u φ h }

/-- **Stacks 00Y7.** For any functor `u : C ⥤ Type w` such that the
appropriate colimits exist, the pushforward functor `presheafPushforward u`
is a right adjoint to the stalk functor `presheafStalk u`. -/
@[stacks 00Y7]
theorem presheafStalk_adjoint_presheafPushforward
    (u : C ⥤ Type w)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type w)] :
    Nonempty (presheafStalk u ⊣ presheafPushforward u) :=
  ⟨adjunction u⟩

/-! ### The stalk of a representable presheaf -/

/-- The canonical map `θ^u_U : u(U) → (h_U)_p`, sending `x ∈ u(U)` to the class
`[(U, x, 𝟙 U)]` of the identity in the stalk of the representable `h_U`. -/
noncomputable def theta (u : C ⥤ Type v)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type v)] (U : C) (x : u.obj U) :
    (presheafStalk u).obj (yoneda.obj U) :=
  stalkMk u (yoneda.obj U) U x (𝟙 U)

/-- The evaluation cocone on the stalk diagram of the representable `h_U`, with apex
`u(U)`: a representative `(V, y, f : V ⟶ U)` is sent to `u(f)(y) ∈ u(U)`.  Its
`colimit.desc` is the inverse `thetaInv` of `θ^u_U`. -/
@[implicit_reducible]
noncomputable def thetaInvCocone (u : C ⥤ Type v) (U : C) :
    Cocone ((CategoryOfElements.π u).op ⋙ yoneda.obj U) where
  pt := u.obj U
  ι :=
    { app := fun j => ↾(fun (f : j.unop.fst ⟶ U) => u.map f (j.unop.snd))
      naturality := by
        intro j j' g
        ext f
        dsimp only [Functor.comp_obj, Functor.op_obj, CategoryOfElements.π_obj, yoneda_obj_obj,
          Functor.const_obj_obj, Functor.comp_map, Functor.op_map, CategoryOfElements.π_map,
          yoneda_obj_map, Quiver.Hom.unop_op, TypeCat.Fun.toFun_apply, types_comp_apply,
          TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Functor.const_obj_map, types_id_apply]
        rw [Functor.map_comp_apply, CategoryOfElements.map_snd] }

/-- `thetaInvCocone` sends the representative `(V, y, f)` to `u(f)(y)`. -/
lemma thetaInvCocone_ι_app_apply (u : C ⥤ Type v) (U : C) (j : u.Elementsᵒᵖ)
    (f : j.unop.fst ⟶ U) : (thetaInvCocone u U).ι.app j f = u.map f j.unop.snd :=
  rfl

/-- The inverse of `θ^u_U`: it sends the class `[(V, y, f)]` of `(h_U)_p` to
`u(f)(y) ∈ u(U)`. -/
noncomputable def thetaInv (u : C ⥤ Type v)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type v)] (U : C) :
    (presheafStalk u).obj (yoneda.obj U) ⟶ u.obj U :=
  colimit.desc _ (thetaInvCocone u U)

/-- `thetaInv` is a left inverse of `θ`: `θ x = [(U, x, 𝟙 U)]` and `thetaInv` evaluates a
representative `(U, x, f)` to `u(f)(x)`, so the composite is `u(𝟙 U)(x) = x`. -/
theorem thetaInv_theta (u : C ⥤ Type v)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type v)] (U : C) (x : u.obj U) :
    thetaInv u U (theta u U x) = x := by
  unfold thetaInv theta stalkMk
  rw [colimit.ι_desc_apply, thetaInvCocone_ι_app_apply]
  simp

/-- `thetaInv` is a right inverse of `θ`.  Every element of the colimit is a class
`[(V, y, f)]`, and `θ ∘ thetaInv` sends it to `[(U, u(f)(y), 𝟙 U)]`, which is the same class
by the colimit relation for the neighbourhood morphism `⟨f, rfl⟩`. -/
theorem theta_thetaInv (u : C ⥤ Type v)
    [HasColimitsOfShape u.Elementsᵒᵖ (Type v)] (U : C)
    (z : (presheafStalk u).obj (yoneda.obj U)) :
    theta u U (thetaInv u U z) = z := by
  obtain ⟨⟨j⟩, f, rfl⟩ :=
    Types.jointly_surjective' (F := (CategoryOfElements.π u).op ⋙ yoneda.obj U) z
  unfold thetaInv theta stalkMk
  rw [colimit.ι_desc_apply, thetaInvCocone_ι_app_apply,
    ← colimit.w_apply _ (CategoryOfElements.homMk j (u.elementsMk U (u.map f j.snd)) f rfl).op]
  simp

end PresheafPushforwardStalkAdjunction

