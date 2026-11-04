module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The lower shriek along a localization, computed by coproducts

Let `(C, J)` be a site, let `U` be an object of `C` and let `G` be a presheaf of sets on the
localized site `C/U`. Stacks 03CD computes the lower-shriek extension of the sheafification of `G`:
`j_{U!}(G^#)` is the sheaf associated to the presheaf
`V ↦ ∐_{φ ∈ Hom_C(V, U)} G(V →φ U)`, with the obvious restriction maps.

`j_U` is Mathlib's `CategoryTheory.Over.forget U`, continuous for `J.over U` and `J`, and `j_{U!}`
is its `Functor.sheafPullback`, the chosen left adjoint of `j_U^{-1} = J.overPullback`. The source
states the conclusion as an equality of sheaves, identifying objects defined up to canonical
isomorphism; the faithful rendering is a canonical isomorphism in `Sh(C)`.

## Implementation

The source argument goes through the presheaf-level formula for `(j_U)_p` (Stacks 00VC) and
"sheafification of a presheaf pushforward is insensitive to sheafifying first" (Stacks 00WY). Here
the same result is obtained by corepresentability, which needs neither: for a sheaf `H` on `C`,
`j_{U!}(G^#)` and `(∐-presheaf)^#` both corepresent `H ↦ Hom_{PSh(C/U)}(G, j_U^{-1}H)`, the first
because `j_{U!} ⊣ j_U^{-1}` and sheafification is left adjoint to the inclusion, the second because
a map out of the coproduct presheaf is exactly a compatible family of maps `G(V →φ U) → H(V)`
(`homEquiv`). Since `coyoneda` is fully faithful, the resulting natural isomorphism of
corepresented functors comes from an isomorphism of the corepresenting objects.

## Main results

* `CategoryTheory.OverShriek.presheaf`: the presheaf `V ↦ ∐_{φ : V ⟶ U} G(V →φ U)` on `C`.
* `CategoryTheory.OverShriek.homEquiv`: a map `∐-presheaf ⟶ F` of presheaves on `C` is the same
  thing as a map `G ⟶ j_U^{-1}F` of presheaves on `C/U`.
* `CategoryTheory.OverShriek.sheafifyIso` and
  `CategoryTheory.OverShriek.overShriek_sheafify_iso`: Stacks 03CD.

Tags covered: 03CD.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {U : C} (G : (Over U)ᵒᵖ ⥤ Type v)

/-! ### Bookkeeping for sections of the coproduct presheaf

A section of the coproduct presheaf over `V` is a pair `(φ, s)` with `φ : V ⟶ U` and
`s ∈ G(V →φ U)`. Two such pairs built by restricting one section `s` along two morphisms of `C/U`
agree as soon as the two morphisms have the same underlying morphism of `C`; this is what makes the
restriction maps functorial. -/

/-- Contravariant functoriality of `G`, in applied form. -/
lemma map_op_comp {A B D : Over U} (a : A ⟶ B) (b : B ⟶ D) (s : G.obj (op D)) :
    G.map a.op (G.map b.op s) = G.map (a ≫ b).op s := by
  rw [op_comp, G.map_comp_apply]

/-- Two morphisms `Over.mk ψ ⟶ Over.mk φ` and `Over.mk ψ' ⟶ Over.mk φ` of `C/U` with the same
underlying morphism of `C` restrict a section `s` of `G` over `Over.mk φ` to the same pair. -/
lemma sigmaMk_eq {V W : C} {φ : W ⟶ U} (s : G.obj (op (Over.mk φ))) {ψ ψ' : V ⟶ U}
    (e : Over.mk ψ ⟶ Over.mk φ) (e' : Over.mk ψ' ⟶ Over.mk φ) (h : e.left = e'.left) :
    (⟨ψ, G.map e.op s⟩ : Σ χ : V ⟶ U, G.obj (op (Over.mk χ))) = ⟨ψ', G.map e'.op s⟩ := by
  have h1 := Over.w e
  have h2 := Over.w e'
  simp only [Over.mk_hom, Over.mk_left] at h1 h2
  have hψ : ψ = ψ' := by rw [← h1, ← h2, h]
  subst hψ
  rw [Over.OverMorphism.ext h]

/-- Restricting along a morphism of `C/U` whose underlying morphism of `C` is the identity does
nothing. -/
lemma sigmaMk_eq_self {V : C} {φ : V ⟶ U} (s : G.obj (op (Over.mk φ))) {ψ : V ⟶ U}
    (e : Over.mk ψ ⟶ Over.mk φ) (h : e.left = 𝟙 V) :
    (⟨ψ, G.map e.op s⟩ : Σ χ : V ⟶ U, G.obj (op (Over.mk χ))) = ⟨φ, s⟩ := by
  have := sigmaMk_eq G s e (𝟙 (Over.mk φ)) (by simpa using h)
  simpa using this

/-- Restricting along a morphism of `C/U` that factors as `e₂ ≫ e₁` is restricting along `e₁` and
then along `e₂`. -/
lemma sigmaMk_eq_comp {V W X : C} {φ : X ⟶ U} (s : G.obj (op (Over.mk φ)))
    {ψ ψ' : V ⟶ U} {χ : W ⟶ U}
    (e : Over.mk ψ ⟶ Over.mk φ) (e₁ : Over.mk χ ⟶ Over.mk φ) (e₂ : Over.mk ψ' ⟶ Over.mk χ)
    (h : e.left = e₂.left ≫ e₁.left) :
    (⟨ψ, G.map e.op s⟩ : Σ ξ : V ⟶ U, G.obj (op (Over.mk ξ)))
      = ⟨ψ', G.map e₂.op (G.map e₁.op s)⟩ := by
  rw [map_op_comp]
  exact sigmaMk_eq G s e (e₂ ≫ e₁) (by simpa using h)

/-! ### The coproduct presheaf -/

/-- The presheaf `V ↦ ∐_{φ ∈ Hom_C(V, U)} G(V →φ U)` on `C` attached to a presheaf `G` on `C/U`,
with the obvious restriction maps: `(φ, s)` restricts along `g : W ⟶ V` to `(g ≫ φ, s|_{W/U})`. -/
def presheaf : Cᵒᵖ ⥤ Type v where
  obj V := Σ φ : V.unop ⟶ U, G.obj (op (Over.mk φ))
  map {X Y} f := ↾fun p =>
    ⟨f.unop ≫ p.1, G.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ p.1) ⟶ Over.mk p.1).op p.2⟩
  map_id X := by
    ext p : 3
    obtain ⟨φ, s⟩ := p
    exact sigmaMk_eq_self G s _ (by simp)
  map_comp {X Y Z} f g := by
    ext p : 3
    obtain ⟨φ, s⟩ := p
    exact sigmaMk_eq_comp G s _ _ _ (by simp)

@[simp]
lemma presheaf_map_apply_fst {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : (presheaf G).obj X) :
    ((presheaf G).map f p).1 = f.unop ≫ p.1 :=
  rfl

/-! ### The universal property of the coproduct presheaf -/

/-- A map out of the coproduct presheaf restricts to a map `G ⟶ j_U^{-1}F` on `C/U`. -/
def toRestricted {F : Cᵒᵖ ⥤ Type v} (α : presheaf G ⟶ F) : G ⟶ (Over.forget U).op ⋙ F where
  app X := ↾fun s => α.app (op X.unop.left) ⟨X.unop.hom, s⟩
  naturality {X Y} h := by
    ext s
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, TypeCat.ofHom_apply, Functor.comp_map]
    have key : ((presheaf G).map ((Over.forget U).op.map h))
        (⟨X.unop.hom, s⟩ : Σ φ : X.unop.left ⟶ U, G.obj (op (Over.mk φ)))
          = ⟨Y.unop.hom, G.map h s⟩ :=
      sigmaMk_eq G s _ h.unop rfl
    exact (congrArg
        (fun t : (presheaf G).obj (op Y.unop.left) => α.app (op Y.unop.left) t) key).symm.trans
      (NatTrans.naturality_apply α ((Over.forget U).op.map h)
        (⟨X.unop.hom, s⟩ : Σ φ : X.unop.left ⟶ U, G.obj (op (Over.mk φ))))

/-- A map `G ⟶ j_U^{-1}F` on `C/U` extends to a map out of the coproduct presheaf. -/
def ofRestricted {F : Cᵒᵖ ⥤ Type v} (β : G ⟶ (Over.forget U).op ⋙ F) : presheaf G ⟶ F where
  app V := ↾fun p => β.app (op (Over.mk p.1)) p.2
  naturality {X Y} f := by
    ext p
    obtain ⟨φ, s⟩ := p
    exact NatTrans.naturality_apply β
      (Over.homMk f.unop rfl : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op s

/-- **The universal property of the coproduct presheaf.** For a presheaf `F` on `C`, maps
`∐-presheaf ⟶ F` are the same thing as maps `G ⟶ j_U^{-1}F` of presheaves on `C/U`: both are
families of maps `G(V →φ U) → F(V)` compatible with restriction. Equivalently, the coproduct
presheaf is the presheaf-level pushforward `(j_U)_p G`. -/
def homEquiv (F : Cᵒᵖ ⥤ Type v) : (presheaf G ⟶ F) ≃ (G ⟶ (Over.forget U).op ⋙ F) where
  toFun := toRestricted G
  invFun := ofRestricted G
  left_inv _ := rfl
  right_inv _ := rfl

/-- `homEquiv` is natural in `F`. -/
lemma homEquiv_naturality {F F' : Cᵒᵖ ⥤ Type v} (γ : F ⟶ F') (α : presheaf G ⟶ F) :
    homEquiv G F' (α ≫ γ) = homEquiv G F α ≫ Functor.whiskerLeft (Over.forget U).op γ :=
  rfl

/-! ### Functoriality in `G`, and the resulting adjunction -/

/-- The coproduct presheaf as a functor `PSh(C/U) ⥤ PSh(C)`: a map `G ⟶ G'` acts on `(φ, s)` by
`s ↦ η(s)`, leaving `φ` alone. -/
def presheafFunctor : ((Over U)ᵒᵖ ⥤ Type v) ⥤ (Cᵒᵖ ⥤ Type v) where
  obj G := presheaf G
  map {G G'} η :=
    { app := fun V => ↾fun p => ⟨p.1, η.app (op (Over.mk p.1)) p.2⟩
      naturality := fun {X Y} f => by
        ext p
        obtain ⟨φ, s⟩ := p
        exact congrArg (Sigma.mk (f.unop ≫ φ))
          (NatTrans.naturality_apply η
            (Over.homMk f.unop rfl : Over.mk (f.unop ≫ φ) ⟶ Over.mk φ).op s) }
  map_id _ := by ext V p; exact rfl
  map_comp _ _ := by ext V p; exact rfl

/-- Restriction of presheaves along `j_U`, i.e. `j_U^{-1}` at the presheaf level. -/
abbrev restrict : (Cᵒᵖ ⥤ Type v) ⥤ ((Over U)ᵒᵖ ⥤ Type v) :=
  (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type v)).obj (Over.forget U).op

/-- **The coproduct presheaf is the left adjoint of restriction along `j_U`**, i.e. it is the
presheaf-level pushforward `(j_U)_p`. This is `homEquiv` made into an adjunction. -/
def presheafAdjunction : presheafFunctor (U := U) ⊣ restrict (U := U) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := fun _ _ => rfl
      homEquiv_naturality_right := fun _ _ => rfl }

/-- The hom-set bijection of `presheafAdjunction` is the universal property `homEquiv` it was
built from. This is not a `simp` lemma: rewriting the bijection itself would hide the two
projections below, which are what a proof computing with `presheafAdjunction` wants. -/
lemma presheafAdjunction_homEquiv (F : Cᵒᵖ ⥤ Type v) :
    (presheafAdjunction (U := U)).homEquiv G F = homEquiv G F :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) G) F

/-- Under `presheafAdjunction`, a map `∐-presheaf ⟶ F` corresponds to its restriction
`toRestricted`. -/
@[simp]
lemma presheafAdjunction_homEquiv_apply {F : Cᵒᵖ ⥤ Type v} (α : presheaf G ⟶ F) :
    (presheafAdjunction (U := U)).homEquiv G F α = toRestricted G α :=
  DFunLike.congr_fun (presheafAdjunction_homEquiv G F) α

/-- Under `presheafAdjunction`, a map `G ⟶ j_U^{-1}F` on `C/U` corresponds to its extension
`ofRestricted`. -/
@[simp]
lemma presheafAdjunction_homEquiv_symm_apply {F : Cᵒᵖ ⥤ Type v}
    (β : G ⟶ (Over.forget U).op ⋙ F) :
    ((presheafAdjunction (U := U)).homEquiv G F).symm β = ofRestricted G β :=
  DFunLike.congr_fun (congrArg Equiv.symm (presheafAdjunction_homEquiv G F)) β

/-! ### Stacks 03CD -/

noncomputable section

variable (J : GrothendieckTopology C)
variable [HasWeakSheafify (J.over U) (Type v)] [HasWeakSheafify J (Type v)]
variable [((Over.forget U).sheafPushforwardContinuous (Type v) (J.over U) J).IsRightAdjoint]

/-- **Stacks 03CD**, natural in `G`.

Both `G ↦ j_{U!}(G^#)` and `G ↦ (∐_{φ : V ⟶ U} G(V →φ U))^#` are left adjoint to the same functor
`Sh(C) ⥤ PSh(C/U)`, namely `H ↦ j_U^{-1}H` viewed as a presheaf: the first because
`j_{U!} ⊣ j_U^{-1}` and `(-)^# ⊣ ι`, the second because the coproduct presheaf is left adjoint to
restriction along `j_U` (`presheafAdjunction`) and `(-)^# ⊣ ι`. That the two right adjoints agree
is Mathlib's `Functor.sheafPushforwardContinuousCompSheafToPresheafIso`, an identity. Uniqueness of
left adjoints therefore identifies the two. -/
@[sga "4 III 1.7" "Clause 2, special case"]
def sheafifyNatIso :
    presheafToSheaf (J.over U) (Type v) ⋙ (Over.forget U).sheafPullback (Type v) (J.over U) J ≅
      presheafFunctor (U := U) ⋙ presheafToSheaf J (Type v) :=
  Adjunction.leftAdjointUniq
    ((sheafificationAdjunction (J.over U) (Type v)).comp
      ((Over.forget U).sheafAdjunctionContinuous (Type v) (J.over U) J))
    (presheafAdjunction.comp (sheafificationAdjunction J (Type v)))

/-- **Stacks 03CD.** The lower shriek `j_{U!}(G^#)` of the sheafification of a presheaf `G` on the
localized site `C/U` is the sheaf associated to the presheaf `V ↦ ∐_{φ : V ⟶ U} G(V →φ U)`. -/
def sheafifyIso :
    ((Over.forget U).sheafPullback (Type v) (J.over U) J).obj
        ((presheafToSheaf (J.over U) (Type v)).obj G) ≅
      (presheafToSheaf J (Type v)).obj (presheaf G) :=
  (sheafifyNatIso J).app G

/-- **Stacks 03CD**, packaged as the existence of the isomorphism
`j_{U!}(G^#) ≅ (∐_{φ : V ⟶ U} G(V →φ U))^#`. -/
@[stacks 03CD]
theorem overShriek_sheafify_iso :
    Nonempty
      (((Over.forget U).sheafPullback (Type v) (J.over U) J).obj
          ((presheafToSheaf (J.over U) (Type v)).obj G) ≅
        (presheafToSheaf J (Type v)).obj (presheaf G)) :=
  ⟨sheafifyIso G J⟩

end

end CategoryTheory.OverShriek
