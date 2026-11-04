module

public import StacksFrontier.CategoryTheory.Monoidal.Cartesian.MulRight
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf

/-!
# Morphisms into the internal Hom of abelian presheaves are pairings

Let `C` be a category, `T` a presheaf of sets and `G`, `F` abelian presheaves on `C`. The
internal Hom `ℋom(G, F)` (`internalHomPresheaf`) has as sections over `X` the morphisms
`G|_X ⟶ F|_X` of abelian presheaves on the slice `C/X`. A morphism of presheaves of sets
`T ⟶ ℋom(G, F)` is the same thing as a morphism `β : T × G ⟶ F` of presheaves of sets which is
additive in its second variable section by section: `φ` gives `β (t, g) = φ(t)_X (g)` (evaluation
at the identity of `X`), and `β` gives `φ(t)_{Y ⟶ X} (g) = β (t|_Y, g)`.

## Main definitions

* `Stacks.ConstantSheaf.IsAddRightPairing` — a pairing `T × G ⟶ F` of functors to sets, additive
  in its second variable; it is `CategoryTheory.IsMulRight` for the internal group structures of
  `CategoryTheory.Sites.AbelianSheaf.presheafGrpObj`
  (`Stacks.ConstantSheaf.isMulRight_iff_isAddRightPairing`).
* `Stacks.ConstantSheaf.internalHomPresheafPairingEquiv` — the bijection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory

universe v u

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C]

section Pairing

universe w

variable {K : Type*} [Category* K] (T : K ⥤ Type w) (G F : K ⥤ AddCommGrpCat.{w})

/-- A morphism `T × G ⟶ F` of functors to sets which is additive in its second variable. -/
def IsAddRightPairing (β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat) : Prop :=
  ∀ (X : K) (t : T.obj X) (a a' : G.obj X),
    β.app X (t, a + a') = β.app X (t, a) + β.app X (t, a')

/-- **Additivity in the second variable is multiplicativity for the internal group structures of
abelian presheaves.** -/
theorem isMulRight_iff_isAddRightPairing
    (β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat) :
    letI := Sites.AbelianSheaf.presheafGrpObj G
    letI := Sites.AbelianSheaf.presheafGrpObj F
    IsMulRight β ↔ IsAddRightPairing T G F β := by
  let := Sites.AbelianSheaf.presheafGrpObj G
  let := Sites.AbelianSheaf.presheafGrpObj F
  exact isMulRight_functorToTypes_iff β

/-- Precomposing a pairing with a morphism in its first variable keeps it additive in the second
variable. -/
lemma IsAddRightPairing.whiskerRight_comp {T' : K ⥤ Type w} (f : T' ⟶ T)
    {β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat}
    (hβ : IsAddRightPairing T G F β) :
    IsAddRightPairing T' G F (f ▷ (G ⋙ forget AddCommGrpCat) ≫ β) :=
  fun X t a a' ↦ hβ X (f.app X t) a a'

end Pairing

section Presheaf

variable {T : Cᵒᵖ ⥤ Type (max u v)} {G F : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}

/-- The local morphism `G|_X ⟶ F|_X` attached to a section `t` over `X` by a pairing additive in
its second variable: on `Y ⟶ X` it is `g ↦ β (t|_Y, g)`. -/
def pairingLocalHom (β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat)
    (hβ : IsAddRightPairing T G F β) (X : Cᵒᵖ) (t : T.obj X) :
    (Over.forget X.unop).op ⋙ G ⟶ (Over.forget X.unop).op ⋙ F where
  app Y := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun g : G.obj (op Y.unop.left) ↦ β.app (op Y.unop.left) (T.map Y.unop.hom.op t, g))
    (fun g g' ↦ hβ _ _ g g'))
  naturality Y Y' f := by
    ext g
    have h := congrArg (fun φ ↦ φ (T.map Y.unop.hom.op t, g)) (β.naturality f.unop.left.op)
    have hw : T.map f.unop.left.op (T.map Y.unop.hom.op t) = T.map Y'.unop.hom.op t := by
      rw [← Functor.map_comp_apply, ← op_comp, Over.w f.unop]
    change β.app (op Y'.unop.left) (T.map Y'.unop.hom.op t, G.map f.unop.left.op g) =
      F.map f.unop.left.op (β.app (op Y.unop.left) (T.map Y.unop.hom.op t, g))
    rw [← hw]
    exact h

/-- The component of `pairingLocalHom β hβ X t` at `Y ⟶ X` sends `g` to `β (t|_Y, g)`. -/
lemma pairingLocalHom_app_apply (β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat)
    (hβ : IsAddRightPairing T G F β) (X : Cᵒᵖ) (t : T.obj X) (Y : (Over X.unop)ᵒᵖ)
    (g : G.obj (op Y.unop.left)) :
    (pairingLocalHom β hβ X t).app Y g = β.app (op Y.unop.left) (T.map Y.unop.hom.op t, g) :=
  rfl

/-- The morphism `T ⟶ ℋom(G, F)` of a pairing additive in its second variable. -/
def pairingTransposeHom (β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat)
    (hβ : IsAddRightPairing T G F β) : T ⟶ internalHomPresheaf G F ⋙ forget AddCommGrpCat where
  app X := TypeCat.ofHom fun t ↦ pairingLocalHom β hβ X t
  naturality X X' h := by
    ext t
    refine NatTrans.ext (funext fun Y ↦ ?_)
    ext g
    change β.app (op Y.unop.left) (T.map Y.unop.hom.op (T.map h t), g) =
      β.app (op Y.unop.left) (T.map (Y.unop.hom ≫ h.unop).op t, g)
    rw [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply]

/-- The pairing `T × G ⟶ F` of a morphism `T ⟶ ℋom(G, F)`: evaluation at the identity. -/
def pairingOfHom (φ : T ⟶ internalHomPresheaf G F ⋙ forget AddCommGrpCat) :
    T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat where
  app X := TypeCat.ofHom fun p ↦
    ((φ.app X p.1 : (Over.forget X.unop).op ⋙ G ⟶ (Over.forget X.unop).op ⋙ F).app
      (op (Over.mk (𝟙 X.unop)))) p.2
  naturality X X' h := by
    ext ⟨t, g⟩
    have hφ := congrArg (fun a : (Over.forget X'.unop).op ⋙ G ⟶ (Over.forget X'.unop).op ⋙ F ↦
      a.app (op (Over.mk (𝟙 X'.unop))) (G.map h g)) (NatTrans.naturality_apply φ h t)
    have hn := ConcreteCategory.congr_hom
      ((φ.app X t : (Over.forget X.unop).op ⋙ G ⟶ (Over.forget X.unop).op ⋙ F).naturality
        (Over.homMk (U := (Over.map h.unop).obj (Over.mk (𝟙 X'.unop))) (V := Over.mk (𝟙 X.unop))
          h.unop (by simp)).op) g
    exact hφ.trans hn

/-- The pairing `pairingOfHom φ` sends `(t, g)` to the component of `φ(t)` at the identity of
`X`, applied to `g`. -/
lemma pairingOfHom_app_apply (φ : T ⟶ internalHomPresheaf G F ⋙ forget AddCommGrpCat)
    (X : Cᵒᵖ) (t : T.obj X) (g : G.obj X) :
    (pairingOfHom φ).app X (t, g) =
      ((φ.app X t : (Over.forget X.unop).op ⋙ G ⟶ (Over.forget X.unop).op ⋙ F).app
        (op (Over.mk (𝟙 X.unop)))) g :=
  rfl

/-- The pairing `pairingOfHom φ` is additive in its second variable. -/
lemma isAddRightPairing_pairingOfHom (φ : T ⟶ internalHomPresheaf G F ⋙ forget AddCommGrpCat) :
    IsAddRightPairing T G F (pairingOfHom φ) := fun X t a a' ↦
  map_add (ConcreteCategory.hom
    ((φ.app X t : (Over.forget X.unop).op ⋙ G ⟶ (Over.forget X.unop).op ⋙ F).app
      (op (Over.mk (𝟙 X.unop))))) a a'

variable (T G F) in
/-- **Morphisms into the internal Hom of abelian presheaves are the pairings additive in the
second variable.** -/
def internalHomPresheafPairingEquiv :
    (T ⟶ internalHomPresheaf G F ⋙ forget AddCommGrpCat) ≃
      {β : T ⊗ (G ⋙ forget AddCommGrpCat) ⟶ F ⋙ forget AddCommGrpCat //
        IsAddRightPairing T G F β} where
  toFun φ := ⟨pairingOfHom φ, isAddRightPairing_pairingOfHom φ⟩
  invFun β := pairingTransposeHom β.1 β.2
  left_inv φ := by
    ext X t
    refine NatTrans.ext (funext fun Y ↦ ?_)
    ext g
    change ((φ.app (op Y.unop.left) (T.map Y.unop.hom.op t) :
        (Over.forget Y.unop.left).op ⋙ G ⟶ _).app (op (Over.mk (𝟙 Y.unop.left)))) g =
      ((φ.app X t : (Over.forget X.unop).op ⋙ G ⟶ _).app Y) g
    rw [NatTrans.naturality_apply φ Y.unop.hom.op t]
    change ((φ.app X t : (Over.forget X.unop).op ⋙ G ⟶ _).app
        (op ((Over.map Y.unop.hom).obj (Over.mk (𝟙 Y.unop.left))))) g = _
    have hn := ConcreteCategory.congr_hom
      ((φ.app X t : (Over.forget X.unop).op ⋙ G ⟶ (Over.forget X.unop).op ⋙ F).naturality
        (Over.homMk (U := (Over.map Y.unop.hom).obj (Over.mk (𝟙 Y.unop.left))) (V := Y.unop)
          (𝟙 Y.unop.left) (by simp)).op) g
    simpa using hn
  right_inv β := by
    refine Subtype.ext ?_
    ext X ⟨t, g⟩
    change β.1.app (op X.unop) (T.map (𝟙 X.unop).op t, g) = β.1.app X (t, g)
    rw [op_id, Functor.map_id_apply]

/-- The bijection `internalHomPresheafPairingEquiv` is natural in the presheaf of sets. -/
lemma pairingOfHom_comp {T' : Cᵒᵖ ⥤ Type (max u v)} (f : T' ⟶ T)
    (φ : T ⟶ internalHomPresheaf G F ⋙ forget AddCommGrpCat) :
    pairingOfHom (f ≫ φ) = f ▷ (G ⋙ forget AddCommGrpCat) ≫ pairingOfHom φ :=
  rfl

end Presheaf

end Stacks.ConstantSheaf

end
