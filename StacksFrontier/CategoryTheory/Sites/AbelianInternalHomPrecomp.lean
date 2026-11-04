module

public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact

/-!
# The abelian internal Hom and precomposition with a functor of sites

Let `Φ : D ⥤ C` be a functor. For presheaves of abelian groups `F, G` on `C`, a section of
`ℋom(F, G)` over `Φ V` is a natural transformation `F|_{Φ V} ⟶ G|_{Φ V}` on `Over (Φ V)`;
whiskering it along `Over.post Φ : Over V ⥤ Over (Φ V)` gives a section of
`ℋom(F ∘ Φ, G ∘ Φ)` over `V`. When every `Over.post Φ` is an equivalence (for instance for
composition with an étale morphism on small étale sites) these maps are bijective, so
precomposition with `Φ` commutes with the internal Hom.

## Main definitions

* `Stacks.AbelianInternalHom.internalHomPresheafPrecomp`: the comparison morphism.
* `Stacks.AbelianInternalHom.internalHomPresheafPrecompIso`: it is an isomorphism when every
  `Over.post Φ` is an equivalence.
* `Stacks.AbelianInternalHom.internalHomSheafPushforwardIso`: the same for sheaves, along a
  continuous functor.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace Stacks.AbelianInternalHom

variable {C D : Type u} [Category.{v} C] [Category.{v} D] (Φ : D ⥤ C)

/-- The component at `V` of the comparison `ℋom(F, G) ∘ Φ ⟶ ℋom(F ∘ Φ, G ∘ Φ)`: whiskering
along `Over.post Φ : Over V ⥤ Over (Φ V)`. -/
def internalHomPresheafPrecompApp (F G : Cᵒᵖ ⥤ Ab.{max u v}) (V : Dᵒᵖ) :
    (Φ.op ⋙ internalHomPresheaf F G).obj V ⟶
      (internalHomPresheaf (Φ.op ⋙ F) (Φ.op ⋙ G)).obj V :=
  AddCommGrpCat.ofHom
    { toFun := fun a => Functor.whiskerLeft (Over.post (X := V.unop) Φ).op a
      map_zero' := by ext; rfl
      map_add' := fun _ _ => by ext; rfl }

/-- The component of the comparison at `V` sends a natural transformation `a` to its whiskering
along `Over.post Φ`. -/
lemma internalHomPresheafPrecompApp_apply (F G : Cᵒᵖ ⥤ Ab.{max u v}) (V : Dᵒᵖ)
    (a : (Over.forget (Φ.obj V.unop)).op ⋙ F ⟶ (Over.forget (Φ.obj V.unop)).op ⋙ G) :
    (internalHomPresheafPrecompApp Φ F G V).hom a =
      Functor.whiskerLeft (Over.post (X := V.unop) Φ).op a := rfl

/-- Components of a natural transformation of functors out of `(Over X)ᵒᵖ` through
`Over.forget` agree at equal objects. -/
private lemma app_heq_of_eq {X : C} {F G : Cᵒᵖ ⥤ Ab.{max u v}}
    (a : (Over.forget X).op ⋙ F ⟶ (Over.forget X).op ⋙ G) {O₁ O₂ : Over X} (h : O₁ = O₂) :
    HEq (a.app (op O₁)) (a.app (op O₂)) := by
  subst h; rfl

/-- The comparison `ℋom(F, G) ∘ Φ ⟶ ℋom(F ∘ Φ, G ∘ Φ)` of presheaves on `D`. -/
def internalHomPresheafPrecomp (F G : Cᵒᵖ ⥤ Ab.{max u v}) :
    Φ.op ⋙ internalHomPresheaf F G ⟶ internalHomPresheaf (Φ.op ⋙ F) (Φ.op ⋙ G) where
  app V := internalHomPresheafPrecompApp Φ F G V
  naturality V V' f := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro a
    refine NatTrans.ext (funext fun x => ?_)
    have h : (Over.map (Φ.map f.unop)).obj ((Over.post Φ).obj x.unop) =
        (Over.post Φ).obj ((Over.map f.unop).obj x.unop) := by
      change Over.mk (Φ.map x.unop.hom ≫ Φ.map f.unop) = Over.mk (Φ.map (x.unop.hom ≫ f.unop))
      rw [Φ.map_comp]
    exact eq_of_heq (app_heq_of_eq a h)

/-- The comparison is bijective at `V` when `Over.post Φ : Over V ⥤ Over (Φ V)` is an
equivalence: whiskering along an equivalence is bijective on natural transformations. -/
lemma bijective_internalHomPresheafPrecompApp (F G : Cᵒᵖ ⥤ Ab.{max u v}) (V : Dᵒᵖ)
    [(Over.post (X := V.unop) Φ).IsEquivalence] :
    Function.Bijective (internalHomPresheafPrecompApp Φ F G V).hom :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ Ab.{max u v}).obj (Over.post (X := V.unop) Φ).op)).map_bijective
      ((Over.forget (Φ.obj V.unop)).op ⋙ F) ((Over.forget (Φ.obj V.unop)).op ⋙ G)

/-- **Precomposition with `Φ` commutes with the internal Hom** when every `Over.post Φ` is an
equivalence. -/
def internalHomPresheafPrecompIso (F G : Cᵒᵖ ⥤ Ab.{max u v})
    [∀ V : D, (Over.post (X := V) Φ).IsEquivalence] :
    Φ.op ⋙ internalHomPresheaf F G ≅ internalHomPresheaf (Φ.op ⋙ F) (Φ.op ⋙ G) :=
  NatIso.ofComponents
    (fun V => (AddEquiv.ofBijective (internalHomPresheafPrecompApp Φ F G V).hom
      (bijective_internalHomPresheafPrecompApp Φ F G V)).toAddCommGrpIso)
    (fun f => (internalHomPresheafPrecomp Φ F G).naturality f)

/-- The forward morphism of `internalHomPresheafPrecompIso` is the comparison
`internalHomPresheafPrecomp`. -/
lemma internalHomPresheafPrecompIso_hom (F G : Cᵒᵖ ⥤ Ab.{max u v})
    [∀ V : D, (Over.post (X := V) Φ).IsEquivalence] :
    (internalHomPresheafPrecompIso Φ F G).hom = internalHomPresheafPrecomp Φ F G := rfl

/-- **Pushforward along a continuous functor commutes with the internal Hom** when every
`Over.post Φ` is an equivalence: `Φ^* ℋom(F, G) ≅ ℋom(Φ^* F, Φ^* G)`. -/
def internalHomSheafPushforwardIso (J : GrothendieckTopology D) (K : GrothendieckTopology C)
    [Φ.IsContinuous J K] [∀ V : D, (Over.post (X := V) Φ).IsEquivalence]
    (F G : Sheaf K Ab.{max u v}) :
    (Φ.sheafPushforwardContinuous Ab.{max u v} J K).obj (internalHomSheaf K F G) ≅
      internalHomSheaf J ((Φ.sheafPushforwardContinuous Ab.{max u v} J K).obj F)
        ((Φ.sheafPushforwardContinuous Ab.{max u v} J K).obj G) :=
  ObjectProperty.isoMk _ (internalHomPresheafPrecompIso Φ F.obj G.obj)

/-- The underlying morphism of presheaves of the forward morphism of
`internalHomSheafPushforwardIso` is the comparison `internalHomPresheafPrecomp`. -/
lemma internalHomSheafPushforwardIso_hom_hom (J : GrothendieckTopology D)
    (K : GrothendieckTopology C) [Φ.IsContinuous J K]
    [∀ V : D, (Over.post (X := V) Φ).IsEquivalence] (F G : Sheaf K Ab.{max u v}) :
    (internalHomSheafPushforwardIso Φ J K F G).hom.hom = internalHomPresheafPrecomp Φ F.obj G.obj :=
  rfl

end Stacks.AbelianInternalHom

end
