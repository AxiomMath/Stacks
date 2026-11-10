module

public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomTensor
public import StacksFrontier.CategoryTheory.Sites.AbelianInternalHomPrecomp

/-!
# Swapping the arguments of the abelian internal Hom

For abelian presheaves `X, G, I` both `Hom(X, ℋom(G, I))` and `Hom(G, ℋom(X, I))` are the
pairings `X × G ⟶ I`, so they are in bijection, naturally in all three variables. We also record
that the comparison of `Stacks.AbelianInternalHom.internalHomPresheafPrecomp` is natural in both
variables.

## Main definitions

* `Stacks.AbelianInternalHom.internalHomSwap`: `Hom(X, ℋom(G, I)) ≃ Hom(G, ℋom(X, I))`.
* `Stacks.AbelianInternalHom.internalHomSheafSwap`: the same for abelian sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v u

namespace Stacks.AbelianInternalHom

variable {C : Type u} [Category.{v} C]

section Presheaf

/-- The flip `X ⊗ G ≅ G ⊗ X` of sectionwise tensor products. -/
def presheafTensorFlip (G X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    presheafTensorObj X G ≅ presheafTensorObj G X :=
  NatIso.ofComponents
    (fun U => (TensorProduct.comm ℤ (X.obj U) (G.obj U)).toAddEquiv.toAddCommGrpIso)
    (fun _ => presheafTensorObj_hom_ext X fun _ _ => rfl)

/-- **Swapping the arguments of the internal Hom**: `Hom(X, ℋom(G, I)) ≃ Hom(G, ℋom(X, I))`,
both sides being the pairings `X × G ⟶ I`. -/
def internalHomSwap (X G I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    (X ⟶ internalHomPresheaf G I) ≃ (G ⟶ internalHomPresheaf X I) :=
  ((pairingEquiv (G := G) X I).symm.trans
    ((presheafTensorFlip G X).symm.homCongr (Iso.refl I))).trans (pairingEquiv (G := X) G I)

/-- The swapped morphism on elements: `x ↦ ψ(x)(g)`. -/
lemma internalHomSwap_apply (X G I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (ψ : X ⟶ internalHomPresheaf G I) (U : Cᵒᵖ) (g : G.obj U) (W : (Over U.unop)ᵒᵖ)
    (x : X.obj (op W.unop.left)) :
    (((((internalHomSwap X G I ψ).app U).hom g).app W).hom x) =
      ((ψ.app (op W.unop.left) x).app (op (Over.mk (𝟙 W.unop.left)))).hom
        (G.map W.unop.hom.op g) := rfl

/-- Two morphisms `X ⟶ ℋom(G, I)` are equal if they agree on all elements. -/
private theorem hom_ext_internalHomPresheaf {X G I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    {f f' : X ⟶ internalHomPresheaf G I}
    (h : ∀ (U : Cᵒᵖ) (x : X.obj U) (W : (Over U.unop)ᵒᵖ),
      ((f.app U).hom x).app W = ((f'.app U).hom x).app W) : f = f' :=
  NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
    NatTrans.ext (funext fun W => h U x W)))

/-- `internalHomSwap` is natural in the first variable. -/
lemma internalHomSwap_comp {X X' G I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (f : X' ⟶ X)
    (ψ : X ⟶ internalHomPresheaf G I) :
    internalHomSwap X' G I (f ≫ ψ) = internalHomSwap X G I ψ ≫ internalHomPresheafMapLeft f I :=
  hom_ext_internalHomPresheaf fun _ _ _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl)

/-- `internalHomSwap` is natural in the second variable. -/
lemma internalHomSwap_comp_mapLeft {X G G' I : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (g : G' ⟶ G)
    (ψ : X ⟶ internalHomPresheaf G I) :
    internalHomSwap X G' I (ψ ≫ internalHomPresheafMapLeft g I) =
      g ≫ internalHomSwap X G I ψ :=
  hom_ext_internalHomPresheaf fun U g₀ W => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => by
    have h : (g.app (op W.unop.left)).hom ((G'.map W.unop.hom.op).hom g₀) =
        (G.map W.unop.hom.op).hom ((g.app U).hom g₀) :=
      ConcreteCategory.congr_hom (g.naturality W.unop.hom.op) g₀
    change ((ψ.app (op W.unop.left) x).app (op (Over.mk (𝟙 W.unop.left)))).hom
        ((g.app (op W.unop.left)).hom ((G'.map W.unop.hom.op).hom g₀)) =
      ((ψ.app (op W.unop.left) x).app (op (Over.mk (𝟙 W.unop.left)))).hom
        ((G.map W.unop.hom.op).hom ((g.app U).hom g₀))
    rw [h])

/-- `internalHomSwap` is natural in the third variable. -/
lemma internalHomSwap_comp_mapRight {X G I I' : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (h : I ⟶ I')
    (ψ : X ⟶ internalHomPresheaf G I) :
    internalHomSwap X G I' (ψ ≫ internalHomPresheafMapRight G h) =
      internalHomSwap X G I ψ ≫ internalHomPresheafMapRight X h :=
  hom_ext_internalHomPresheaf fun _ _ _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => rfl)

variable {D : Type u} [Category.{v} D] (Φ : D ⥤ C)

/-- The comparison `ℋom(F, G) ∘ Φ ⟶ ℋom(F ∘ Φ, G ∘ Φ)` is natural in `F`. -/
lemma internalHomPresheafPrecomp_naturality_left {F F' G : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (f : F ⟶ F') :
    Functor.whiskerLeft Φ.op (internalHomPresheafMapLeft f G) ≫
        internalHomPresheafPrecomp Φ F G =
      internalHomPresheafPrecomp Φ F' G ≫
        internalHomPresheafMapLeft (Functor.whiskerLeft Φ.op f) (Φ.op ⋙ G) :=
  NatTrans.ext (funext fun _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ =>
    NatTrans.ext (funext fun _ => rfl)))

/-- The comparison `ℋom(F, G) ∘ Φ ⟶ ℋom(F ∘ Φ, G ∘ Φ)` is natural in `G`. -/
lemma internalHomPresheafPrecomp_naturality_right {F G G' : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}}
    (g : G ⟶ G') :
    Functor.whiskerLeft Φ.op (internalHomPresheafMapRight F g) ≫
        internalHomPresheafPrecomp Φ F G' =
      internalHomPresheafPrecomp Φ F G ≫
        internalHomPresheafMapRight (Φ.op ⋙ F) (Functor.whiskerLeft Φ.op g) :=
  NatTrans.ext (funext fun _ => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ =>
    NatTrans.ext (funext fun _ => rfl)))

end Presheaf

section Sheaf

variable (K : GrothendieckTopology C)

/-- Precomposition `ℋom(X, I) ⟶ ℋom(X', I)` with `f : X' ⟶ X`, with its source and target
spelled as internal Hom sheaves. -/
def internalHomSheafMapLeft {X X' : Sheaf K AddCommGrpCat.{max u v}} (f : X' ⟶ X)
    (I : Sheaf K AddCommGrpCat.{max u v}) :
    internalHomSheaf K X I ⟶ internalHomSheaf K X' I :=
  (internalHomFunctor K I).map f.op

/-- Postcomposition `ℋom(G, I) ⟶ ℋom(G, I')` with `h : I ⟶ I'`, with its source and target
spelled as internal Hom sheaves. -/
def internalHomSheafMapRight (G : Sheaf K AddCommGrpCat.{max u v})
    {I I' : Sheaf K AddCommGrpCat.{max u v}} (h : I ⟶ I') :
    internalHomSheaf K G I ⟶ internalHomSheaf K G I' :=
  (internalHomRightFunctor K G).map h

/-- The underlying morphism of presheaves of `internalHomSheafMapLeft K f I` is
`internalHomPresheafMapLeft f.hom I.obj`. -/
lemma internalHomSheafMapLeft_hom {X X' : Sheaf K AddCommGrpCat.{max u v}} (f : X' ⟶ X)
    (I : Sheaf K AddCommGrpCat.{max u v}) :
    (internalHomSheafMapLeft K f I).hom = internalHomPresheafMapLeft f.hom I.obj := rfl

/-- The underlying morphism of presheaves of `internalHomSheafMapRight K G h` is
`internalHomPresheafMapRight G.obj h.hom`. -/
lemma internalHomSheafMapRight_hom (G : Sheaf K AddCommGrpCat.{max u v})
    {I I' : Sheaf K AddCommGrpCat.{max u v}} (h : I ⟶ I') :
    (internalHomSheafMapRight K G h).hom = internalHomPresheafMapRight G.obj h.hom := rfl

/-- **Swapping the arguments of the internal Hom of abelian sheaves**:
`Hom(X, ℋom(G, I)) ≃ Hom(G, ℋom(X, I))`. -/
def internalHomSheafSwap (X G I : Sheaf K AddCommGrpCat.{max u v}) :
    (X ⟶ internalHomSheaf K G I) ≃ (G ⟶ internalHomSheaf K X I) where
  toFun φ := ObjectProperty.homMk (internalHomSwap X.obj G.obj I.obj φ.hom)
  invFun ψ := ObjectProperty.homMk ((internalHomSwap X.obj G.obj I.obj).symm ψ.hom)
  left_inv φ := Sheaf.hom_ext ((internalHomSwap X.obj G.obj I.obj).symm_apply_apply φ.hom)
  right_inv ψ := Sheaf.hom_ext ((internalHomSwap X.obj G.obj I.obj).apply_symm_apply ψ.hom)

/-- The underlying morphism of presheaves of `internalHomSheafSwap K X G I φ` is
`internalHomSwap X.obj G.obj I.obj φ.hom`. -/
lemma internalHomSheafSwap_hom (X G I : Sheaf K AddCommGrpCat.{max u v})
    (φ : X ⟶ internalHomSheaf K G I) :
    (internalHomSheafSwap K X G I φ).hom = internalHomSwap X.obj G.obj I.obj φ.hom := rfl

/-- `internalHomSheafSwap` is natural in the first variable. -/
lemma internalHomSheafSwap_comp {X X' G I : Sheaf K AddCommGrpCat.{max u v}} (f : X' ⟶ X)
    (ψ : X ⟶ internalHomSheaf K G I) :
    internalHomSheafSwap K X' G I (f ≫ ψ) =
      internalHomSheafSwap K X G I ψ ≫ internalHomSheafMapLeft K f I :=
  Sheaf.hom_ext (internalHomSwap_comp f.hom ψ.hom)

/-- `internalHomSheafSwap` is natural in the second variable. -/
lemma internalHomSheafSwap_comp_map {X G G' I : Sheaf K AddCommGrpCat.{max u v}} (g : G' ⟶ G)
    (ψ : X ⟶ internalHomSheaf K G I) :
    internalHomSheafSwap K X G' I (ψ ≫ internalHomSheafMapLeft K g I) =
      g ≫ internalHomSheafSwap K X G I ψ :=
  Sheaf.hom_ext (internalHomSwap_comp_mapLeft g.hom ψ.hom)

/-- `internalHomSheafSwap` is natural in the third variable. -/
lemma internalHomSheafSwap_comp_mapRight {X G I I' : Sheaf K AddCommGrpCat.{max u v}}
    (h : I ⟶ I') (ψ : X ⟶ internalHomSheaf K G I) :
    internalHomSheafSwap K X G I' (ψ ≫ internalHomSheafMapRight K G h) =
      internalHomSheafSwap K X G I ψ ≫ internalHomSheafMapRight K X h :=
  Sheaf.hom_ext (internalHomSwap_comp_mapRight h.hom ψ.hom)

end Sheaf

end Stacks.AbelianInternalHom

end
