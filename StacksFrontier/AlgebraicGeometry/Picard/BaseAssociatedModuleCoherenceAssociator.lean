module

public import StacksFrontier.AlgebraicGeometry.Picard.BaseAssociatedModuleCoherenceBraiding

/-!
# The associativity coherence of the tensor comparison of the associated-module functor

`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'` is Stacks 03EL at the morphism of
ringed sites `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`, packaged as the object-level tensor comparison
`Stacks.SheafOfModules.Picard.TensorIso` of the associated-module functor `𝓕 ↦ 𝓕^a` of Stacks
03DU (4).  Of the four data that
`Stacks.SheafOfModules.TensorPowerTransport.powerTransportIso_tensor` asks for, naturality is
`AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_natural` and the symmetry coherence
is `AlgebraicGeometry.BigFppfOver.baseAssociatedModuleTensorIso'_braiding`.  This file supplies
the transport lemma for the **associativity** one.

## Main results

* `Stacks.SheafOfModules.TransportCoherence.transported_associator'`: **the associativity
  coherence transports along a natural isomorphism of functors**, with the binary operation, its
  associativity constraint and its action on pairs of morphisms as explicit data rather than as a
  `CategoryTheory.MonoidalCategory` instance.

## Implementation notes

This is the companion of `Stacks.SheafOfModules.TransportCoherence.transported_braiding`, and it
exists for the same reason that one does:
`Stacks.SheafOfModules.TransportCoherence.transported_associator` is stated with the monoidal
notation, so applying it to sheaves of modules asks instance resolution to match the localized
monoidal structure of `Stacks.SheafOfModules.monoidalCategory` against the fixed constraints of
Tag 01CA, which is a `whnf` that exhausts the heartbeat budget.  At the spelling below nothing
has to be matched.

The three structural laws of the action on morphisms that the transport needs — that it preserves
composition, that it preserves identities, and that the associativity constraint is natural for
it — are hypotheses.  For the tensor product of Tag 01CA they are the functoriality of
`Stacks.SheafOfModules.Invertible.tensorProductBifunctor` and
`Stacks.SheafOfModules.Invertible.tensorProductAssociator_naturality`.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u v' u'

namespace Stacks.SheafOfModules.TransportCoherence

variable {C₁ : Type u} [Category.{v} C₁] {C₂ : Type u'} [Category.{v'} C₂]
  {G₁ G₂ : C₁ ⥤ C₂} (Z : G₁ ≅ G₂)
  (T₁ : C₁ → C₁ → C₁) (T₂ : C₂ → C₂ → C₂)
  (t₂ : ∀ X X' Y Y' : C₂, (X ⟶ X') → (Y ⟶ Y') → (T₂ X Y ⟶ T₂ X' Y'))
  (a₁ : ∀ A B D : C₁, T₁ (T₁ A B) D ≅ T₁ A (T₁ B D))
  (a₂ : ∀ X Y W : C₂, T₂ (T₂ X Y) W ≅ T₂ X (T₂ Y W))
  (δ : ∀ A B : C₁, G₁.obj (T₁ A B) ⟶ T₂ (G₁.obj A) (G₁.obj B))

/-- **The associativity coherence transports along a natural isomorphism of functors.**  Let
`Z : G₁ ≅ G₂` be an isomorphism of functors, let `T₁` and `T₂` be binary operations on objects
carrying associativity constraints `a₁` and `a₂`, let `t₂` act on pairs of morphisms, and let
`δ A B : G₁(T₁ A B) ⟶ T₂ (G₁ A) (G₁ B)` be a comparison compatible with them (`hδ`).  Then the
comparison `h` of `G₂` obtained from `δ` by conjugating with `Z` (`hh`) is compatible with them
as well.

`ht₂comp` is the functoriality of `t₂` and `ha₂` the naturality of `a₂`.  As in
`Stacks.SheafOfModules.TransportCoherence.transported_braiding`, the operation and its constraint
are explicit data rather than a `CategoryTheory.MonoidalCategory` instance, so that nothing has
to be matched against a competing instance when this is used on sheaves of modules. -/
public theorem transported_associator'
    (h : ∀ A B : C₁, G₂.obj (T₁ A B) ⟶ T₂ (G₂.obj A) (G₂.obj B))
    (hh : ∀ A B : C₁, h A B =
      Z.inv.app (T₁ A B) ≫ δ A B ≫
        t₂ (G₁.obj A) (G₂.obj A) (G₁.obj B) (G₂.obj B) (Z.hom.app A) (Z.hom.app B))
    (ht₂comp : ∀ (X X' X'' Y Y' Y'' : C₂) (u : X ⟶ X') (u' : X' ⟶ X'') (v : Y ⟶ Y')
      (v' : Y' ⟶ Y''), t₂ X X' Y Y' u v ≫ t₂ X' X'' Y' Y'' u' v' =
        t₂ X X'' Y Y'' (u ≫ u') (v ≫ v'))
    (ha₂ : ∀ (X X' Y Y' W W' : C₂) (u : X ⟶ X') (v : Y ⟶ Y') (t : W ⟶ W'),
      t₂ (T₂ X Y) (T₂ X' Y') W W' (t₂ X X' Y Y' u v) t ≫ (a₂ X' Y' W').hom =
        (a₂ X Y W).hom ≫ t₂ X X' (T₂ Y W) (T₂ Y' W') u (t₂ Y Y' W W' v t))
    (hδ : ∀ A B D : C₁, G₁.map (a₁ A B D).hom ≫ δ A (T₁ B D) ≫
        t₂ (G₁.obj A) (G₁.obj A) (G₁.obj (T₁ B D)) (T₂ (G₁.obj B) (G₁.obj D))
          (𝟙 (G₁.obj A)) (δ B D) =
      δ (T₁ A B) D ≫
        t₂ (G₁.obj (T₁ A B)) (T₂ (G₁.obj A) (G₁.obj B)) (G₁.obj D) (G₁.obj D)
          (δ A B) (𝟙 (G₁.obj D)) ≫
        (a₂ (G₁.obj A) (G₁.obj B) (G₁.obj D)).hom)
    (A B D : C₁) :
    G₂.map (a₁ A B D).hom ≫ h A (T₁ B D) ≫
        t₂ (G₂.obj A) (G₂.obj A) (G₂.obj (T₁ B D)) (T₂ (G₂.obj B) (G₂.obj D))
          (𝟙 (G₂.obj A)) (h B D) =
      h (T₁ A B) D ≫
        t₂ (G₂.obj (T₁ A B)) (T₂ (G₂.obj A) (G₂.obj B)) (G₂.obj D) (G₂.obj D)
          (h A B) (𝟙 (G₂.obj D)) ≫
        (a₂ (G₂.obj A) (G₂.obj B) (G₂.obj D)).hom := by
  -- Split the two collapsed tensor actions back into the shape `hδ` and `ha₂` are stated in.
  have s1 : ∀ (X X' Y Y' Y'' : C₂) (u : X ⟶ X') (v : Y ⟶ Y') (w : Y' ⟶ Y''),
      t₂ X X' Y Y'' u (v ≫ w) = t₂ X X Y Y' (𝟙 X) v ≫ t₂ X X' Y' Y'' u w := by
    intro X X' Y Y' Y'' u v w
    rw [ht₂comp, Category.id_comp]
  have s2 : ∀ (X X' X'' Y Y' : C₂) (u : X ⟶ X') (v : X' ⟶ X'') (w : Y ⟶ Y'),
      t₂ X X'' Y Y' (u ≫ v) w = t₂ X X' Y Y u (𝟙 Y) ≫ t₂ X' X'' Y Y' v w := by
    intro X X' X'' Y Y' u v w
    rw [ht₂comp, Category.id_comp]
  rw [hh A (T₁ B D), hh (T₁ A B) D, hh A B, hh B D]
  simp only [Category.assoc]
  rw [Z.inv.naturality_assoc (a₁ A B D).hom]
  rw [ht₂comp _ _ _ _ _ _ (Z.hom.app A) (𝟙 (G₂.obj A)) (Z.hom.app (T₁ B D))
    (Z.inv.app (T₁ B D) ≫ δ B D ≫
      t₂ (G₁.obj B) (G₂.obj B) (G₁.obj D) (G₂.obj D) (Z.hom.app B) (Z.hom.app D))]
  rw [reassoc_of% (ht₂comp _ _ _ _ _ _ (Z.hom.app (T₁ A B))
    (Z.inv.app (T₁ A B) ≫ δ A B ≫
      t₂ (G₁.obj A) (G₂.obj A) (G₁.obj B) (G₂.obj B) (Z.hom.app A) (Z.hom.app B))
    (Z.hom.app D) (𝟙 (G₂.obj D)))]
  simp only [Category.comp_id, Iso.hom_inv_id_app_assoc]
  rw [s1 _ _ _ _ _ _ _ _, reassoc_of% (s2 _ _ _ _ _ _ _ _),
    ha₂ (G₁.obj A) (G₂.obj A) (G₁.obj B) (G₂.obj B) (G₁.obj D) (G₂.obj D)
      (Z.hom.app A) (Z.hom.app B) (Z.hom.app D)]
  rw [reassoc_of% (hδ A B D)]

end Stacks.SheafOfModules.TransportCoherence

end
