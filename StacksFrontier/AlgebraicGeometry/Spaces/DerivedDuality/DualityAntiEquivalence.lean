module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Opposites

/-!
# Anti-equivalences from a duality functor with an invertible biduality

Let `D : Cᵒᵖ ⥤ C` be a functor with a natural transformation `β : 𝟭 C ⟶ D.rightOp ⋙ D`, the
*biduality*, with components `β_L : L ⟶ D(D(L))`. If two classes of objects `Q₁`, `Q₂` are
exchanged by `D` and `β` is invertible at all their objects, then `D` restricts to an
anti-equivalence `Q₁ᵒᵖ ≌ Q₂`, and on `Q₁ = Q₂` the biduality is a natural isomorphism
`𝟭 ≅ D ∘ D`.

We also transport a duality and its biduality along an equivalence `P : C ≌ C'`.

## Main definitions

* `CategoryTheory.dualityAntiEquivalence`: the anti-equivalence `Q₁ᵒᵖ ≌ Q₂`.
* `CategoryTheory.dualityBidualityIso`: the natural isomorphism `𝟭 ≅ D ∘ D` on `Q`.
* `CategoryTheory.Equivalence.conjDual`, `CategoryTheory.Equivalence.conjBiduality`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type*} [Category C] (D : Cᵒᵖ ⥤ C) (β : 𝟭 C ⟶ D.rightOp ⋙ D)
  (Q₁ Q₂ : ObjectProperty C)

/-- The restriction of `D` to a functor `Q₁ᵒᵖ ⥤ Q₂`. -/
def dualityRestrict (h : ∀ L, Q₁ L → Q₂ (D.obj (op L))) :
    Q₁.FullSubcategoryᵒᵖ ⥤ Q₂.FullSubcategory :=
  Q₂.lift (Q₁.ι.op ⋙ D) fun L => h _ L.unop.2

/-- The restriction of `D` composed with the inclusion is `D` on the inclusion. -/
def dualityRestrictCompι (h : ∀ L, Q₁ L → Q₂ (D.obj (op L))) :
    dualityRestrict D Q₁ Q₂ h ⋙ Q₂.ι ≅ Q₁.ι.op ⋙ D :=
  Iso.refl _

section AntiEquivalence

variable (h₁ : ∀ L, Q₁ L → Q₂ (D.obj (op L))) (h₂ : ∀ L, Q₂ L → Q₁ (D.obj (op L)))
  (hβ₁ : ∀ L, Q₁ L → IsIso (β.app L)) (hβ₂ : ∀ L, Q₂ L → IsIso (β.app L))

include β

/-- The biduality at the objects of `Q₂`, as a natural isomorphism of functors to `Q₂`. -/
def dualityCounitIso :
    (dualityRestrict D Q₂ Q₁ h₂).rightOp ⋙ dualityRestrict D Q₁ Q₂ h₁ ≅ 𝟭 Q₂.FullSubcategory :=
  ((Q₂.fullyFaithfulι.whiskeringRight _).preimageIso
    (NatIso.ofComponents (fun L => @asIso _ _ _ _ (β.app L.1) (hβ₂ L.1 L.2))
      (fun f => β.naturality f.hom) : 𝟭 Q₂.FullSubcategory ⋙ Q₂.ι ≅
      ((dualityRestrict D Q₂ Q₁ h₂).rightOp ⋙ dualityRestrict D Q₁ Q₂ h₁) ⋙ Q₂.ι)).symm

/-- The biduality at the objects of `Q₁`, as a natural isomorphism of functors to `Q₁ᵒᵖ`. -/
def dualityUnitIso :
    𝟭 Q₁.FullSubcategoryᵒᵖ ≅ dualityRestrict D Q₁ Q₂ h₁ ⋙ (dualityRestrict D Q₂ Q₁ h₂).rightOp :=
  (NatIso.op ((Q₁.fullyFaithfulι.whiskeringRight _).preimageIso
    (NatIso.ofComponents (fun L => @asIso _ _ _ _ (β.app L.1) (hβ₁ L.1 L.2))
      (fun f => β.naturality f.hom) : 𝟭 Q₁.FullSubcategory ⋙ Q₁.ι ≅
      ((dualityRestrict D Q₁ Q₂ h₁).rightOp ⋙ dualityRestrict D Q₂ Q₁ h₂) ⋙ Q₁.ι))).symm

/-- **The anti-equivalence induced by a duality functor**: if `D` exchanges `Q₁` and `Q₂` and the
biduality is invertible on both, then `D` restricts to an equivalence `Q₁ᵒᵖ ≌ Q₂`. -/
def dualityAntiEquivalence : Q₁.FullSubcategoryᵒᵖ ≌ Q₂.FullSubcategory :=
  Equivalence.mk (dualityRestrict D Q₁ Q₂ h₁) (dualityRestrict D Q₂ Q₁ h₂).rightOp
    (dualityUnitIso D β Q₁ Q₂ h₁ h₂ hβ₁) (dualityCounitIso D β Q₁ Q₂ h₁ h₂ hβ₂)

/-- The functor of `dualityAntiEquivalence` is `dualityRestrict D Q₁ Q₂ h₁`. -/
theorem dualityAntiEquivalence_functor :
    (dualityAntiEquivalence D β Q₁ Q₂ h₁ h₂ hβ₁ hβ₂).functor = dualityRestrict D Q₁ Q₂ h₁ :=
  rfl

end AntiEquivalence

/-- **The biduality isomorphism `𝟭 ≅ D ∘ D`** on a class `Q` preserved by `D` on which the
biduality is invertible. -/
def dualityBidualityIso (Q : ObjectProperty C) (h : ∀ L, Q L → Q (D.obj (op L)))
    (hβ : ∀ L, Q L → IsIso (β.app L)) :
    𝟭 Q.FullSubcategory ≅ (dualityRestrict D Q Q h).rightOp ⋙ dualityRestrict D Q Q h :=
  (dualityCounitIso D β Q Q h h hβ).symm

/-- The component of `dualityBidualityIso` at `L`, viewed in `C`, is `β.app L.1`. -/
theorem dualityBidualityIso_hom_app (Q : ObjectProperty C) (h : ∀ L, Q L → Q (D.obj (op L)))
    (hβ : ∀ L, Q L → IsIso (β.app L)) (L : Q.FullSubcategory) :
    Q.ι.map ((dualityBidualityIso D β Q h hβ).hom.app L) = β.app L.1 := by
  simp [dualityBidualityIso, dualityCounitIso]
  try rfl

namespace Equivalence

variable {C' : Type*} [Category C'] (P : C ≌ C') (D' : C'ᵒᵖ ⥤ C')
  (β' : 𝟭 C' ⟶ D'.rightOp ⋙ D')

/-- A duality functor on `C'` conjugated by an equivalence `P : C ≌ C'`. -/
def conjDual : Cᵒᵖ ⥤ C := P.functor.op ⋙ D' ⋙ P.inverse

/-- **The conjugated biduality**, a natural transformation `𝟭 ⟶ D ∘ D`: the unit of `P`, the
biduality of `D'`, and `D'` of the counit of `P`. -/
def conjBiduality : 𝟭 C ⟶ (conjDual P D').rightOp ⋙ conjDual P D' :=
  P.unit ≫ Functor.whiskerLeft P.functor (Functor.whiskerRight β' P.inverse) ≫
    Functor.whiskerLeft (P.functor ⋙ D'.rightOp)
      (Functor.whiskerRight (NatTrans.op P.counit) (D' ⋙ P.inverse))

/-- The component of `conjBiduality` at `L`: the unit of `P` at `L`, then `P.inverse` of the
biduality of `D'` at `P.functor.obj L`, then `P.inverse` of `D'` of the counit of `P`. -/
theorem conjBiduality_app (L : C) :
    (conjBiduality P D' β').app L = P.unit.app L ≫ P.inverse.map (β'.app (P.functor.obj L)) ≫
      P.inverse.map (D'.map (P.counit.app (D'.obj (Opposite.op (P.functor.obj L)))).op) :=
  rfl

/-- The conjugated biduality is invertible where the biduality is. -/
theorem isIso_conjBiduality_app (L : C) (h : IsIso (β'.app (P.functor.obj L))) :
    IsIso ((conjBiduality P D' β').app L) := by
  rw [conjBiduality_app]
  have := h
  have : IsIso (P.unit.app L) := inferInstanceAs (IsIso (P.unitIso.hom.app L))
  have : IsIso (D'.map (P.counit.app (D'.obj (Opposite.op (P.functor.obj L)))).op) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' (P.inverse.map_isIso _) (P.inverse.map_isIso _))

end Equivalence

end CategoryTheory

end
