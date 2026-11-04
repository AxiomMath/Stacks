module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Transporting a right adjoint of an inclusion along a left adjoint

Let `F : D ⥤ D'` be a left adjoint, `P` a property of the objects of `D` and `P'` one of the
objects of `D'`, such that `F` carries `P` into `P'` and induces an equivalence between the full
subcategories.  If the inclusion of `P` has a right adjoint, so does the inclusion of `P'`: it is
`P'.ι ≅ (F|_P)⁻¹ ⋙ P.ι ⋙ F`, a composite of left adjoints.

This is how the existence of a coherator is moved between categories of modules on different
sites, for instance across the comparison `ε : X_étale ⟶ X_Zar` of Stacks 071Q.

## Main results

* `CategoryTheory.ObjectProperty.isLeftAdjoint_ι_of_isEquivalence_lift`
* `CategoryTheory.ObjectProperty.isEquivalence_lift_of_isEquivalence`: the hypothesis of the
  previous result, for `F` an equivalence which detects `P'` exactly on `P`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ObjectProperty

variable {D : Type*} [Category* D] {D' : Type*} [Category* D']

/-- **The inclusion of `P'` has a right adjoint as soon as that of `P` does**, when `P'` is the
image of `P` under a left adjoint `F` inducing an equivalence of full subcategories. -/
theorem isLeftAdjoint_ι_of_isEquivalence_lift (P : ObjectProperty D) (P' : ObjectProperty D')
    (F : D ⥤ D') [F.IsLeftAdjoint] (hF : ∀ X, P X → P' (F.obj X))
    [(P'.lift (P.ι ⋙ F) fun X => hF X.obj X.property).IsEquivalence] [P.ι.IsLeftAdjoint] :
    P'.ι.IsLeftAdjoint := by
  let G := P'.lift (P.ι ⋙ F) fun X => hF X.obj X.property
  let e : P'.ι ≅ G.inv ⋙ (P.ι ⋙ F) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight G.asEquivalence.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (P'.liftCompιIso _ _)
  exact Functor.isLeftAdjoint_of_iso e.symm

/-- An equivalence `F : D ⥤ D'` which detects `P'` exactly on `P` induces an equivalence between
the full subcategories, provided `P'` is closed under isomorphisms. -/
theorem isEquivalence_lift_of_isEquivalence (P : ObjectProperty D) (P' : ObjectProperty D')
    [P'.IsClosedUnderIsomorphisms] (F : D ⥤ D') [F.IsEquivalence]
    (hF : ∀ X, P' (F.obj X) ↔ P X) :
    (P'.lift (P.ι ⋙ F) fun X => (hF X.obj).2 X.property).IsEquivalence := by
  let G := P'.lift (P.ι ⋙ F) fun X => (hF X.obj).2 X.property
  have hG : G.FullyFaithful := Functor.FullyFaithful.ofCompFaithful (G := P'.ι)
    ((P.fullyFaithfulι.comp F.asEquivalence.fullyFaithfulFunctor).ofIso
      (P'.liftCompιIso _ _).symm)
  have := hG.full
  have := hG.faithful
  have : G.EssSurj := ⟨fun Y => ⟨⟨_, (hF _).1 (P'.prop_of_iso (F.asEquivalence.counitIso.app _).symm
    Y.property)⟩, ⟨P'.fullyFaithfulι.preimageIso (F.asEquivalence.counitIso.app Y.obj)⟩⟩⟩
  exact { }

end CategoryTheory.ObjectProperty
