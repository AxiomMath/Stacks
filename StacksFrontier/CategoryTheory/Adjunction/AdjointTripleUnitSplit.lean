module

public import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# When the two outer adjoints agree, the inner unit splits

Let `F ⊣ G ⊣ H` be an adjoint triple, with `F H : C ⥤ D` and `G : D ⥤ C`, and let `F` and `H`
be fully faithful.  The canonical comparison `CategoryTheory.Adjunction.Triple.leftToRight : F ⟶ H`
is an isomorphism as soon as `F` and `H` are isomorphic by any isomorphism, and whenever it is an
isomorphism the unit `X ⟶ H.obj (G.obj X)` of `G ⊣ H` is a split epimorphism, with a natural
section.

## Main definitions

* `CategoryTheory.Adjunction.Triple.unitSection`: the natural section `G ⋙ H ⟶ 𝟭 D` of the unit
  of `G ⊣ H`.
* `CategoryTheory.Adjunction.Triple.splitEpiUnit` and
  `CategoryTheory.Adjunction.Triple.splitEpiUnitOfIso`: the resulting splitting of the unit at an
  object.

## Main results

* `CategoryTheory.Adjunction.Triple.leftToRight_triangle`: the transpose of the canonical
  comparison across `F ⊣ G` is the inverse of the counit of `G ⊣ H`.
* `CategoryTheory.Adjunction.Triple.isIso_leftToRight`: an arbitrary isomorphism `F ≅ H` makes
  the canonical comparison an isomorphism.
* `CategoryTheory.Adjunction.Triple.unitSection_comp_unit`: the section composed with the unit is
  the identity of `G ⋙ H`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Adjunction.Triple

variable {C D : Type*} [Category C] [Category D] {F H : C ⥤ D} {G : D ⥤ C}
  (t : Adjunction.Triple F G H) [F.Full] [F.Faithful] [H.Full] [H.Faithful]

omit [H.Full] [H.Faithful] in
/-- The transpose across `F ⊣ G` of the canonical comparison `F ⟶ H` of an adjoint triple
`F ⊣ G ⊣ H` with `F` and `H` fully faithful is the inverse of the counit of `G ⊣ H`. -/
theorem leftToRight_triangle (X : C) :
    t.adj₁.unit.app X ≫ G.map (t.leftToRight.app X) ≫ t.adj₂.counit.app X = 𝟙 X := by
  rw [t.leftToRight_app, ← Functor.map_inv, Functor.map_comp, Category.assoc,
    show G.map (H.map (inv (t.adj₁.unit.app X))) ≫ t.adj₂.counit.app X =
      t.adj₂.counit.app (G.obj (F.obj X)) ≫ inv (t.adj₁.unit.app X) from
      (t.adj₂.counit.naturality (inv (t.adj₁.unit.app X)))]
  slice_lhs 2 3 => rw [t.adj₂.left_triangle_components]
  simp

/-- If the two outer functors of an adjoint triple `F ⊣ G ⊣ H` are fully faithful and isomorphic
by *any* isomorphism, then the canonical comparison `F ⟶ H` is an isomorphism. -/
theorem isIso_leftToRight (θ : F ≅ H) : IsIso t.leftToRight := by
  suffices ∀ X : C, IsIso (t.leftToRight.app X) from NatIso.isIso_of_isIso_app _
  intro X
  set α : X ⟶ X := t.adj₁.unit.app X ≫ G.map (θ.hom.app X) ≫ t.adj₂.counit.app X with hα
  have hαiso : IsIso α := by rw [hα]; infer_instance
  have hnat : t.adj₁.unit.app X ≫ G.map (F.map α) = α ≫ t.adj₁.unit.app X :=
    (t.adj₁.unit.naturality α).symm
  have hc : t.adj₁.unit.app X ≫ G.map (t.leftToRight.app X) = inv (t.adj₂.counit.app X) :=
    (IsIso.inv_eq_of_inv_hom_id ((Category.assoc _ _ _).trans (t.leftToRight_triangle X))).symm
  have key : θ.hom.app X = F.map α ≫ t.leftToRight.app X := by
    apply (t.adj₁.homEquiv X (H.obj X)).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, hnat, Category.assoc, hc, hα, Category.assoc, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id]
  have : IsIso (F.map α ≫ t.leftToRight.app X) := by rw [← key]; infer_instance
  exact IsIso.of_isIso_comp_left (F.map α) _

section Split

variable [IsIso t.leftToRight]

/-- The natural section `G ⋙ H ⟶ 𝟭 D` of the unit of `G ⊣ H`, for an adjoint triple
`F ⊣ G ⊣ H` whose canonical comparison `F ⟶ H` is invertible: invert the comparison and follow
with the counit of `F ⊣ G`. -/
noncomputable def unitSection : G ⋙ H ⟶ 𝟭 D :=
  Functor.whiskerLeft G (inv t.leftToRight) ≫ t.adj₁.counit

omit [H.Full] [H.Faithful] in
/-- The component of the natural section of the unit, written out. -/
theorem unitSection_app (X : D) :
    t.unitSection.app X = inv (t.leftToRight.app (G.obj X)) ≫ t.adj₁.counit.app X := by
  simp [unitSection]

omit [H.Full] [H.Faithful] in
/-- **The unit of `G ⊣ H` is a split epimorphism, naturally**: the section followed by the unit
is the identity of `G ⋙ H`. -/
theorem unitSection_comp_unit : t.unitSection ≫ t.adj₂.unit = 𝟙 (G ⋙ H) := by
  ext X
  rw [NatTrans.comp_app, t.unitSection_app, Category.assoc, NatTrans.id_app,
    IsIso.inv_comp_eq, Category.comp_id]
  exact t.leftToRight_app_obj.symm

/-- **The unit `X ⟶ H.obj (G.obj X)` of `G ⊣ H` is a split epimorphism** for an adjoint triple
`F ⊣ G ⊣ H` with fully faithful outer adjoints whose canonical comparison is invertible. -/
noncomputable def splitEpiUnit (X : D) : SplitEpi (t.adj₂.unit.app X) where
  section_ := inv (t.leftToRight.app (G.obj X)) ≫ t.adj₁.counit.app X
  id := by
    rw [Category.assoc, IsIso.inv_comp_eq, Category.comp_id]
    exact t.leftToRight_app_obj.symm

end Split

/-- **The unit `X ⟶ H.obj (G.obj X)` of `G ⊣ H` is a split epimorphism** as soon as the two outer
adjoints of the triple are fully faithful and isomorphic to one another. -/
noncomputable def splitEpiUnitOfIso (θ : F ≅ H) (X : D) : SplitEpi (t.adj₂.unit.app X) :=
  have : IsIso t.leftToRight := t.isIso_leftToRight θ
  t.splitEpiUnit X

end CategoryTheory.Adjunction.Triple

end
