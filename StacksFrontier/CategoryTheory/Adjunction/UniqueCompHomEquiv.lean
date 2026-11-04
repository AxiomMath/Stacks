module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Transposing the comparison of a composite left adjoint under its outer adjunction

Let `adj₁ : F ⊣ G` and `adj₂ : H ⊣ I` be composable adjunctions, so that `F ⋙ H` is left
adjoint to `I ⋙ G`, and let `adj' : F' ⊣ I ⋙ G` be a second adjunction with the same right
adjoint. `CategoryTheory.Adjunction.leftAdjointUniq` then compares `F ⋙ H` with `F'`, and
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` computes the transpose of its
component followed by anything — but under the *composite* adjunction, so the answer is a
morphism out of the outer object `X` rather than out of `F.obj X`.

That is the wrong shape for a consumer who has already peeled off an outer factor. The component
in question is a morphism `H.obj (F.obj X) ⟶ F'.obj X`, and a chain of morphisms starting with
it is transposed one factor at a time under `adj₂` alone, by
`CategoryTheory.Adjunction.homEquiv_naturality_left` and
`CategoryTheory.Adjunction.homEquiv_naturality_right`. This file supplies the value of that
transpose.

A second adjunction with the *same* right adjoint is the exception rather than the rule: a
comparison of left adjoints is usually produced from an isomorphism `e : I ⋙ G ≅ G'` of the two
right adjoints, so that the comparison is of `F ⋙ H` read through `e` with `F'`. That shape is
handled too, and the same-right-adjoint statement is the case `e = Iso.refl`.

## Main results

* `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp`: the
  transpose under `adj₂` of the component of the comparison of `F ⋙ H`, read through an
  isomorphism `e : I ⋙ G ≅ G'` of right adjoints, with a left adjoint `F'` of `G'`, followed by
  a morphism `g` out of `F'.obj X`.
* `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_hom_app_comp`: the transpose under
  `adj₂` of the component of the comparison followed by a morphism `g` out of `F'.obj X` is the
  inverse transpose under `adj₁` of the transpose of `g` under `adj'`.
* `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp_of_unit`
  and `CategoryTheory.Adjunction.leftAdjointUniq_comp_ofNatIsoRight_hom_app_of_unit`: the same
  two values when `F` is compared to `F' ⋙ I` by a 2-cell `c` *compatible with the two units*.
  Then the comparison is `H` of `c` followed by the counit of `adj₂`, and its transpose is `c`
  followed by `I` of `g`: neither `adj₁` nor `adj'` occurs any more. See the implementation
  notes.

## Implementation notes

The composite adjunction's hom-equivalence is the composite of the two,
`CategoryTheory.Adjunction.comp_homEquiv`, so the statement is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_hom_app_comp` for the composite adjunction
read through that factorisation and then through the bijectivity of `adj₁.homEquiv`. The useful
feature of the right-hand side is that the comparison has disappeared from it entirely: what
remains mentions only `adj₁`, the second adjunction's own transpose, and `e`.

The same-right-adjoint statement is deduced from the `e`-version at `e = Iso.refl`, which needs
`CategoryTheory.Adjunction.ofNatIsoRight_refl` — transporting an adjunction along the identity
isomorphism of its right adjoint returns it unchanged.

**Why the unit-compatible variant.** `adj₁` and `adj'` still occur in the right-hand sides above,
and that is useless to a consumer for whom they are *chosen* data — the adjunction fields of an
existence statement's `Classical.choice`, say — since then nothing can be computed about their
units. The variant removes them. Its hypothesis is a single compatibility: given a 2-cell
`c : F ⟶ F' ⋙ I` factoring the left adjoint through `I`, the composite
`adj₁.unit ≫ G(c) ≫ e.hom` is `adj'.unit`. Under it the comparison *is* `H(c)` followed by
`adj₂.counit`, which is the mate-style description — the comparison read off the 2-cell and the
outer adjunction alone — and the transpose collapses to `c ≫ I(g)` by the triangle identity. The
hypothesis is exactly the content that remains: it says that the identification of the two right
adjoints induced by `c` and `e` is the one the two units already agree on.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Adjunction

/-- **The transpose, under the outer adjunction, of the comparison of a composite left adjoint
with a left adjoint of an isomorphic functor.**

`F ⋙ H` is left adjoint to `I ⋙ G`, hence to `G'` through an isomorphism `e : I ⋙ G ≅ G'`, and
`F'` is left adjoint to `G'`; so the two are compared by
`CategoryTheory.Adjunction.leftAdjointUniq`. For a morphism `g : F'.obj X ⟶ Y`, the transpose
under `adj₂` of the comparison's component at `X` followed by `g` is the inverse transpose under
`adj₁` of the transpose of `g` under `adj'`, read back along `e`.

This is the shape in which a comparison of left adjoints is usually produced: the composite of
two right adjoints is identified with a third functor, and that identification is what the
comparison of the left adjoints is built from. -/
theorem homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {F' : C ⥤ E} {G' : E ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (e : I ⋙ G ≅ G') (adj' : F' ⊣ G') (X : C) {Y : E}
    (g : F'.obj X ⟶ Y) :
    adj₂.homEquiv (F.obj X) Y
        ((leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj').hom.app X ≫ g) =
      (adj₁.homEquiv X (I.obj Y)).symm (adj'.homEquiv X Y g ≫ e.inv.app Y) := by
  have h := homEquiv_leftAdjointUniq_hom_app_comp
    ((adj₁.comp adj₂).ofNatIsoRight e) adj' g
  rw [homEquiv_ofNatIsoRight_apply] at h
  refine (Equiv.eq_symm_apply _).mpr ?_
  rw [← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id, comp_homEquiv,
    Equiv.trans_apply]

/-- **The transpose, under the outer adjunction, of the comparison of a composite left adjoint
with another left adjoint of the same functor.**

`F ⋙ H` and `F'` are both left adjoint to `I ⋙ G`, so they are compared by
`CategoryTheory.Adjunction.leftAdjointUniq`. For a morphism `g : F'.obj X ⟶ Y`, the transpose
under `adj₂` of the comparison's component at `X` followed by `g` is the inverse transpose under
`adj₁` of the transpose of `g` under `adj'`.

Taking `g` to be the identity gives the transpose of the component itself; the general `g` is
what makes the lemma usable on a chain of morphisms, whose later factors need not be touched.

This is `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp` at
the identity isomorphism of `I ⋙ G`. -/
theorem homEquiv_leftAdjointUniq_comp_hom_app_comp {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {F' : C ⥤ E}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (adj' : F' ⊣ I ⋙ G) (X : C) {Y : E} (g : F'.obj X ⟶ Y) :
    adj₂.homEquiv (F.obj X) Y
        ((leftAdjointUniq (adj₁.comp adj₂) adj').hom.app X ≫ g) =
      (adj₁.homEquiv X (I.obj Y)).symm (adj'.homEquiv X Y g) := by
  have h := homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp adj₁ adj₂
    (Iso.refl (I ⋙ G)) adj' X g
  rw [ofNatIsoRight_refl] at h
  simpa using h

/-- **The transpose of the comparison of a composite left adjoint, with neither adjunction in the
answer.**

Suppose the left adjoint `F` of `adj₁` is compared to `F' ⋙ I` by a 2-cell `c : F ⟶ F' ⋙ I`, and
that `c` is compatible with the two units in the sense of `hc`: transporting `adj₁.unit` by `G` of
`c` and then by the comparison `e` of the right adjoints gives `adj'.unit`. Then for a morphism
`g : F'.obj X ⟶ Y` the transpose under `adj₂` of the comparison's component at `X` followed by `g`
is `c` at `X` followed by `I` of `g`.

Compare `CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp`,
which needs no hypothesis but whose value is an expression in the hom-set bijections of `adj₁`
and `adj'`. Here they have both disappeared: the value mentions only the 2-cell `c` and the
functor `I`. That is what makes the statement usable when `adj₁` and `adj'` are chosen data, so
that nothing is known about their units beyond `hc` itself. -/
theorem homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp_of_unit {C : Type u₁}
    [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {F' : C ⥤ E} {G' : E ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (e : I ⋙ G ≅ G') (adj' : F' ⊣ G') (c : F ⟶ F' ⋙ I)
    (hc : ∀ X : C, adj₁.unit.app X ≫ G.map (c.app X) ≫ e.hom.app (F'.obj X) =
      adj'.unit.app X)
    (X : C) {Y : E} (g : F'.obj X ⟶ Y) :
    adj₂.homEquiv (F.obj X) Y
        ((leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj').hom.app X ≫ g) =
      c.app X ≫ I.map g := by
  rw [homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp]
  refine (Equiv.symm_apply_eq _).mpr ?_
  rw [homEquiv_unit, homEquiv_unit, ← hc X]
  have hnat : G'.map g ≫ e.inv.app Y = e.inv.app (F'.obj X) ≫ (I ⋙ G).map g :=
    e.inv.naturality g
  rw [Category.assoc, Category.assoc, hnat]
  simp

/-- **The comparison of a composite left adjoint is the counit of the outer adjunction.**

In the situation of
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp_of_unit`, the
comparison's component at `X` is `H` applied to the 2-cell `c` at `X`, followed by the counit of
`adj₂`. Neither `adj₁` nor `adj'` occurs: the comparison is read off `c` and the outer adjunction
alone.

This is the case `g = 𝟙` of that lemma, the two sides having the same transpose — the right-hand
side because the transpose of `H` of a morphism followed by the counit is the morphism itself,
which is `CategoryTheory.Adjunction.homEquiv_counit` read backwards. -/
theorem leftAdjointUniq_comp_ofNatIsoRight_hom_app_of_unit {C : Type u₁}
    [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {E : Type u₃} [Category.{v₃} E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {I : E ⥤ D} {F' : C ⥤ E} {G' : E ⥤ C}
    (adj₁ : F ⊣ G) (adj₂ : H ⊣ I) (e : I ⋙ G ≅ G') (adj' : F' ⊣ G') (c : F ⟶ F' ⋙ I)
    (hc : ∀ X : C, adj₁.unit.app X ≫ G.map (c.app X) ≫ e.hom.app (F'.obj X) =
      adj'.unit.app X)
    (X : C) :
    (leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj').hom.app X =
      H.map (c.app X) ≫ adj₂.counit.app (F'.obj X) := by
  refine (adj₂.homEquiv (F.obj X) (F'.obj X)).injective ?_
  rw [show H.map (c.app X) ≫ adj₂.counit.app (F'.obj X) =
        (adj₂.homEquiv (F.obj X) (F'.obj X)).symm (c.app X) from
      (homEquiv_counit adj₂ (F.obj X) (F'.obj X) (c.app X)).symm,
    Equiv.apply_symm_apply,
    show (leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj').hom.app X =
        (leftAdjointUniq ((adj₁.comp adj₂).ofNatIsoRight e) adj').hom.app X ≫
          𝟙 (F'.obj X) from (Category.comp_id _).symm,
    homEquiv_leftAdjointUniq_comp_ofNatIsoRight_hom_app_comp_of_unit adj₁ adj₂ e adj' c hc X]
  simp

end CategoryTheory.Adjunction

end
