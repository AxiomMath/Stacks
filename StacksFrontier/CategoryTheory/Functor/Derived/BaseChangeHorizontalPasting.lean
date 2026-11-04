module

public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePasting

/-!
# Horizontal pasting of base change maps of right derived functors

Consider two squares of functors side by side,
```
K₁ --Kt₁--> K₂ --Kt₂--> K₃
|           |           |
Ft₁         Ft₂         Ft₃
v           v           v
K₄ --Lt₁--> K₅ --Lt₂--> K₆
```
with isomorphisms `e₁ : Ft₁ ⋙ Lt₁ ≅ Kt₁ ⋙ Ft₂` and `e₂ : Ft₂ ⋙ Lt₂ ≅ Kt₂ ⋙ Ft₃`, and an outer
rectangle with horizontal functors `Kt ≅ Kt₁ ⋙ Kt₂`, `Lt ≅ Lt₁ ⋙ Lt₂` and an isomorphism
`e : Ft₁ ⋙ Lt ≅ Kt ⋙ Ft₃` which is the pasting of `e₁` and `e₂`. Each square, and the rectangle,
has a base change map `Stacks.DerivedBaseChange.squareMap` between the right derived functors of
the vertical functors. If the functors induced on the localizations by the composite horizontal
functors are identified with the composites of the induced functors compatibly with the
identifications of the underived functors, then the base change map of the rectangle is the
composite of the base change maps of the two squares.

In the situation of the source the horizontal functors are the functors induced on homotopy
categories by the exact functors `g'_!`, `g_!`, `h'_!`, `h_!` and `(g ∘ g')_!`, `(h ∘ h')_!`, and
this is [Stacks, Tag 0F7D].

## Main definitions

* `Stacks.DerivedBaseChange.HorizontalPasteLaw`: the pasting law for two squares side by side,
  an isomorphism of the outer rectangle and comparisons of the composite horizontal functors.

## Main results

* `Stacks.DerivedBaseChange.HorizontalPasteLaw.conj`: the pasting law is preserved by
  conjugating all functors by isomorphisms (`Stacks.DerivedBaseChange.squareIsoTransport`).
* `Stacks.DerivedBaseChange.HorizontalPasteLaw.of_faithful`: the pasting law is reflected by
  faithful functors along which the functors in sight are lifted.
* `Stacks.DerivedBaseChange.homotopySquareIso_horizontal_paste`: the pasting law passes to the
  induced square isomorphisms of homotopy categories.
* `Stacks.DerivedBaseChange.squareMap_horizontal_paste`: the base change map of the outer
  rectangle is the composite of the base change maps of the two squares.

## References

* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0F7D](https://stacks.math.columbia.edu/tag/0F7D)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.DerivedBaseChange

section Law

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {C₃ : Type*} [Category* C₃]
  {C₄ : Type*} [Category* C₄] {C₅ : Type*} [Category* C₅] {C₆ : Type*} [Category* C₆]
  {a₁ : C₁ ⥤ C₂} {a₂ : C₂ ⥤ C₃} {a : C₁ ⥤ C₃} {b₁ : C₄ ⥤ C₅} {b₂ : C₅ ⥤ C₆} {b : C₄ ⥤ C₆}
  {v₁ : C₁ ⥤ C₄} {v₂ : C₂ ⥤ C₅} {v₃ : C₃ ⥤ C₆}

/-- **The horizontal pasting law** for two squares `e₁ : v₁ ⋙ b₁ ≅ a₁ ⋙ v₂` and
`e₂ : v₂ ⋙ b₂ ≅ a₂ ⋙ v₃` side by side, an isomorphism `e : v₁ ⋙ b ≅ a ⋙ v₃` of the outer
rectangle and identifications `cA : a₁ ⋙ a₂ ≅ a`, `cB : b₁ ⋙ b₂ ≅ b` of the composite horizontal
functors: `cB` followed by `e` is `e₁`, followed by `e₂` and by `cA`. -/
def HorizontalPasteLaw (cA : a₁ ⋙ a₂ ≅ a) (cB : b₁ ⋙ b₂ ≅ b) (e₁ : v₁ ⋙ b₁ ≅ a₁ ⋙ v₂)
    (e₂ : v₂ ⋙ b₂ ≅ a₂ ⋙ v₃) (e : v₁ ⋙ b ≅ a ⋙ v₃) : Prop :=
  ∀ X : C₁, cB.hom.app (v₁.obj X) ≫ e.hom.app X =
    b₂.map (e₁.hom.app X) ≫ e₂.hom.app (a₁.obj X) ≫ v₃.map (cA.hom.app X)

end Law

section Conjugation

/-! ### Transporting the horizontal pasting law along isomorphisms -/

variable {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂] {C₃ : Type*} [Category* C₃]
  {C₄ : Type*} [Category* C₄] {C₅ : Type*} [Category* C₅] {C₆ : Type*} [Category* C₆]
  {a₁ p₁ : C₁ ⥤ C₂} {a₂ p₂ : C₂ ⥤ C₃} {a p : C₁ ⥤ C₃}
  {b₁ q₁ : C₄ ⥤ C₅} {b₂ q₂ : C₅ ⥤ C₆} {b q : C₄ ⥤ C₆}
  {v₁ r₁ : C₁ ⥤ C₄} {v₂ r₂ : C₂ ⥤ C₅} {v₃ r₃ : C₃ ⥤ C₆}

/-- **The horizontal pasting law is preserved by conjugating every functor by isomorphisms.**
If squares `sq₁`, `sq₂`, `sq` of functors `pᵢ`, `qᵢ`, `rᵢ` and comparisons `cp`, `cq` of the
composite horizontal functors satisfy the pasting law, so do the squares obtained by replacing
each `pᵢ`, `qᵢ` by an isomorphic `aᵢ`, `bᵢ` and each `rᵢ` by an isomorphic `vᵢ`, with the
comparisons transported accordingly. -/
lemma HorizontalPasteLaw.conj
    (na₁ : a₁ ≅ p₁) (na₂ : a₂ ≅ p₂) (na : a ≅ p) (nb₁ : b₁ ≅ q₁) (nb₂ : b₂ ≅ q₂) (nb : b ≅ q)
    (s₁ : r₁ ≅ v₁) (s₂ : r₂ ≅ v₂) (s₃ : r₃ ≅ v₃)
    {sq₁ : r₁ ⋙ q₁ ≅ p₁ ⋙ r₂} {sq₂ : r₂ ⋙ q₂ ≅ p₂ ⋙ r₃} {sq : r₁ ⋙ q ≅ p ⋙ r₃}
    {cp : p₁ ⋙ p₂ ≅ p} {cq : q₁ ⋙ q₂ ≅ q} (hP : HorizontalPasteLaw cp cq sq₁ sq₂ sq) :
    HorizontalPasteLaw
      (Functor.isoWhiskerRight na₁ a₂ ≪≫ Functor.isoWhiskerLeft p₁ na₂ ≪≫ cp ≪≫ na.symm)
      (Functor.isoWhiskerRight nb₁ b₂ ≪≫ Functor.isoWhiskerLeft q₁ nb₂ ≪≫ cq ≪≫ nb.symm)
      (squareIsoTransport s₁ s₂ na₁ nb₁ sq₁) (squareIsoTransport s₂ s₃ na₂ nb₂ sq₂)
      (squareIsoTransport s₁ s₃ na nb sq) := by
  intro F
  have hfac := cq.hom.naturality (s₁.inv.app F)
  have hS := NatIso.naturality_2 s₂ (na₁.inv.app F)
  have hSq := sq₂.hom.naturality (na₁.inv.app F)
  have hSf := s₃.hom.naturality (p₂.map (na₁.inv.app F))
  have hSf' := s₃.hom.naturality (cp.hom.app F)
  have hN : p₂.map (na₁.inv.app F) ≫ na₂.inv.app (a₁.obj F) ≫ a₂.map (na₁.hom.app F) ≫
      na₂.hom.app (p₁.obj F) = 𝟙 _ := by
    rw [← na₂.inv.naturality_assoc, ← Functor.map_comp_assoc]
    simp
  simp only [Functor.comp_obj, Functor.comp_map] at hfac hSq hSf hSf'
  simp only [squareIsoTransport, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 1
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  refine Eq.trans ?_ (NatTrans.naturality_assoc nb₂.hom _ _).symm
  congr 1
  rw [reassoc_of% hfac.symm, reassoc_of% (hP F)]
  simp only [Functor.map_comp, Category.assoc]
  congr 2
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc, hS]
  rw [reassoc_of% hSq]
  congr 1
  rw [reassoc_of% hSf, reassoc_of% hSf']
  congr 1
  simp only [← Functor.map_comp, reassoc_of% hN]

end Conjugation

section Faithful

/-! ### Transporting the horizontal pasting law along faithful functors -/

variable {𝓜₁ : Type*} [Category* 𝓜₁] {𝓜₂ : Type*} [Category* 𝓜₂] {𝓜₃ : Type*} [Category* 𝓜₃]
  {𝓜₄ : Type*} [Category* 𝓜₄] {𝓜₅ : Type*} [Category* 𝓜₅] {𝓜₆ : Type*} [Category* 𝓜₆]
  {𝓐₁ : Type*} [Category* 𝓐₁] {𝓐₂ : Type*} [Category* 𝓐₂] {𝓐₃ : Type*} [Category* 𝓐₃]
  {𝓐₄ : Type*} [Category* 𝓐₄] {𝓐₅ : Type*} [Category* 𝓐₅] {𝓐₆ : Type*} [Category* 𝓐₆]
  {φ₁ : 𝓜₁ ⥤ 𝓐₁} {φ₂ : 𝓜₂ ⥤ 𝓐₂} {φ₃ : 𝓜₃ ⥤ 𝓐₃} {φ₄ : 𝓜₄ ⥤ 𝓐₄} {φ₅ : 𝓜₅ ⥤ 𝓐₅}
  {φ₆ : 𝓜₆ ⥤ 𝓐₆}
  {a₁ₘ : 𝓜₁ ⥤ 𝓜₂} {a₂ₘ : 𝓜₂ ⥤ 𝓜₃} {aₘ : 𝓜₁ ⥤ 𝓜₃} {b₁ₘ : 𝓜₄ ⥤ 𝓜₅} {b₂ₘ : 𝓜₅ ⥤ 𝓜₆}
  {bₘ : 𝓜₄ ⥤ 𝓜₆} {v₁ₘ : 𝓜₁ ⥤ 𝓜₄} {v₂ₘ : 𝓜₂ ⥤ 𝓜₅} {v₃ₘ : 𝓜₃ ⥤ 𝓜₆}
  {a₁ : 𝓐₁ ⥤ 𝓐₂} {a₂ : 𝓐₂ ⥤ 𝓐₃} {a : 𝓐₁ ⥤ 𝓐₃} {b₁ : 𝓐₄ ⥤ 𝓐₅} {b₂ : 𝓐₅ ⥤ 𝓐₆}
  {b : 𝓐₄ ⥤ 𝓐₆} {v₁ : 𝓐₁ ⥤ 𝓐₄} {v₂ : 𝓐₂ ⥤ 𝓐₅} {v₃ : 𝓐₃ ⥤ 𝓐₆}

/-- **Horizontal pasting is reflected by faithful functors.** Suppose functors `Xₘ` between
categories `𝓜ᵢ` are lifts of functors `X` between categories `𝓐ᵢ` along functors
`φᵢ : 𝓜ᵢ ⥤ 𝓐ᵢ`, through isomorphisms `ηX : Xₘ ⋙ φ ≅ φ ⋙ X`, and that the isomorphisms of squares
and of composites with subscript `ₘ` lift the ones without, in the sense that `φ` takes their
components to those of the latter conjugated by the `η`. If `φ₆` is faithful and the latter
satisfy the horizontal pasting law, so do their lifts. -/
lemma HorizontalPasteLaw.of_faithful [φ₆.Faithful]
    (ηa₁ : a₁ₘ ⋙ φ₂ ≅ φ₁ ⋙ a₁) (ηa₂ : a₂ₘ ⋙ φ₃ ≅ φ₂ ⋙ a₂) (ηa : aₘ ⋙ φ₃ ≅ φ₁ ⋙ a)
    (ηb₁ : b₁ₘ ⋙ φ₅ ≅ φ₄ ⋙ b₁) (ηb₂ : b₂ₘ ⋙ φ₆ ≅ φ₅ ⋙ b₂) (ηb : bₘ ⋙ φ₆ ≅ φ₄ ⋙ b)
    (ηv₁ : v₁ₘ ⋙ φ₄ ≅ φ₁ ⋙ v₁) (ηv₂ : v₂ₘ ⋙ φ₅ ≅ φ₂ ⋙ v₂) (ηv₃ : v₃ₘ ⋙ φ₆ ≅ φ₃ ⋙ v₃)
    {cAₘ : a₁ₘ ⋙ a₂ₘ ≅ aₘ} {cBₘ : b₁ₘ ⋙ b₂ₘ ≅ bₘ} {e₁ₘ : v₁ₘ ⋙ b₁ₘ ≅ a₁ₘ ⋙ v₂ₘ}
    {e₂ₘ : v₂ₘ ⋙ b₂ₘ ≅ a₂ₘ ⋙ v₃ₘ} {eₘ : v₁ₘ ⋙ bₘ ≅ aₘ ⋙ v₃ₘ}
    {cA : a₁ ⋙ a₂ ≅ a} {cB : b₁ ⋙ b₂ ≅ b} {e₁ : v₁ ⋙ b₁ ≅ a₁ ⋙ v₂}
    {e₂ : v₂ ⋙ b₂ ≅ a₂ ⋙ v₃} {e : v₁ ⋙ b ≅ a ⋙ v₃}
    (hcA : ∀ A, φ₃.map (cAₘ.hom.app A) = ηa₂.hom.app (a₁ₘ.obj A) ≫ a₂.map (ηa₁.hom.app A) ≫
      cA.hom.app (φ₁.obj A) ≫ ηa.inv.app A)
    (hcB : ∀ A, φ₆.map (cBₘ.hom.app A) = ηb₂.hom.app (b₁ₘ.obj A) ≫ b₂.map (ηb₁.hom.app A) ≫
      cB.hom.app (φ₄.obj A) ≫ ηb.inv.app A)
    (he₁ : ∀ A, φ₅.map (e₁ₘ.hom.app A) = ηb₁.hom.app (v₁ₘ.obj A) ≫ b₁.map (ηv₁.hom.app A) ≫
      e₁.hom.app (φ₁.obj A) ≫ v₂.map (ηa₁.inv.app A) ≫ ηv₂.inv.app (a₁ₘ.obj A))
    (he₂ : ∀ A, φ₆.map (e₂ₘ.hom.app A) = ηb₂.hom.app (v₂ₘ.obj A) ≫ b₂.map (ηv₂.hom.app A) ≫
      e₂.hom.app (φ₂.obj A) ≫ v₃.map (ηa₂.inv.app A) ≫ ηv₃.inv.app (a₂ₘ.obj A))
    (he : ∀ A, φ₆.map (eₘ.hom.app A) = ηb.hom.app (v₁ₘ.obj A) ≫ b.map (ηv₁.hom.app A) ≫
      e.hom.app (φ₁.obj A) ≫ v₃.map (ηa.inv.app A) ≫ ηv₃.inv.app (aₘ.obj A))
    (h : HorizontalPasteLaw cA cB e₁ e₂ e) : HorizontalPasteLaw cAₘ cBₘ e₁ₘ e₂ₘ eₘ := by
  intro A
  apply φ₆.map_injective
  have hb₂' := (NatIso.naturality_2 ηb₂ (e₁ₘ.hom.app A)).symm
  have hv₃' := (NatIso.naturality_2 ηv₃ (cAₘ.hom.app A)).symm
  have n₁ := cB.hom.naturality (ηv₁.hom.app A)
  have n₂ := e₂.hom.naturality (ηa₁.inv.app A)
  simp only [Functor.comp_obj, Functor.comp_map] at hb₂' hv₃' n₁ n₂
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, hcB, he, he₂, hb₂', he₁, hv₃', hcA]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  congr 2
  rw [← reassoc_of% n₁, reassoc_of% (h (φ₁.obj A))]
  congr 2
  rw [← b₂.map_comp_assoc (ηv₂.inv.app _), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% n₂, ← v₃.map_comp_assoc (ηa₂.inv.app _), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, ← v₃.map_comp_assoc (a₂.map _),
    ← a₂.map_comp, Iso.inv_hom_id_app]
  simp

end Faithful

section HomotopyCategory

/-! ### The horizontal pasting law on homotopy categories -/

variable {C₁ : Type*} [Category* C₁] [Preadditive C₁] {C₂ : Type*} [Category* C₂] [Preadditive C₂]
  {C₃ : Type*} [Category* C₃] [Preadditive C₃] {C₄ : Type*} [Category* C₄] [Preadditive C₄]
  {C₅ : Type*} [Category* C₅] [Preadditive C₅] {C₆ : Type*} [Category* C₆] [Preadditive C₆]
  {ι : Type*} (c : ComplexShape ι)
  {a₁ : C₁ ⥤ C₂} {a₂ : C₂ ⥤ C₃} {a : C₁ ⥤ C₃} {b₁ : C₄ ⥤ C₅} {b₂ : C₅ ⥤ C₆} {b : C₄ ⥤ C₆}
  {v₁ : C₁ ⥤ C₄} {v₂ : C₂ ⥤ C₅} {v₃ : C₃ ⥤ C₆}
  [a₁.Additive] [a₂.Additive] [a.Additive] [b₁.Additive] [b₂.Additive] [b.Additive]
  [v₁.Additive] [v₂.Additive] [v₃.Additive]

/-- **Horizontal pasting of square isomorphisms is inherited by the induced square isomorphisms
of homotopy categories.** -/
lemma homotopySquareIso_horizontal_paste {cA : a₁ ⋙ a₂ ≅ a} {cB : b₁ ⋙ b₂ ≅ b}
    {e₁ : v₁ ⋙ b₁ ≅ a₁ ⋙ v₂} {e₂ : v₂ ⋙ b₂ ≅ a₂ ⋙ v₃} {e : v₁ ⋙ b ≅ a ⋙ v₃}
    (h : HorizontalPasteLaw cA cB e₁ e₂ e) :
    HorizontalPasteLaw (Functor.mapHomotopyCategoryCompIso cA c)
      (Functor.mapHomotopyCategoryCompIso cB c) (homotopySquareIso c e₁)
      (homotopySquareIso c e₂) (homotopySquareIso c e) := by
  intro X
  obtain ⟨X, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  simp only [homotopySquareIso_hom_app, mapHomotopyCategoryCompIso_hom_app,
    HomotopyCategory.quotient_obj_as]
  change (HomotopyCategory.quotient C₆ c).map
        ((NatTrans.mapHomologicalComplex cB.hom c).app ((v₁.mapHomologicalComplex c).obj X)) ≫
      (HomotopyCategory.quotient C₆ c).map ((NatTrans.mapHomologicalComplex e.hom c).app X) =
    (HomotopyCategory.quotient C₆ c).map ((b₂.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex e₁.hom c).app X)) ≫
      (HomotopyCategory.quotient C₆ c).map
        ((NatTrans.mapHomologicalComplex e₂.hom c).app ((a₁.mapHomologicalComplex c).obj X)) ≫
      (HomotopyCategory.quotient C₆ c).map ((v₃.mapHomologicalComplex c).map
        ((NatTrans.mapHomologicalComplex cA.hom c).app X))
  simp only [← Functor.map_comp]
  congr 1
  ext n
  simpa using h (X.X n)

end HomotopyCategory

variable {K₁ : Type*} [Category* K₁] {K₂ : Type*} [Category* K₂]
  {K₃ : Type*} [Category* K₃] {K₄ : Type*} [Category* K₄]
  {K₅ : Type*} [Category* K₅] {K₆ : Type*} [Category* K₆]
  {D₁ : Type*} [Category* D₁] {D₂ : Type*} [Category* D₂]
  {D₃ : Type*} [Category* D₃] {D₄ : Type*} [Category* D₄]
  {D₅ : Type*} [Category* D₅] {D₆ : Type*} [Category* D₆]
  {Q₁ : K₁ ⥤ D₁} {Q₂ : K₂ ⥤ D₂} {Q₃ : K₃ ⥤ D₃} {Q₄ : K₄ ⥤ D₄} {Q₅ : K₅ ⥤ D₅} {Q₆ : K₆ ⥤ D₆}
  {Kt₁ : K₁ ⥤ K₂} {KD₁ : D₁ ⥤ D₂} {Kt₂ : K₂ ⥤ K₃} {KD₂ : D₂ ⥤ D₃}
  {Kt : K₁ ⥤ K₃} {KD : D₁ ⥤ D₃}
  {Lt₁ : K₄ ⥤ K₅} {LD₁ : D₄ ⥤ D₅} {Lt₂ : K₅ ⥤ K₆} {LD₂ : D₅ ⥤ D₆}
  {Lt : K₄ ⥤ K₆} {LD : D₄ ⥤ D₆}
  {Ft₁ : K₁ ⥤ K₄} {RF₁ : D₁ ⥤ D₄} {Ft₂ : K₂ ⥤ K₅} {RF₂ : D₂ ⥤ D₅}
  {Ft₃ : K₃ ⥤ K₆} {RF₃ : D₃ ⥤ D₆}
  (W₁ : MorphismProperty K₁) [Q₁.IsLocalization W₁]
  (W₂ : MorphismProperty K₂) [Q₂.IsLocalization W₂]

/-- **Horizontal pasting of base change maps.** Given two squares `e₁ : Ft₁ ⋙ Lt₁ ≅ Kt₁ ⋙ Ft₂`
and `e₂ : Ft₂ ⋙ Lt₂ ≅ Kt₂ ⋙ Ft₃` side by side, composite horizontal functors
`dK : Kt₁ ⋙ Kt₂ ≅ Kt` and `dL : Lt₁ ⋙ Lt₂ ≅ Lt`, and an isomorphism `e : Ft₁ ⋙ Lt ≅ Kt ⋙ Ft₃`
for the outer rectangle which is the pasting of `e₁` and `e₂` (the hypothesis `hpaste`), let
`cK : KD₁ ⋙ KD₂ ≅ KD` and `cL : LD₁ ⋙ LD₂ ≅ LD` identify the induced functors of the composites
with the composites of the induced functors, compatibly with `dK` and `dL` on the image of the
localizations (the hypotheses `hK` and `hL`). Then the base change map of the rectangle is the
identification `LD ≅ LD₁ ⋙ LD₂`, followed by the base change map of the left square, the base
change map of the right square, and the identification `KD₁ ⋙ KD₂ ≅ KD`. -/
theorem squareMap_horizontal_paste
    (φK₁ : Q₁ ⋙ KD₁ ≅ Kt₁ ⋙ Q₂) (φK₂ : Q₂ ⋙ KD₂ ≅ Kt₂ ⋙ Q₃) (φK : Q₁ ⋙ KD ≅ Kt ⋙ Q₃)
    (φL₁ : Q₄ ⋙ LD₁ ≅ Lt₁ ⋙ Q₅) (φL₂ : Q₅ ⋙ LD₂ ≅ Lt₂ ⋙ Q₆) (φL : Q₄ ⋙ LD ≅ Lt ⋙ Q₆)
    (α₁ : Ft₁ ⋙ Q₄ ⟶ Q₁ ⋙ RF₁) (α₂ : Ft₂ ⋙ Q₅ ⟶ Q₂ ⋙ RF₂) (α₃ : Ft₃ ⋙ Q₆ ⟶ Q₃ ⋙ RF₃)
    (dK : Kt₁ ⋙ Kt₂ ≅ Kt) (dL : Lt₁ ⋙ Lt₂ ≅ Lt) (cK : KD₁ ⋙ KD₂ ≅ KD) (cL : LD₁ ⋙ LD₂ ≅ LD)
    (hK : ∀ X : K₁, cK.hom.app (Q₁.obj X) = KD₂.map (φK₁.hom.app X) ≫
      φK₂.hom.app (Kt₁.obj X) ≫ Q₃.map (dK.hom.app X) ≫ φK.inv.app X)
    (hL : ∀ Y : K₄, cL.hom.app (Q₄.obj Y) = LD₂.map (φL₁.hom.app Y) ≫
      φL₂.hom.app (Lt₁.obj Y) ≫ Q₆.map (dL.hom.app Y) ≫ φL.inv.app Y)
    (e₁ : Ft₁ ⋙ Lt₁ ≅ Kt₁ ⋙ Ft₂) (e₂ : Ft₂ ⋙ Lt₂ ≅ Kt₂ ⋙ Ft₃) (e : Ft₁ ⋙ Lt ≅ Kt ⋙ Ft₃)
    (hpaste : HorizontalPasteLaw dK dL e₁ e₂ e)
    [(RF₁ ⋙ LD₁).IsRightDerivedFunctor (whiskerUnit α₁ LD₁) W₁]
    [(RF₂ ⋙ LD₂).IsRightDerivedFunctor (whiskerUnit α₂ LD₂) W₂]
    [(RF₁ ⋙ LD).IsRightDerivedFunctor (whiskerUnit α₁ LD) W₁] :
    squareMap W₁ φK φL α₁ α₃ e =
      Functor.whiskerLeft RF₁ cL.inv ≫ (Functor.associator RF₁ LD₁ LD₂).inv ≫
        Functor.whiskerRight (squareMap W₁ φK₁ φL₁ α₁ α₂ e₁) LD₂ ≫
        (Functor.associator KD₁ RF₂ LD₂).hom ≫
        Functor.whiskerLeft KD₁ (squareMap W₂ φK₂ φL₂ α₂ α₃ e₂) ≫
        (Functor.associator KD₁ KD₂ RF₃).inv ≫ Functor.whiskerRight cK.hom RF₃ := by
  apply (RF₁ ⋙ LD).rightDerived_ext (whiskerUnit α₁ LD) W₁
  ext X
  -- the identifications of the composites, read as relations between the comparison maps
  have hK' : φK₂.inv.app (Kt₁.obj X) ≫ KD₂.map (φK₁.inv.app X) ≫ cK.hom.app (Q₁.obj X) =
      Q₃.map (dK.hom.app X) ≫ φK.inv.app X := by
    rw [hK X, ← KD₂.map_comp_assoc]
    simp
  have hL' : cL.inv.app (Q₄.obj (Ft₁.obj X)) ≫ LD₂.map (φL₁.hom.app (Ft₁.obj X)) ≫
      φL₂.hom.app (Lt₁.obj (Ft₁.obj X)) =
      φL.hom.app (Ft₁.obj X) ≫ Q₆.map (dL.inv.app (Ft₁.obj X)) := by
    rw [← cancel_epi (cL.hom.app (Q₄.obj (Ft₁.obj X))), Iso.hom_inv_id_app_assoc,
      hL (Ft₁.obj X)]
    simp [← Q₆.map_comp]
  have he : e.hom.app X = dL.inv.app (Ft₁.obj X) ≫ Lt₂.map (e₁.hom.app X) ≫
      e₂.hom.app (Kt₁.obj X) ≫ Ft₃.map (dK.hom.app X) := by
    rw [← hpaste X, Iso.inv_hom_id_app_assoc]
  have hcL := cL.inv.naturality (α₁.app X)
  have hτ₂ := (squareMap W₂ φK₂ φL₂ α₂ α₃ e₂).naturality (φK₁.inv.app X)
  have hα₃ := α₃.naturality (dK.hom.app X)
  have hφL₂ := φL₂.hom.naturality (e₁.hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at hcL hτ₂ hα₃ hφL₂
  simp only [whiskerUnit, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_obj, Category.comp_id,
    Category.id_comp]
  rw [squareMap_fac_app, reassoc_of% hcL, ← LD₂.map_comp_assoc, squareMap_fac_app,
    LD₂.map_comp, LD₂.map_comp, LD₂.map_comp, Category.assoc, Category.assoc, Category.assoc,
    reassoc_of% hτ₂, squareMap_fac_app_assoc, ← RF₃.map_comp, ← RF₃.map_comp, hK',
    RF₃.map_comp, ← reassoc_of% hα₃, reassoc_of% hφL₂, reassoc_of% hL', he]
  simp only [Q₆.map_comp, Category.assoc]

end Stacks.DerivedBaseChange

end
