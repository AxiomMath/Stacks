module

public import StacksFrontier.CategoryTheory.KanExtension.DenseCompactSubcategory

/-! # Commuting with filtered colimits versus being a left Kan extension

Let `P` be a property of objects of `C` consisting of categorically compact objects
(Stacks 0FWX, i.e. Mathlib's `IsFinitelyPresentable`) such that every object of `C` is a
filtered colimit of objects satisfying `P`. This file proves the two implications that make
`P.ι` behave like the inclusion of a set of "finite" generators:

* `isLeftKanExtension_of_preservesFilteredColimits`: a functor `E : C ⥤ D` that commutes with
  filtered colimits is a left Kan extension of its own restriction `P.ι ⋙ E` along `P.ι`.
  Since `P.ι` is dense, `E` merely has to preserve the canonical colimit presentations.
* `preservesFilteredColimitsOfSize_right`: conversely, a pointwise left Kan extension along
  `P.ι` commutes with filtered colimits. Here compactness of the `P`-objects is what lets one
  push an arrow `A ⟶ colim Xλ` down to some `A ⟶ Xλ`, which produces the inverse of the
  canonical map `colim E(Xλ) ⟶ E(colim Xλ)`.

Together they say that restriction along `P.ι` is a bijection between filtered-colimit
preserving functors out of `C` and arbitrary functors out of the subcategory; this is the
content of Stacks 0FWY, assembled in `StacksFrontier.CategoryTheory.KanExtension.Extend`.
-/

@[expose] public section

open CategoryTheory Category Limits ObjectProperty

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- A finitely presentable object cannot tell two factorisations apart. Let `K` be a small
filtered diagram with colimit cocone `c` and let `A` be `w`-finitely presentable. If
`g₁ : A ⟶ K.obj l₁` and `g₂ : A ⟶ K.obj l₂` become equal in `c.pt`, then for every functor
`E : C ⥤ D` they induce the same morphism `E.obj A ⟶ colimit (K ⋙ E)`.

Indeed `g₁` and `g₂` are already coequalized by some `K.map u`, `K.map v` into a common index,
and the coprojections of `K ⋙ E` identify the two indices with that one. -/
lemma IsFinitelyPresentable.map_comp_colimit_ι_eq {A : C} [IsFinitelyPresentable.{w} A]
    {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ] {K : Λ ⥤ C} {c : Cocone K} (hc : IsColimit c)
    (E : C ⥤ D) [HasColimit (K ⋙ E)] {l₁ l₂ : Λ} (g₁ : A ⟶ K.obj l₁) (g₂ : A ⟶ K.obj l₂)
    (h : g₁ ≫ c.ι.app l₁ = g₂ ≫ c.ι.app l₂) :
    E.map g₁ ≫ colimit.ι (K ⋙ E) l₁ = E.map g₂ ≫ colimit.ι (K ⋙ E) l₂ := by
  obtain ⟨l₃, u, v, huv⟩ := IsFinitelyPresentable.exists_eq_of_isColimit hc g₁ g₂ h
  rw [← colimit.w (K ⋙ E) u, ← colimit.w (K ⋙ E) v, Functor.comp_map, Functor.comp_map,
    ← reassoc_of% E.map_comp, ← reassoc_of% E.map_comp, huv]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The comma categories `CostructuredArrow P.ι X` are filtered, finally `w`-small and locally
`w`-small. -/
private theorem costructuredArrow_ι_instances [LocallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X) (X : C) :
    IsFiltered (CostructuredArrow P.ι X) ∧ FinallySmall.{w} (CostructuredArrow P.ι X) ∧
      LocallySmall.{w} (CostructuredArrow P.ι X) :=
  ⟨isFiltered_costructuredArrow_ι P hP hgen X, finallySmall_costructuredArrow_ι P hP hgen X,
    locallySmall_of_faithful.{w} (CostructuredArrow.proj P.ι X)⟩

/-- A functor commuting with `w`-filtered colimits is a left Kan extension of its restriction
to the full subcategory of `P`-objects, the unit being the identity. -/
theorem isLeftKanExtension_of_preservesFilteredColimits
    [LocallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
    (E : C ⥤ D) [PreservesFilteredColimitsOfSize.{w, w} E] :
    Functor.IsLeftKanExtension E (𝟙 (P.ι ⋙ E)) := by
  have hd : P.ι.IsDense := isDense_ι P hP hgen
  have key : ∀ X : C,
      Nonempty ((Functor.LeftExtension.mk E (𝟙 (P.ι ⋙ E))).IsPointwiseLeftKanExtensionAt X) := by
    intro X
    obtain ⟨_, _, _⟩ := costructuredArrow_ι_instances P hP hgen X
    have : PreservesColimitsOfShape (CostructuredArrow P.ι X) E :=
      FinallySmall.preservesColimitsOfShape_of_isFiltered _ E
    exact ⟨IsColimit.ofIsoColimit (isColimitOfPreserves E (P.ι.denseAt X))
      (Cocone.ext (Iso.refl _))⟩
  exact Functor.LeftExtension.IsPointwiseLeftKanExtension.isLeftKanExtension
    (fun X ↦ (key X).some)

/-- Every `P`-object over the vertex of a small filtered colimit factors through the diagram:
compactness of the `P`-objects lets one choose, for each `g : CostructuredArrow P.ι c.pt`, an
index `lam g` and a factorisation `gg g` of the structure map `g.hom` through `K.obj (lam g)`. -/
theorem exists_factorisation (hP : P ≤ isFinitelyPresentable.{w} C)
    {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ] {K : Λ ⥤ C} {c : Cocone K} (hc : IsColimit c) :
    ∃ (lam : CostructuredArrow P.ι c.pt → Λ)
      (gg : ∀ g, P.ι.obj g.left ⟶ K.obj (lam g)), ∀ g, gg g ≫ c.ι.app (lam g) = g.hom := by
  choose lam gg hgg using fun g : CostructuredArrow P.ι c.pt ↦
    have : IsFinitelyPresentable.{w} (P.ι.obj g.left) := hP _ g.left.2
    IsFinitelyPresentable.exists_hom_of_isColimit hc g.hom
  exact ⟨lam, gg, hgg⟩

section

variable [HasFilteredColimitsOfSize.{w, w} D] (hP : P ≤ isFinitelyPresentable.{w} C)
  {F' : P.FullSubcategory ⥤ D} (Ex : Functor.LeftExtension P.ι F')
  {Λ : Type w} [SmallCategory Λ] [IsFiltered Λ] {K : Λ ⥤ C} {c : Cocone K} (hc : IsColimit c)
  (lam : CostructuredArrow P.ι c.pt → Λ) (gg : ∀ g, P.ι.obj g.left ⟶ K.obj (lam g))
  (hgg : ∀ g, gg g ≫ c.ι.app (lam g) = g.hom)

/-- The cocone on `CostructuredArrow.proj P.ι c.pt ⋙ F'` with vertex `colim E(Kλ)` assembled from
a factorisation `(lam, gg)` as supplied by `exists_factorisation`: the component at `g` maps
`F'(g.left)` into `colim E(Kλ)` through `E(gg g)`.

Its naturality is the assertion that the component does not depend on the chosen factorisation,
which is `IsFinitelyPresentable.map_comp_colimit_ι_eq`. -/
noncomputable def factorisationCocone :
    Cocone (CostructuredArrow.proj P.ι c.pt ⋙ F') where
  pt := colimit (K ⋙ Ex.right)
  ι :=
    { app := fun g ↦ Ex.hom.app g.left ≫ Ex.right.map (gg g) ≫ colimit.ι (K ⋙ Ex.right) (lam g)
      naturality := fun g₁ g₂ φ ↦ by
        have : IsFinitelyPresentable.{w} (P.ι.obj g₁.left) := hP _ g₁.left.2
        have h := Ex.hom.naturality φ.left
        dsimp at h ⊢
        rw [Category.comp_id, reassoc_of% h,
          IsFinitelyPresentable.map_comp_colimit_ι_eq hc Ex.right (gg g₁)
            (P.ι.map φ.left ≫ gg g₂) (by rw [hgg g₁, assoc, hgg g₂, CostructuredArrow.w φ]),
          Ex.right.map_comp, assoc]
        rfl }

include hP hc hgg in
/-- The canonical comparison `colim E(Kλ) ⟶ E(colim Kλ)` out of a small filtered colimit is an
isomorphism as soon as some `θ : E(colim Kλ) ⟶ colim E(Kλ)` has its components on the Kan
extension colimit computed by a factorisation `(lam, gg)`: such a `θ` is then a two-sided inverse.

`θ ≫ comparison = 𝟙` is checked on each `g : CostructuredArrow P.ι c.pt` and reduces to
`hgg g`. For `comparison ≫ θ = 𝟙` one compares on each coprojection `colimit.ι (K ⋙ E) l`,
which turns the goal into one about maps out of the Kan extension colimit at `K.obj l`; there the
independence lemma `IsFinitelyPresentable.map_comp_colimit_ι_eq` applies with the two
factorisations `gg _` and `g.hom` of the structure map `g.hom ≫ c.ι.app l`. -/
theorem isIso_colimit_desc_mapCocone_of_fac
    (θ : Ex.right.obj c.pt ⟶ colimit (K ⋙ Ex.right))
    (hθ : ∀ g, (Ex.coconeAt c.pt).ι.app g ≫ θ
      = Ex.hom.app g.left ≫ Ex.right.map (gg g) ≫ colimit.ι (K ⋙ Ex.right) (lam g))
    (hEx : Ex.IsPointwiseLeftKanExtension) :
    IsIso (colimit.desc (K ⋙ Ex.right) (Ex.right.mapCocone c)) := by
  refine ⟨θ, colimit.hom_ext fun l ↦ Eq.trans ?_ (Category.comp_id _).symm,
    (hEx c.pt).hom_ext fun g ↦ Eq.trans ?_ (Category.comp_id _).symm⟩
  · rw [← assoc, colimit.ι_desc]
    dsimp
    refine (hEx (K.obj l)).hom_ext fun g ↦ ?_
    have : IsFinitelyPresentable.{w}
        (P.ι.obj (CostructuredArrow.mk (Y := g.left) (g.hom ≫ c.ι.app l)).left) := hP _ g.left.2
    have key : (Ex.coconeAt (K.obj l)).ι.app g ≫ Ex.right.map (c.ι.app l)
        = (Ex.coconeAt c.pt).ι.app (CostructuredArrow.mk (Y := g.left) (g.hom ≫ c.ι.app l)) := by
      dsimp
      rw [assoc, ← Ex.right.map_comp]
    rw [reassoc_of% key, hθ,
      IsFinitelyPresentable.map_comp_colimit_ι_eq hc Ex.right
        (gg (CostructuredArrow.mk (Y := g.left) (g.hom ≫ c.ι.app l))) g.hom
        (hgg (CostructuredArrow.mk (Y := g.left) (g.hom ≫ c.ι.app l)))]
    dsimp
    rw [assoc]
  · rw [reassoc_of% hθ g, colimit.ι_desc]
    dsimp
    rw [← Ex.right.map_comp, hgg g]

end

/-- A pointwise left Kan extension along `P.ι` commutes with `w`-filtered colimits.

Write `X = colim Xλ` for a small filtered diagram. Compactness of the `P`-objects factors
every arrow `A ⟶ X` with `A` in `P` through some `Xλ` (`exists_factorisation`), and the resulting
arrow `F'(A) ⟶ colim E(Xλ)` is independent of the factorisation, so it assembles into
`factorisationCocone`; the map it induces out of the Kan extension colimit is inverse to the
canonical comparison (`isIso_colimit_desc_mapCocone_of_fac`). -/
theorem preservesFilteredColimitsOfSize_right [HasFilteredColimitsOfSize.{w, w} D]
    (hP : P ≤ isFinitelyPresentable.{w} C)
    {F' : P.FullSubcategory ⥤ D} (Ex : Functor.LeftExtension P.ι F')
    (hEx : Ex.IsPointwiseLeftKanExtension) :
    PreservesFilteredColimitsOfSize.{w, w} Ex.right := by
  refine ⟨fun Λ _ _ ↦ ⟨fun {K} ↦ ⟨fun {c} hc ↦ ?_⟩⟩⟩
  obtain ⟨lam, gg, hgg⟩ := exists_factorisation P hP hc
  have := isIso_colimit_desc_mapCocone_of_fac P hP Ex hc lam gg hgg
    ((hEx c.pt).desc (factorisationCocone P hP Ex hc lam gg hgg)) ((hEx c.pt).fac _) hEx
  exact ⟨IsColimit.ofIsoColimit (colimit.isColimit (K ⋙ Ex.right))
    (Cocone.ext (asIso (colimit.desc (K ⋙ Ex.right) (Ex.right.mapCocone c))) (fun l ↦ by simp))⟩

/-- Under the hypotheses of Stacks 0FWY, every functor out of the full subcategory of
`P`-objects admits a pointwise left Kan extension along `P.ι`: the indexing comma categories
are filtered and finally `w`-small, so the required colimits are `w`-filtered ones. -/
theorem hasPointwiseLeftKanExtension_ι [HasFilteredColimitsOfSize.{w, w} D]
    [LocallySmall.{w} P.FullSubcategory]
    (hP : P ≤ isFinitelyPresentable.{w} C) (hgen : ∀ X : C, P.ind.{w} X)
    (F' : P.FullSubcategory ⥤ D) :
    P.ι.HasPointwiseLeftKanExtension F' := by
  intro Y
  obtain ⟨_, _, _⟩ := costructuredArrow_ι_instances P hP hgen Y
  exact Functor.Final.hasColimit_of_comp
    (FinallySmall.fromFilteredFinalModel.{w} (CostructuredArrow P.ι Y))

end ObjectProperty

end CategoryTheory
