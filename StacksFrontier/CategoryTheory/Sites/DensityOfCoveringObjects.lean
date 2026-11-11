module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.CategoryTheory.Sites.Density

/-!
# Sheaves as colimits of sheafified representables of a covering family of objects

Every sheaf of sets `F` on a site is the colimit of the sheafified representables `h_U^#` over
its category of elements (`CategoryTheory.Sheaf.colimitOfRepresentable`). If `E` is a property
of objects such that every object of the site has a covering by objects satisfying `E`, the
same holds with the diagram restricted to the pairs `(U, s)` with `U` in `E` and `s ∈ F(U)`.

The proof identifies a cocone with point `G` over the restricted diagram with a morphism of
presheaves `F|_E ⟶ G|_E` on the full subcategory of `E`, via Yoneda's lemma for sheaves
(`CategoryTheory.Sheaf.sectionEquiv`). Since the inclusion of `E` is cover-dense, such a
morphism extends uniquely to a morphism `F ⟶ G` of sheaves
(`CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom`).

## Main definitions

* `CategoryTheory.Sheaf.restrictedIndexingDiagram`: the diagram `(U, s) ↦ U` over the opposite
  of the category of elements of `F` restricted to `E`.
* `CategoryTheory.Sheaf.restrictedCocone`: the cocone on the sheafified representables of the
  restricted diagram with point `F`.

## Main results

* `CategoryTheory.Sheaf.isCoverDense_ι_of_forall_exists_covering`: if every object has a
  covering by objects of `E`, the inclusion of `E` is cover-dense.
* `CategoryTheory.Sheaf.isColimitRestrictedCocone`: the restricted cocone is a colimit.
* `CategoryTheory.Sheaf.exists_isColimit_sheafifiedYoneda`: Stacks 0GLW, both parts.

## References

* [Stacks Project, Tag 0GLW](https://stacks.math.columbia.edu/tag/0GLW)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J (Type max u v)]

/-- If every object `X` of the site has a covering `{U_j ⟶ X}` by objects satisfying `E`, then
the inclusion of the full subcategory of `E` is cover-dense. -/
theorem isCoverDense_ι_of_forall_exists_covering (E : ObjectProperty C)
    (hE : ∀ X : C, ∃ R : Presieve X, Sieve.generate R ∈ J X ∧ ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → E Y) :
    E.ι.IsCoverDense J where
  is_cover X := by
    obtain ⟨R, hR, hRE⟩ := hE X
    refine J.superset_covering ?_ hR
    rintro Y f ⟨Z, h, g, hg, rfl⟩
    exact ⟨{ obj := ⟨Z, hRE g hg⟩, lift := h, map := g }⟩

variable (F : Sheaf J (Type max u v)) (E : ObjectProperty C)

/-- The diagram `(U, s) ↦ U` over the opposite of the category of elements of the restriction of
`F` to the full subcategory of `E`: its objects are the pairs `(U, s)` with `U` in `E` and
`s ∈ F(U)`. -/
def restrictedIndexingDiagram : (E.ι.op ⋙ F.obj).Elementsᵒᵖ ⥤ C :=
  (CategoryOfElements.π (E.ι.op ⋙ F.obj)).leftOp ⋙ E.ι

/-- Every object of the restricted diagram satisfies `E`. -/
theorem restrictedIndexingDiagram_obj_mem (i : (E.ι.op ⋙ F.obj).Elementsᵒᵖ) :
    E ((restrictedIndexingDiagram J F E).obj i) :=
  (unop i).1.unop.property

/-- The cocone on the sheafified representables `h_U^#` of the restricted diagram with point
`F`, whose leg at `(U, s)` is the morphism `h_U^# ⟶ F` corresponding to `s`. -/
noncomputable def restrictedCocone :
    Cocone (restrictedIndexingDiagram J F E ⋙ sheafifiedYoneda J) where
  pt := F
  ι :=
    { app := fun i => (sectionEquiv J).symm (unop i).2
      naturality := fun i j f => by
        have hf : F.obj.map (f.unop.1.unop.hom).op (unop j).2 = (unop i).2 := f.unop.2
        exact (sectionEquiv_symm_map J f.unop.1.unop.hom (unop j).2).symm.trans
          ((congrArg (sectionEquiv J).symm hf).trans (Category.comp_id _).symm) }

/-- The section of `F` over `U` corresponding to the leg of the restricted cocone at `(U, s)` is
`s`. -/
theorem sectionEquiv_restrictedCocone_ι_app (i : (E.ι.op ⋙ F.obj).Elementsᵒᵖ) :
    sectionEquiv J ((restrictedCocone J F E).ι.app i) = (unop i).2 :=
  Equiv.apply_symm_apply _ _

variable {J F E}

/-- The morphism of presheaves `F|_E ⟶ G|_E` on the full subcategory of `E` underlying a cocone
with point `G` over the restricted diagram. -/
noncomputable def restrictedCoconeHom
    (s : Cocone (restrictedIndexingDiagram J F E ⋙ sheafifiedYoneda J)) :
    E.ι.op ⋙ F.obj ⟶ E.ι.op ⋙ s.pt.obj where
  app U := TypeCat.ofHom fun x =>
    sectionEquiv J (s.ι.app (op ((E.ι.op ⋙ F.obj).elementsMk U x)))
  naturality U V g := by
    ext x
    have hw := s.w (Functor.Elements.homMk (x := (E.ι.op ⋙ F.obj).elementsMk U x)
      (y := (E.ι.op ⋙ F.obj).elementsMk V ((E.ι.op ⋙ F.obj).map g x)) g rfl).op
    exact (congrArg (sectionEquiv J) hw.symm).trans (sectionEquiv_map_comp J _ _)

/-- If every object of the site has a covering by objects of `E`, the cocone on the sheafified
representables `h_U^#` of the pairs `(U, s)` with `U` in `E` and `s ∈ F(U)` is a colimit: `F` is
the colimit of the restricted diagram. -/
noncomputable def isColimitRestrictedCocone [E.ι.IsCoverDense J] :
    IsColimit (restrictedCocone J F E) where
  desc s := ObjectProperty.homMk (Functor.IsCoverDense.restrictHomEquivHom (G := E.ι)
    (ℱ' := s.pt) (restrictedCoconeHom s))
  fac s i := by
    apply (sectionEquiv J).injective
    rw [sectionEquiv_comp, sectionEquiv_restrictedCocone_ι_app]
    have h := congrArg (fun τ => τ.app (unop i).1 (unop i).2)
      ((Functor.IsCoverDense.restrictHomEquivHom (G := E.ι) (ℱ' := s.pt)).left_inv
        (restrictedCoconeHom s))
    exact h
  uniq s m hm := by
    apply Sheaf.hom_ext
    have key : (Functor.IsCoverDense.restrictHomEquivHom (G := E.ι) (ℱ := F.obj)
        (ℱ' := s.pt)).symm m.hom = restrictedCoconeHom s := by
      ext U x
      exact (congrArg (fun y => m.hom.app _ y)
        (sectionEquiv_restrictedCocone_ι_app J F E
          (op ((E.ι.op ⋙ F.obj).elementsMk U x)))).symm.trans
          ((sectionEquiv_comp J _ m).symm.trans
            (congrArg (sectionEquiv J) (hm (op ((E.ι.op ⋙ F.obj).elementsMk U x)))))
    exact (Equiv.symm_apply_eq _).mp key

/-- **Stacks 0GLW.** Let `F` be a sheaf of sets on a site. Then there is a diagram
`I ⥤ C`, `i ↦ U_i`, such that `F` is the colimit of the sheafified representables `h_{U_i}^#`.
Moreover, if `E` is a property of objects such that every object of the site has a covering by
objects satisfying `E`, then the diagram may be taken with `U_i` in `E` for every `i`. -/
@[stacks 0GLW "Both parts. The diagram of the first part is the one of
  `CategoryTheory.Sheaf.colimitOfRepresentable`, over the opposite of the category of elements
  of `F`; for the second part it is restricted to the pairs `(U, s)` with `U` in `E`, and the
  colimit property is `CategoryTheory.Sheaf.isColimitRestrictedCocone`, deduced from Mathlib's
  `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom`. The equality `F = colim h_{U_i}^#`
  is a cocone with point `F` that is a colimit cocone. A covering of `X` by elements of `E` is a
  presieve on `X` of arrows with domains in `E` generating a covering sieve. The sheafified
  representable `h_U^#` is `CategoryTheory.Sheaf.sheafifiedYoneda`, with sections in
  `Type (max u v)`."]
theorem exists_isColimit_sheafifiedYoneda (F : Sheaf J (Type max u v)) :
    (∃ (I : Type (max u v)) (_ : Category.{v} I) (D : I ⥤ C)
        (ι : D ⋙ sheafifiedYoneda J ⟶ (Functor.const I).obj F),
        Nonempty (IsColimit (Cocone.mk F ι))) ∧
      ∀ E : ObjectProperty C,
        (∀ X : C, ∃ R : Presieve X, Sieve.generate R ∈ J X ∧
          ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → E Y) →
        ∃ (I : Type (max u v)) (_ : Category.{v} I) (D : I ⥤ C)
          (ι : D ⋙ sheafifiedYoneda J ⟶ (Functor.const I).obj F),
          (∀ i, E (D.obj i)) ∧ Nonempty (IsColimit (Cocone.mk F ι)) := by
  refine ⟨⟨_, inferInstance, indexingDiagram J F, (coconeOfRepresentable J F).ι,
    ⟨colimitOfRepresentable J F⟩⟩, fun E hE => ?_⟩
  haveI := isCoverDense_ι_of_forall_exists_covering J E hE
  exact ⟨_, inferInstance, restrictedIndexingDiagram J F E, (restrictedCocone J F E).ι,
    restrictedIndexingDiagram_obj_mem J F E, ⟨isColimitRestrictedCocone⟩⟩

end CategoryTheory.Sheaf
