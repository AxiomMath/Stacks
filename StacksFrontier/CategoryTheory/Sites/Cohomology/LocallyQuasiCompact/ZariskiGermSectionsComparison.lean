module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiGermSectionsSheaf

/-!
# The comparison inverse image is the germ-model sections presheaf

Let `X'` be an object of the locally quasi-compact Zariski site and `F` a sheaf of sets on its
space. The sections formula of Stacks 09X3 identifies the comparison inverse image `π_{X'}^{-1}F`
with the germ-model sections presheaf `germSectionsPresheaf S X' F`. This file performs the
formal half of that identification: **a universal property determines the comparison inverse
image**.

Precisely, suppose that the germ-model sections sheaf of `ZariskiGermSectionsSheaf.lean`,
together with the germ map `germSectionsUnit`, corepresents morphisms out of the comparison
inverse image — i.e. for every sheaf `H` on the localized site every `φ : F ⟶ H|_{Opens X'}`
factors uniquely through the germ map. Then the germ-model sections sheaf *is* the comparison
inverse image, naturally in the object of the localized site; the isomorphism is
`comparisonInverseImageGermSectionsNatIso`. Both objects solve the same mapping-out problem:
`π_{X'}^{-1}F` does so by the comparison adjunction, and the germ-model sections sheaf does so by
hypothesis, so the two transposes are mutually inverse.

Feeding that natural isomorphism, at `X` and at `Y`, into
`isIso_zariskiComparisonBaseChangeMap_of_germSectionsIso` gives clause (7a) of Stacks 0DCU, which
is `isIso_zariskiComparisonBaseChangeMap_of_univ`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsSheafIso`: the comparison
  inverse image is the germ-model sections sheaf.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.comparisonInverseImageGermSectionsNatIso`:
  the same, read as an isomorphism of presheaves on the localized site — the natural form of the
  sections formula of Stacks 09X3.

## Main results

* `isIso_zariskiComparisonBaseChangeMap_of_univ`:
  **clause (7a) of Stacks 0DCU** follows from the mapping-out property of the germ-model sections
  sheaf, at `X` and at `Y`.

## Implementation notes

Nothing here inspects the construction of `comparisonInverseImage`: it is used only through the
comparison adjunction `comparisonAdjunction`, whose hom-equivalence is the uniqueness statement
that the two mapping-out problems share. In particular no coherence property of
`CategoryTheory.Adjunction.leftAdjointUniq` is needed, and the clause-(5) isomorphisms
`zariskiComparisonSquareIso` do not appear.

## References

* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound) (X' : S.category)
  (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t)))

/-- The mapping-out property of the germ-model sections presheaf: every morphism from `F` to the
restriction of a sheaf `H` on the localized site to the opens of `X'` factors uniquely through the
germ map. This is the content of the sections formula of Stacks 09X3 that is not formal. -/
def GermSectionsMapOutProperty : Prop :=
  ∀ (H : Sheaf (S.zariskiTopology.over X') (Type (max u t)))
    (φ : F.1 ⟶ (S.opensToSlice X').1.op ⋙ H.1),
    ∃! ψ : germSectionsPresheaf S X' F ⟶ H.1,
      germSectionsUnit S X' F ≫ Functor.whiskerLeft (S.opensToSlice X').1.op ψ = φ

/-- The germ map, as a morphism of sheaves from `F` to the comparison direct image of the
germ-model sections sheaf. -/
def germSectionsUnitSheafHom :
    F ⟶ (S.comparisonDirectImage X' (Type (max u t))).obj (germSectionsSheaf S X' F) :=
  ObjectProperty.homMk (germSectionsUnit S X' F)

/-- **The comparison inverse image is the germ-model sections sheaf.** Both solve the same
mapping-out problem over `F` — the comparison inverse image by the comparison adjunction, the
germ-model sections sheaf by `GermSectionsMapOutProperty` — so they are isomorphic, by the
uniqueness halves of the two universal properties. -/
def germSectionsSheafIso (huniv : GermSectionsMapOutProperty S X' F) :
    (comparisonInverseImage.{u, w, t} S X').obj F ≅ germSectionsSheaf S X' F :=
  let adj := comparisonAdjunction.{u, w, t} S X'
  let hex := (huniv ((comparisonInverseImage.{u, w, t} S X').obj F) (adj.unit.app F).hom).exists
  let v : germSectionsPresheaf S X' F ⟶ ((comparisonInverseImage.{u, w, t} S X').obj F).obj :=
    hex.choose
  have hv : germSectionsUnit S X' F ≫ Functor.whiskerLeft (S.opensToSlice X').1.op v =
      (adj.unit.app F).hom := hex.choose_spec
  have hal : adj.unit.app F ≫ (S.comparisonDirectImage X' (Type (max u t))).map
        ((adj.homEquiv F (germSectionsSheaf S X' F)).symm
          (germSectionsUnitSheafHom S X' F)) =
      germSectionsUnitSheafHom S X' F := by
    have h := (adj.homEquiv F (germSectionsSheaf S X' F)).apply_symm_apply
      (germSectionsUnitSheafHom S X' F)
    rwa [adj.homEquiv_unit] at h
  { hom := (adj.homEquiv F (germSectionsSheaf S X' F)).symm
      (germSectionsUnitSheafHom S X' F)
    inv := ObjectProperty.homMk v
    hom_inv_id := by
      refine (adj.homEquiv F _).injective ?_
      rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply, adj.homEquiv_id]
      exact ObjectProperty.hom_ext _ hv
    inv_hom_id := by
      apply ObjectProperty.hom_ext
      refine (huniv (germSectionsSheaf S X' F) (germSectionsUnit S X' F)).unique ?_ ?_
      · change germSectionsUnit S X' F ≫ Functor.whiskerLeft (S.opensToSlice X').1.op
          (v ≫ _) = _
        rw [Functor.whiskerLeft_comp, ← Category.assoc, hv]
        exact congrArg InducedCategory.Hom.hom hal
      · simp }

/-- **The sections formula of Stacks 09X3, naturally in the object of the localized site.** The
comparison inverse image `π_{X'}^{-1}F` and the germ-model sections presheaf
`(h : W ⟶ X') ↦ Γ(W, h^{-1}F)` are isomorphic as presheaves on the localized Zariski site. -/
def comparisonInverseImageGermSectionsNatIso (huniv : GermSectionsMapOutProperty S X' F) :
    ((comparisonInverseImage.{u, w, t} S X').obj F).obj ≅ germSectionsPresheaf S X' F :=
  (sheafToPresheaf _ _).mapIso (germSectionsSheafIso S X' F huniv)

variable {X Y : S.category} (f : X ⟶ Y)

/-- **Clause (7a) of Stacks 0DCU.** If the germ-model sections sheaf has the mapping-out property
of the sections formula of Stacks 09X3, at the source and at the target of a morphism `f` of the
site whose underlying continuous map is proper, then the base-change map of the Zariski comparison
morphisms is an isomorphism. -/
theorem isIso_zariskiComparisonBaseChangeMap_of_univ
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f))
    (huX : ∀ G : Sheaf (Opens.grothendieckTopology X.obj) (Type u),
      GermSectionsMapOutProperty.{u, w, u} S X G)
    (huY : ∀ G : Sheaf (Opens.grothendieckTopology Y.obj) (Type u),
      GermSectionsMapOutProperty.{u, w, u} S Y G) :
    IsIso (zariskiComparisonBaseChangeMap.{u, w, u} S f) :=
  isIso_zariskiComparisonBaseChangeMap_of_germSectionsIso.{u, w} S f hf
    (fun G => comparisonInverseImageGermSectionsNatIso.{u, w, u} S X G (huX G))
    (fun G => comparisonInverseImageGermSectionsNatIso.{u, w, u} S Y G (huY G))

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
