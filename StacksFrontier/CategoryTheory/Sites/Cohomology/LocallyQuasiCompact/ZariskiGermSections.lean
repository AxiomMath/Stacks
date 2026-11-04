module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ProperBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiProperBaseChangeReduction

/-!
# The germ map into the germ-model sections presheaf

Let `X'` be an object of the locally quasi-compact Zariski site and let `F` be a sheaf of sets on
its space. The germ-model sections presheaf `germSectionsPresheaf S X' F` of
`ZariskiProperBaseChangeReduction.lean` assigns to an object `h : W ⟶ X'` of the localized site
the global sections of the germ-model inverse image `h^{-1}F`. Over an *open* `U ⊆ X'`, viewed
as the object `opensToSlice U` of the localized site, there is a canonical map

`F(U) ⟶ Γ(U, (U → X')^{-1}F)`,

sending a section to its family of germs. This file records that map and its naturality in `U`.

This is the restriction to opens of the comparison between the two sides of the sections formula
of Stacks 09X3: the left-hand side `π_{X'}^{-1}F` has the unit of the comparison adjunction as
its map from `F` over an open, and the right-hand side has this germ map.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsOfSection`: the family of
  germs of a section of `F` over an open `U ⊆ X'`, as a section of the germ-model sections
  presheaf over `opensToSlice U`.
* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsUnit`: the same, as a morphism
  of presheaves on the small Zariski site of the space of `X'`.

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

variable (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t)))

/-- **The germ map at an open.** A section of `F` over an open `U ⊆ X'` determines, by taking
germs, a section of the germ-model inverse image of `F` along the inclusion `U → X'` over all of
`U`, i.e. a section of `germSectionsPresheaf` over the object `opensToSlice U` of the localized
Zariski site. -/
def germSectionsOfSection (U : Opens X'.obj) (s : F.1.obj (op U)) :
    (germSectionsPresheaf S X' F).obj (op ((S.opensToSlice X').1.obj U)) :=
  GermPullback.ofSection
    (g := ⇑((siteToTop S).map ((S.opensToSlice X').1.obj U).hom)) (𝒢 := F.1)
    (W := ⊤) (V := U) (fun z => opensToSlice_hom_mem S (T := X') U z.1) s

/-- The value of the germ map at an open: the germ section `germSectionsOfSection S X' F U s`
sends a point `z` of the space of `opensToSlice U` to its image in `U` together with the germ of
`s` at that image. -/
@[simp]
lemma germSectionsOfSection_val (U : Opens X'.obj) (s : F.1.obj (op U))
    (z : (⊤ : Opens ((siteToTop S).obj ((S.opensToSlice X').1.obj U).left))) :
    (germSectionsOfSection S X' F U s).1 z =
      ⟨((S.opensToSlice X').1.obj U).hom z.1,
        TopCat.Presheaf.germOfSize F.1 U (((S.opensToSlice X').1.obj U).hom z.1)
          (opensToSlice_hom_mem S (T := X') U z.1) s⟩ :=
  rfl

/-- **The germ map, as a morphism of presheaves on the small Zariski site.** Taking germs is
natural in the open `U ⊆ X'`: restricting a section and then taking germs is taking germs and
then restricting the germ-model section. -/
def germSectionsUnit :
    F.1 ⟶ (S.opensToSlice X').1.op ⋙ germSectionsPresheaf S X' F where
  app U := TypeCat.ofHom fun s => germSectionsOfSection S X' F U.unop s
  naturality {U U'} i := by
    refine ConcreteCategory.hom_ext _ _ fun s => ?_
    refine GermPullback.ext fun z => ?_
    exact congrArg (fun t => (⟨_, t⟩ : GermPullback.Germs F.1))
      (TopCat.Presheaf.germOfSize_res_apply F.1 i.unop _ _ s)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
