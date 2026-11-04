module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiGermSections

/-!
# The germ-model sections presheaf over an open is the sheaf itself

Let `X'` be an object of the locally quasi-compact Zariski site, `F` a sheaf of sets on its space
and `U ⊆ X'` an open. Over the object `opensToSlice U` of the localized Zariski site the
germ-model sections presheaf of `ZariskiProperBaseChangeReduction.lean` has sections
`Γ(U, (U → X')^{-1}F)`, and the germ map of `ZariskiGermSections.lean`

`F(U) ⟶ Γ(U, (U → X')^{-1}F)`

is a bijection: a section of `F` over `U` is the same thing as a continuous family of germs of
`F` along `U`. Equivalently, the restriction of the germ-model sections presheaf to the opens of
`X'` — its comparison direct image — is `F` itself.

This is the restriction to opens of the sections formula of Stacks 09X3; it says that the
germ-model sections presheaf is a candidate for `π_{X'}^{-1}F`, since the unit of the comparison
adjunction is an isomorphism over opens by clause (3) of Stacks 0DCU.

## Main results

All in the namespace `Stacks.Topology.LocallyQuasiCompactZariskiSituation`:

* `injective_germSectionsOfSection`: a section of `F` over an open is determined by its germs.
* `surjective_germSectionsOfSection`: a continuous family of germs of `F` along an open comes
  from a section.
* `isIso_germSectionsUnit`: the germ map is an isomorphism of presheaves on the small Zariski
  site of the space of `X'`.

## Implementation notes

Injectivity is `TopCat.Presheaf.sectionOfSize_ext` — a section of a sheaf is determined by its
germs —
together with the fact that the structure morphism of `opensToSlice U` is onto `U`. Surjectivity
is the local-to-global argument of the germ model: `GermPullback.exists_repr` writes the family
of germs locally as the germs of a section of `F` on an open of `X'`, the open images of those
neighbourhoods cover `U`, the local sections agree on overlaps because the structure morphism is
injective and germs determine sections, and `TopCat.Sheaf.existsUnique_gluing'` glues them.

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

/-- Every point of an open `U ⊆ X'` is the image of a point of `opensToSlice U`: the structure
morphism of `opensToSlice U` has image exactly `U`. -/
lemma exists_opensToSlice_hom_eq {U : Opens X'.obj} {x : X'.obj} (hx : x ∈ U) :
    ∃ z : ((S.opensToSlice X').1.obj U).left.obj,
      ((S.opensToSlice X').1.obj U).hom z = x := by
  have h := ((S.opensToSlice X').2 U).2
  have hxr : x ∈ Set.range (((S.opensToSlice X').1.obj U).hom : _ → X'.obj) := by
    rw [h]; exact hx
  exact hxr

/-- The structure morphism of `opensToSlice U` is injective: it is an open embedding. -/
lemma injective_opensToSlice_hom (U : Opens X'.obj) :
    Function.Injective (((S.opensToSlice X').1.obj U).hom : _ → X'.obj) :=
  ((S.opensToSlice X').2 U).1.isEmbedding.injective

/-- The germ of a section at a point equals the germ of its restriction to a smaller open. -/
private lemma germs_mk_eq_restrict {V V' : Opens X'.obj} (i : V ⟶ V') (s : F.1.obj (op V'))
    {y : X'.obj} (hy : y ∈ V') (hy' : y ∈ V) :
    (⟨y, TopCat.Presheaf.germOfSize F.1 V' y hy s⟩ : GermPullback.Germs F.1) =
      ⟨y, TopCat.Presheaf.germOfSize F.1 V y hy' (F.1.map i.op s)⟩ :=
  congrArg (fun a => (⟨y, a⟩ : GermPullback.Germs F.1))
    (TopCat.Presheaf.germOfSize_res_apply F.1 i y hy' s).symm

/-- **A section of `F` over an open is determined by its germs.** The germ map at an open `U` of
the space of `X'` is injective. -/
lemma injective_germSectionsOfSection (U : Opens X'.obj) :
    Function.Injective (germSectionsOfSection S X' F U) := by
  intro s t hst
  refine TopCat.Presheaf.sectionOfSize_ext F U s t ?_
  intro x hx
  obtain ⟨z, hz⟩ := exists_opensToSlice_hom_eq S X' hx
  have h := congrArg (fun σ => σ.1 ⟨z, trivial⟩) hst
  simp only [germSectionsOfSection_val] at h
  have h2 := GermPullback.Sets.snd_eq_of_mk_eq h
  subst hz
  exact h2

/-- Near each point of an open `U ⊆ X'` a germ-model section of `F` over `opensToSlice U` is the
family of germs of a section of `F` on an open subset of `U`. The open is the image of a
neighbourhood in `opensToSlice U` of a preimage of the point, so the local sections obtained this
way determine the germ-model section at every point above their domain. -/
lemma exists_local_section_of_germSections {U : Opens X'.obj}
    (σ : (germSectionsPresheaf S X' F).obj (op ((S.opensToSlice X').1.obj U))) (x : U) :
    ∃ (V₀ : Opens X'.obj) (_ : x.1 ∈ V₀) (_ : V₀ ≤ U) (t : F.1.obj (op V₀)),
      ∀ (z : ((S.opensToSlice X').1.obj U).left.obj)
        (hz : ((S.opensToSlice X').1.obj U).hom z ∈ V₀),
        σ.1 ⟨z, trivial⟩ =
          ⟨((S.opensToSlice X').1.obj U).hom z,
            TopCat.Presheaf.germOfSize F.1 V₀ _ hz t⟩ := by
  obtain ⟨z₀, hz₀⟩ := exists_opensToSlice_hom_eq S X' x.2
  obtain ⟨W₀, hzW₀, i, V, hV, s, hs⟩ :=
    GermPullback.exists_repr (g := ⇑((siteToTop S).map ((S.opensToSlice X').1.obj U).hom))
      (𝒢 := F.1) σ (show z₀ ∈ (⊤ : Opens _) from trivial)
  refine ⟨⟨(fun y => ((S.opensToSlice X').1.obj U).hom y) '' W₀.1,
    ((S.opensToSlice X').2 U).1.isOpenMap _ W₀.2⟩, ⟨z₀, hzW₀, hz₀⟩, ?_, ?_, ?_⟩
  · rintro p ⟨y, -, rfl⟩
    exact opensToSlice_hom_mem S (T := X') U y
  · refine F.1.map (homOfLE ?_).op s
    rintro p ⟨y, hy, rfl⟩
    exact hV ⟨y, hy⟩
  · rintro z ⟨y, hy, hyz⟩
    have hzy : z = y := (injective_opensToSlice_hom S X' U hyz).symm
    subst hzy
    have hiz : i ⟨z, hy⟩ = (⟨z, trivial⟩ : (⊤ : Opens _)) := Subtype.ext rfl
    have h1 := hs ⟨z, hy⟩
    rw [hiz] at h1
    exact h1.trans (germs_mk_eq_restrict S X' F (homOfLE _) s _ _)

/-- **A continuous family of germs along an open comes from a section.** The germ map at an open
`U` of the space of `X'` is surjective: the local sections provided by
`exists_local_section_of_germSections` agree on overlaps, because the structure morphism of
`opensToSlice U` is onto `U` and a section of a sheaf is determined by its germs, so they glue to
a section of `F` over `U` whose germs are the given family. -/
lemma surjective_germSectionsOfSection (U : Opens X'.obj) :
    Function.Surjective (germSectionsOfSection S X' F U) := by
  classical
  intro σ
  choose V₀ hxV₀ hV₀U t ht using exists_local_section_of_germSections S X' F σ
  have hcover : U ≤ iSup V₀ := by
    intro p hp
    simp only [Opens.mem_iSup]
    exact ⟨⟨p, hp⟩, hxV₀ ⟨p, hp⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 V₀ t := by
    intro x y
    refine TopCat.Presheaf.sectionOfSize_ext F _ _ _ ?_
    intro p hp
    obtain ⟨z, hz⟩ := exists_opensToSlice_hom_eq S X' (hV₀U x hp.1)
    subst hz
    rw [TopCat.Presheaf.germOfSize_res_apply, TopCat.Presheaf.germOfSize_res_apply]
    exact GermPullback.Sets.snd_eq_of_mk_eq ((ht x z hp.1).symm.trans (ht y z hp.2))
  obtain ⟨s, hs, -⟩ :=
    TopCat.Sheaf.existsUnique_gluing' F V₀ U (fun x => homOfLE (hV₀U x)) hcover t hcompat
  refine ⟨s, GermPullback.ext fun z => ?_⟩
  set x : U :=
    ⟨((S.opensToSlice X').1.obj U).hom z.1, opensToSlice_hom_mem S (T := X') U z.1⟩ with hxdef
  have hzz : (⟨z.1, trivial⟩ : (⊤ : Opens _)) = z := Subtype.ext rfl
  have h1 : σ.1 z =
      ⟨((S.opensToSlice X').1.obj U).hom z.1,
        TopCat.Presheaf.germOfSize F.1 (V₀ x) _ (hxV₀ x) (t x)⟩ :=
    (congrArg (fun w => σ.1 w) hzz).symm.trans (ht x z.1 (hxV₀ x))
  rw [germSectionsOfSection_val, h1, ← hs x]
  exact germs_mk_eq_restrict S X' F (homOfLE (hV₀U x)) s _ _

/-- **The germ map at an open is a bijection.** -/
lemma bijective_germSectionsOfSection (U : Opens X'.obj) :
    Function.Bijective (germSectionsOfSection S X' F U) :=
  ⟨injective_germSectionsOfSection S X' F U, surjective_germSectionsOfSection S X' F U⟩

/-- **The restriction of the germ-model sections presheaf to the opens of `X'` is `F`.** The germ
map is an isomorphism of presheaves on the small Zariski site of the space of `X'`. -/
theorem isIso_germSectionsUnit : IsIso (germSectionsUnit S X' F) := by
  have h : ∀ V, IsIso ((germSectionsUnit S X' F).app V) := fun V =>
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_germSectionsOfSection S X' F V.unop)
  exact NatIso.isIso_of_isIso_app _

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
