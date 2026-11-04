module

public import StacksFrontier.CategoryTheory.Functor.IsCoreInclusion
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Functoriality

/-!
# The functor between two-fibre products induced by iso-wide functors is iso-wide

Let `Φ : 𝒳 ×_𝒵 𝒴 ⥤ 𝒜 ×_𝒞 ℬ` be the functor `CategoryTheory.Limits.CategoricalPullback.map`
(Stacks 02XA) induced by functors `L : 𝒳 ⥤ 𝒜`, `K : 𝒴 ⥤ ℬ`, `M : 𝒵 ⥤ 𝒞` and two fillers.  If `L`
and `K` present `𝒳` and `𝒴` as wide subcategories of isomorphisms
(`CategoryTheory.Functor.IsIsoWide`) and `M` is faithful, then so does `Φ`.

This is what lets an equivalence of two-fibre products of categories be restricted to the
two-fibre products of their maximal subgroupoids, through
`CategoryTheory.Functor.isEquivalence_of_isCoreInclusion`: a two-fibre product of groupoids is not
literally the core of the two-fibre product of the ambient categories, but its comparison with it
is iso-wide.

## Main results

* `CategoryTheory.Limits.CategoricalPullback.isIsoWide_map`.

## References

* [Stacks Project, Tag 02XA](https://stacks.math.columbia.edu/tag/02XA)
-/

@[expose] public section

namespace CategoryTheory.Limits.CategoricalPullback

variable {𝒳 𝒴 𝒵 𝒜 ℬ 𝒞 : Type*}
  [Category 𝒳] [Category 𝒴] [Category 𝒵] [Category 𝒜] [Category ℬ] [Category 𝒞]
  {H : 𝒳 ⥤ 𝒵} {I : 𝒴 ⥤ 𝒵} {L : 𝒳 ⥤ 𝒜} {K : 𝒴 ⥤ ℬ} {M : 𝒵 ⥤ 𝒞} {F : 𝒜 ⥤ 𝒞} {G : ℬ ⥤ 𝒞}
  {α : K ⋙ G ≅ I ⋙ M} {β : H ⋙ M ≅ L ⋙ F}

/-- **The functor between two-fibre products induced by two iso-wide functors and a faithful one
is iso-wide.** -/
theorem isIsoWide_map (hL : L.IsIsoWide) (hK : K.IsIsoWide) [M.Faithful] :
    (map H I L K M F G α β).IsIsoWide := by
  have := hL.faithful
  have := hK.faithful
  have hfaith : (map H I L K M F G α β).Faithful := by
    refine ⟨fun {x y} g g' h => ?_⟩
    refine CategoricalPullback.hom_ext (L.map_injective ?_) (K.map_injective ?_)
    · exact congrArg (fun k => k.fst) h
    · exact congrArg (fun k => k.snd) h
  have hiso : ∀ {x y : H ⊡ I} (g : x ⟶ y), IsIso ((map H I L K M F G α β).map g) := by
    intro x y g
    have h₁ := hL.isIso_map g.fst
    have h₂ := hK.isIso_map g.snd
    exact (mkIso (x := (map H I L K M F G α β).obj x) (y := (map H I L K M F G α β).obj y)
      (@asIso _ _ _ _ (L.map g.fst) h₁) (@asIso _ _ _ _ (K.map g.snd) h₂)
      ((map H I L K M F G α β).map g).w).isIso_hom
  have hex : ∀ {x y : H ⊡ I} (e : (map H I L K M F G α β).obj x ≅ (map H I L K M F G α β).obj y),
      ∃ g : x ⟶ y, (map H I L K M F G α β).map g = e.hom := by
    intro x y e
    obtain ⟨g₁, hg₁⟩ := hL.exists_iso_map_eq (X := x.fst) (Y := y.fst) ((π₁ F G).mapIso e)
    obtain ⟨g₂, hg₂⟩ := hK.exists_iso_map_eq (X := x.snd) (Y := y.snd) ((π₂ F G).mapIso e)
    have hw := e.hom.w
    refine ⟨(mkIso g₁ g₂ (M.map_injective ?_)).hom, ?_⟩
    · simp only [Functor.mapIso_hom, π₁_map, π₂_map] at hg₁ hg₂
      have hw1 : F.map (L.map g₁.hom) ≫ β.inv.app y.fst ≫ M.map y.iso.hom ≫ α.inv.app y.snd =
          (β.inv.app x.fst ≫ M.map x.iso.hom ≫ α.inv.app x.snd) ≫ G.map (K.map g₂.hom) := by
        have := e.hom.w
        simp only [map_obj_iso_hom, map_obj_fst, map_obj_snd] at this
        simpa only [hg₁, hg₂] using this
      have hβ1 : F.map (L.map g₁.hom) ≫ β.inv.app y.fst =
          β.inv.app x.fst ≫ M.map (H.map g₁.hom) := (β.inv.naturality g₁.hom)
      have hα1 : α.inv.app x.snd ≫ G.map (K.map g₂.hom) =
          M.map (I.map g₂.hom) ≫ α.inv.app y.snd := (α.inv.naturality g₂.hom).symm
      rw [← Category.assoc, hβ1, Category.assoc, Category.assoc, Category.assoc, hα1] at hw1
      have hw2 := (cancel_epi (β.inv.app x.fst)).1 hw1
      rw [← Category.assoc, ← Category.assoc] at hw2
      have hw3 := (cancel_mono (α.inv.app y.snd)).1 hw2
      rw [Functor.map_comp, Functor.map_comp]
      exact hw3
    · refine CategoricalPullback.hom_ext ?_ ?_
      · exact hg₁
      · exact hg₂
  exact ⟨hfaith, hiso, hex⟩

end CategoryTheory.Limits.CategoricalPullback

end
