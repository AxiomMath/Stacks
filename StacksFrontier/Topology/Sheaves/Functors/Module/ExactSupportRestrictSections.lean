module

public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportRestrictToAnOpen

/-!
# Sections of a module over `i_* 𝒪_Z` on two opens differing off the image of `Z`

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces. An `i_* 𝒪_Z`-module `𝓜` on `X`
vanishes on every open disjoint from the image of `Z`
(`ClosedQuotientMorphismOfRingedSpaces.eq_zero_of_le_opensComplRange`), so if `W' ⊆ W` are opens
of `X` whose difference misses that image, then `𝓜(W) ⟶ 𝓜(W')` is **bijective**: a section over
`W` is glued from its restriction to `W'` and the zero section on `W ∖ i(Z)`.

This is the mechanism behind descent — `moduleDescend 𝓜` has `𝓜(i_! V)` for its sections over
`V`, and `i_! V` differs from any other open with inverse image `V` only off the image of `Z` —
and it is what makes **descent compatible with restriction to an open subspace** `U ⊆ X`: for
`V ⊆ i⁻¹U` the two candidate opens `i_! V` and `i_! V ⊓ U` differ off the image of `Z`, so the
sections of the descent over `V` can be computed inside `U`.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.bijective_presheaf_map_of_opensMap_le`: **the
  bijectivity**, for a pair of opens whose difference misses the image of `Z`.
* `ClosedQuotientMorphismOfRingedSpaces.bijective_presheaf_map_opensFunctor_inf`: the case the
  restriction comparison needs, `𝓜(i_! V) ≅ 𝓜(i_! V ⊓ U)` for `V ⊆ i⁻¹U`.
* `ClosedQuotientMorphismOfRingedSpaces.opensFunctor_inf_eq`: the open `i_! V ⊓ U` **is** the
  `i_!` of the restricted situation, read as an open of `X`.
* `ClosedQuotientMorphismOfRingedSpaces.bijective_presheaf_map_opensFunctor_restrict`: the two
  put together — **descent commutes with restriction to `U`, on sections**: the sections over an
  open `V` of `Z|_{i⁻¹U}` of the descent to `Z` restricted to `i⁻¹U` are the sections over `V`
  of the descent of `𝓜|_U` to `Z|_{i⁻¹U}`.

## What this is the content of

The functor-level statement that `ClosedQuotientMorphismOfRingedSpaces.moduleDescend` commutes
with restriction to `U` **is** now proved, as
`ClosedQuotientMorphismOfRingedSpaces.moduleDescendRestrictIso` in
`StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictDescend.lean`, and the two
results below are its content on sections: that isomorphism is, on sections over `V`, exactly
the bijection `bijective_presheaf_map_opensFunctor_restrict` supplies, as
`ClosedQuotientMorphismOfRingedSpaces.moduleDescendRestrictIso_hom_app_val_app` records. Earlier
versions of this note said the functor-level statement was not proved, and then that what it was
missing was the comparison of the two sheaves of rings `(i_* 𝒪_Z)|_U` and
`(i|_{i⁻¹U})_* 𝒪_{Z|_{i⁻¹U}}` over which the two descent functors are taken; that comparison is
`ClosedQuotientMorphismOfRingedSpaces.pushedRingSheafRestrictIso`, together with the
compatibility of the two comorphisms that makes it a comparison of algebras over `𝒪_{X|_U}`,
`ClosedQuotientMorphismOfRingedSpaces.pushedRingHom_comp_pushedRingSheafRestrictIso_inv`, in
`StacksFrontier/Topology/Sheaves/Functors/Module/ExactSupportRestrictRingSheaf.lean`, and with it
the statement went through.

## What is not proved

Invertibility of the comparison
`ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison` is **not** proved.
Descent is only one of the two factors of
`ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupport`; the other is the internal Hom
`ℰom_{𝒪_X}(i_* 𝒪_Z, -)`, and what remains is that factor's restriction isomorphism together with
the identification of the mate with the composite of the two. See the notes of
`ExactSupportRestrictDescend.lean` for what the internal Hom factor is waiting on.

## Implementation notes

The bijectivity generalises
`ClosedQuotientMorphismOfRingedSpaces.bijective_descendCounitPresheaf_app`, which is the special
case `W = i_! i⁻¹ W'`; that declaration is left as it stands, since it is stated for the counit
of the descent adjunction rather than for a restriction map and is consumed as such by
`ClosedQuotientMorphismOfRingedSpaces.descendCounitIso`.

The statement is about the underlying presheaf of abelian groups. The restriction maps of a
presheaf of modules over a varying sheaf of rings are semilinear, so they are not morphisms in
a single module category; bijectivity is a statement about the underlying additive map, and that
is the shape the gluing axiom is available in.

## References

* [Stacks Project, Tag 0A74](https://stacks.math.columbia.edu/tag/0A74)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite Topology TopologicalSpace

universe v u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- Two parallel inclusions of opens induce the same restriction map, the opens of a space
forming a poset. -/
private alias presheaf_map_eq_map := map_eq_map

/-- **An `i_* 𝒪_Z`-module has the same sections on two opens whose difference misses the image
of `Z`.** If `W' ≤ W` are opens of `X` with `i⁻¹ W ≤ i⁻¹ W'`, then restriction from `W` to `W'`
is bijective on sections of any `i_* 𝒪_Z`-module.

The two opens `W'` and `W ⊓ (X ∖ i(Z))` cover `W`: a point of `W` in the image of `Z` comes from
`i⁻¹ W ⊆ i⁻¹ W'`, so it lies in `W'`. The module vanishes on every open contained in
`X ∖ i(Z)`, so a section over `W'` extends uniquely by zero, and a section over `W` is
determined by its restriction to `W'`. -/
lemma bijective_presheaf_map_of_opensMap_le (M : SheafOfModules.{max u v} S.pushedRingSheaf)
    {W W' : Opens S.X} (hle : W' ≤ W)
    (hZ : (opensMap S.i).obj W ≤ (opensMap S.i).obj W') :
    Function.Bijective (ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op)) := by
  let F : TopCat.Sheaf AddCommGrpCat.{max u v} S.X.carrier := ⟨M.val.presheaf, M.isSheaf⟩
  let B : Opens S.X := W ⊓ S.opensComplRange
  let Wf : Bool → Opens S.X := fun b => match b with | true => W' | false => B
  have hWfle : ∀ b, Wf b ≤ W := by
    rintro (_ | _)
    · exact inf_le_left
    · exact hle
  have hcover : W ≤ iSup Wf := by
    intro x hx
    by_cases hr : x ∈ Set.range ⇑(ConcreteCategory.hom S.baseMap)
    · obtain ⟨z, rfl⟩ := hr
      exact Opens.mem_iSup.2 ⟨true, hZ hx⟩
    · exact Opens.mem_iSup.2 ⟨false, ⟨hx, hr⟩⟩
  have hzero : ∀ {W₀ : Opens S.X}, W₀ ≤ B → ∀ x y : ToType (F.1.obj (op W₀)), x = y := by
    intro W₀ hW₀ x y
    have h : W₀ ≤ S.opensComplRange := le_trans hW₀ inf_le_right
    exact (S.eq_zero_of_le_opensComplRange M.val W₀ h x).trans
      (S.eq_zero_of_le_opensComplRange M.val W₀ h y).symm
  let sf : ToType (F.1.obj (op W')) → ∀ b, ToType (F.1.obj (op (Wf b))) := fun m b =>
    match b with | true => m | false => 0
  have key : ∀ m : ToType (F.1.obj (op W')),
      ∃! s : ToType (F.1.obj (op W)), ∀ b, F.1.map (homOfLE (hWfle b)).op s = sf m b := by
    intro m
    refine TopCat.Sheaf.existsUnique_gluing' F Wf W (fun b => homOfLE (hWfle b)) hcover _ ?_
    rintro (_ | _) (_ | _)
    · exact hzero inf_le_left _ _
    · exact hzero inf_le_left _ _
    · exact hzero inf_le_right _ _
    · exact presheaf_map_eq_map F.1 _ _ m
  have hres : ∀ y : ToType (F.1.obj (op W)),
      F.1.map (homOfLE (hWfle true)).op y =
        ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op) y :=
    fun y => presheaf_map_eq_map F.1 _ _ y
  refine ⟨fun s s' hss' => ?_, fun m => ?_⟩
  · obtain ⟨t, -, huniq⟩ := key (ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op) s)
    have hspec : ∀ y : ToType (F.1.obj (op W)),
        ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op) y =
            ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op) s →
          ∀ b, F.1.map (homOfLE (hWfle b)).op y =
            sf (ConcreteCategory.hom (M.val.presheaf.map (homOfLE hle).op) s) b := by
      rintro y hy (_ | _)
      · exact hzero le_rfl _ _
      · exact (hres y).trans hy
    exact (huniq s (hspec s rfl)).trans (huniq s' (hspec s' hss'.symm)).symm
  · obtain ⟨s, hs, -⟩ := key m
    exact ⟨s, (hres s).symm.trans (hs true)⟩

/-- **The sections of an `i_* 𝒪_Z`-module over `i_! V` are its sections over `i_! V ⊓ U`**, for
an open `V ⊆ i⁻¹U` of `Z`. This is the instance of
`ClosedQuotientMorphismOfRingedSpaces.bijective_presheaf_map_of_opensMap_le` that descent
compatible with restriction to the open subspace `U` rests on: the inverse image of `i_! V` is
`V`, which is contained in `i⁻¹U`, hence in the inverse image of `i_! V ⊓ U`. -/
lemma bijective_presheaf_map_opensFunctor_inf (M : SheafOfModules.{max u v} S.pushedRingSheaf)
    (U : Opens S.X) {V : Opens S.Z} (hV : V ≤ (opensMap S.i).obj U) :
    Function.Bijective (ConcreteCategory.hom (M.val.presheaf.map
      (homOfLE (inf_le_left : S.opensFunctor.obj V ⊓ U ≤ S.opensFunctor.obj V)).op)) := by
  refine S.bijective_presheaf_map_of_opensMap_le M _ ?_
  exact fun z hz => ⟨hz, hV ((S.opensMap_opensFunctor_obj V).le hz)⟩

/-- **`i_!` of the restricted situation is `i_!` intersected with `U`.** For an open `V` of
`Z|_{i⁻¹U}`, the largest open of `U` whose inverse image under `i|_{i⁻¹U}` is contained in `V`
is, read as an open of `X`, the intersection with `U` of the largest open of `X` whose inverse
image under `i` is contained in the image of `V` in `Z`.

Both inclusions are point chases. A point of `Z` over the left-hand side lies in `i⁻¹U`, so it
comes from a point of `Z|_{i⁻¹U}` over the corresponding point of `U`, which lies in `V`; and a
point of `U` whose `i`-fibre lies in the image of `V` has its `i|_{i⁻¹U}`-fibre in `V`. -/
lemma opensFunctor_inf_eq (U : Opens S.X) (V : Opens (S.restrict U).Z) :
    U.isOpenEmbedding.functor.obj ((S.restrict U).opensFunctor.obj V) =
      S.opensFunctor.obj
          ((Stacks.Cohomology.HigherDirectImage.preimageOpen S.i
            U).isOpenEmbedding.functor.obj V) ⊓ U := by
  refine le_antisymm (le_inf (S.le_opensFunctor_obj_iff.2 ?_)
    (Stacks.Cohomology.HigherDirectImage.isOpenEmbeddingFunctor_obj_le U _)) ?_
  · rintro z ⟨x, hx, hxz⟩
    have hzU : z ∈ Stacks.Cohomology.HigherDirectImage.preimageOpen S.i U := by
      have hx2 : (ConcreteCategory.hom U.inclusion') x ∈ U := x.2
      rwa [hxz] at hx2
    refine ⟨⟨z, hzU⟩, ?_, rfl⟩
    refine ((S.restrict U).baseMap_mem_opensFunctor_obj_iff V ⟨z, hzU⟩).1 ?_
    have hxeq : ConcreteCategory.hom (S.restrict U).baseMap ⟨z, hzU⟩ = x :=
      Subtype.ext hxz.symm
    rwa [hxeq]
  · rintro x ⟨hxF, hxU⟩
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    have hsub : (Opens.map (Opens.inclusion' U)).obj
          (S.opensFunctor.obj ((Stacks.Cohomology.HigherDirectImage.preimageOpen S.i
            U).isOpenEmbedding.functor.obj V)) ≤ (S.restrict U).opensFunctor.obj V := by
      refine (S.restrict U).le_opensFunctor_obj_iff.2 ?_
      intro w hw
      obtain ⟨w', hw'V, hww'⟩ := (S.baseMap_mem_opensFunctor_obj_iff _ w.1).1 hw
      exact (Subtype.ext hww' : w' = w) ▸ hw'V
    exact hsub hxF

/-- **Descent commutes with restriction to an open subspace, on sections.** For an open `V` of
`Z|_{i⁻¹U}`, the sections over `V` of the descent of an `i_* 𝒪_Z`-module `𝓜` to `Z`, restricted
to `i⁻¹U`, are the sections over `V` of the descent to `Z|_{i⁻¹U}` of `𝓜|_U`: the first are
`𝓜(i_! V)`, the second are `𝓜(i_! V ⊓ U)` by
`ClosedQuotientMorphismOfRingedSpaces.opensFunctor_inf_eq`, and the restriction between them is
bijective because the two opens differ off the image of `Z`.

This is the content on sections of the comparison of
`ClosedQuotientMorphismOfRingedSpaces.moduleDescend` with restriction to `U`, which is proved as
`ClosedQuotientMorphismOfRingedSpaces.moduleDescendRestrictIso`. -/
lemma bijective_presheaf_map_opensFunctor_restrict
    (M : SheafOfModules.{max u v} S.pushedRingSheaf) (U : Opens S.X)
    (V : Opens (S.restrict U).Z) :
    Function.Bijective (ConcreteCategory.hom (M.val.presheaf.map
      (homOfLE ((S.opensFunctor_inf_eq U V).le.trans inf_le_left)).op)) := by
  refine S.bijective_presheaf_map_of_opensMap_le M _ ?_
  intro z hz
  obtain ⟨w, hwV, hwz⟩ := (S.opensMap_opensFunctor_obj _).le hz
  exact ⟨⟨ConcreteCategory.hom S.baseMap w.1, w.2⟩,
    ((S.restrict U).baseMap_mem_opensFunctor_obj_iff V w).2 hwV,
    congrArg (ConcreteCategory.hom S.baseMap) hwz⟩

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
