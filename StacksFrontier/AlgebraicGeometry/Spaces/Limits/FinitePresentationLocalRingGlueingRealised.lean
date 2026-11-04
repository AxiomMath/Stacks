module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationSliceGlueingSubterminalEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationSpecStalkGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationStageColimitEquivalence

/-!
# Glueing algebraic spaces of finite presentation near a point

Let `S` be a scheme, `U` a retrocompact open of `S` and `s` a point of `S`, and put
`V = Spec 𝒪_{S, s} ∩ U`. Base change identifies the `2`-fibre product
`FP_U ×_{FP_V} FP_{Spec 𝒪_{S, s}}` with the filtered `2`-colimit of the categories `FP_{U'}` of
algebraic spaces of finite presentation over the opens `U'` of `S` with `U ⊆ U'` and `s ∈ U'`.
The colimit is taken over the stages `U ∪ W`, where `W` runs over the affine open neighbourhoods
of `s` contained in a fixed one, `W₀`; these stages are cofinal among the opens `U'`.

## Main definitions

* `AlgebraicGeometry.glueingStageSiteDiagram`: the stages `U ∪ W`, as a diagram in the big fppf
  category over `S` indexed by the affine open neighbourhoods of `s` contained in `W₀`.
* `AlgebraicGeometry.glueingStageToU`, `AlgebraicGeometry.glueingStageToW` and
  `AlgebraicGeometry.glueingStageToM`: the morphisms to a stage from `U`, from the neighbourhood
  and from `Spec 𝒪_{S, s}`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.specStalkStageColimitFunctor`: the comparison
  functor out of the filtered `2`-colimit of the categories `FP_{U ∪ W}`.

## Main results

* `AlgebraicGeometry.isPullback_glueingStage`: the overlap `W ∩ U` is the fibre product
  `U ×_{U ∪ W} W`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_glueingFunctor_glueingStage`:
  base change is an equivalence from `FP_{U ∪ W}` to `FP_U ×_{FP_{W ∩ U}} FP_W`.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isGlueingColimitEquivalence_specStalk`: the
  elementary form of the colimit identification over the stages.
* `AlgebraicGeometry.FinitePresentationSpacesOver.isEquivalence_specStalkStageColimitFunctor`:
  the comparison functor is an equivalence of categories.

## References

* [Stacks Project, Tag 0E91](https://stacks.math.columbia.edu/tag/0E91)
* [Stacks Project, Tag 0E90](https://stacks.math.columbia.edu/tag/0E90)
* [Stacks Project, Tag 0E8Z](https://stacks.math.columbia.edu/tag/0E8Z)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : S)
  (W₀ : AffineOpenNhds S s) (U : S.Opens)

/-! ### The stages `U ∪ W` -/

/-- The stages `U ∪ W`, as a diagram in the big fppf category over `S` indexed by the affine
open neighbourhoods `W` of `s` contained in `W₀`. -/
noncomputable def glueingStageSiteDiagram : Over W₀ ⥤ BigFppfOver B S hS where
  obj j := BigFppfOver.opensObj B S hS (U ⊔ j.left.obj.1)
  map {j k} e := BigFppfOver.opensHom B S hS
    (sup_le_sup_left (show j.left.obj.1 ≤ k.left.obj.1 from
      leOfHom ((affineOpenNhds S s).ι.map e.left)) U)
  map_id _ := @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS _ _) _ _
  map_comp _ _ := @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS _ _) _ _

/-- The stage at the neighbourhood `j` is the open `U ⊔ j` of `S`. -/
@[simp]
theorem glueingStageSiteDiagram_obj (j : Over W₀) :
    (glueingStageSiteDiagram B S hS s W₀ U).obj j =
      BigFppfOver.opensObj B S hS (U ⊔ j.left.obj.1) :=
  rfl

/-- The open immersion of `U` into a stage, as a morphism of the big fppf category over `S`. -/
noncomputable def glueingStageToU (j : Over W₀) :
    BigFppfOver.opensObj B S hS U ⟶ (glueingStageSiteDiagram B S hS s W₀ U).obj j :=
  BigFppfOver.opensHom B S hS (le_sup_left : U ≤ U ⊔ j.left.obj.1)

/-- The open immersion of a neighbourhood into the stage it sits in, as a morphism of the big
fppf category over `S`. -/
noncomputable def glueingStageToW (j : Over W₀) :
    (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).obj j ⟶
      (glueingStageSiteDiagram B S hS s W₀ U).obj j :=
  BigFppfOver.opensHom B S hS (le_sup_right : j.left.obj.1 ≤ U ⊔ j.left.obj.1)

/-- The morphism from `Spec 𝒪_{S, s}` to a stage: the canonical morphism to the neighbourhood,
followed by the open immersion of the neighbourhood into the stage. -/
noncomputable def glueingStageToM (j : Over W₀) :
    (restrictedSpecStalkSiteCone B S hS s W₀).pt ⟶
      (glueingStageSiteDiagram B S hS s W₀ U).obj j :=
  (restrictedSpecStalkSiteCone B S hS s W₀).π.app j ≫ glueingStageToW B S hS s W₀ U j

/-- The structure morphism of a stage to the canonical terminal object is a monomorphism. -/
theorem mono_mkIdTerminal_from_glueingStage (j : Over W₀) :
    Mono (Over.mkIdTerminal.from ((glueingStageSiteDiagram B S hS s W₀ U).obj j)) :=
  ⟨fun {X} g h _ => @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS X _) g h⟩

/-- The overlap `W ∩ U` is the fibre product `U ×_{U ∪ W} W` in the big fppf category over
`S`. -/
theorem isPullback_glueingStage (j : Over W₀) :
    IsPullback (opensSpecStalkStageToU B S hS s W₀ U j)
      (opensSpecStalkStageToW B S hS s W₀ U j) (glueingStageToU B S hS s W₀ U j)
      (glueingStageToW B S hS s W₀ U j) := by
  have := mono_mkIdTerminal_from_glueingStage B S hS s W₀ U j
  refine IsPullback.of_comp_mono'
    (Over.mkIdTerminal.from ((glueingStageSiteDiagram B S hS s W₀ U).obj j)) ?_
  convert isPullback_opensSpecStalkStage B S hS s W₀ U j using 1 <;>
    exact Over.mkIdTerminal.hom_ext _ _

/-- A stage is covered by the images of `U` and of the neighbourhood it is the union with. -/
theorem range_union_glueingStage (j : Over W₀)
    (x : (BigFppfOver.toScheme B S hS).obj ((glueingStageSiteDiagram B S hS s W₀ U).obj j)) :
    x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (glueingStageToU B S hS s W₀ U j)) ∨
      x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (glueingStageToW B S hS s W₀ U j)) := by
  obtain ⟨x, hx⟩ := x
  rcases TopologicalSpace.Opens.mem_sup.1 hx with hxU | hxW
  · exact Or.inl ⟨⟨x, hxU⟩, Scheme.homOfLE_apply' (le_sup_left : U ≤ _) x hxU⟩
  · exact Or.inr ⟨⟨x, hxW⟩, Scheme.homOfLE_apply' (le_sup_right : _ ≤ U ⊔ _) x hxW⟩

/-! ### The compatibilities of the stages with `U`, with the neighbourhoods and with the cone -/

/-- The open immersions of `U` into the stages are compatible with the transition morphisms of
the system of stages. -/
theorem glueingStageToU_comp {i j : Over W₀} (e : j ⟶ i) :
    glueingStageToU B S hS s W₀ U j ≫ (glueingStageSiteDiagram B S hS s W₀ U).map e =
      glueingStageToU B S hS s W₀ U i :=
  @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS _ _) _ _

/-- The open immersions of the neighbourhoods into the stages are compatible with the transition
morphisms of the two systems. -/
theorem glueingStageToW_comp {i j : Over W₀} (e : j ⟶ i) :
    (restrictedAffineOpenNhdsSiteDiagram B S hS s W₀).map e ≫ glueingStageToW B S hS s W₀ U i =
      glueingStageToW B S hS s W₀ U j ≫ (glueingStageSiteDiagram B S hS s W₀ U).map e :=
  @Subsingleton.elim _ (BigFppfOver.subsingleton_hom_opensObj B S hS _ _) _ _

/-- The morphism from `Spec 𝒪_{S, s}` to a stage is the canonical morphism to the neighbourhood
followed by the open immersion of the neighbourhood. -/
theorem specStalkπ_comp_glueingStageToW (j : Over W₀) :
    (restrictedSpecStalkSiteCone B S hS s W₀).π.app j ≫ glueingStageToW B S hS s W₀ U j =
      glueingStageToM B S hS s W₀ U j :=
  rfl

/-! ### The stages are cofinal among the opens `U'` with `U ⊆ U'` and `s ∈ U'` -/

/-- Every stage is an open containing `U` and the point `s`. -/
theorem le_and_mem_glueingStageOpen (j : Over W₀) :
    U ≤ U ⊔ j.left.obj.1 ∧ s ∈ U ⊔ j.left.obj.1 :=
  ⟨le_sup_left, TopologicalSpace.Opens.mem_sup.2 (Or.inr j.left.obj.2)⟩

/-- Every open containing `U` and the point `s` contains a stage. -/
theorem exists_glueingStageOpen_le (U' : S.Opens) (hUU' : U ≤ U') (hsU' : s ∈ U') :
    ∃ j : Over W₀, U ⊔ j.left.obj.1 ≤ U' := by
  obtain ⟨W, hW⟩ := exists_affineOpenNhds_le S s ⟨U' ⊓ W₀.obj.1, ⟨hsU', W₀.obj.2⟩⟩
  have h : W.obj.1 ≤ U' ⊓ W₀.obj.1 := hW
  exact ⟨Over.mk (ObjectProperty.homMk (X := W) (Y := W₀)
      (homOfLE (show W.obj ≤ W₀.obj from h.trans inf_le_right))),
    sup_le hUU' (h.trans inf_le_left)⟩

/-! ### Stacks 0E8Z at a stage -/

namespace FinitePresentationSpacesOver

/-- Base change is an equivalence from the algebraic spaces of finite presentation over the stage
`U ∪ W` to the `2`-fibre product `FP_U ×_{FP_{W ∩ U}} FP_W`. -/
theorem isEquivalence_glueingFunctor_glueingStage (j : Over W₀) :
    (glueingFunctor B S hS (isPullback_glueingStage B S hS s W₀ U j).w).IsEquivalence :=
  isEquivalence_glueingFunctor_of_mono_hom B S hS (isPullback_glueingStage B S hS s W₀ U j)
    (inferInstanceAs (IsOpenImmersion (S.homOfLE (le_sup_left : U ≤ U ⊔ j.left.obj.1))))
    (inferInstanceAs (IsOpenImmersion
      (S.homOfLE (le_sup_right : j.left.obj.1 ≤ U ⊔ j.left.obj.1))))
    (range_union_glueingStage B S hS s W₀ U j)
    (BigFppfOver.isOpenImmersion_opensObj_hom B S hS U)
    (isOpenImmersion_restrictedAffineOpenNhdsSiteDiagram_obj_hom B S hS s W₀ j)
    (inferInstanceAs (Mono (Scheme.Opens.ι (X := S) (U ⊔ j.left.obj.1))))

/-! ### Stacks 0E91 -/

/-- Let `S` be a scheme, `U` a retrocompact open of `S` and `s` a point of `S`, and put
`V = Spec 𝒪_{S, s} ∩ U`. Every stage `U ∪ W` is an open containing `U` and `s`; every open
containing `U` and `s` contains a stage; and base change exhibits
`FP_U ×_{FP_V} FP_{Spec 𝒪_{S, s}}` as the filtered `2`-colimit of the categories `FP_{U ∪ W}`
in the sense of `IsGlueingColimitEquivalence`: every object of the `2`-fibre product is, up to
isomorphism, the image of an object over some stage; a morphism between the images of two objects
of a stage is the image of a morphism at a later stage; and two morphisms of a stage whose images
agree already agree at a later stage. -/
theorem isGlueingColimitEquivalence_specStalk (hU : IsRetrocompact (U : Set S)) :
    (∀ j : Over W₀, U ≤ U ⊔ j.left.obj.1 ∧ s ∈ U ⊔ j.left.obj.1) ∧
      (∀ U' : S.Opens, U ≤ U' → s ∈ U' → ∃ j : Over W₀, U ⊔ j.left.obj.1 ≤ U') ∧
        IsGlueingColimitEquivalence B S hS (glueingStageSiteDiagram B S hS s W₀ U)
          (glueingStageToU B S hS s W₀ U) (glueingStageToM B S hS s W₀ U)
          (glueingSquare B S hS (isPullback_glueingStage B S hS s W₀ U)
            (specStalkπ_comp_glueingStageToW B S hS s W₀ U)
            (opensSpecStalkSiteπ_comp_stageToU B S hS s W₀ U)
            (opensSpecStalkSiteπ_comp_stageToW B S hS s W₀ U))
          (fun {_ _} e => glueingStageToU_comp B S hS s W₀ U e)
          (glueingCone B S hS (fun {_ _} e => glueingStageToW_comp B S hS s W₀ U e)
            (specStalkπ_comp_glueingStageToW B S hS s W₀ U)
            (fun {_ _} e => (restrictedSpecStalkSiteCone B S hS s W₀).w e)) :=
  ⟨le_and_mem_glueingStageOpen S s W₀ U,
    fun U' hUU' hsU' => exists_glueingStageOpen_le S s W₀ U U' hUU' hsU',
    isGlueingColimitEquivalence_of_colimit B S hS
      (hsqW := isPullback_glueingStage B S hS s W₀ U)
      (hjUZ := fun {_ _} e => glueingStageToU_comp B S hS s W₀ U e)
      (hjWZ := fun {_ _} e => glueingStageToW_comp B S hS s W₀ U e)
      (hjMW := specStalkπ_comp_glueingStageToW B S hS s W₀ U)
      (hpM := fun {_ _} e => (restrictedSpecStalkSiteCone B S hS s W₀).w e)
      (hpN := fun {_ _} e => (opensSpecStalkSiteCone B S hS s W₀ U).w e)
      (hpNU := opensSpecStalkSiteπ_comp_stageToU B S hS s W₀ U)
      (hpNW := opensSpecStalkSiteπ_comp_stageToW B S hS s W₀ U)
      (hiUn := fun {_ _} e => opensSpecStalkSiteDiagram_map_comp_stageToU B S hS s W₀ U e)
      (hiWn := fun {_ _} e => opensSpecStalkSiteDiagram_map_comp_stageToW B S hS s W₀ U e)
      (hloc := isFinitePresentationColimit_restrictedSpecStalkSiteCone B S hS s W₀)
      (hoverlap := isFinitePresentationColimit_opensSpecStalkSiteCone B S hS s W₀ U hU)
      (hstage := isEquivalence_glueingFunctor_glueingStage B S hS s W₀ U)⟩

/-! ### Stacks 0E91: the equivalence of categories out of the filtered `2`-colimit -/

/-- The comparison functor out of the filtered `2`-colimit of the categories of algebraic spaces
of finite presentation over the stages `U ∪ W` to the `2`-fibre product
`FP_U ×_{FP_V} FP_{Spec 𝒪_{S, s}}`. It takes a space over a stage to its base changes to `U` and
to `Spec 𝒪_{S, s}`, together with the canonical identification of their further base changes to
`V`. -/
noncomputable def specStalkStageColimitFunctor :
    StageColimit B S hS (glueingStageSiteDiagram B S hS s W₀ U) ⥤
      IsoComma (baseChange B S hS (opensSpecStalkApexToU B S hS s W₀ U))
        (baseChange B S hS (opensSpecStalkApexToM B S hS s W₀ U)) :=
  StageColimit.glueingColimitFunctor B S hS
    (glueingSquare B S hS (isPullback_glueingStage B S hS s W₀ U)
      (specStalkπ_comp_glueingStageToW B S hS s W₀ U)
      (opensSpecStalkSiteπ_comp_stageToU B S hS s W₀ U)
      (opensSpecStalkSiteπ_comp_stageToW B S hS s W₀ U))
    (fun {_ _} e => glueingStageToU_comp B S hS s W₀ U e)
    (glueingCone B S hS (fun {_ _} e => glueingStageToW_comp B S hS s W₀ U e)
      (specStalkπ_comp_glueingStageToW B S hS s W₀ U)
      (fun {_ _} e => (restrictedSpecStalkSiteCone B S hS s W₀).w e))

/-- Let `S` be a scheme, `U` a retrocompact open of `S` and `s` a point of `S`, and put
`V = Spec 𝒪_{S, s} ∩ U`. Then the comparison functor
`colim_{s ∈ U' ⊇ U open} FP_{U'} ⟶ FP_U ×_{FP_V} FP_{Spec 𝒪_{S, s}}`
is an equivalence of categories.

The colimit is the category `StageColimit` over the stages `U ∪ W`, `W` running over the affine
open neighbourhoods of `s` contained in `W₀`. The first two clauses say that the stages are
cofinal among the opens `U'` of `S` with `U ⊆ U'` and `s ∈ U'`; the third and fourth identify
the remaining vertices of the `2`-fibre product as `Spec 𝒪_{S, s}` and as `V`, the preimage of
`U` in `Spec 𝒪_{S, s}`; the fifth is the equivalence. -/
@[stacks 0E91 "the equivalence of categories out of the filtered 2-colimit. The colimit of the \
categories `FP_{U ∪ W}` is the category `StageColimit` — objects the spaces over a stage, \
morphisms the germs — and the comparison functor `specStalkStageColimitFunctor` out of it to \
`FP_U ×_{FP_V} FP_{Spec O_{S,s}}` is full, faithful and essentially surjective, which is the \
fifth clause. The colimit runs over the stages `U ∪ W`, `W` an affine open neighbourhood of `s` \
inside a fixed one; the first two clauses say these are a cofinal family among the tag's opens \
`U'` with `U ⊆ U'` and `s ∈ U'`, so the colimit is the tag's. The third and fourth clauses pin \
the other two vertices: `Spec O_{S,s}`, and `V` as the preimage of `U` in it. The sole \
hypothesis is the tag's, that `U` is retrocompact in `S`; the tag's `s ∉ U` is unused, so the \
statement covers it"]
theorem isEquivalence_specStalkStageColimitFunctor (hU : IsRetrocompact (U : Set S)) :
    (∀ j : Over W₀, U ≤ U ⊔ j.left.obj.1 ∧ s ∈ U ⊔ j.left.obj.1) ∧
      (∀ U' : S.Opens, U ≤ U' → s ∈ U' → ∃ j : Over W₀, U ⊔ j.left.obj.1 ≤ U') ∧
        (BigFppfOver.toScheme B S hS).obj (restrictedSpecStalkSiteCone B S hS s W₀).pt =
            Spec (S.presheaf.stalk s) ∧
          (BigFppfOver.toScheme B S hS).obj (opensSpecStalkSiteObj B S hS s W₀ U) =
              (S.fromSpecStalk s ⁻¹ᵁ U).toScheme ∧
            (specStalkStageColimitFunctor B S hS s W₀ U).IsEquivalence :=
  ⟨le_and_mem_glueingStageOpen S s W₀ U,
    fun U' hUU' hsU' => exists_glueingStageOpen_le S s W₀ U U' hUU' hsU',
    toScheme_obj_specStalkSiteObj B S hS s,
    toScheme_obj_opensSpecStalkSiteObj_eq B S hS s W₀ U,
    StageColimit.isEquivalence_glueingColimitFunctor B S hS _ _ _
      (isGlueingColimitEquivalence_specStalk B S hS s W₀ U hU).2.2⟩

end FinitePresentationSpacesOver

end AlgebraicGeometry

end
