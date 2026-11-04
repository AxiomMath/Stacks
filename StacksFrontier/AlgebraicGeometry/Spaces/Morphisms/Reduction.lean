module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# The reduction of an algebraic space is universally homeomorphic to it

Let `X` be an algebraic space over a scheme `S`. Its *reduction* is the reduced closed subspace
supported on all of its points, `AlgebraicGeometry.Space.reducedClosedSubspace` of Stacks 03IQ
taken at `Set.univ`. Stacks 08AK says that the canonical morphism from the reduction to `X` is a
universal homeomorphism, and that is what is proved here.

## Main results

* `AlgebraicGeometry.Space.universallyOpen_ι_invariantSubspace`: the inclusion of the subspace
  cut out by an invariant subscheme of a surjective étale chart is universally open as soon as
  the subscheme is universally open in the chart.
* `AlgebraicGeometry.Space.universallyOpen_ι_reducedClosedSubspace_univ`: the inclusion of the
  reduction of an algebraic space is universally open.
* `AlgebraicGeometry.Space.universalHomeomorphism_ι_reducedClosedSubspace_univ`: **Stacks
  08AK**, the inclusion of the reduction is a universal homeomorphism.
* `AlgebraicGeometry.universallyOpen_of_isClosedImmersion_of_surjective`: a surjective closed
  immersion of schemes is universally open.

## Implementation notes

The statement is *topological*, and that is what makes it unconditional. A universal
homeomorphism in the sense of Stacks 05Z5 is a condition on the maps of point sets of the
presheaf fibre products `Z ×_X X_{red}`, and those fibre products exist in the presheaf category
whether or not the inclusion of the reduction is representable. Representability of that
inclusion — the closed-subspace clause of Stacks 03IQ, which
`StacksFrontier/AlgebraicGeometry/Spaces/ReducedClosedSubspace.lean` proves only under an effective
descent hypothesis — is therefore not used, and no hypothesis beyond algebraicity of `X`
appears. `Spaces/Morphisms/UniversalHomeomorphism.lean` previously carried a conditional form of
this
statement, which obtained the embedding half of the conclusion from Stacks 0ABJ applied to the
base change of the inclusion and so had to know that the inclusion is an immersion. This
statement subsumes it and that one has been removed.

Each of the three clauses of `IsHomeomorph` is obtained separately, and none of them needs the
inclusion to be an immersion:

* *continuity* is clause (2) of Stacks 03BX, `AlgebraicGeometry.Space.continuous_pointsMap`;
* *injectivity* is Stacks 06RV, `AlgebraicGeometry.Space.pointsMap_injective_of_mono`: the
  inclusion of a subfunctor is a monomorphism, and so is its base change;
* *surjectivity* is Stacks 03H4 applied to the point of the reduction over a given point of the
  test space, which exists because the point set of the reduction is everything;
* *openness* is `AlgebraicGeometry.Space.universallyOpen_of_universallyOpen_etaleChart`, clause
  (3) implies clause (1) of Stacks 03Z5: universal openness may be checked after base change
  along one surjective étale chart of the target. Over the chart `φ : U ⟶ X` the base change of
  the inclusion is the reduced induced closed subscheme `U_{red} ⟶ U` of the chart, by
  `AlgebraicGeometry.Space.exists_isPullback_yoneda_presentation`; that is a *surjective* closed
  immersion of schemes, because the part of the chart lying over all of `|X|` is all of `U`, and
  a surjective closed immersion is a homeomorphism, hence universally open.

The openness step is the whole content, and it is where the restriction to `Set.univ` enters: for
a proper closed subset of `|X|` the base change of the inclusion to the chart is a closed
immersion which is not surjective, and nothing about it is open.

## References

* [Stacks Project, Tag 08AK](https://stacks.math.columbia.edu/tag/08AK)
* [Stacks Project, Tag 03IQ](https://stacks.math.columbia.edu/tag/03IQ)
* [Stacks Project, Tag 03Z5](https://stacks.math.columbia.edu/tag/03Z5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A surjective closed immersion of schemes is universally open.** Every base change of it is
again a surjective closed immersion, and a surjective closed embedding of topological spaces is a
homeomorphism. -/
theorem universallyOpen_of_isClosedImmersion_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] : UniversallyOpen f := by
  rw [UniversallyOpen.eq]
  intro X' Y' i₁ i₂ f' hf
  have hf'c : IsClosedImmersion f' := MorphismProperty.of_isPullback hf.flip inferInstance
  have hf's : Surjective f' := MorphismProperty.of_isPullback hf.flip inferInstance
  exact (isHomeomorph_iff_continuous_isClosedMap_bijective.2
    ⟨f'.continuous, f'.isClosedEmbedding.isClosedMap,
      f'.isClosedEmbedding.injective, f'.surjective⟩).isOpenMap

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transport of universal openness -/

section Transport

variable {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- If a morphism of presheaves on the big fppf site of `S` becomes, after precomposition with an
isomorphism, a universally open morphism, then it is itself universally open: the two base
changes along a common morphism to the target differ by the induced isomorphism, and
`AlgebraicGeometry.Space.isOpenMap_pointsMap_of_comp_isIso` transports openness across it. -/
theorem universallyOpen_of_comp_isIso (e : F ⟶ F') [IsIso e] {g : F' ⟶ G} {f : F ⟶ G}
    (hfg : e ≫ g = f) (hg : UniversallyOpen B S hS g) :
    UniversallyOpen B S hS f := by
  subst hfg
  intro Z hZ h
  have hcond : pullback.fst h (e ≫ g) ≫ h = (pullback.snd h (e ≫ g) ≫ e) ≫ g := by
    rw [Category.assoc, pullback.condition]
  have hcond' : pullback.fst h g ≫ h = (pullback.snd h g ≫ inv e) ≫ e ≫ g := by
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.condition]
  have hiso : IsIso (pullback.lift (pullback.fst h (e ≫ g))
      (pullback.snd h (e ≫ g) ≫ e) hcond) := by
    refine ⟨pullback.lift (pullback.fst h g) (pullback.snd h g ≫ inv e) hcond', ?_, ?_⟩ <;>
      refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, IsIso.hom_inv_id, IsIso.inv_hom_id, Category.comp_id,
        Category.id_comp]
  exact isOpenMap_pointsMap_of_comp_isIso B S hS
    (pullback.lift (pullback.fst h (e ≫ g)) (pullback.snd h (e ≫ g) ≫ e) hcond)
    (pullback.lift_fst _ _ _) (hg Z hZ h)

/-- Universal openness of a morphism of presheaves on the big fppf site of `S` depends only on
the isomorphism class of its arrow: the base change of `g` along `k` is identified, over the
same base, with the base change of `f` along `k` followed by the inverse of the isomorphism of
the targets. -/
theorem universallyOpen_of_arrowIso {X X' Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : X ⟶ Y} {g : X' ⟶ Y'} (e : Arrow.mk f ≅ Arrow.mk g)
    (hf : UniversallyOpen B S hS f) : UniversallyOpen B S hS g := by
  intro Z hZ k
  have hsq : IsPullback (pullback.fst (k ≫ e.inv.right) f)
      (pullback.snd (k ≫ e.inv.right) f ≫ e.hom.left) k g :=
    (IsPullback.of_hasPullback (k ≫ e.inv.right) f).of_iso (Iso.refl _) (Iso.refl _)
      (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) (by simp) rfl
      (by
        show (k ≫ e.inv.right) ≫ e.hom.right = 𝟙 _ ≫ k
        rw [Category.assoc, ← Arrow.comp_right, e.inv_hom_id, Arrow.id_right]
        exact (Category.comp_id k).trans (Category.id_comp k).symm)
      (Arrow.w e.hom).symm
  exact isOpenMap_pointsMap_of_comp_isIso B S hS hsq.isoPullback.inv
    (by rw [Iso.inv_comp_eq, hsq.isoPullback_hom_fst]) (hf Z hZ (k ≫ e.inv.right))

/-- The base change along a chart `φ` of a morphism which that chart presents by a morphism `i`
of the site is universally open as soon as the underlying morphism of schemes of `i` is. -/
theorem universallyOpen_pullback_fst_of_isPullback_yoneda {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ X} {V U : BigFppfOver B S hS} {i : V ⟶ U} {k : yoneda.obj V ⟶ F}
    {φ : yoneda.obj U ⟶ X} (hsq : IsPullback k (yoneda.map i) f φ)
    (hi : AlgebraicGeometry.UniversallyOpen ((BigFppfOver.toScheme B S hS).map i)) :
    UniversallyOpen B S hS (pullback.fst φ f) := by
  have hy : UniversallyOpen B S hS (yoneda.map i) :=
    universallyOpen_of_presheaf_universallyOpen B S hS _
      (presheaf_yoneda_map_of_inverseImage B S hS inferInstance i hi)
  refine universallyOpen_of_comp_isIso B S hS hsq.flip.isoPullback.inv ?_ hy
  rw [Iso.inv_comp_eq]
  exact hsq.flip.isoPullback_hom_fst.symm

end Transport

/-! ### The reduction of an algebraic space -/

section Reduction

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS}
    {φ : yoneda.obj U ⟶ X}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)

include hs he in
/-- **The inclusion of the subspace cut out by an invariant subscheme of a surjective étale chart
is universally open**, as soon as the subscheme is universally open in the chart.

Universal openness is checked after base change along the chart, by clause (3) implies clause (1)
of Stacks 03Z5; over the chart the base change of the inclusion is the subscheme itself, by
`AlgebraicGeometry.Space.exists_isPullback_yoneda_presentation`. -/
theorem universallyOpen_ι_invariantSubspace (hX : IsAlgebraicSpace B S hS X)
    (Z : Subobject ((BigFppfOver.toScheme B S hS).obj U))
    (hZim : AlgebraicGeometry.IsImmersion Z.arrow)
    (hZopen : AlgebraicGeometry.UniversallyOpen Z.arrow)
    (hinv : IsInvariantSubscheme B S hS hs Z) :
    UniversallyOpen B S hS (invariantSubspace B S hS φ Z).ι := by
  obtain ⟨k, hsq⟩ := exists_isPullback_yoneda_presentation B S hS hs Z hinv
    (subschemeι B S hS Z hZim) (Iso.refl _) (Category.id_comp _)
  refine universallyOpen_of_universallyOpen_etaleChart B S hS hX _ φ
    (isSurjective_of_presheafSurjective B S hS φ hs)
    ((isEtale_iff_presheaf_of_yoneda B S hS φ).2 he) ?_
  refine universallyOpen_pullback_fst_of_isPullback_yoneda B S hS hsq ?_
  rw [toScheme_map_subschemeι]
  exact hZopen

include hs he in
/-- **The inclusion of the reduction of an algebraic space is universally open**, computed from
a chart.

The reduced induced closed subscheme of the chart on the part of the chart lying over all of
`|X|` is all of the chart, so it is a surjective closed immersion, and a surjective closed
immersion is universally open. -/
theorem universallyOpen_ι_reducedClosedSubspaceOfChart_univ (hX : IsAlgebraicSpace B S hS X) :
    UniversallyOpen B S hS
      (reducedClosedSubspaceOfChart B S hS φ Set.univ isClosed_univ).ι := by
  have hsurjι : AlgebraicGeometry.Surjective
      (atlasVanishingIdeal B S hS φ Set.univ isClosed_univ).subschemeι := by
    rw [AlgebraicGeometry.surjective_iff, ← Set.range_eq_univ,
      Scheme.IdealSheafData.range_subschemeι, coe_support_atlasVanishingIdeal]
    exact Set.eq_univ_of_forall fun x ↦
      (mem_atlasPointSet_iff B S hS φ Set.univ x).2 (Set.mem_univ _)
  have hopen : AlgebraicGeometry.UniversallyOpen
      (atlasReducedSubscheme B S hS φ Set.univ isClosed_univ).arrow := by
    rw [show (atlasReducedSubscheme B S hS φ Set.univ isClosed_univ).arrow =
        (Subobject.underlyingIso
          (atlasVanishingIdeal B S hS φ Set.univ isClosed_univ).subschemeι).hom ≫
          (atlasVanishingIdeal B S hS φ Set.univ isClosed_univ).subschemeι from
      (Subobject.underlyingIso_hom_comp_eq_mk _).symm]
    exact (MorphismProperty.cancel_left_of_respectsIso (@AlgebraicGeometry.UniversallyOpen.{u})
      (Subobject.underlyingIso
        (atlasVanishingIdeal B S hS φ Set.univ isClosed_univ).subschemeι).hom
      (atlasVanishingIdeal B S hS φ Set.univ isClosed_univ).subschemeι).2
      (universallyOpen_of_isClosedImmersion_of_surjective _)
  exact universallyOpen_ι_invariantSubspace B S hS hs he hX _
    (isImmersion_arrow_atlasReducedSubscheme B S hS φ Set.univ isClosed_univ) hopen
    (isInvariantSubscheme_atlasReducedSubscheme B S hS hs he Set.univ isClosed_univ)

end Reduction

section Univ

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The inclusion of the reduction of an algebraic space is universally open.** -/
theorem universallyOpen_ι_reducedClosedSubspace_univ (hX : IsAlgebraicSpace B S hS X) :
    UniversallyOpen B S hS (reducedClosedSubspace B S hS X hX Set.univ isClosed_univ).ι :=
  universallyOpen_ι_reducedClosedSubspaceOfChart_univ B S hS
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).1
    (Classical.choose_spec (Classical.choose_spec hX.exists_atlas)).2 hX

/-- **Stacks 08AK.** The canonical morphism from the reduction of an algebraic space over `S` —
the reduced closed subspace supported on all of its points — to the space itself is a universal
homeomorphism.

The four clauses are independent of one another: continuity is clause (2) of Stacks 03BX,
injectivity is Stacks 06RV applied to the base change of a subfunctor inclusion, surjectivity is
Stacks 03H4 together with the computation of the point set of the reduction, and openness is
`AlgebraicGeometry.Space.universallyOpen_ι_reducedClosedSubspace_univ`. None of them needs the
inclusion to be representable, so no effective descent hypothesis appears. -/
@[stacks 08AK, ega "IV 2.4.8" "(ii) univ. homeo"]
theorem universalHomeomorphism_ι_reducedClosedSubspace_univ (hX : IsAlgebraicSpace B S hS X) :
    UniversalHomeomorphism B S hS
      (reducedClosedSubspace B S hS X hX Set.univ isClosed_univ).ι := by
  intro Z hZ g
  refine ⟨continuous_pointsMap B S hS _,
    universallyOpen_ι_reducedClosedSubspace_univ B S hS hX Z hZ g,
    pointsMap_injective_of_mono B S hS _, fun y ↦ ?_⟩
  obtain ⟨x, hx⟩ : pointsMap B S hS Z g y ∈ Set.range (pointsMap B S hS
      (reducedClosedSubspace B S hS X hX Set.univ isClosed_univ).toFunctor
      (reducedClosedSubspace B S hS X hX Set.univ isClosed_univ).ι) := by
    rw [range_pointsMap_ι_reducedClosedSubspace]
    exact Set.mem_univ _
  obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g
      (reducedClosedSubspace B S hS X hX Set.univ isClosed_univ).ι) y x hx.symm
  exact ⟨w, hw⟩

end Univ

end Space

end AlgebraicGeometry

end
