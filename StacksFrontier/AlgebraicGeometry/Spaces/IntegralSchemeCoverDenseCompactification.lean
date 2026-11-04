module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImmersionFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionIntoQuotientStackSubspace

/-!
# Making a relative compactification scheme-theoretically dense

Let `j : U ⟶ Y` be a quasi-compact open immersion of algebraic spaces over a scheme `S` and let
`π : Y ⟶ X` be integral. The sentence "we may and do assume that `j(U)` is scheme theoretically
dense in `Y`" of the proof of Stacks 09YB replaces `Y` by the scheme-theoretic closure of `j(U)`
in it. This file carries out that replacement.

The intermediate space is the scheme-theoretic image of Stacks 082X. The whole content is
already in the library:

* it is a closed subspace of `Y`
  (`AlgebraicGeometry.Space.isClosedSubspace_schemeTheoreticImageSubfunctor`), so it is integral
  over `Y` by Stacks 081Y and hence integral over `X` by Stacks 03ZR;
* `U` maps to it by an *open* immersion, which is the quasi-compact case of Stacks 088G
  (`AlgebraicGeometry.Space.isOpenImmersion_toSchemeTheoreticImage`);
* that morphism has scheme-theoretic image everything
  (`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top`).

The last of these is the scheme-theoretic closure of the *range* being everything, and Stacks
0835 turns that into genuine scheme-theoretic density because the inclusion of the range is
quasi-compact — which it is, being an isomorphism away from the quasi-compact `j`.

## Main results

* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_range_toSchemeTheoreticImage`: for a
  quasi-compact open immersion of algebraic spaces, the range of the induced morphism onto the
  scheme-theoretic image is scheme-theoretically dense there.
  Topological density of the same range is part (4) of Stacks 082Z,
  `AlgebraicGeometry.Space.denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact`, and is
  carried along in the package below rather than reproved.
* `AlgebraicGeometry.Space.exists_isSchemeTheoreticallyDense_isIntegralHom_factorization`: the
  replacement itself, in the shape the proof of Stacks 09YB uses it — a factorization of
  `j ≫ π` through an algebraic space integral over `X` in which the image of `U` is
  scheme-theoretically dense and still a quasi-compact open subspace, and *topologically* dense
  as well, which is the form in which the fibre-degree bookkeeping of the induction consumes it.

## Implementation notes

**Why the range and not the morphism.** `AlgebraicGeometry.Space.IsSchemeTheoreticallyDense` is
a predicate on a *subfunctor*, so the statement is about `CategoryTheory.Subfunctor.range` of the
morphism onto the image rather than about that morphism. The two are reconciled by
`CategoryTheory.Subfunctor.toRange` being an isomorphism — the morphism is a monomorphism,
being an open immersion — together with
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_comp_of_epi`, which says the
scheme-theoretic image does not see precomposition with an epimorphism.

**Quasi-compactness of the inclusion** is needed twice: once as a hypothesis of Stacks 088G, and
once as the hypothesis of Stacks 0835 under which "the scheme-theoretic closure is everything"
is equivalent to scheme-theoretic density. In the source it is the word "quasi-compact" in
"quasi-compact open immersion", which is what Stacks 0ABS delivers.

**Nothing here is a Stacks statement in its own right**, so nothing carries a tag; it is the
reduction step of the proof of Stacks 09YB, assembled from tagged results.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 0835](https://stacks.math.columbia.edu/tag/0835)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
* [Stacks Project, Tag 081U](https://stacks.math.columbia.edu/tag/081U)
* [Stacks Project, Tag 081Y](https://stacks.math.columbia.edu/tag/081Y)
* [Stacks Project, Tag 03ZR](https://stacks.math.columbia.edu/tag/03ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The morphism from the source of a quasi-compact morphism onto its scheme-theoretic image is
quasi-compact: the square exhibiting it as a base change of the morphism along the inclusion of
the image is cartesian, the inclusion being a monomorphism. -/
theorem isQuasiCompact_toSchemeTheoreticImage (f : U ⟶ Y) (hq : IsQuasiCompact B S hS f) :
    IsQuasiCompact B S hS (toSchemeTheoreticImage B S hS f) := by
  have hmono : Mono (schemeTheoreticImageSubfunctor B S hS f).ι := inferInstance
  have hsq : IsPullback (𝟙 U) (toSchemeTheoreticImage B S hS f)
      (toSchemeTheoreticImage B S hS f ≫ (schemeTheoreticImageSubfunctor B S hS f).ι)
      (schemeTheoreticImageSubfunctor B S hS f).ι :=
    IsPullback.of_horiz_isIso_mono (CommSq.mk (by rw [Category.id_comp]))
  rw [toSchemeTheoreticImage_ι] at hsq
  exact isQuasiCompact_of_isPullback B S hS hsq hq

/-- The inverse of the isomorphism onto the range of a monomorphism, followed by the monomorphism,
is the inclusion of the range. -/
private theorem inv_toRange_comp_of_mono (f : U ⟶ Y) [Mono f] :
    (asIso (Subfunctor.toRange f)).inv ≫ f = (Subfunctor.range f).ι :=
  (Iso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm

/-- The range of the morphism onto the scheme-theoretic image of a quasi-compact immersion is an
open subspace of that image, and its inclusion is quasi-compact. -/
theorem isOpenSubspace_isQuasiCompact_range_toSchemeTheoreticImage
    (hU : IsAlgebraicSpace B S hS U) (hY : IsAlgebraicSpace B S hS Y) (f : U ⟶ Y)
    (hf : IsImmersion B S hS f) (hq : IsQuasiCompact B S hS f) :
    IsOpenSubspace B S hS (Subfunctor.range (toSchemeTheoreticImage B S hS f)) ∧
      IsQuasiCompact B S hS (Subfunctor.range (toSchemeTheoreticImage B S hS f)).ι := by
  have hoi : IsOpenImmersion B S hS (toSchemeTheoreticImage B S hS f) :=
    isOpenImmersion_toSchemeTheoreticImage B S hS hY f hf hq
  have hmono : Mono (toSchemeTheoreticImage B S hS f) :=
    mono_of_isOpenImmersion B S hS _ hoi
  refine ⟨⟨isAlgebraicSpace_range_of_mono B S hS _ hU,
    prop_range_ι_of_mono B S hS _ _ hoi⟩, ?_⟩
  rw [← inv_toRange_comp_of_mono]
  exact isQuasiCompact_isIso_comp B S hS _
    (isQuasiCompact_toSchemeTheoreticImage B S hS f hq)

/-- **The range of a quasi-compact immersion is scheme-theoretically dense in its
scheme-theoretic image.** This is the reduction "we may and do assume that `j(U)` is scheme
theoretically dense in `Y`" of the proof of Stacks 09YB.

The scheme-theoretic closure of the range is the scheme-theoretic image of the morphism onto the
image, which is everything; the inclusion of the range is quasi-compact, so Stacks 0835 upgrades
that to density. -/
theorem isSchemeTheoreticallyDense_range_toSchemeTheoreticImage
    (hU : IsAlgebraicSpace B S hS U) (hY : IsAlgebraicSpace B S hS Y) (f : U ⟶ Y)
    (hf : IsImmersion B S hS f) (hq : IsQuasiCompact B S hS f) :
    IsSchemeTheoreticallyDense B S hS
      (Subfunctor.range (toSchemeTheoreticImage B S hS f)) := by
  obtain ⟨hopen, hqc⟩ :=
    isOpenSubspace_isQuasiCompact_range_toSchemeTheoreticImage B S hS hU hY f hf hq
  have hoi : IsOpenImmersion B S hS (toSchemeTheoreticImage B S hS f) :=
    isOpenImmersion_toSchemeTheoreticImage B S hS hY f hf hq
  have hmono : Mono (toSchemeTheoreticImage B S hS f) :=
    mono_of_isOpenImmersion B S hS _ hoi
  have hkey : schemeTheoreticClosure B S hS
      (Subfunctor.range (toSchemeTheoreticImage B S hS f)) = ⊤ := by
    show schemeTheoreticImageSubfunctor B S hS
      (Subfunctor.range (toSchemeTheoreticImage B S hS f)).ι = ⊤
    rw [← inv_toRange_comp_of_mono, schemeTheoreticImageSubfunctor_comp_of_epi]
    exact schemeTheoreticImageSubfunctor_toSchemeTheoreticImage_eq_top B S hS f hY
  intro V hV φ hφ
  exact (isSchemeTheoreticallyDense_iff_schemeTheoreticClosure_eq_top B S hS
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS f hY).1 _ hopen hqc).2 hkey hV φ hφ

/-- **The dense relative compactification of the proof of Stacks 09YB.** Let `j : U ⟶ Y` be a
quasi-compact open immersion of algebraic spaces over `S` and let `π : Y ⟶ X` be integral. Then
`j ≫ π` factors as a quasi-compact open immersion `j' : U ⟶ Y'` followed by an integral
`π' : Y' ⟶ X`, with `Y'` an algebraic space in which the range of `j'` is a quasi-compact open
subspace which is *scheme-theoretically dense*.

`Y'` is the scheme-theoretic closure of `j(U)` in `Y`: a closed subspace of `Y`, hence integral
over `Y` by Stacks 081Y and so over `X` by Stacks 03ZR. The source proves this by the same
replacement. -/
theorem exists_isSchemeTheoreticallyDense_isIntegralHom_factorization
    (hU : IsAlgebraicSpace B S hS U) (hY : IsAlgebraicSpace B S hS Y) (j : U ⟶ Y)
    (hj : IsOpenImmersion B S hS j) (hjqc : IsQuasiCompact B S hS j) (π : Y ⟶ X)
    (hπ : IsIntegralHom B S hS π) :
    ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (j' : U ⟶ Y') (π' : Y' ⟶ X),
      IsAlgebraicSpace B S hS Y' ∧ IsOpenImmersion B S hS j' ∧
        IsQuasiCompact B S hS j' ∧ IsIntegralHom B S hS π' ∧ j' ≫ π' = j ≫ π ∧
        IsOpenSubspace B S hS (Subfunctor.range j') ∧
        IsQuasiCompact B S hS (Subfunctor.range j').ι ∧
        IsSchemeTheoreticallyDense B S hS (Subfunctor.range j') ∧
        DenseRange (pointsMap B S hS U j') := by
  have hjim : IsImmersion B S hS j := isImmersion_of_isOpenImmersion B S hS hj
  have hclosed : IsClosedSubspace B S hS (schemeTheoreticImageSubfunctor B S hS j) :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS j hY
  obtain ⟨hopen, hqc⟩ :=
    isOpenSubspace_isQuasiCompact_range_toSchemeTheoreticImage B S hS hU hY j hjim hjqc
  refine ⟨(schemeTheoreticImageSubfunctor B S hS j).toFunctor,
    toSchemeTheoreticImage B S hS j,
    (schemeTheoreticImageSubfunctor B S hS j).ι ≫ π, hclosed.1,
    isOpenImmersion_toSchemeTheoreticImage B S hS hY j hjim hjqc,
    isQuasiCompact_toSchemeTheoreticImage B S hS j hjqc,
    isIntegralHom_comp B S hS
      (isIntegralHom_of_isClosedImmersion B S hS _ hclosed.2) hπ, ?_, hopen, hqc,
    isSchemeTheoreticallyDense_range_toSchemeTheoreticImage B S hS hU hY j hjim hjqc,
    denseRange_pointsMap_toSchemeTheoreticImage_of_isQuasiCompact B S hS j hU hY hjqc⟩
  rw [← Category.assoc, toSchemeTheoreticImage_ι]

end AlgebraicGeometry.Space

end
