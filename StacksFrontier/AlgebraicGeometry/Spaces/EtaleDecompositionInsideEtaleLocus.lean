module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleNeighbourhoodOpenCopyFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealOfQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyDescentSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentIdealPowers

/-!
# An étale decomposition whose isomorphic piece lies inside a prescribed étale locus

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S` and let
`a : A ⟶ X` be an open immersion such that the composite `a ≫ f` is étale — so `f` is étale
on the open piece `A` of `X`. For a point `α` of `|A|` there are an étale morphism
`g : A ⟶ Y`, namely `a ≫ f` itself, and a decomposition of the base change `A ×_Y X` into two
open and closed pieces, one of which maps isomorphically onto `A` and carries a point over
`α`.

What this file adds to
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_of_isEtaleAt` is that the
isomorphic piece **factors through `a`**: the composite of its inclusion with the second
projection `A ×_Y X ⟶ X` is `t ≫ a` for a morphism `t` out of the piece. In the earlier
result the open piece on which `f` is étale is read off `AlgebraicGeometry.Space.IsEtaleAt` and
then discarded, so no containment can be stated; taking it as an explicit input exposes one.

## Main results

* `AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough`: the
  decomposition above, with the factorization of the isomorphic piece through `a`.
* `AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough_chart`: the
  same in the situation of [Stacks, Tag 0GUY], where `f` is the finite morphism `π : Y ⟶ X` of
  the situation and `a` is the open immersion `j : V ⟶ Y` of its affine chart.
* `AlgebraicGeometry.Space.isIso_etaleModulePullback_map_idealSheafPow_ι_of_comp_eq_chart`: in
  that situation, the sheaf of ideals `ℐ` of [Stacks, Tag 0GUY] restricts to the whole structure
  sheaf along any étale morphism factoring through the chart — so `ℐⁿ|_W = 𝒪_W` for the
  isomorphic piece `W` produced above.

## Implementation notes

The étale neighbourhood is `A` itself and the étale morphism to `Y` is `a ≫ f`, so the base
change is `A ×_Y X` and the isomorphic piece is the range of the graph
`(𝟙 A, a) : A ⟶ A ×_Y X`. The three facts about that graph are the ones of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleNeighbourhoodOpenCopy.lean`: it is an open immersion
by `AlgebraicGeometry.Space.isOpenImmersion_pullbackLift_id_of_isEtale`, which is exactly where
`a` being an open immersion is used; the inclusion of its range followed by the first projection
is an isomorphism by
`AlgebraicGeometry.Space.isIso_range_ι_comp_pullbackFst_pullbackLift_id`; and its range carries
a point over `α` and over `a(α)` by
`AlgebraicGeometry.Space.exists_point_range_pullbackLift_id`. It is a closed immersion because
it is a section of the separated base change `A ×_Y X ⟶ A`, by part (3) of [Stacks, Tag 03KP].

The factorization is free: the morphism `t` is the isomorphism `V.ι ≫ pullback.fst` of the
conclusion itself, viewed as a morphism to `A`. Both `t ≫ a` and `V.ι ≫ pullback.snd` become
`a` after precomposition with `CategoryTheory.Subfunctor.toRange` of the graph, by
`CategoryTheory.Limits.pullback.lift_fst` and `CategoryTheory.Limits.pullback.lift_snd`
respectively, and that morphism is invertible because the graph is a monomorphism.

The complementary piece and the two lattice identities are obtained from the clopen point set
of the isomorphic piece exactly as in
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_of_isEtaleAt`: the point set is
open because the piece is an open subspace and closed because it is a closed subspace, and the
piece is recovered from its point set because an open subspace is determined by its points, by
part (1) of [Stacks, Tag 03BZ].

### What this is for, and what is still missing for [Stacks, Tag 0GUZ]

The proof of [Stacks, Tag 0GUZ] chooses an étale neighbourhood `(U, u) ⟶ (X, x)` splitting
`U ×_X Y` as `W ⊔ W'` with `W ⟶ U` an isomorphism, and then says "after shrinking `U` further
if necessary we may assume `W` maps into `V ⊂ Y` by the projection". That clause is the
factorization proved here, and `AlgebraicGeometry.Space.IsEtaleAt` makes the shrinking
unnecessary: the neighbourhood produced is the chart itself, so the copy lies inside it by
construction.

**No part of [Stacks, Tag 0GUZ] is claimed, and nothing here carries `@[stacks 0GUZ]`.** The
hypotheses of that tag's surjectivity step are met in the situation of [Stacks, Tag 0GUY] by
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough_chart` below, but
the step itself — identifying the restriction of the map
`AlgebraicGeometry.Space.resolutionSituationSigma` to the distinguished summand of
`π_*(ℐ^{n_i})|_U` with the section it came from — is not performed, and its inputs are not in
the development. The module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/AffinePushforwardRightAdjoint.lean` records that those
maps `σ` are obtained from
`AlgebraicGeometry.Space.homEquivAffinePushforwardRightAdjoint`, a composite of the hom-set
bijections of [Stacks, Tag 03D4] and of restriction-coextension; **no compatibility of any of
those bijections with étale localization on the base is proved anywhere**, and no result in the
development consumes `AlgebraicGeometry.Space.homEquivAffinePushforwardRightAdjoint` at all.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 04HL](https://stacks.math.columbia.edu/tag/04HL)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY)
* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale decomposition whose isomorphic piece factors through a prescribed open piece of
the source.**

Let `f : X ⟶ Y` be a **separated** morphism of algebraic spaces over `S`, let `a : A ⟶ X` be an
**open immersion** of algebraic spaces with `a ≫ f` **étale**, and let `α` be a point of `|A|`.
Then there are an algebraic space `U` over `S`, an **étale** morphism `g : U ⟶ Y` and a point
`u` of `|U|` over the image of `a(α)`, together with a decomposition of `U ×_Y X` into two
open-and-closed subspaces `W` and `V` — their join sheafifies to everything and their meet is
the sheafification of nothing — such that

* `V ⟶ U` is an **isomorphism**,
* the composite of the inclusion of `V` with the projection `U ×_Y X ⟶ X` **factors through
  `a`**, and
* some point of `|V|` lies over `u` and over `a(α)`.

This is `AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_of_isEtaleAt` with the
open piece on which `f` is étale supplied as an input rather than read off
`AlgebraicGeometry.Space.IsEtaleAt`, which is what makes the factorization statable. It is the
shrinking clause of the proof of [Stacks, Tag 0GUZ]; see the module documentation. -/
theorem exists_etale_decomposition_isIso_part_factorsThrough
    {A X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hA : IsAlgebraicSpace B S hS A) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hsep : IsSeparated B S hS f)
    (a : A ⟶ X) (ha : IsOpenImmersion B S hS a) (haf : IsEtale B S hS (a ≫ f))
    (α : points B S hS A) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
      (u : points B S hS U) (W V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS U g u = pointsMap B S hS X f (pointsMap B S hS A a α) ∧
      IsOpenSubspace B S hS W ∧
      IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS V ∧
      IsClosedSubspace B S hS V ∧
      (W ⊔ V).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ V = (⊥ : Subfunctor (pullback g f)).sheafify (BigFppfOver.topology B S hS) ∧
      IsIso (V.ι ≫ pullback.fst g f) ∧
      (∃ t : V.toFunctor ⟶ A, t ≫ a = V.ι ≫ pullback.snd g f) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v =
          pointsMap B S hS A a α := by
  have hcomm : 𝟙 A ≫ (a ≫ f) = a ≫ f := Category.id_comp _
  -- The graph of `a` over `Y`, inside the base change `A ×_Y X`.
  have hΓfst : pullback.lift (𝟙 A) a hcomm ≫ pullback.fst (a ≫ f) f = 𝟙 A :=
    pullback.lift_fst _ _ _
  have hΓsnd : pullback.lift (𝟙 A) a hcomm ≫ pullback.snd (a ≫ f) f = a :=
    pullback.lift_snd _ _ _
  have hΓopen : IsOpenImmersion B S hS (pullback.lift (𝟙 A) a hcomm) :=
    isOpenImmersion_pullbackLift_id_of_isEtale B S hS hX hY hA hcomm haf ha
  have hΓclosed : IsClosedImmersion B S hS (pullback.lift (𝟙 A) a hcomm) :=
    isClosedImmersion_of_isSeparated_of_section B S hS (pullback.fst (a ≫ f) f)
      (isSeparated_pullbackFst B S hS (a ≫ f) hsep)
      (pullback.lift (𝟙 A) a hcomm) hΓfst
  have hP : IsAlgebraicSpace B S hS (pullback (a ≫ f) f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (a ≫ f) f hA hX hY
  have hVo : IsOpenSubspace B S hS (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)) :=
    isOpenSubspace_subfunctorRange B S hS hA hΓopen
  have hVc : IsClosedSubspace B S hS (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)) :=
    isClosedSubspace_range_of_isClosedImmersion B S hS _ hA hΓclosed
  have hiso : IsIso ((Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι ≫
      pullback.fst (a ≫ f) f) :=
    isIso_range_ι_comp_pullbackFst_pullbackLift_id B S hS hcomm
  have hv := exists_point_range_pullbackLift_id B S hS hcomm α (pointsMap B S hS A a α) rfl
  -- The factorization through `a`: both sides agree after precomposing with the invertible
  -- `CategoryTheory.Subfunctor.toRange` of the graph.
  have hmono : Mono (pullback.lift (𝟙 A) a hcomm) := mono_of_mono_fac hΓfst
  have hfac : ((Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι ≫
        pullback.fst (a ≫ f) f) ≫ a =
      (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι ≫ pullback.snd (a ≫ f) f := by
    refine (cancel_epi (Subfunctor.toRange (pullback.lift (𝟙 A) a hcomm))).1 ?_
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, Subfunctor.toRange_ι,
      hΓfst, hΓsnd, Category.id_comp]
  -- The point set of the copy, named so that rewriting the copy does not touch it.
  obtain ⟨T, hTdef⟩ : ∃ T : Set (points B S hS (pullback (a ≫ f) f)),
      T = Set.range (pointsMap B S hS
        (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).toFunctor
        (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι) := ⟨_, rfl⟩
  have hTo : IsOpen T :=
    hTdef ▸ isOpen_range_pointsMap_of_isOpenImmersion B S hS
      (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι hVo.2
  have hTc : IsClosed T :=
    hTdef ▸ isClosed_range_pointsMap_of_isClosedImmersion B S hS hP
      (Subfunctor.range (pullback.lift (𝟙 A) a hcomm)).ι hVc.2
  have hVeq : Subfunctor.range (pullback.lift (𝟙 A) a hcomm) =
      openSubspaceOfPoints B S hS (pullback (a ≫ f) f) T := by
    refine le_antisymm (le_of_range_pointsMap_ι_subset B S hS
      (isOpenSubspace_openSubspaceOfPoints B S hS hP T hTo) ?_)
      (le_of_range_pointsMap_ι_subset B S hS hVo ?_) <;>
    rw [range_pointsMap_ι_openSubspaceOfPoints, hTdef]
  rw [hVeq] at hVo hVc hiso hv hfac
  exact ⟨A, hA, a ≫ f, α, openSubspaceOfPoints B S hS (pullback (a ≫ f) f) Tᶜ,
    openSubspaceOfPoints B S hS (pullback (a ≫ f) f) T, haf,
    pointsMap_comp_apply B S hS a f α,
    isOpenSubspace_openSubspaceOfPoints B S hS hP Tᶜ hTc.isOpen_compl,
    isClosedSubspace_openSubspaceOfPoints B S hS hP Tᶜ hTc.isOpen_compl hTo.isClosed_compl,
    hVo, hVc, sheafify_sup_openSubspaceOfPoints_eq_top B S hS T hTo hTc,
    inf_openSubspaceOfPoints_eq_sheafify_bot B S hS T, hiso, ⟨_, hfac⟩, hv⟩

/-- **The geometric input of the surjectivity step of [Stacks, Tag 0GUZ], in the situation of
[Stacks, Tag 0GUY].**

In the situation of [Stacks, Tag 0GUY] — a quasi-compact and quasi-separated algebraic space
`X` over `S` with an affine surjective étale chart `φ : V ⟶ X` factored as an open immersion
`j : V ⟶ Y` followed by a finite morphism `π : Y ⟶ X` — for every point `v` of `|V|` there are
an étale morphism `g : U ⟶ X` and a point `u` of `|U|` over the image of `v` in `|X|`, together
with a decomposition of `U ×_X Y` into two open-and-closed pieces `W` and `W_V` such that
`W_V ⟶ U` is an **isomorphism**, the composite `W_V ⟶ U ×_X Y ⟶ Y` **factors through `j`**, and
some point of `|W_V|` lies over `u` and over `j(v)`.

The hypotheses of
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough` are met by the
data of the situation: `j` is an open immersion with `j ≫ π = φ` étale, and `π` is finite,
hence separated by part (1) of [Stacks, Tag 03KP] for a finite morphism
(`AlgebraicGeometry.Space.isSeparated_of_isFinite`). The chart is a scheme of the site, so its
Yoneda embedding is an algebraic space by `AlgebraicGeometry.Space.isAlgebraicSpace_yoneda`.

This is the étale neighbourhood that the proof of [Stacks, Tag 0GUZ] chooses before checking
the surjectivity of its map; see the module documentation for what remains of that step. -/
theorem exists_etale_decomposition_isIso_part_factorsThrough_chart
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)
    (v : points B S hS (yoneda.obj D.V)) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ X.1)
      (u : points B S hS U) (W WV : Subfunctor (pullback g D.π)),
      IsEtale B S hS g ∧
      pointsMap B S hS U g u =
        pointsMap B S hS D.Y.1 D.π (pointsMap B S hS (yoneda.obj D.V) D.j v) ∧
      IsOpenSubspace B S hS W ∧
      IsClosedSubspace B S hS W ∧
      IsOpenSubspace B S hS WV ∧
      IsClosedSubspace B S hS WV ∧
      (W ⊔ WV).sheafify (BigFppfOver.topology B S hS) = ⊤ ∧
      W ⊓ WV = (⊥ : Subfunctor (pullback g D.π)).sheafify (BigFppfOver.topology B S hS) ∧
      IsIso (WV.ι ≫ pullback.fst g D.π) ∧
      (∃ t : WV.toFunctor ⟶ yoneda.obj D.V,
        t ≫ D.j = WV.ι ≫ pullback.snd g D.π) ∧
      ∃ w : points B S hS WV.toFunctor,
        pointsMap B S hS WV.toFunctor (WV.ι ≫ pullback.fst g D.π) w = u ∧
        pointsMap B S hS WV.toFunctor (WV.ι ≫ pullback.snd g D.π) w =
          pointsMap B S hS (yoneda.obj D.V) D.j v :=
  exists_etale_decomposition_isIso_part_factorsThrough B S hS
    (isAlgebraicSpace_yoneda B S hS D.V) D.Y.2 X.2 D.π
    (isSeparated_of_isFinite B S hS D.π D.Y.2 X.2 D.isFinite_π)
    D.j D.isOpenImmersion_j (D.comp_eq ▸ D.isEtale_φ) v

/-- **`ℐⁿ` restricts to the whole structure sheaf along an étale morphism factoring through the
chart**, in the situation of [Stacks, Tag 0GUY].

If `c : Z ⟶ Y` is étale and factors as `t ≫ j` through the open immersion `j : V ⟶ Y` of the
situation, then the inclusion `ℐⁿ ⟶ 𝒪_Y` becomes invertible after restriction to `Z`; that is,
`ℐⁿ|_Z = 𝒪_Z`.

This is the step "since `W` maps into `V` we see that `ℐ^{n_i}|_W = 𝒪_W`" of the proof of
[Stacks, Tag 0GUZ], and it applies to the isomorphic piece of
`AlgebraicGeometry.Space.exists_etale_decomposition_isIso_part_factorsThrough_chart`, whose
factorization through `j` is exactly the hypothesis here.

The condition `|V(ℐ)| = |Y| ∖ |j(V)|` of the situation says that the unit locus of `ℐ` *is* the
image of `j`, so the image of `c` lies in it; a positive power has the same unit locus
(`AlgebraicGeometry.Space.idealUnitLocus_idealSheafPow`) and the zeroth power is the whole
structure sheaf, so `ℐⁿ` is the unit ideal on every chart of `Z` by
`AlgebraicGeometry.Space.idealSheaf_obj_smallEtalePostcomp_eq_top`, which is what
`AlgebraicGeometry.Space.isIso_etaleModulePullback_map_idealSheaf_ι` asks for. -/
theorem isIso_etaleModulePullback_map_idealSheafPow_ι_of_comp_eq_chart
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS)
    (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)
    {Z : AlgebraicSpaces B S hS} (c : Z ⟶ D.Y) (hc : IsEtale B S hS c.hom)
    (t : Z.1 ⟶ yoneda.obj D.V) (ht : t ≫ D.j = c.hom) (n : ℕ) :
    IsIso ((etaleModulePullback.{u, u} B S hS c hc).map
      (SheafOfModules.idealSheafPow D.I n).ι) := by
  -- The unit locus of `ℐ` is the image of the chart, the condition of the situation being an
  -- equality of the complements.
  have hcompl : (idealUnitLocus B S hS D.Y D.I)ᶜ =
      (Set.range (pointsMap B S hS (yoneda.obj D.V) D.j))ᶜ := D.idealZeroLocus_I
  have hunit : idealUnitLocus B S hS D.Y D.I =
      Set.range (pointsMap B S hS (yoneda.obj D.V) D.j) := by
    simpa using congrArg compl hcompl
  have hrange : Set.range (pointsMap B S hS Z.1 c.hom) ⊆ idealUnitLocus B S hS D.Y D.I := by
    rw [hunit]
    rintro _ ⟨z, rfl⟩
    exact ⟨pointsMap B S hS Z.1 t z, by rw [← pointsMap_comp_apply, ht]⟩
  have hpow : idealUnitLocus B S hS D.Y D.I ⊆
      idealUnitLocus B S hS D.Y (SheafOfModules.idealSheafPow D.I n) := by
    cases n with
    | zero =>
      have h : SheafOfModules.idealSheafPow D.I 0 = ⊤ :=
        (idealSheafPow_eq_idealPow B S hS D.Y D.I 0).trans (Stacks.Sites.idealPow_zero D.I)
      rw [h, idealUnitLocus_top]
      exact Set.subset_univ _
    | succ m => rw [idealUnitLocus_idealSheafPow B S hS D.Y D.I (Nat.succ_pos m)]
  exact isIso_etaleModulePullback_map_idealSheaf_ι B S hS c hc
    (SheafOfModules.idealSheafPow D.I n)
    (idealSheaf_obj_smallEtalePostcomp_eq_top B S hS c hc
      (SheafOfModules.idealSheafPow D.I n) (hrange.trans hpow))

end AlgebraicGeometry.Space

end
