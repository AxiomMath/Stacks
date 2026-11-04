module

public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimensionDenseOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceOfRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace

/-!
# Enlarging the recursion's open subspace of [Stacks, Tag 09YB] to a dense one

The inductive step of [Stacks, Tag 09YB] produces, from a quasi-compact open immersion
`j : h_U ⟶ Y` with dense point range and the complementary summand `W` of the splitting
`h_U ×_X Y = h_U ⨿ W`, an open subspace `V ⊆ Y` — the image of `W` — whose point set together
with `j(U)` is the whole of `|Y|`, and a chart of `V` all of whose field-valued fibres have
degree strictly below the previous bound
(`AlgebraicGeometry.Space.exists_isOpenSubspace_chart_isFiniteLocallyFreeOfRank_lt`).

That `V` is **not** dense in `Y`, and [Stacks, Tag 0GUL] — the same induction carrying in
addition a quasi-compact dense open of the base over which the cover is finite étale — needs a
dense one, because its final shrink of the open subspace of the base needs the integral
`π : Y ⟶ X` to carry the complement of the recursion's open to a set that is nowhere dense in
`|X|`.

This file supplies the enlargement. Put

```
O := |Y| ∖ closure |V|,    V⁺ := |V| ∪ O.
```

Then `O` is open and disjoint from `|V|`, hence contained in `|Y| ∖ |V|` and therefore — by the
covering hypothesis — in `j(U)`, so `O` is an open subspace of a representable open subspace of
`Y` and is a **scheme**; `V⁺` is open and **dense**, its complement being the boundary of `|V|`,
which is closed with empty interior; `V ≤ V⁺` and `O ≤ V⁺`; and the complement of `V⁺` is again
contained in `j(U)`, so that the extension step of [Stacks, Tag 0G2D] and the schemehood argument
of `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_openSubspace_cover` apply to
`V⁺` exactly as they do to `V`.

**Why the enlargement is by a disjoint open and not by a coproduct of charts.** The source of
[Stacks, Tag 0GUL] strengthens the induction hypothesis to a *finite family* of étale morphisms
with jointly surjective total morphism, because `V ⨿ W ⟶ Y` has fibre degree the *sum* of the
two degrees and so no smaller bound to recurse at. Enlarging by an open `O` **disjoint** from
`|V|` costs nothing in degree: over a point of `O` the fibre of `V`'s chart is empty and only the
identity of `O` contributes, and over a point of `|V|` the identity of `O` contributes nothing.
So the single-chart induction survives, and the family — whose inductive step is unsound, the
morphism `V_j ⨿ W_j ⟶ Y_j` it applies the induction hypothesis to being in general not
surjective — is not needed.

**Why the complement must be the complement of `V⁺` and not of `|V|`.** [Stacks, Tag 09YB] glues
its extended cover with the *reduced* induced structure on `|Y| ∖ |V|`. Over the interior of that
set the reduction of an open subspace is finite over `Y` but not étale unless the open subspace is
already reduced, so this is not available to [Stacks, Tag 0GUL], which needs the glued cover to be
finite étale over a dense open. Replacing `|V|` by `V⁺` deletes that interior: the complement of
`V⁺` has empty interior, and the reduced structure on it is empty over `V⁺` and hence finite étale
of degree `0` there.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_denseOpenSubspace_representableComplement_of_cover`: **the
  enlargement.** The open subspaces `O` and `V⁺` with all of the properties above.
* `AlgebraicGeometry.Space.exists_reducedClosedSubspace_compl_of_dense_of_le_range`: **the
  closed half of the assembly.** The reduced induced structure on the complement of a dense open
  subspace whose complement lies in `j(U)` is a closed subspace, a **scheme**, **integral** over
  `Y`, disjoint from the dense open and of **empty interior**.

## Use

Nothing here carries a Stacks attribute. These are inputs of the inductive step of
[Stacks, Tag 0GUL], which is
`AlgebraicGeometry.Space.exists_cover_of_openSubspace_cover` in
`StacksFrontier.AlgebraicGeometry.Spaces.IntegralSchemeCoverEtaleInduction`. No chart of `V⁺` is
needed there: the induction recurses into `V` only, and the cover of `V⁺` is the cover of `V`
glued with the identity of a quasi-compact open of `O`.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0GUL](https://stacks.math.columbia.edu/tag/0GUL)
* [Stacks Project, Tag 0G2D](https://stacks.math.columbia.edu/tag/0G2D)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Enlargement

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The dense enlargement of the recursion's open subspace of [Stacks, Tag 09YB].** Let `Y` be
an algebraic space over `S`, let `j : h_U ⟶ Y` be an open immersion from a representable
presheaf, and let `V ⊆ Y` be an open subspace whose point set together with `j(U)` exhausts
`|Y|`. Then there are open subspaces `O` and `V⁺` of `Y` with

* `O` representable — a scheme — with point set `|Y| ∖ closure |V|`;
* `V ≤ V⁺` and `O ≤ V⁺`, the point set of `V⁺` being the union of those of `V` and `O`;
* `|V|` and `|O|` **disjoint**;
* `|V⁺|` **dense** in `|Y|`; and
* the complement of `|V⁺|` contained in `j(U)`.

`O` is a scheme because it is disjoint from `|V|`, hence contained in `|Y| ∖ |V|` and so in
`j(U)` by the covering hypothesis: it is the image along the open immersion `j` of an open
subspace of the representable `h_U`, which is representable by
`AlgebraicGeometry.Space.isRepresentable_of_isOpenSubspace_yoneda`. Density of `|V⁺|` is the
statement that `A ∪ (closure A)ᶜ` is dense for `A` open: a nonempty open set either meets
`(closure A)ᶜ` or is contained in `closure A`, and a nonempty open subset of `closure A` meets
`A`. -/
theorem exists_denseOpenSubspace_representableComplement_of_cover
    (hY : IsAlgebraicSpace B S hS Y) (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ Y)
    (hj : IsOpenImmersion B S hS j) (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hcov : Set.range (pointsMap B S hS (yoneda.obj U) j) ∪
      Set.range (pointsMap B S hS V.toFunctor V.ι) = Set.univ) :
    ∃ O Vp : Subfunctor Y,
      IsOpenSubspace B S hS O ∧ O.toFunctor.IsRepresentable ∧
      IsOpenSubspace B S hS Vp ∧ V ≤ Vp ∧ O ≤ Vp ∧
      Set.range (pointsMap B S hS O.toFunctor O.ι) =
        (closure (Set.range (pointsMap B S hS V.toFunctor V.ι)))ᶜ ∧
      Set.range (pointsMap B S hS Vp.toFunctor Vp.ι) =
        Set.range (pointsMap B S hS V.toFunctor V.ι) ∪
          Set.range (pointsMap B S hS O.toFunctor O.ι) ∧
      Disjoint (Set.range (pointsMap B S hS V.toFunctor V.ι))
        (Set.range (pointsMap B S hS O.toFunctor O.ι)) ∧
      Dense (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι)) ∧
      (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ ⊆
        Set.range (pointsMap B S hS (yoneda.obj U) j) := by
  classical
  set A := Set.range (pointsMap B S hS V.toFunctor V.ι) with hAdef
  have hAopen : IsOpen A := isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY V hV
  have hΩopen : IsOpen ((closure A)ᶜ) := isClosed_closure.isOpen_compl
  -- everything off `A` is in `j(U)`, by the covering hypothesis
  have hoff : ∀ x, x ∉ A → x ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) := by
    intro x hx
    have hmem : x ∈ Set.range (pointsMap B S hS (yoneda.obj U) j) ∪ A := hcov ▸ Set.mem_univ x
    rcases hmem with h | h
    · exact h
    · exact absurd h hx
  have hΩsub : (closure A)ᶜ ⊆ Set.range (pointsMap B S hS (yoneda.obj U) j) :=
    fun x hx => hoff x fun h => hx (subset_closure h)
  -- the two open subspaces
  have hOopen : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS Y ((closure A)ᶜ)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ hΩopen
  have hVpopen : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS Y (A ∪ (closure A)ᶜ)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hY _ (hAopen.union hΩopen)
  have hOrange : Set.range
      (pointsMap B S hS (openSubspaceOfPoints B S hS Y ((closure A)ᶜ)).toFunctor
        (openSubspaceOfPoints B S hS Y ((closure A)ᶜ)).ι) = (closure A)ᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hVprange : Set.range
      (pointsMap B S hS (openSubspaceOfPoints B S hS Y (A ∪ (closure A)ᶜ)).toFunctor
        (openSubspaceOfPoints B S hS Y (A ∪ (closure A)ᶜ)).ι) = A ∪ (closure A)ᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  -- `O` is a scheme: it is the image along `j` of an open subspace of the representable `h_U`
  have hPopen : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS (yoneda.obj U)
      (pointsMap B S hS (yoneda.obj U) j ⁻¹' (closure A)ᶜ)) :=
    isOpenSubspace_openSubspaceOfPoints B S hS (isAlgebraicSpace_yoneda B S hS U) _
      (hΩopen.preimage (continuous_pointsMap B S hS j))
  have hPrep : (openSubspaceOfPoints B S hS (yoneda.obj U)
      (pointsMap B S hS (yoneda.obj U) j ⁻¹' (closure A)ᶜ)).toFunctor.IsRepresentable :=
    isRepresentable_of_isOpenSubspace_yoneda B S hS U _ hPopen
  have hOrep : (openSubspaceOfPoints B S hS Y ((closure A)ᶜ)).toFunctor.IsRepresentable := by
    have h := isRepresentable_openSubspaceOfPoints_range_comp_of_isOpenImmersion B S hS hj
      hPopen hPrep
    have himg : Set.range (pointsMap B S hS (openSubspaceOfPoints B S hS (yoneda.obj U)
        (pointsMap B S hS (yoneda.obj U) j ⁻¹' (closure A)ᶜ)).toFunctor
          ((openSubspaceOfPoints B S hS (yoneda.obj U)
            (pointsMap B S hS (yoneda.obj U) j ⁻¹' (closure A)ᶜ)).ι ≫ j)) = (closure A)ᶜ := by
      rw [pointsMap_comp B S hS _ _ j, Set.range_comp,
        range_pointsMap_ι_openSubspaceOfPoints B S hS
          (pointsMap B S hS (yoneda.obj U) j ⁻¹' (closure A)ᶜ),
        Set.image_preimage_eq_of_subset hΩsub]
    rwa [himg] at h
  -- density of the enlargement
  have hdense : Dense (A ∪ (closure A)ᶜ) := by
    rw [dense_iff_inter_open]
    intro N hNopen hNne
    rcases Set.eq_empty_or_nonempty (N ∩ (closure A)ᶜ) with hemp | hne
    · obtain ⟨x, hxN⟩ := hNne
      have hxcl : x ∈ closure A := by
        by_contra hxc
        exact Set.eq_empty_iff_forall_notMem.1 hemp x ⟨hxN, hxc⟩
      obtain ⟨y, hyN, hyA⟩ := mem_closure_iff.1 hxcl N hNopen hxN
      exact ⟨y, hyN, Or.inl hyA⟩
    · obtain ⟨x, hxN, hxc⟩ := hne
      exact ⟨x, hxN, Or.inr hxc⟩
  refine ⟨openSubspaceOfPoints B S hS Y ((closure A)ᶜ),
    openSubspaceOfPoints B S hS Y (A ∪ (closure A)ᶜ), hOopen, hOrep, hVpopen, ?_, ?_, hOrange,
    ?_, ?_, ?_, ?_⟩
  · exact le_of_range_pointsMap_ι_subset B S hS hVpopen
      (by rw [hVprange]; exact Set.subset_union_left)
  · exact le_of_range_pointsMap_ι_subset B S hS hVpopen
      (by rw [hVprange, hOrange]; exact Set.subset_union_right)
  · rw [hVprange, hOrange]
  · rw [hOrange]
    exact Set.disjoint_left.mpr fun a ha hc => hc (subset_closure ha)
  · rw [hVprange]; exact hdense
  · rw [hVprange]
    exact fun x hx => hoff x fun h => hx (Or.inl h)

end Enlargement

section Complement

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The closed half of the assembly of [Stacks, Tag 0GUL].** Let `Y` be an algebraic space over
`S`, let `j : h_U ⟶ Y` be an open immersion from a representable presheaf and let `V⁺ ⊆ Y` be an
open subspace whose point set is **dense** and whose complement is contained in `j(U)`. Then the
reduced induced structure on that complement
(`AlgebraicGeometry.Space.reducedClosedSubspace`, [Stacks, Tag 03IQ]) is a closed subspace `T`
which

* is **representable** — a scheme — being a closed subspace of `Y` whose point set lies in the
  representable open subspace `j(U)`;
* is **integral** over `Y`, its inclusion being a closed immersion ([Stacks, Tag 081Y]);
* has point set exactly the complement of `|V⁺|`, hence is **disjoint** from `|V⁺|` — so the
  morphism `T ⟶ Y` has empty fibres over `V⁺` and is finite étale of degree `0` there; and
* has **empty interior**, so it is nowhere dense in `|Y|`.

This is what replaces the reduced structure on `|Y| ∖ |V|` of [Stacks, Tag 09YB]: that set has
nonempty interior in general, and over its interior the reduced structure is the reduction of an
*open* subspace, which is finite over `Y` but not étale unless the open subspace is already
reduced. The enlargement of
`AlgebraicGeometry.Space.exists_denseOpenSubspace_representableComplement_of_cover` is exactly
what makes the complement have empty interior. -/
theorem exists_reducedClosedSubspace_compl_of_dense_of_le_range
    (hY : IsAlgebraicSpace B S hS Y) (U : BigFppfOver B S hS) (j : yoneda.obj U ⟶ Y)
    (hj : IsOpenImmersion B S hS j) (Vp : Subfunctor Y) (hVp : IsOpenSubspace B S hS Vp)
    (hdense : Dense (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι)))
    (hsub : (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ ⊆
      Set.range (pointsMap B S hS (yoneda.obj U) j)) :
    ∃ T : Subfunctor Y,
      IsClosedSubspace B S hS T ∧ T.toFunctor.IsRepresentable ∧
      IsIntegralHom B S hS T.ι ∧
      Set.range (pointsMap B S hS T.toFunctor T.ι) =
        (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ ∧
      Disjoint (Set.range (pointsMap B S hS T.toFunctor T.ι))
        (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι)) ∧
      interior (Set.range (pointsMap B S hS T.toFunctor T.ι)) = ∅ := by
  classical
  have hVpopen : IsOpen (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι)) :=
    isOpen_range_pointsMap_ι_of_isOpenSubspace B S hS hY Vp hVp
  have hclosed : _root_.IsClosed (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ :=
    hVpopen.isClosed_compl
  have hTcs : IsClosedSubspace B S hS (reducedClosedSubspace B S hS Y hY
      (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ hclosed) :=
    isClosedSubspace_reducedClosedSubspace B S hS Y hY _ hclosed
  have hTrange : Set.range (pointsMap B S hS (reducedClosedSubspace B S hS Y hY
        (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ hclosed).toFunctor
      (reducedClosedSubspace B S hS Y hY
        (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ hclosed).ι) =
      (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ :=
    range_pointsMap_ι_reducedClosedSubspace B S hS Y hY _ hclosed
  have _ : Mono j := mono_of_isOpenImmersion B S hS j hj
  have hjopen : IsOpenSubspace B S hS (Subfunctor.range j) :=
    isOpenSubspace_range_of_isOpenImmersion U j hj
  have hle : reducedClosedSubspace B S hS Y hY
      (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ hclosed ≤ Subfunctor.range j := by
    refine le_of_range_pointsMap_ι_subset B S hS hjopen ?_
    rw [hTrange, range_pointsMap_ι_range B S hS j]
    exact hsub
  refine ⟨reducedClosedSubspace B S hS Y hY
      (Set.range (pointsMap B S hS Vp.toFunctor Vp.ι))ᶜ hclosed, hTcs,
    isRepresentable_of_le_of_isClosedSubspace B S hS hTcs hle
      (isRepresentable_range_of_isOpenImmersion U j hj),
    isIntegralHom_of_isClosedImmersion B S hS _ hTcs.2, hTrange, ?_, ?_⟩
  · rw [hTrange]
    exact disjoint_compl_left
  · rw [hTrange, interior_compl, hdense.closure_eq, Set.compl_univ]

end Complement

end AlgebraicGeometry.Space

end
