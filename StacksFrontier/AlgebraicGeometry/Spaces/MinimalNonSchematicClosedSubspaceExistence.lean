module

public import StacksFrontier.AlgebraicGeometry.Spaces.MinimalNonSchematicClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspacesCardinality
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStageSiteSmall
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescentToLimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.SubfunctorSmall

/-!
# A minimal non-schematic closed subspace, with nothing assumed

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` which is not a
scheme. Then `X` has a closed subspace `Z` which is not a scheme but all of whose proper closed
subspaces are schemes. This is Stacks 0B7Y, and this file proves it outright. It is the companion of Stacks 0B7Z
(`StacksFrontier/AlgebraicGeometry/Spaces/MinimalNonSchematicSpace.lean`), whose hypotheses it
produces.

Being a scheme is `CategoryTheory.Functor.IsRepresentable` of the presheaf underlying the space.
A *proper* closed subspace is a closed subspace `W` with `W ≠ ⊤` as a subfunctor — strictly
smaller than the whole space in the scheme-theoretic sense, which is what "proper closed subspace
`Z ⊂ X`" means in the source and which has nothing to do with the morphism property of being
proper. The two occurrences of the word in the source statement are nested: the outer subspace is
a closed subspace of `X`, and the inner quantifier runs over the proper closed subspaces *of that
subspace*, which here are the subfunctors of `Z.toFunctor`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_isClosedSubspace_minimal_not_isRepresentable`:
  **Stacks 0B7Y**, with nothing assumed beyond the tag's own hypotheses.

## Implementation notes

The argument is the source's, by Zorn's lemma applied to the set of closed subspaces of `X`
which are not schemes, ordered by inclusion. It is nonempty because `⊤` is a closed subspace
(`AlgebraicGeometry.Space.isClosedSubspace_top_subfunctor`) isomorphic to `X`, which is not a
scheme by hypothesis — this is the only place the hypothesis that `X` is not a scheme is used,
and it is what keeps the conclusion from being about an empty poset. A chain has the infimum of
its members as a lower bound: that infimum is again a closed subspace by
`AlgebraicGeometry.Space.isClosedSubspace_sInf`, and it is not a scheme because it is the inverse
limit of the chain, by `AlgebraicGeometry.Space.isLimitClosedSubspaceCone`, so Stacks 07SR would
make one member of the chain a scheme. The empty chain is bounded below by `⊤`. Minimality is
then turned into the inner clause by pushing a proper closed subspace `Z'` of the minimal `Z`
forward to `CategoryTheory.Subfunctor.range (Z'.ι ≫ Z.ι)`, a closed subspace of `X` isomorphic
to `Z'` and contained in `Z`; were it not a scheme, minimality would force it to equal `Z`, and
hence `Z'` to be `⊤`.

*Where Stacks 07SR comes from, and why no bound on the chain is needed.* Stacks 07SR — that a
stage of a limit situation is a scheme as soon as the limit is — is
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`,
and it asks of the inverse system only that it be small for the site,
`AlgebraicGeometry.Space.IsSiteSmall`. A Zorn chain of closed subspaces meets that condition
unconditionally: its transition morphisms are the inclusions of one closed subspace in
another, hence closed immersions, hence monomorphisms, and
`AlgebraicGeometry.Space.IsSiteSmall.of_mono` asks nothing of the index for such a system.
This is what makes the registration carry no side condition on the site: the chain is handed
to Stacks 07SR through `AlgebraicGeometry.Space.LimitSituation.toDescentSituation`, whose one
extra field — that the limit is an algebraic space — is free here because the limit is assumed
representable.

Feeding the chain of this argument to a statement of that shape needs the chain to be indexed
by a `Type u`, since the index set of a limit situation is one, whereas the chain is indexed by
its own members and `CategoryTheory.Subfunctor X` lives in `Type (u + 1)`. The chain is
therefore re-indexed along `equivShrink`, which `CategoryTheory.Subfunctor.small` makes
available: a subfunctor of a presheaf of `u`-types is determined by its values on a small
skeleton of the site, and the big fppf site over `S` is essentially small by
`AlgebraicGeometry.BigFppfOver.essentiallySmall`. The re-indexed chain is a limit situation
because its transition morphisms, being closed immersions, are affine by Stacks 07U2
(`AlgebraicGeometry.Space.isAffineHom_of_isClosedImmersion`).

**Why the chain is not thinned.** An earlier form of this argument asked the ambient site for
a regular cutoff, so that the bound `#chain < B.cutoff` supplied by
`AlgebraicGeometry.Space.mk_lt_cutoff_of_injective_closedSubspaces` would meet a Stacks 07SR
stated at `< B.cutoff.ord.cof`. That route is impossible and is not taken: for
`κ = ℶ_{ω₁}`, which satisfies every condition `AlgebraicGeometry.BigFppfSite` imposes while
being singular of cofinality `ω₁`, take `A = F[x_α : α < ω₁]` over a field `F`, `N` a
quasi-compact quasi-separated non-schematic algebraic space of size below `κ`, and
`X = Spec A ⨿ N`; the chain `Z_β = V(x_α : α < β) ⨿ N` of closed subspaces of `X` consists of
non-schemes and has downward cofinality exactly `ω₁ = cof (κ.ord)`, so no subchain below the
cofinality is cofinal in it or has its infimum. The monomorphism route used instead needs no
thinning at all.

Quasi-compactness and quasi-separatedness of `X` are load-bearing, and both are used in exactly
one place: they are passed to the stages of the chain, each of which is a closed subspace of `X`,
by `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isClosedImmersion` and by
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_isQuasiSeparated` applied to the
quasi-separated morphism `AlgebraicGeometry.Space.isQuasiSeparated_of_isClosedImmersion`. They
are what makes the system a system of the kind Stacks 07SR speaks about. This is in contrast with
Stacks 0B7Z, where the reducedness half of the source proof uses neither.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 07SR](https://stacks.math.columbia.edu/tag/07SR)
* [Stacks Project, Tag 0A0U](https://stacks.math.columbia.edu/tag/0A0U)
* [Stacks Project, Tag 0B7Y](https://stacks.math.columbia.edu/tag/0B7Y)
* [Stacks Project, Tag 0B7Z](https://stacks.math.columbia.edu/tag/0B7Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The chain step of Stacks 0B7Y.** The infimum of a nonempty chain of closed subspaces of a
quasi-compact quasi-separated algebraic space, none of which is a scheme, is not a scheme.

The infimum is the inverse limit of the chain, so Stacks 07SR makes one member of the chain a
scheme.

The chain is a set of subfunctors of `X`, so it is indexed by a `Type (u + 1)`, while the index
set of a limit situation is a `Type u`. It is therefore transported along `equivShrink` to a
`Type u` carrying the reversed order of the chain, which `CategoryTheory.Subfunctor.small`
permits, and the limit situation is assembled there.

Nothing is asked of the size of the chain: the transition morphisms of the system are closed
immersions, hence monomorphisms, so the system is small for the site by
`AlgebraicGeometry.Space.IsSiteSmall.of_mono` whatever its index. -/
private theorem not_isRepresentable_sInf_of_chain (hT : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hT X)
    {c : Set (Subfunctor X)} (hne : c.Nonempty)
    (htotal : ∀ W ∈ c, ∀ W' ∈ c, W ≤ W' ∨ W' ≤ W)
    (hclosed : ∀ W ∈ c, IsClosedSubspace B S hS W)
    (hnot : ∀ W ∈ c, ¬ W.toFunctor.IsRepresentable) :
    ¬ (sInf c).toFunctor.IsRepresentable := by
  intro hrep
  obtain ⟨W₀, hW₀⟩ := hne
  have : Small.{u} (Subfunctor X) := CategoryTheory.Subfunctor.small X
  have : Small.{u} (↥c) := small_of_injective (f := Subtype.val) Subtype.coe_injective
  let : Preorder (Shrink.{u} (↥c)) :=
    Preorder.lift fun i => OrderDual.toDual ((equivShrink (↥c)).symm i)
  set Z : Shrink.{u} (↥c) → Subfunctor X := fun i => ((equivShrink (↥c)).symm i).1
  have hmem : ∀ i : Shrink.{u} (↥c), Z i ∈ c := fun i => ((equivShrink (↥c)).symm i).2
  have hZinj : Function.Injective Z :=
    fun _ _ h => (equivShrink (↥c)).symm.injective (Subtype.ext h)
  have hanti : ∀ ⦃i j : Shrink.{u} (↥c)⦄, i ≤ j → Z j ≤ Z i := fun _ _ h => h
  have : IsDirected (Shrink.{u} (↥c)) (· ≤ ·) := by
    refine ⟨fun i j => ?_⟩
    rcases htotal _ (hmem i) _ (hmem j) with h | h
    · exact ⟨i, le_rfl, h⟩
    · exact ⟨j, h, le_rfl⟩
  have hle : ∀ i, sInf c ≤ Z i := fun i => sInf_le (hmem i)
  have hge : (⨅ i, Z i) ≤ sInf c := by
    refine le_sInf fun W hW => ?_
    have hZk : Z (equivShrink (↥c) ⟨W, hW⟩) = W := by
      show ((equivShrink (↥c)).symm (equivShrink (↥c) ⟨W, hW⟩)).1 = W
      rw [Equiv.symm_apply_apply]
    exact hZk ▸ iInf_le Z (equivShrink (↥c) ⟨W, hW⟩)
  have hci : ∀ {i j : (Shrink.{u} (↥c))ᵒᵖ} (f : i ⟶ j),
      IsClosedImmersion B S hS (Subfunctor.homOfLe (hanti (leOfHom f.unop))) :=
    fun {i _} f => isClosedImmersion_homOfLe' B S hS (hclosed _ (hmem i.unop)).2 _
  let A : LimitSituation B S hS hT (sInf c).toFunctor :=
    { I := Shrink.{u} (↥c)
      system := closedSubspaceDiagram B S hS Z hanti
      isAlgebraicSpace := fun i => (hclosed _ (hmem i)).1
      transition_affine := fun f => isAffineHom_of_isClosedImmersion B S hS _ (hci f)
      quasiCompact := fun i => isQuasiCompactSpace_of_isClosedImmersion B S hS hqc (Z i).ι
        (hclosed _ (hmem i)).2
      quasiSeparated := fun i => isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hT
        (hclosed _ (hmem i)).1 hqs
        (isQuasiSeparated_of_isClosedImmersion B S hS (hclosed _ (hmem i)).2)
      π := (closedSubspaceCone B S hS Z hanti (sInf c) hle).π
      isLimit := isLimitClosedSubspaceCone B S hS (equivShrink (↥c) ⟨W₀, hW₀⟩) Z hanti (sInf c)
        hle hge
      base := equivShrink (↥c) ⟨W₀, hW₀⟩ }
  have : (sInf c).toFunctor.IsRepresentable := hrep
  obtain ⟨i, hi⟩ := DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall
    (A.toDescentSituation (isAlgebraicSpace_of_isRepresentable B S hS (sInf c).toFunctor))
    (.of_mono fun {_ _} f => mono_of_isClosedImmersion B S hS _ (hci f))
    hrep
  exact hnot _ (hmem i) hi

/-- A functor isomorphic to a non-representable functor is not representable. -/
private theorem not_isRepresentable_of_iso {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type v}
    (e : F ≅ G) (h : ¬ F.IsRepresentable) : ¬ G.IsRepresentable :=
  fun hG => h (by have := hG; exact isRepresentable_of_natIso G e.symm)

/-- **Stacks 0B7Y.** Let `X` be a quasi-compact and quasi-separated algebraic space over `S`
which is not a scheme. Then there is a closed subspace `Z` of `X` which is not a scheme but
every closed subspace of `Z` other than `Z` itself — every *proper* closed subspace of `Z` — is
a scheme.

This is the source's proof, by Zorn's lemma applied to the closed subspaces of `X` which are
not schemes, ordered by inclusion: `⊤` is one of them, and the infimum of a chain of them is
one of them because it is the inverse limit of the chain, which is
`AlgebraicGeometry.Space.not_isRepresentable_sInf_of_isChain`. A minimal one is the required
`Z`, and minimality becomes the inner clause by pushing a proper closed subspace of `Z` forward
to a closed subspace of `X` contained in `Z`.

Nothing is assumed beyond the tag's own hypotheses. In particular no condition is imposed on
the size of the chain and none on the site's size cutoff: the chain step is discharged by
`AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj_of_isSiteSmall`,
the library's Stacks 07SR, whose smallness hypothesis is met through
`AlgebraicGeometry.Space.IsSiteSmall.of_mono` because the transition morphisms of the chain are
closed immersions, hence monomorphisms. -/
@[stacks 0B7Y]
theorem exists_isClosedSubspace_minimal_not_isRepresentable (hT : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hT X)
    (hXnotScheme : ¬ X.IsRepresentable) :
    ∃ Z : Subfunctor X, IsClosedSubspace B S hS Z ∧ ¬ Z.toFunctor.IsRepresentable ∧
      ∀ Z' : Subfunctor Z.toFunctor, IsClosedSubspace B S hS Z' → Z' ≠ ⊤ →
        Z'.toFunctor.IsRepresentable := by
  classical
  set 𝒵 : Set (Subfunctor X) :=
    {W | IsClosedSubspace B S hS W ∧ ¬ W.toFunctor.IsRepresentable}
  have hmemtop : (⊤ : Subfunctor X) ∈ 𝒵 := by
    exact ⟨isClosedSubspace_top_subfunctor B S hS hX,
      not_isRepresentable_of_iso (asIso (Subfunctor.ι (⊤ : Subfunctor X))).symm hXnotScheme⟩
  have hbound : ∀ c ⊆ 𝒵, IsChain (fun W W' : Subfunctor X => W' ≤ W) c →
      ∃ lb ∈ 𝒵, ∀ W ∈ c, lb ≤ W := by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊤, hmemtop, by simp⟩
    have htotal : ∀ W ∈ c, ∀ W' ∈ c, W ≤ W' ∨ W' ≤ W := by
      intro W hW W' hW'
      rcases eq_or_ne W W' with rfl | hWW'
      · exact Or.inl le_rfl
      · exact (hchain hW hW' hWW').symm
    refine ⟨sInf c, ⟨isClosedSubspace_sInf B S hS hX c fun W hW => (hc hW).1, ?_⟩,
      fun W hW => sInf_le hW⟩
    exact not_isRepresentable_sInf_of_chain B S hS hT hqc hqs hne htotal
      (fun W hW => (hc hW).1) (fun W hW => (hc hW).2)
  obtain ⟨Z, hZmem, hZmin⟩ := zorn_ge₀ 𝒵 hbound
  refine ⟨Z, hZmem.1, hZmem.2, ?_⟩
  intro Z' hZ' hZ'ne
  have _ : Mono (Z'.ι ≫ Z.ι) := mono_comp _ _
  have hcomp : IsClosedImmersion B S hS (Z'.ι ≫ Z.ι) :=
    isClosedImmersion_comp B S hS _ _ hZ'.2 hZmem.1.2
  have e : Z'.toFunctor ≅ (Subfunctor.range (Z'.ι ≫ Z.ι)).toFunctor :=
    asIso (Subfunctor.toRange (Z'.ι ≫ Z.ι))
  have hfac : inv (Subfunctor.toRange (Z'.ι ≫ Z.ι)) ≫ (Z'.ι ≫ Z.ι) =
      (Subfunctor.range (Z'.ι ≫ Z.ι)).ι :=
    IsIso.inv_hom_id_assoc (Subfunctor.toRange (Z'.ι ≫ Z.ι))
      (Subfunctor.range (Z'.ι ≫ Z.ι)).ι
  have hWci : IsClosedImmersion B S hS (Subfunctor.range (Z'.ι ≫ Z.ι)).ι := by
    rw [← hfac]
    exact MorphismProperty.RespectsIso.precomp _ _ _ hcomp
  have hWle : Subfunctor.range (Z'.ι ≫ Z.ι) ≤ Z := by
    have hsub := Subfunctor.range_comp_le Z'.ι Z.ι
    rwa [Subfunctor.range_ι] at hsub
  by_contra hnotrep
  have hWmem : Subfunctor.range (Z'.ι ≫ Z.ι) ∈ 𝒵 :=
    ⟨⟨hZ'.1.of_iso e, hWci⟩, not_isRepresentable_of_iso e hnotrep⟩
  have hWeq : Subfunctor.range (Z'.ι ≫ Z.ι) = Z := le_antisymm hWle (hZmin hWmem hWle)
  have hinj : ∀ i, Function.Injective (Z.ι.app i) := fun _ => Subtype.coe_injective
  refine hZ'ne ?_
  have hrc : Z'.image Z.ι = Subfunctor.range (Z'.ι ≫ Z.ι) := by
    rw [Subfunctor.range_comp, Subfunctor.range_ι]
  have himg : Z'.image Z.ι = (⊤ : Subfunctor Z.toFunctor).image Z.ι := by
    rw [hrc, hWeq, Subfunctor.image_top, Subfunctor.range_ι]
  -- a subfunctor of `Z` is recovered from its image in `X`, `Z.ι` being injective
  have hpre : ∀ G : Subfunctor Z.toFunctor, (G.image Z.ι).preimage Z.ι = G := by
    intro G
    ext i x
    simp only [Subfunctor.preimage_obj, Subfunctor.image_obj, Set.mem_preimage, Set.mem_image]
    refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
    rintro ⟨y, hy, hxy⟩
    exact hinj i hxy ▸ hy
  calc Z' = (Z'.image Z.ι).preimage Z.ι := (hpre Z').symm
    _ = ((⊤ : Subfunctor Z.toFunctor).image Z.ι).preimage Z.ι := by rw [himg]
    _ = ⊤ := hpre ⊤

end AlgebraicGeometry.Space

end
