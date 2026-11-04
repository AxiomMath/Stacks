module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CohenMacaulayQuasiFiniteRefinement

/-!
# The quotient sheaf is unchanged by restricting to the Cohen-Macaulay open

Step 1 of the proof of [Stacks Project, Tag 0489] replaces the object scheme `U` of a flat,
locally finitely presented equivalence-relation groupoid by the Cohen-Macaulay open `W` of
[Stacks Project, Tag 0460].  The replacement is harmless because the reach map of the open
immersion `W ⟶ U` is an fppf covering: it is flat and locally of finite presentation, being an
open immersion followed by the source map, and it is *surjective*, which is part (3) of
[Stacks Project, Tag 0460], `AlgebraicGeometry.source_from_target_surjective`.  So
[Stacks Project, Tag 02VH] makes `W/R₁ ⟶ U/R` an isomorphism.

Together with
`AlgebraicGeometry.exists_restriction_locallyQuasiFinite_isIso_quotientMap_cohenMacaulay` this
gives the conclusion of [Stacks Project, Tag 0489] in the form the rest of the Bootstrap
argument consumes: a groupoid whose source and target are locally quasi-finite (as well as
flat, locally of finite presentation and locally of finite type) with the *same* quotient
sheaf.  Chaining the two isomorphisms of quotient sheaves avoids identifying the restriction
of a restriction with a restriction along the composite, which the library does not have.

## Main results

* `AlgebraicGeometry.isIso_restrictionQuotientMap_of_flat_reachMap`: if the reach map of
  `g : U' ⟶ U` is flat, locally of finite presentation and surjective and the three schemes
  involved lie in the site, then `U'/R' ⟶ U/R` is an isomorphism.  This is
  [Stacks Project, Tag 02VH] with its covering hypothesis discharged.
* `AlgebraicGeometry.isIso_restrictionQuotientMap_cohenMacaulayOpen`: **Step 1 of the proof of
  [Stacks Project, Tag 0489]** -- restricting to the Cohen-Macaulay open does not change the
  quotient sheaf.
* `AlgebraicGeometry.exists_locallyQuasiFinite_groupoid_quotientSheaf_iso`:
  **[Stacks Project, Tag 0489]**, unconditionally, in the form its consumers use: an
  equivalence-relation groupoid with flat, locally finitely presented, locally of finite type
  and locally quasi-finite source and target whose quotient sheaf is isomorphic to the given
  one.

## Implementation notes

The reach map of an open immersion `W.ι` is identified with
`(t ⁻¹ᵁ W).ι ≫ s` by `AlgebraicGeometry.reachSourceIsoTargetPreimage`, which is
`AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq` for the two opens of the arrow scheme: the
range of `pullback.snd W.ι t` is `t ⁻¹' W` by
`AlgebraicGeometry.IsOpenImmersion.range_pullbackSnd`.  That is the form in which part (3) of
[Stacks Project, Tag 0460] states surjectivity.

Flatness and local finite presentation of that reach map need nothing from
[Stacks Project, Tag 0460]: the first projection of the fibre product along an open immersion
is an open immersion, and the source map is flat and locally of finite presentation by
hypothesis.

## References

* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The reach map of an open immersion into the object scheme is, up to an isomorphism of its
source, the restriction of the source map to the inverse image of the open under the target
map. -/
noncomputable def reachSourceIsoTargetPreimage {S : Scheme.{u}} {G : GroupoidScheme S}
    (W : G.objects.left.Opens) :
    pullback W.ι G.target.left ≅ (G.target.left ⁻¹ᵁ W : Scheme.{u}) :=
  IsOpenImmersion.isoOfRangeEq (pullback.snd W.ι G.target.left)
    (G.target.left ⁻¹ᵁ W).ι (by simp [IsOpenImmersion.range_pullbackSnd])

/-- The comparison of `AlgebraicGeometry.reachSourceIsoTargetPreimage` carries the inclusion of
the inverse image to the second projection. -/
theorem reachSourceIsoTargetPreimage_hom_comp {S : Scheme.{u}} {G : GroupoidScheme S}
    (W : G.objects.left.Opens) :
    (reachSourceIsoTargetPreimage W).hom ≫ (G.target.left ⁻¹ᵁ W).ι =
      pullback.snd W.ι G.target.left :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **[Stacks Project, Tag 02VH] with its covering hypothesis discharged.**

If the reach map of `g : U' ⟶ U` is flat, locally of finite presentation and surjective -- so
an fppf covering -- and `U`, `U'` and the arrow scheme lie in the big fppf site, then the map
`U'/R' ⟶ U/R` of quotient sheaves induced by any realization of the restriction is an
isomorphism. -/
theorem isIso_restrictionQuotientMap_of_flat_reachMap
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {G : GroupoidScheme S} {U' : Over S} (g : U' ⟶ G.objects)
    (hU : B.Contains G.objects.left) (hU' : B.Contains U'.left)
    (hR : B.Contains G.arrows.left)
    (hflat : Flat (pullback.snd g.left G.target.left ≫ G.source.left))
    (hlfp : LocallyOfFinitePresentation (pullback.snd g.left G.target.left ≫ G.source.left))
    (hsurj : Surjective (pullback.snd g.left G.target.left ≫ G.source.left))
    (H : GroupoidScheme.Restriction G g) :
    IsIso (GroupoidScheme.restrictionQuotientMap (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) G g H) := by
  have hri : ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange → P.RespectsIso :=
    fun _ h => h.respectsIso
  have hflat' : Flat (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hflat
  have hlfp' : LocallyOfFinitePresentation
      (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hlfp
  have hsurj' : Surjective (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hsurj
  have hP : B.Contains (pullback g G.target).left := contains_reachSource B g hU' hR
  obtain ⟨a, ha⟩ : ∃ a : siteObject B S hS hP (pullback g G.target).hom ⟶
      siteObject B S hS hU G.objects.hom,
      (Over.post (X := B.obj hS) B.inclusion).map a =
        GroupoidScheme.restrictionReachMap G g :=
    (Over.post (X := B.obj hS) B.inclusion).map_surjective _
  have hleft : (BigFppfOver.toScheme B S hS).map a =
      (GroupoidScheme.restrictionReachMap G g).left :=
    congrArg Over.Hom.left ha
  exact GroupoidScheme.isIso_restrictionQuotientMap_of_reach_cover
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion) inferInstance G g H
    _ _ (Iso.refl _) (Iso.refl _) a
    ((Category.comp_id _).trans (ha.trans (Category.id_comp _).symm))
    (Space.singleton_mem_bigFppfOver_topology_of_flat B S hS a
      (by rwa [hleft]) (by rwa [hleft]) (by rwa [hleft]))

/-- **Step 1 of the proof of [Stacks Project, Tag 0489].**  Restricting a flat, locally
finitely presented equivalence-relation groupoid to the Cohen-Macaulay open of
[Stacks Project, Tag 0460] does not change the quotient sheaf. -/
theorem isIso_restrictionQuotientMap_cohenMacaulayOpen
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (G : GroupoidScheme S)
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]
    (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left) :
    let W := cohenMacaulayOpen G
    let gW : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
    ∀ H : GroupoidScheme.Restriction G gW,
      IsIso (GroupoidScheme.restrictionQuotientMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) G gW H) := by
  intro W gW H
  have hcomp : (reachSourceIsoTargetPreimage W).hom ≫
      ((G.target.left ⁻¹ᵁ W).ι ≫ G.source.left) =
      pullback.snd gW.left G.target.left ≫ G.source.left := by
    rw [← Category.assoc, reachSourceIsoTargetPreimage_hom_comp]
    rfl
  have transfer : ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange →
      P ((G.target.left ⁻¹ᵁ W).ι ≫ G.source.left) →
        P (pullback.snd gW.left G.target.left ≫ G.source.left) := fun P hP h => by
    rw [← hcomp]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := P) (hP := hP.respectsIso)
      (reachSourceIsoTargetPreimage W).hom _).2 h
  exact isIso_restrictionQuotientMap_of_flat_reachMap B S hS gW hU
    (Scheme.size_lt_of_isOpenImmersion W.ι hU) hR
    (transfer @Flat.{u} inferInstance inferInstance)
    (transfer @LocallyOfFinitePresentation.{u} inferInstance inferInstance)
    (transfer @Surjective.{u} inferInstance (source_from_target_surjective G)) H

/-- **[Stacks Project, Tag 0489], unconditionally, in the form its consumers use.**

Let `G` be a groupoid scheme over `S` whose target and source are an internal equivalence
relation and are flat and locally of finite presentation, and whose object and arrow schemes
belong to the big fppf site `B`.  Then there is a groupoid scheme `G''` over `S` which is
again an equivalence relation, whose source and target are flat, locally of finite
presentation, locally of finite type *and locally quasi-finite*, and whose quotient sheaf is
isomorphic to that of `G`.

The two steps are composed at the level of quotient sheaves: Step 1 replaces `G` by its
Cohen-Macaulay restriction without changing the quotient
(`AlgebraicGeometry.isIso_restrictionQuotientMap_cohenMacaulayOpen`), and Steps 2 and 3
refine that restriction
(`AlgebraicGeometry.exists_restriction_locallyQuasiFinite_isIso_quotientMap_cohenMacaulay`). -/
theorem exists_locallyQuasiFinite_groupoid_quotientSheaf_iso
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)] (G : GroupoidScheme S)
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]
    (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left) :
    ∃ G'' : GroupoidScheme S,
      CategoryTheory.IsEquivalenceRelation G''.target G''.source ∧
      Flat G''.source.left ∧ LocallyOfFinitePresentation G''.source.left ∧
      LocallyOfFiniteType G''.source.left ∧ LocallyQuasiFinite G''.source.left ∧
      Flat G''.target.left ∧ LocallyOfFinitePresentation G''.target.left ∧
      LocallyOfFiniteType G''.target.left ∧ LocallyQuasiFinite G''.target.left ∧
      Nonempty (quotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (groupoidPreRelation G'') ≅
        quotientSheaf (BigFppfOver.topology B S hS)
          (Over.post (X := B.obj hS) B.inclusion) (groupoidPreRelation G)) := by
  set W := cohenMacaulayOpen G
  set gW : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
  set G₁ := (GroupoidScheme.restrict G gW).groupoid
  have : CategoryTheory.IsEquivalenceRelation G₁.target G₁.source :=
    isEquivalenceRelation_cohenMacaulayRestriction G
  have h₁ := isIso_restrictionQuotientMap_cohenMacaulayOpen B S hS G hU hR
    (GroupoidScheme.restrict G gW)
  obtain ⟨U'', g'', hprops⟩ :=
    exists_restriction_locallyQuasiFinite_isIso_quotientMap_cohenMacaulay B S hS G hU
  obtain ⟨hrel, hsf, hsp, hst, hsq, htf, htp, htt, htq, hiso⟩ :=
    hprops (GroupoidScheme.restrict G₁ g'')
  exact ⟨(GroupoidScheme.restrict G₁ g'').groupoid, hrel, hsf, hsp, hst, hsq, htf, htp, htt,
    htq, ⟨(@asIso _ _ _ _ _ hiso).trans (@asIso _ _ _ _ _ h₁)⟩⟩

end AlgebraicGeometry

end
