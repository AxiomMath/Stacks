module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.AffineCriteria
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.CohenMacaulaySliceBridge
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.ReachMapFiniteTypePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RefinementFromReachMap

/-!
# Step 3 of the proof of Stacks 0489 for the Cohen-Macaulay restriction

Steps 1 and 2 of the proof of [Stacks Project, Tag 0489] are joined in
`AlgebraicGeometry.exists_affine_slice_cohenMacaulayRestriction`: for the restriction `G₁` of
an equivalence-relation groupoid `G` with flat, locally finitely presented source and target to
the Cohen-Macaulay open `W` of [Stacks Project, Tag 0460], every finite type point `u` of `W`
has an affine slice `g_u : U'_u ⟶ W`, an immersion locally of finite presentation through `u`,
whose reach map `h_u` is flat, locally of finite presentation and locally quasi-finite.

Step 3 forms `U' = ∐_u U'_u` over those points and `g = ∐_u g_u`.  This module carries it out
and so produces a `Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` of `G₁` for the big
fppf site, which makes [Stacks Project, Tag 0489] unconditional for `G₁`.

Everything it needs is in place.  The three geometric properties of the total reach map follow
from those of the `h_u` because each is Zariski-local at the source
(`AlgebraicGeometry.reachMap_sigmaDesc_mem`); surjectivity follows because each `h_u` is flat
and locally of finite presentation, hence has open image, and that image contains `u`
(`AlgebraicGeometry.surjective_reachMap_sigmaDesc_of_finiteTypePoints`); the coproduct is an
object of the site because the `g_u` are monomorphisms into one scheme and the index type is a
set of points of it (`AlgebraicGeometry.Scheme.size_sigma_lt_of_mono`); the arrow scheme is
because `G₁` is an equivalence relation
(`AlgebraicGeometry.BigFppfSite.contains_arrows_of_isEquivalenceRelation`); and the whole
site-theoretic datum is assembled by
`AlgebraicGeometry.quasiFiniteRefinementOfReachMap`.

## Main results

* `AlgebraicGeometry.exists_quasiFiniteRefinement_cohenMacaulayRestriction`: **Step 3 of the
  proof of [Stacks Project, Tag 0489]** -- the Cohen-Macaulay restriction of an
  equivalence-relation groupoid whose object scheme belongs to the site admits a
  `QuasiFiniteRefinement`.
* `AlgebraicGeometry.exists_restriction_locallyQuasiFinite_isIso_quotientMap_cohenMacaulay`:
  **[Stacks Project, Tag 0489] for the Cohen-Macaulay restriction, unconditionally.**

## Implementation notes

The index type is the subtype of finite type points of the object scheme of `G₁`, which lies in
`Type u` because the underlying space of a `Scheme.{u}` does; the family of slices is chosen
from the existential statement of Steps 1 and 2 by `choose`.

The restriction `G₁` is the canonical `AlgebraicGeometry.GroupoidScheme.restrict` of `G` along
the open immersion of the Cohen-Macaulay open, as in
`AlgebraicGeometry.exists_affine_slice_cohenMacaulayRestriction`, so the statements of the two
match without transport.  Its object scheme belongs to the site because the object scheme of
`G` does and an open of a scheme of the site is in the site
(`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion`); the identification of
`G₁.objects` with the open is the field `objects_eq` of
`AlgebraicGeometry.GroupoidScheme.Restriction`.

What this module does *not* do is pass from `G₁` back to `G`.  The reach map of the open
immersion `W ⟶ U` is flat, locally of finite presentation and surjective -- surjectivity is
part (3) of [Stacks Project, Tag 0460],
`AlgebraicGeometry.source_from_target_surjective` -- so it is a covering and `W/R₁ ⟶ U/R` is
an isomorphism by [Stacks Project, Tag 02VH]; but it is not locally quasi-finite, so the open
immersion is not itself a `QuasiFiniteRefinement`, and composing the two refinements needs the
restriction of a restriction to be identified with a restriction.

## References

* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Step 3 of the proof of [Stacks Project, Tag 0489].**

Let `G` be a groupoid scheme over `S` whose target and source are an internal equivalence
relation and are flat and locally of finite presentation, with object scheme belonging to the
big fppf site `B`.  Then the restriction `G₁` of `G` to the Cohen-Macaulay open of
[Stacks Project, Tag 0460] admits a
`Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` for the big fppf site over `S`: the
coproduct of the affine slices of [Stacks Project, Tag 04N0] over the finite type points of
that open. -/
theorem exists_quasiFiniteRefinement_cohenMacaulayRestriction (G : GroupoidScheme S)
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]
    (hU : B.Contains G.objects.left) :
    let W := cohenMacaulayOpen G
    let gW : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
    Nonempty (GroupoidScheme.QuasiFiniteRefinement (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) (GroupoidScheme.restrict G gW).groupoid) := by
  classical
  intro W gW
  let : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  let : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)
  set G₁ := (GroupoidScheme.restrict G gW).groupoid with hG₁
  have hrel : CategoryTheory.IsEquivalenceRelation G₁.target G₁.source :=
    isEquivalenceRelation_cohenMacaulayRestriction G
  -- the object scheme of the restriction is the Cohen-Macaulay open, hence in the site
  have hobj : B.Contains G₁.objects.left := by
    have h : G₁.objects.left = (W : Scheme.{u}) :=
      congrArg (fun T : Over S => T.left) (GroupoidScheme.restrict G gW).objects_eq
    rw [show B.Contains G₁.objects.left = B.Contains (W : Scheme.{u}) from by rw [h]]
    exact Scheme.size_lt_of_isOpenImmersion W.ι hU
  have harrows : B.Contains G₁.arrows.left :=
    B.contains_arrows_of_isEquivalenceRelation G₁ hobj
  -- Steps 1 and 2: a slice at every finite type point of the Cohen-Macaulay open
  have hslice := exists_affine_slice_cohenMacaulayRestriction G
  have hfam : ∀ i : {x : G₁.objects.left // IsFiniteTypePoint x},
      ∃ (U' : Scheme.{u}) (g : U' ⟶ G₁.objects.left) (u' : U'),
        g u' = i.1 ∧ IsAffine U' ∧ IsImmersion g ∧ LocallyOfFinitePresentation g ∧
        Flat (pullback.snd g G₁.target.left ≫ G₁.source.left) ∧
        LocallyOfFinitePresentation (pullback.snd g G₁.target.left ≫ G₁.source.left) ∧
        LocallyQuasiFinite (pullback.snd g G₁.target.left ≫ G₁.source.left) := by
    intro i
    obtain ⟨U'', g, u', h₁, h₂, h₃, h₄, h₅, h₆, h₇, -⟩ := hslice i.1 i.2
    exact ⟨U'', g, u', h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩
  choose V q u' hpt haff himm hgl hflat hlfp hlqf using hfam
  -- the coproduct of the slices is an object of the site
  have hsigma : B.Contains (∐ V) := by
    refine Scheme.size_sigma_lt_of_mono B.cutoff_isStrongPrelimit hobj V q (fun i => ?_)
      (Cardinal.mk_subtype_le _)
    have := himm i
    infer_instance
  -- the total reach map
  have hflat' : Flat (pullback.snd (Sigma.desc q) G₁.target.left ≫ G₁.source.left) :=
    reachMap_sigmaDesc_mem (P := @Flat.{u}) G₁ q hflat
  have hlfp' : LocallyOfFinitePresentation
      (pullback.snd (Sigma.desc q) G₁.target.left ≫ G₁.source.left) :=
    reachMap_sigmaDesc_mem (P := @LocallyOfFinitePresentation.{u}) G₁ q hlfp
  have hlqf' : LocallyQuasiFinite
      (pullback.snd (Sigma.desc q) G₁.target.left ≫ G₁.source.left) :=
    reachMap_sigmaDesc_mem (P := @LocallyQuasiFinite.{u}) G₁ q hlqf
  have hsurj' : Surjective (pullback.snd (Sigma.desc q) G₁.target.left ≫ G₁.source.left) :=
    surjective_reachMap_sigmaDesc_of_finiteTypePoints G₁ q hflat hlfp
      (fun x hx => ⟨⟨x, hx⟩, u' ⟨x, hx⟩, hpt ⟨x, hx⟩⟩)
  exact ⟨quasiFiniteRefinementOfReachMap B S hS
    (Over.homMk (Sigma.desc q) : Over.mk (Sigma.desc q ≫ G₁.objects.hom) ⟶ G₁.objects)
    hobj hsigma harrows hflat' hlfp' hlqf' hsurj'⟩

/-- **[Stacks Project, Tag 0489] for the Cohen-Macaulay restriction, unconditionally.**

Let `G` be a groupoid scheme over `S` whose target and source are an internal equivalence
relation and are flat and locally of finite presentation, with object scheme in the big fppf
site `B`, and let `G₁` be its restriction to the Cohen-Macaulay open of
[Stacks Project, Tag 0460].  Then there is a morphism `g : U' ⟶ W` to the object scheme of
`G₁` such that *every* groupoid scheme realizing the restriction `G₁|_{U'}` is again an
equivalence relation, has flat, locally finitely presented, locally of finite type and locally
quasi-finite source and target maps, and has `U'/R' ⟶ W/R₁` an isomorphism of quotient
sheaves.

This is `Stacks.Groupoids.GroupoidScheme.exists_restriction_locallyQuasiFinite_isIso_quotientMap`
with its `QuasiFiniteRefinement` hypothesis discharged by
`AlgebraicGeometry.exists_quasiFiniteRefinement_cohenMacaulayRestriction`. -/
theorem exists_restriction_locallyQuasiFinite_isIso_quotientMap_cohenMacaulay
    (G : GroupoidScheme S)
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left] [LocallyOfFinitePresentation G.target.left]
    (hU : B.Contains G.objects.left) :
    letI : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
    let W := cohenMacaulayOpen G
    let gW : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
    let G₁ := (GroupoidScheme.restrict G gW).groupoid
    ∃ (U' : Over S) (g : U' ⟶ G₁.objects),
      ∀ R' : GroupoidScheme.Restriction G₁ g,
      CategoryTheory.IsEquivalenceRelation R'.groupoid.target R'.groupoid.source ∧
      Flat R'.groupoid.source.left ∧
      LocallyOfFinitePresentation R'.groupoid.source.left ∧
      LocallyOfFiniteType R'.groupoid.source.left ∧
      LocallyQuasiFinite R'.groupoid.source.left ∧
      Flat R'.groupoid.target.left ∧
      LocallyOfFinitePresentation R'.groupoid.target.left ∧
      LocallyOfFiniteType R'.groupoid.target.left ∧
      LocallyQuasiFinite R'.groupoid.target.left ∧
      IsIso (GroupoidScheme.restrictionQuotientMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) G₁ g R') := by
  intro W gW G₁
  have : CategoryTheory.IsEquivalenceRelation G₁.target G₁.source :=
    isEquivalenceRelation_cohenMacaulayRestriction G
  obtain ⟨N⟩ := exists_quasiFiniteRefinement_cohenMacaulayRestriction B S hS G hU
  exact GroupoidScheme.exists_restriction_locallyQuasiFinite_isIso_quotientMap
    (BigFppfOver.topology B S hS) (Over.post (X := B.obj hS) B.inclusion) inferInstance G₁ N

end AlgebraicGeometry

end
