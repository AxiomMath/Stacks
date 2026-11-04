module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CohenMacaulayRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.MaxSliceQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.EquivalenceRelationTrivial
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionEquivalenceRelation

/-!
# Steps 1 and 2 of the proof of Stacks 0489, joined

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose target and source are an internal
equivalence relation and whose source and target maps are flat and locally of finite
presentation.

Step 1 of the proof of [Stacks Project, Tag 0489] shrinks `U` to the open
`AlgebraicGeometry.cohenMacaulayOpen` over which `s` becomes Cohen–Macaulay; that is
[Stacks Project, Tag 0460], and in this library it is
`AlgebraicGeometry.restricted_source_cohenMacaulay` and its three companions.  Step 2 produces,
for each finite type point of the shrunken object scheme, an affine slice along which the
restricted groupoid has flat, locally finitely presented, locally quasi-finite structure maps;
that is [Stacks Project, Tag 04N0], in this library
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`.

This file joins the two.  What Step 2 asks for and Step 1 does not provide on its own is the
local quasi-finiteness of the stabilizer group scheme, and for an equivalence relation that is
automatic: the stabilizer is the object scheme itself
(`AlgebraicGeometry.isIso_stabilizer_hom`), and being an equivalence relation is inherited by
the restriction (`AlgebraicGeometry.restriction_isEquivalenceRelation`).  So no hypothesis
beyond those of the tag is needed, and the two steps compose into a single statement.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.isEquivalenceRelation_cohenMacaulayRestriction`: the restriction to the
  Cohen–Macaulay open is again an equivalence relation.
* `AlgebraicGeometry.exists_affine_slice_cohenMacaulayRestriction`: every finite type point of
  the Cohen–Macaulay open admits the affine slice of [Stacks Project, Tag 04N0].

## Implementation notes

The statement names the restriction through `AlgebraicGeometry.GroupoidScheme.restrict`, the
realization built by `Classical.choice`, because that is the groupoid for which
[Stacks Project, Tag 0460] is stated here; the `let` bindings in the statement follow the shape
of the four part-(5) results of that tag.

What remains of the proof of [Stacks Project, Tag 0489] after this file is Step 3: the
coproduct `∐_u U'_u` of the slices over the finite type points of the Cohen–Macaulay open, the
fact that its reach map is surjective — every finite type point is in the image of its own
slice's reach map, and the finite type points are dense — and the realization of that coproduct
as an object of the site.  That is what
`Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` still carries.

## References

* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/-- **The restriction of an equivalence-relation groupoid to its Cohen–Macaulay open is again
an equivalence relation.**  This is `AlgebraicGeometry.restriction_isEquivalenceRelation` for
the open of [Stacks Project, Tag 0460]. -/
theorem isEquivalenceRelation_cohenMacaulayRestriction (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    let W := cohenMacaulayOpen G
    let g : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
    IsEquivalenceRelation (GroupoidScheme.restrict G g).groupoid.target
      (GroupoidScheme.restrict G g).groupoid.source :=
  restriction_isEquivalenceRelation G _ (GroupoidScheme.restrict G _)

/-- **Steps 1 and 2 of the proof of [Stacks Project, Tag 0489].**  Let `G` be a groupoid scheme
whose target and source are an internal equivalence relation and whose source and target maps
are flat and locally of finite presentation.  Then every finite type point `u` of the
Cohen–Macaulay open of [Stacks Project, Tag 0460] admits an affine slice `g : U' ⟶ U''`, an
immersion locally of finite presentation through `u`, for which the reach map
`h : U' ×_{g, U'', t} R'' ⟶ U''` and the source and target maps of the groupoid restricted
along `g` are flat, locally of finite presentation and locally quasi-finite.

The two Cohen–Macaulay hypotheses of [Stacks Project, Tag 04N0] come from
[Stacks Project, Tag 0460] and its local quasi-finiteness hypothesis on the stabilizer from
`AlgebraicGeometry.locallyQuasiFinite_stabilizer_hom`, so no hypothesis beyond those of
[Stacks Project, Tag 0489] is assumed. -/
theorem exists_affine_slice_cohenMacaulayRestriction (G : GroupoidScheme S)
    [IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [Flat G.target.left]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left] :
    let W := cohenMacaulayOpen G
    let gW : Over.mk (W.ι ≫ G.objects.hom) ⟶ G.objects := Over.homMk W.ι
    let G₁ := (GroupoidScheme.restrict G gW).groupoid
    ∀ (u : G₁.objects.left), AlgebraicGeometry.IsFiniteTypePoint u →
      ∃ (U' : Scheme.{u}) (g : U' ⟶ G₁.objects.left) (u' : U'),
        g u' = u ∧ IsAffine U' ∧ IsImmersion g ∧ LocallyOfFinitePresentation g ∧
        Flat (pullback.snd g G₁.target.left ≫ G₁.source.left) ∧
        LocallyOfFinitePresentation (pullback.snd g G₁.target.left ≫ G₁.source.left) ∧
        LocallyQuasiFinite (pullback.snd g G₁.target.left ≫ G₁.source.left) ∧
        Flat (GroupoidScheme.restrict G₁
          (Over.homMk g : Over.mk (g ≫ G₁.objects.hom) ⟶ G₁.objects)).groupoid.source.left ∧
        LocallyOfFinitePresentation (GroupoidScheme.restrict G₁
          (Over.homMk g : Over.mk (g ≫ G₁.objects.hom) ⟶ G₁.objects)).groupoid.source.left ∧
        LocallyQuasiFinite (GroupoidScheme.restrict G₁
          (Over.homMk g : Over.mk (g ≫ G₁.objects.hom) ⟶ G₁.objects)).groupoid.source.left ∧
        Flat (GroupoidScheme.restrict G₁
          (Over.homMk g : Over.mk (g ≫ G₁.objects.hom) ⟶ G₁.objects)).groupoid.target.left ∧
        LocallyOfFinitePresentation (GroupoidScheme.restrict G₁
          (Over.homMk g : Over.mk (g ≫ G₁.objects.hom) ⟶ G₁.objects)).groupoid.target.left ∧
        LocallyQuasiFinite (GroupoidScheme.restrict G₁
          (Over.homMk g : Over.mk (g ≫ G₁.objects.hom) ⟶ G₁.objects)).groupoid.target.left := by
  intro W gW G₁ u hu
  have _ : IsEquivalenceRelation G₁.target G₁.source :=
    isEquivalenceRelation_cohenMacaulayRestriction G
  have _ : LocallyOfFinitePresentation G₁.source.left :=
    restricted_source_locallyOfFinitePresentation G
  have _ : LocallyOfFinitePresentation G₁.target.left :=
    restricted_target_locallyOfFinitePresentation G
  exact exists_affine_slice_locallyQuasiFinite G₁ u hu
    (restricted_source_cohenMacaulay G) (restricted_target_cohenMacaulay G)

end AlgebraicGeometry

end
